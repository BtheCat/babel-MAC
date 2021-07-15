Parameter key: Type.
Parameter bytes: Type.
Parameter hostname: Type.

Parameter process: bytes -> bytes.



Inductive event: Type :=
  | Request: hostname -> hostname -> bytes -> event
  | Response: hostname -> hostname -> bytes -> bytes -> event
  | Corrupted: hostname -> event.

Axiom log: Type.

Definition asn := event -> Prop. (* TODO: should be [log -> Prop] *)

Axiom Level_Low : forall A, A -> asn.
Arguments Level_Low [_] a.

Definition isEvent (e: event): asn :=
  fun e' => e = e'. (* TODO: should be [Logged e] *)

Definition RecvRequest (a b: hostname)(req: bytes): asn :=
  fun e => e = Request a b req \/ e = Corrupted(a) \/ e = Corrupted(b).

Definition RecvResponse (a b: hostname)(req resp: bytes): asn :=
  fun e => e = Response a b req resp \/ e = Corrupted(a) \/ e = Corrupted(b).



Inductive Sig: Type -> Type :=
(* Assertions *)
| Assume: asn -> Sig unit
| Assert: asn -> Sig unit
(* Cryptographic operations *)
| MAC: forall A, key -> A -> Sig bytes
| Verify: forall A, key -> A -> bytes -> Sig unit
| Fresh_key: hostname -> hostname -> Sig key
(* Network I/O *)
| Send: forall A, hostname -> A -> Sig unit
| Receive: forall A, Sig A.

Arguments MAC [_] k a.
Arguments Verify [_] k a b.
Arguments Send [_] h msg.

Inductive M (X: Type) :=
  | ret: X -> M X
  | op: forall O, Sig O -> (O -> M X) -> M X.

Arguments ret [_] v.
Arguments op [_] [_] s k.

Notation "'assume!' a" := (op (Assume a) (@ret _)) (at level 10).
Notation "'assert!' a" := (op (Assert a) (@ret _)) (at level 10).
Notation "'mac!' k m" := (op (MAC k m) (@ret _)) (at level 10, k,m at next level).
Notation "'verify!' k v m" := (op (Verify k v m) (@ret _)) (at level 10, k,v,m at next level).
Notation "'fresh_key!' a b" := (op (Fresh_key a b) (@ret _)) (at level 10, a, b at next level).
Notation "'send!' a m" := (op (Send a m) (@ret _)) (at level 10, a, m at next level).
Notation "'receive!' T" := (op (Receive T) (@ret _)) (at level 10, T at next level).

Fixpoint bind {X Y} (m: M X)(mf: X -> M Y): M Y :=
  match m with
  | ret v => mf v
  | op s k => op s (fun o => bind (k o) mf)
  end.

Notation "'let!' x := c1 'in' c2" := (@bind _ _ c1 (fun x => c2))
    (at level 61, x pattern, c1 at next level, right associativity).

Notation "e1 ;; e2" := (@bind _ _ e1 (fun _ => e2))
    (at level 61, right associativity).

Inductive requestMAC := Req (req: bytes).
Inductive responseMAC := Resp (req: bytes)(resp: bytes).

Definition client (a b: hostname)(k: key)(req: bytes): M unit :=
  assume! (isEvent (Request a b req)) ;;
  let! mac := mac! k (Req req) in
  send! b (req, mac) ;;
  let! (resp, mac) := receive! (bytes * bytes) in
  verify! k (Resp req resp) mac ;;
  assert! (RecvResponse a b req resp).

Definition server (a b: hostname)(k: key): M unit :=
  let! (req, mac) := receive! (bytes * bytes) in
  verify! k (Req req) mac ;;
  assert! (RecvRequest a b req) ;;
  let resp := process req in
  assume! (isEvent (Response a b req resp)) ;;
  let! mac := mac! k (Resp req resp) in
  send! a (resp, mac).

Axiom triple : forall X, asn -> M X -> (X -> asn) -> Prop.

Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").

Parameter spec_triple: forall (P P': asn) X (Q Q': X -> asn) (m: M X),
    triple _ P m Q ->
    (forall e, P' e -> P e) ->
    (forall x e, Q x e -> Q' x e) ->
    triple _ P' m Q'.

Parameter spec_ret: forall X x,
    triple _ (fun _ => True) (@ret X x) (fun x' _ => x = x').
Parameter spec_bind: forall X Y (e1: M X)(e2: X -> M Y) P (Q: X -> asn) R,
    {{ P }} e1 {{ v ; Q v }} ->
    (forall v, triple _ (Q v) (e2 v) R) ->
    (* {{ P }} (let! v := e1 in e2 v) {{ R }} *)
    triple _ P (let! v := e1 in e2 v) R.

Parameter spec_assert: forall P,
  {{ P }} assert! P {{ _ ; fun _ => True }}.
Parameter spec_assume: forall P Q,
  {{ P }} assume! Q {{ _ ; fun e => P e /\ Q e }}.


(* Opponent API *)

Parameter spec_mac: forall k A (a: A),
    {{ Level_Low (k, a) }} mac! k a {{ m ; Level_Low m }}.
Parameter spec_verify: forall k A (a: A) m,
    {{ Level_Low (k, a, m) }} verify! k a m {{ _ ; fun _ => True }}.
Parameter spec_fresh_key: forall a b,
    {{ Level_Low (a, b) }} fresh_key! a b {{ k ; Level_Low k }}.

Parameter spec_send: forall A (a: A) h,
    {{ Level_Low (a, h) }} send! h a {{ _ ; fun _ => True }}.
Parameter spec_receive: forall A,
    {{ fun _ => True }} receive! A {{ a ; Level_Low a }}.

Record aRPC := { impl_client: bytes -> M unit;
                 impl_server: M unit;
                 release_client: M key;
                 release_server: M key }.

Definition setup (a b: hostname): M aRPC :=
  let! k := fresh_key! a b in
  ret (Build_aRPC (fun req => client a b k req)
                  (server a b k)
                  (assume! (isEvent (Corrupted a)) ;; ret k)
                  (assume! (isEvent (Corrupted b)) ;; ret k)).

Record spec_aRPC (rpc: aRPC) :=
  { spec_client: forall req,
      {{ Level_Low req }} rpc.(impl_client) req {{ _ ; fun _ => True }} ;
    spec_server:
      {{ fun _ => True }} rpc.(impl_server) {{ _ ; fun _ => True }} ;
    spec_release_client:
      {{ fun _ => True }} rpc.(release_client)  {{ k ; Level_Low k }};
    spec_release_server:
      {{ fun _ => True }} rpc.(release_server) {{ k ; Level_Low k }} }.

(* NOT USEFUL! *)
(*
Axiom IO : Type.

Parameter attacker: (hostname -> hostname -> M (* { rpc : *) aRPC (* | spec_aRPC rpc } *)) -> IO -> M unit.

Theorem correctness: forall io, triple _
                                       (fun _ => True)
                                       (attacker setup io)
                                       (fun _ _ => True).
*)
