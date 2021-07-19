Require Import ListSet.
Require Import Ascii.

Parameter nonce: Type.
Parameter bytes: Type.
Parameter hostname: Type.
Parameter key: Type.

Inductive event: Type :=
    | MsgRequest: hostname -> hostname -> bytes -> (nat * nat)%type -> event
    | MsgResponse: hostname -> hostname -> bytes -> bytes -> event 
    | ChallengeRequest: hostname -> hostname -> bytes -> nonce -> event 
    | ChallengeReply: hostname -> hostname -> nonce -> event
    | Corrupted: hostname -> event.

Definition log := set event.
Definition asn := log -> Prop.

Axiom Level_Low : forall A, A -> asn.
Arguments Level_Low [_] a.

Definition Logged (e: event) (L: log): Prop := set_In e L.

Definition isEvent (e: event): asn :=
    fun L => Logged e L.

Definition RecvMsg (a b: hostname) (pc_b index_b: nat) (msg: bytes): asn :=
    fun L => Logged (MsgRequest a b msg (pc_b, index_b)) L \/ Logged (Corrupted b) L.
    

Inductive Sig: Type -> Type :=
    (* Assertions *)
    | Assume: asn -> Sig unit 
    | Assert: asn -> Sig unit 
    (* Cryptographic operations *)
    | MAC: forall A, key -> A -> Sig bytes 
    | Verify: forall A, key -> A -> bytes -> Sig unit 
    | Fresh_key: hostname -> hostname -> Sig key 
    (* Protocol operations *)
    | Fresh_nonce: hostname -> Sig nat
    | Verify_nonce: nonce -> nonce -> Sig unit 
    | Incr_PC: hostname -> Sig nat 
    | Modify_PC_index: hostname -> set nat -> hostname -> (nat * nat)%type -> Sig unit
    | Fresh_index: hostname -> Sig nat 
    | Verify_PC_index: hostname -> (nat * nat)%type -> set nat -> Sig bool
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
Notation "'fresh_nonce!' h" := (op (Fresh_nonce h) (@ret _)) (at level 10, h at next level).
Notation "'verify_nonce!' n0 n" := (op (Verify_nonce n0 n) (@ret _)) (at level 10, n0,n at next level).
Notation "'incr_pc!' h" := (op (Incr_PC h) (@ret _)) (at level 10, h at next level).
Notation "'fresh_index!' h" := (op (Fresh_index h) (@ret _)) (at level 10, h at next level).
Notation "'verify_pc_index! h inds t" := (op (Verify_PC_index h inds t) (@ret _)) (at level 10, h,inds,t at next level).
Notation "'send!' a m" := (op (Send a m) (@ret _)) (at level 10, a, m at next level).
Notation "'receive!' T" := (op (Receive T) (@ret _)) (at level 10, T at next level).

Fixpoint bind {X Y} (m: M X) (mf: X -> M Y): M Y :=
    match m with 
    | ret v => mf v
    | op s k => op s (fun o => bind (k o) mf)
    end.

Notation "'let!' x := c1 'in' c2" := (@bind _ _ c1 (fun x => c2))
    (at level 61, x pattern, c1 at next level, right associativity).

Notation "e1 ;; e2" := (@bind _ _ e1 (fun _ => e2))
    (at level 61, right associativity).

Inductive messageMac := Msg (msg: bytes) (index pc: nat).
Inductive challengeReplyMAC := ChallReply (msg: bytes) (index pc: nat).

Parameter TagChallengeRequest: ascii.
Parameter TagChallengeReply: ascii.

Definition client (a b: hostname) (k: key) (index pc: nat) (msg: bytes): M unit :=
    let! mac := mac! k (Msg msg index pc) in
    send! a (msg, index, pc, mac) ;;
    incr_pc! b ;;
    let! (tagChallReq, n) := receive! (ascii * nat) in
    let! index' := fresh_index! b in
    let! mac := mac! k (ChallReply index' pc) in
    send! a (TagChallengeReply, msg, n, index', pc, mac).

Definition server (a b: hostname) (k: key) (t: set nat): M unit :=
    let! (msg, mac) := receive! (bytes * bytes) in
    verifiy! k (Msg msg index pc) mac ;;
    if verify_pc_index! a (index, pc) t then (
        modify_pc_index! a t b (index, pc)
    ) else (
        let! n0 := fresh_nonce! a in 
        send! b (TagChallengeRequest, n0) ;;
        let! (tagChallReply, msg, n, index, pc, mac) := 
            receive! (ascii * bytes * nonce * nat * nat * bytes) in
        verify! k (ChallReply index' pc) mac ;;
        verify_nonce! n0 n ;;
        modify_pc_index! a t b (index', pc)
    ).