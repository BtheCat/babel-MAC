Require Import ListSet.
Require Import String.
Require Import List.
Require Import Bool.

Parameter key: Type.

(* Agents: 
    - Given a number i, Friend i is the corresponding agent.
    - The malicious agent is modelled by the nullary constructor Spy
    - Most symmetric-key protocols rely on a trusted third party, Server, 
        which has access to all agents' long-term secrets.
*)

Inductive agent := 
    | Friend : nat -> agent 
    | Spy : agent.

Definition eq_agent (A B: agent): bool :=
    match A, B with 
        | Friend i, Friend j => Nat.eqb i j
        | Spy, Spy => true 
        | _, _ => false 
    end.

Parameter shrK : agent -> agent -> key.

(* Messages *)

Inductive msg :=
    | Agent : agent -> msg 
    (*| Tag : string -> msg *)
    | Nonce : nat -> msg 
    | Index : agent -> string -> msg 
    | PC : agent -> nat -> msg 
    | Key : key -> msg 
    | Pair : msg -> msg -> msg 
    | Hash : key -> msg -> msg
    | Number : string -> msg 
    | Msg : string -> msg (* Index *) -> msg (* PC *) -> msg
    | Resp : string -> string -> msg (* Index *) -> msg (* PC *) -> msg
    | ChallengeRequest : msg (* Nonce *) -> msg
    | ChallengeReply : string -> msg (* Nonce *) -> msg (* Number *) -> msg (* PC *) -> msg
    (*| Bad : agent -> msg*).

(* Axiom crypt_secure: forall (k: key) (x: msg), Crypt k x /\ Level_Low x -> Level_Low k. *)

(* Events *)
Inductive event := 
    | Says  : agent ->  agent -> msg -> event 
    | Notes :           agent -> msg -> event.

(* Spy's knowledge *)

Inductive initState: agent -> (msg -> Prop) -> Prop :=
    | initState_Friend i (L: msg -> Prop): L (PC (Friend i) 0) 
            -> L (Index (Friend i) "init") 
            -> initState (Friend i) L.


Inductive analz: msg -> (msg -> Prop) -> Prop :=
    | analz_init X (H: msg -> Prop): (H X) -> analz X H
    | analz_pair_left X Y H: analz (Pair X Y) H -> analz X H
    | analz_pair_right X Y H: analz (Pair X Y) H -> analz Y H
    | analz_hash K X H: analz (Hash K X) H -> analz (Key K) H -> analz X H.

Inductive synth: msg -> (msg -> Prop) -> Prop :=
    | synth_init X (H: msg -> Prop): (H X) -> synth X H
    | synth_agent (a: agent) H: synth (Agent a) H
    | synth_pair X Y H: synth X H -> synth Y H -> synth (Pair X Y) H
    | synth_crypt K X H: synth (Key K) H -> synth X H -> synth (Hash K X) H.

Inductive parts: msg -> (msg -> Prop) -> Prop :=
    | parts_init X (H: msg -> Prop): (H X) -> parts X H
    | parts_pair_left X Y H: parts (Pair X Y) H -> parts X H
    | parts_pair_right X Y H: parts (Pair X Y) H -> parts Y H
    | parts_hash K X H: parts (Hash K X) H -> parts X H.

Lemma analz_implies_parts:
    forall X H, analz X H -> parts X H.
Proof.
    intros X H. intro Hanalz. induction Hanalz.
    - apply parts_init. assumption.
    - apply parts_pair_left with (Y:=Y). assumption.
    - apply parts_pair_right with (X:=X). assumption.
    - apply parts_hash with (K:=K). assumption. 
Qed.

Fixpoint used (evs: list event) (m: msg): Prop :=
    match evs with 
        | nil => False 
        | (Says A B p)::evs' => (parts p (fun m' => m' = m)) \/ used evs' m 
        | (Notes A p)::evs' => (parts p (fun m' => m' = m)) \/ used evs' m 
    end.

Definition gt_nat_option (no mo: option nat): Prop :=
    match no, mo with 
        | Some n, Some m => n > m 
        | _, _ => False 
    end. 

Fixpoint fresh_msg (evs: list event) (A: agent) (m: msg): Prop :=
    match evs with 
        | nil => False 
        | (Says X Y p)::evs' => ( (X = A /\ parts p (fun m' => m' = m)) 
                                    \/ (Y = A /\ parts p (fun m' => m' = m) ) )
                                \/ fresh_msg evs' A m
        | (Notes X p)::evs' => ( X = A /\ parts p (fun m' => m' = m) ) \/ fresh_msg evs' A m
    end. 

Fixpoint get_index (evs: list event) (A B: agent): option string :=
    match evs with
        | nil => None
        | (Notes X (Index Y index_Y))::evs' => 
                if (eq_agent X A) && (eq_agent Y B) then Some index_Y else get_index evs' A B 
        | _::evs' => get_index evs' A B
    end.

Fixpoint get_PC (evs: list event) (A B: agent): option nat :=
    match evs with 
        | nil => None
        | (Notes X (PC Y PC_Y))::evs' =>
                if (eq_agent X A) && (eq_agent Y B) then Some PC_Y else get_PC evs' A B 
        | _::evs' => get_PC evs' A B 
    end. 

Inductive Logged: list event -> Prop :=
    | Logged_init: forall (X: agent), 
        Logged (cons (Notes X (PC X 0)) (cons (Notes X (Index X "init")) nil))

    | Logged_init_msg: forall evs A B index_B PC_B kab messg,
        Logged evs -> kab = shrK A B -> Some PC_B = get_PC evs B B -> Some index_B = get_index evs B B ->
        let messg_msg := Msg messg (Index B index_B) (PC B PC_B) in
        Logged ( cons (Says B A (Pair messg_msg (Hash kab messg_msg)))
                    ( cons (Notes B (PC B (PC_B + 1))) evs ))
    
    | Logged_accept_msg: forall evs A B index_B PC_B kab messg resp,
        let messg_msg := Msg messg (Index B index_B) (PC B PC_B) in
        Logged evs -> In (Says B A (Pair messg_msg (Hash kab messg_msg))) evs ->
            Some index_B = get_index evs A B -> gt_nat_option (Some PC_B) (get_PC evs A B) ->
        let resp_msg := Resp messg resp (Index B index_B) (PC B PC_B) in
        Logged ( cons (Notes A (PC B PC_B)) ( cons (Says A B (Pair resp_msg (Hash kab resp_msg))) evs ) )
        
    | Logged_refuse_msg: forall evs A B index_B PC_B kab messg n0,
        let messg_msg := Msg messg (Index B index_B) (PC B PC_B) in
        Logged evs -> In (Says B A (Pair messg_msg (Hash kab messg_msg))) evs ->
        fresh_msg evs A (Nonce n0) -> let challRequest_msg := ChallengeRequest (Nonce n0) in
        Logged ( cons (Says A B (Pair challRequest_msg (Hash kab challRequest_msg))) evs )
        
    | Logged_chall_reply: forall evs A B n0 kab messg index_B,
        let challRequest_msg := ChallengeRequest (Nonce n0) in 
        Logged evs -> In (Says A B (Pair challRequest_msg (Hash kab challRequest_msg))) evs ->
        fresh_msg evs B (Index B index_B) -> let challReply_msg := ChallengeReply messg (Nonce n0) (Number index_B) (PC B 0) in
        Logged ( cons (Says B A (Pair challReply_msg (Hash kab challReply_msg)))
                    ( cons (Notes B (Index B index_B)) 
                        ( cons (Notes B (PC B 0)) evs ) ) )
                        
    | Logged_chall_accept: forall evs A B n0 kab index_B PC_B messg resp,
        let challReply_msg := ChallengeReply messg (Nonce n0) (Number index_B) (PC B PC_B) in 
        let challRequest_msg := ChallengeRequest (Nonce n0) in
        Logged evs -> In (Says B A (Pair challReply_msg (Hash kab challReply_msg))) evs ->
        In (Says A B (Pair challRequest_msg (Hash kab challRequest_msg))) evs ->
        let resp_msg := Resp messg resp (Index B index_B) (PC B PC_B) in
        Logged ( cons (Says A B (Pair resp_msg (Hash kab resp_msg))) 
                    ( cons (Notes A (Index B index_B)) 
                        ( cons (Notes A (PC B PC_B)) evs ) ) ).
