Require Import String.
Require Import List.
Require Import Sets.Ensembles.

Import ListNotations.

Parameter bytes: Type.

(* Agents *)

Inductive agent := 
    | Peer : nat -> agent 
    | Attacker : agent.

(* Messages *)

Variant public :=
    | Literal : bytes -> public 
    | Agent : agent -> public
    | PC : nat -> public 
    | Msg : public
    | RespFast : public 
    | ChallengeRequest : public 
    | ChallengeReply : public
    | RespSlow : public.

Variant private :=
    | Nonce : nat -> private 
    | Index : string -> private.
 
Inductive msg :=
    | Tuple : list msg -> msg 
    | MAC : msg -> msg
    | Public :> public -> msg
    | Private :> private -> msg.

Inductive analz (H: Ensemble msg) (X: msg): Prop :=
    | analz_init: In msg H X -> analz H X
    | analz_tuple Xs: analz H (Tuple Xs) -> List.In X Xs -> analz H X.

Inductive synth (H: Ensemble msg): Ensemble msg :=
    | synth_init X: In msg H X -> synth H X
    | synth_public p: synth H (Public p)
    | synth_tuple Xs: (forall X, List.In X Xs -> synth H X) -> synth H (Tuple Xs)
    | synth_mac X: synth H X -> synth H (MAC X).

Inductive parts (X: msg) (H: Ensemble msg): Prop :=
    | parts_init: In msg H X -> parts X H
    | parts_tuple Xs: parts (Tuple Xs) H -> List.In X Xs -> parts X H
    | parts_mac: parts (MAC X) H -> parts X H.
    
(* Events *)

Variant visibility :=
    | Publicly  : agent ->  agent -> visibility 
    | Privately :           agent -> visibility.

Record event := E { mode: visibility ; payload: msg }.

Definition publicly A B msg := E (Publicly A B) msg.
Definition privately A msg := E (Privately A) msg.

Definition format_index B index := Tuple [(Agent B: msg) ; (Index index: msg)].
Definition format_PC B pc := Tuple [(Agent B: msg) ; (PC pc: msg)].

Definition privately_index A B index := privately A (format_index B index).
Definition privately_PC A B pc := privately A (format_PC B pc).

Definition format_Msg req index pc := Tuple [Public Msg ; Public (Literal req) ; 
    Private (Index index) ; Public (PC pc)].
Definition format_RespFast req resp index pc := Tuple [Public RespFast ; Public (Literal req) ; 
    Public (Literal resp) ; Private (Index index) ; Public (PC pc)].
Definition format_ChallengeRequest n0 := Tuple [Public ChallengeRequest ; Private (Nonce n0)].
Definition format_ChallengeReply req n0 index pc := Tuple [Public ChallengeReply ; Public (Literal req) ;
    Private (Nonce n0) ; Private (Index index) ; Public (PC pc)].
Definition format_RespSlow req resp index pc := Tuple [Public RespSlow ; Public (Literal req) ; 
    Public (Literal resp) ; Private (Index index) ; Public (PC pc)].

Definition publicly_Msg A B req index pc := 
    let msg := format_Msg req index pc in publicly A B (Tuple [msg ; MAC msg]).
Definition publicly_RespFast A B req resp index pc := 
    let msg := format_RespFast req resp index pc in publicly A B (Tuple [msg ; MAC msg]).
Definition publicly_ChallengeRequest A B n0 := 
    let msg := format_ChallengeRequest n0 in publicly A B (Tuple [msg ; MAC msg]).
Definition publicly_ChallengeReply A B req n0 index pc := 
    let msg := format_ChallengeReply req n0 index pc in publicly A B (Tuple [msg ; MAC msg]).
Definition publicly_RespSlow A B req resp index pc := 
    let msg := format_RespSlow req resp index pc in publicly A B (Tuple [msg ; MAC msg]).

Definition capture := list event.

Inductive init_state: agent -> Ensemble msg :=
    | init_state_PC: forall A B, init_state A (format_PC B 0)
    | init_state_index: forall A s, init_state A (format_index A s).

Inductive knows: agent -> capture -> Ensemble msg :=
    | knows_init A m: init_state A m -> knows A [] m 
    | knows_attacker A B X evs: knows Attacker ( publicly A B X :: evs ) X
    | knows_privately A X evs: knows A ( privately A X :: evs ) X
    | knows_publicly A B X evs: knows A ( publicly A B X :: evs ) X
    | knows_later A e evs m: knows A evs m -> knows A ( e :: evs ) m.

Inductive used (m: msg): capture -> Prop :=
    | used_init A: parts m (init_state A) -> used m []
    | used_now ev evs: parts m (Singleton msg ev.(payload)) -> used m (ev :: evs)
    | used_later ev evs: used m evs -> used m (ev :: evs).

Definition fresh_index B evs index := not ( analz (knows B evs) (Index index) ).
Definition fresh_nonce A evs n0 := not ( analz (knows A evs) (Nonce n0) ).

(* Parameters A B: agent.
Definition evs := [ publicly_ChallengeRequest A B 42].
Lemma f:
    fresh_nonce A evs 42 -> False.
Proof.
    unfold fresh_nonce. intro H. apply H.
    assert ( List.In (Private (Nonce 42)) [Public ChallengeRequest ; Private (Nonce 42) ]  ).
    firstorder.
    
    assert ( List.In (Tuple [Public ChallengeRequest ; Private (Nonce 42)]) 
        [Tuple [Public ChallengeRequest ; Private (Nonce 42) ] ; 
            MAC (Tuple [Public ChallengeRequest ; Private (Nonce 42)])]  ).
    firstorder.
    eapply analz_tuple ; eauto.
    eapply analz_tuple ; eauto. 
    apply analz_init. unfold In.
    apply knows_publicly.
Qed. *)

Inductive saved (A: agent) (P Q: msg -> Prop): capture -> Prop :=
    | saved_now m evs: P m -> Q m -> saved A P Q ( (privately A m) :: evs )
    | saved_later A' m evs: (A = A' -> not (P m)) -> saved A P Q evs -> saved A P Q ( (privately A' m) :: evs )
    | saved_skip A' B m evs: saved A P Q evs -> saved A P Q ( (publicly A' B m) :: evs ).

Definition saved_PC A B pc evs :=
    saved A (fun m => exists pc', m = format_PC B pc') (fun m => m = format_PC B pc) evs.

Definition saved_index A B index evs :=
    saved A (fun m => exists index', m = format_index B index') 
        (fun m => m = format_index B index) evs.

Inductive Network: list event -> Prop :=
    | Network_Attack: forall evs X B,
        Network evs ->
        synth (analz (knows Attacker evs)) X ->
        Network ( publicly Attacker B X :: evs )
    
    | Network_init: Network []

    | Network_reset: forall evs B index_B,
        Network evs -> 
        fresh_index B evs index_B ->
        Network ( privately_index B B index_B :: 
                privately_PC B B 0 :: evs )

    | Network_Msg: forall evs A B req index_B pc_B,
        Network evs -> 
        saved_index B B index_B evs -> 
        saved_PC B B pc_B evs ->
        Network ( privately_PC B B (pc_B + 1) ::
                publicly_Msg B A req index_B pc_B :: evs )
    
    | Network_RespFast: forall evs A B index_B pc_B req resp pc,
        Network evs -> 
        List.In (publicly_Msg B A req index_B pc_B) evs ->
        saved_index A B index_B evs ->
        saved_PC A B pc evs -> pc < pc_B -> 
        Network ( privately_PC A B pc_B ::
                publicly_RespFast A B req resp index_B pc_B :: evs )
        
    | Network_ChallengeRequest: forall evs A B index_B pc_B req n0,
        Network evs -> 
        List.In (publicly_Msg B A req index_B pc_B) evs ->
        fresh_nonce A evs n0 ->
        Network ( publicly_ChallengeRequest A B n0 :: evs )
        
    | Network_ChallengeReply: forall evs A B n0 req index_B,
        Network evs -> 
        List.In (publicly_ChallengeRequest A B n0) evs ->
        fresh_index B evs index_B ->
        Network ( privately_index B B index_B ::
                privately_PC B B 0 :: 
                publicly_ChallengeReply B A req n0 index_B 0 :: evs ) 
                        
    | Network_RespSlow: forall evs A B n0 index_B pc_B req resp,
        Network evs -> 
        List.In (publicly_ChallengeRequest A B n0) evs ->
        List.In (publicly_ChallengeReply B A req n0 index_B pc_B) evs ->
        Network ( privately_index A B index_B ::
                privately_PC A B pc_B :: 
                publicly_RespSlow A B req resp index_B pc_B :: evs ).