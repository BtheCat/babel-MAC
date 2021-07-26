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
    | TagMsg : public
    | TagRespFast : public 
    | TagChallengeRequest : public 
    | TagChallengeReply : public
    | TagRespSlow : public.

Variant private :=
    | Nonce : nat -> private 
    | Index : string -> private.
 
Inductive msg :=
    | Tuple : list msg -> msg 
    | MAC : msg -> msg
    | Atom : public + private -> msg. 

(* Le prédicat inductif 'analz' permet de générer un ensemble de message à partir d'un ensemble de message de départ.
    - tout message appartenant à l'ensemble de départ est analysé
    - si un message analysé est un tuple, alors on peut analyser tout les sous messages de ce tuple
    - il n'y a pas d'autres prédicat récursif donc ces deux règles suffisent
    - les prédicats unitaires peuvent être analysé du moment qu'ils sont présent dans un Tuple grâce à la deuxième règle
    - on ne peut pas analyser le contenu d'un MAC *)

Inductive analz (H: Ensemble msg) (X: msg): Prop :=
    | analz_init: In msg H X -> analz H X
    | analz_tuple Xs: analz H (Tuple Xs) -> List.In X Xs -> analz H X.

(* Le prédicat inductif 'synth' permet de générer un ensemble de message synthétisables à partir de messages de départ.
    - tout message de départ est synthétisable
    - n'importe quel message de type Public est synthétisable
    - un tuple est synthétisable lorsque tout les messages qui le compose le sont
    - un mac d'un message synthétisable est synthétisable *)

Inductive synth (H: Ensemble msg): Ensemble msg :=
    | synth_init X: In msg H X -> synth H X
    | synth_public p: synth H (Atom (inl p))
    | synth_tuple Xs: (forall X, List.In X Xs -> synth H X) -> synth H (Tuple Xs)
    | synth_mac X: synth H X -> synth H (MAC X).
    
(* Events *)

Variant visibility :=
    | Publicly  : agent ->  agent -> visibility 
    | Privately :           agent -> visibility.

Record event := E { mode: visibility ; payload: msg }.

Definition publicly A B msg := E (Publicly A B) msg.
Definition privately A msg := E (Privately A) msg.

Definition format_index B index := Tuple [Atom (inl (Agent B)) ; Atom (inr (Index index))].
Definition format_PC B pc := Tuple [Atom (inl (Agent B)) ; Atom (inl (PC pc))].

Definition privately_index A B index := privately A (format_index B index).
Definition privately_PC A B pc := privately A (format_PC B pc).

Definition format_Msg req index pc := [Atom (inl TagMsg) ; Atom (inl (Literal req)) ; 
    Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_RespFast req resp index pc := [Atom (inl TagRespFast) ; Atom (inl (Literal req)) ; 
    Atom (inl (Literal resp)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_ChallengeRequest n0 := [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce n0))].
Definition format_ChallengeReply req n0 index pc := [Atom (inl TagChallengeReply) ; Atom (inl (Literal req)) ;
    Atom (inr (Nonce n0)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_RespSlow req resp index pc := [Atom (inl TagRespSlow) ; Atom (inl (Literal req)) ; 
    Atom (inl (Literal resp)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].

Definition produce_mac msg src dest :=
    MAC ( Tuple ( (Atom (inl (Agent src))) :: (Atom (inl (Agent dest))) :: msg ) ).

Definition publicly_Msg A B req index pc := 
    let msg := format_Msg req index pc in publicly B A (Tuple [Tuple msg ; produce_mac msg B A]).
Definition publicly_RespFast A B req resp index pc := 
    let msg := format_RespFast req resp index pc in publicly A B (Tuple [Tuple msg ; produce_mac msg A B]).
Definition publicly_ChallengeRequest A B n0 := 
    let msg := format_ChallengeRequest n0 in publicly A B (Tuple [Tuple msg ; produce_mac msg A B]).
Definition publicly_ChallengeReply A B req n0 index pc := 
    let msg := format_ChallengeReply req n0 index pc in publicly A B (Tuple [Tuple msg ; produce_mac msg B A]).
Definition publicly_RespSlow A B req resp index pc := 
    let msg := format_RespSlow req resp index pc in publicly A B (Tuple [Tuple msg ; produce_mac msg A B]).

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

Definition fresh_index B evs index := not ( analz (knows B evs) (Atom (inr (Index index))) ).
Definition fresh_nonce A evs n0 := not ( analz (knows A evs) (Atom (inr (Nonce n0))) ).

Parameters A B: agent.
Definition evs := [ publicly_ChallengeRequest A B 42].
Lemma f:
    fresh_nonce A evs 42 -> False.
Proof.
    unfold fresh_nonce. intro H. apply H.
    unfold evs. unfold publicly_ChallengeRequest.
    unfold format_ChallengeRequest. 
    apply analz_tuple with (Xs := [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42))]) ; try firstorder.
    apply analz_tuple with (Xs := [Tuple [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42)) ] ; 
        MAC (Tuple [Atom (inl (Agent A)) ; Atom (inl (Agent B)) ; Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42))])]) ; try firstorder.
    apply analz_init. unfold In. apply knows_publicly.

    (*
    unfold fresh_nonce. intro H. apply H.
    assert ( List.In (Private (Nonce 42)) [Public TagChallengeRequest ; Private (Nonce 42) ]  ).
    firstorder.
    
    assert ( List.In (Tuple [Public TagChallengeRequest ; Private (Nonce 42)]) 
        [Tuple [Public TagChallengeRequest ; Private (Nonce 42) ] ; 
            MAC (Tuple [Public TagChallengeRequest ; Private (Nonce 42)])]  ).
    firstorder.
    eapply analz_tuple ; eauto.
    eapply analz_tuple ; eauto. 
    apply analz_init. unfold In.
    apply knows_publicly.
    *)
Qed.

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


Lemma not_synth_mac:
    forall H X, synth H (MAC X) -> False.
Proof.
Admitted.

Lemma can_send_Mac:
    synth (analz (knows Attacker evs)) (produce_mac (format_ChallengeRequest 42) A B).
Proof.
    unfold evs. unfold publicly_ChallengeRequest.
    apply synth_init. unfold In.
    apply analz_tuple with (Xs:=[Tuple (format_ChallengeRequest 42) ; produce_mac (format_ChallengeRequest 42) A B]) ; try firstorder.
    apply analz_init. unfold In. apply knows_attacker.
Qed.