Require Import String.
Require Import List.
Require Import Sets.Ensembles.

Import ListNotations.

Parameter bytes: Type.

(* Agents *)

Inductive agent := 
    | Peer : nat -> agent 
    | Attacker : agent.

Definition eqb (A B: agent) :=
    match A, B with
        | Peer i, Peer j => Nat.eqb i j
        | Attacker, Attacker => true 
        | _, _ => false 
    end.

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
    | synth_tuple Xs: (forall X, List.In X Xs -> synth H X) -> synth H (Tuple Xs).

Lemma not_synth_MAC:
    forall H X, ~ (H (MAC X)) -> ~ synth H (MAC X).
Proof.
    intros H X. intros HnotMAC Hsynth.
    inversion Hsynth. subst. apply HnotMAC. apply H0.
Qed.

Lemma can_send_MAC:
    forall H X, synth H (MAC X) -> H (MAC X).
Proof.
    intros H X. intro Hsynth.
    inversion Hsynth. subst. auto.
Qed.
    
(* Events *)

Variant visibility :=
    | Publicly  : agent ->  agent -> visibility 
    | Privately :           agent -> visibility.

Record event := E { mode: visibility ; payload: msg }.

Definition publicly A B msg := E (Publicly A B) msg.
Definition privately A msg := E (Privately A) msg.

Definition format_index index := Atom (inr (Index index)).
Definition format_nonce nonce := Atom (inr (Nonce nonce)).

Definition privately_index A index := privately A (format_index index).
Definition privately_nonce A nonce := privately A (format_nonce nonce).

Definition format_Msg req index pc := Tuple [Atom (inl TagMsg) ; Atom (inl (Literal req)) ; 
    Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_RespFast req resp index pc := Tuple [Atom (inl TagRespFast) ; Atom (inl (Literal req)) ; 
    Atom (inl (Literal resp)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_ChallengeRequest n0 := Tuple [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce n0))].
Definition format_ChallengeReply req n0 index pc := Tuple [Atom (inl TagChallengeReply) ; Atom (inl (Literal req)) ;
    Atom (inr (Nonce n0)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_RespSlow req resp index pc := Tuple [Atom (inl TagRespSlow) ; Atom (inl (Literal req)) ; 
    Atom (inl (Literal resp)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].

Definition format_MAC src dest msg :=
    Tuple [ msg ; MAC ( Tuple [ Atom (inl (Agent src)) ; Atom (inl (Agent dest)) ; msg ] ) ].

Definition format_MAC_Msg src dest req index pc := 
    format_MAC src dest (format_Msg req index pc).
Definition format_MAC_RespFast src dest req resp index pc :=
    format_MAC src dest (format_RespFast req resp index pc).
Definition format_MAC_ChallengeRequest src dest n0 :=
    format_MAC src dest (format_ChallengeRequest n0).
Definition format_MAC_ChallengeReply src dest req n0 index pc :=
    format_MAC src dest (format_ChallengeReply req n0 index pc).
Definition format_MAC_RespSlow src dest req resp index pc :=
    format_MAC src dest (format_RespSlow req resp index pc).

Definition publicly_Msg A B req index pc := 
    publicly A B (format_MAC_Msg A B req index pc).
Definition publicly_RespFast A B req resp index pc := 
    publicly A B (format_MAC_RespFast A B req resp index pc).
Definition publicly_ChallengeRequest A B n0 := 
    publicly A B (format_MAC_ChallengeRequest A B n0).
Definition publicly_ChallengeReply A B req n0 index pc := 
    publicly A B (format_MAC_ChallengeReply A B req n0 index pc).
Definition publicly_RespSlow A B req resp index pc := 
    publicly A B (format_MAC_RespSlow A B req resp index pc).

Definition capture := list event.

Parameter index_seed: agent -> string.
Inductive init_state: agent -> Ensemble msg :=
    | init_state_index: forall A s, s = index_seed A -> init_state A (format_index s).

Inductive knows: agent -> capture -> Ensemble msg :=
    | knows_init A m: init_state A m -> knows A [] m 
    | knows_attacker A B X evs: knows Attacker ( publicly A B X :: evs ) X
    | knows_privately A X evs: knows A ( privately A X :: evs ) X
    | knows_publicly A B X evs: knows A ( publicly A B X :: evs ) X
    | knows_later A e evs m: knows A evs m -> knows A ( e :: evs ) m.

Definition fresh_index B evs index := not ( analz (knows B evs) (Atom (inr (Index index))) ).
Definition fresh_nonce A evs n0 := not ( analz (knows A evs) (Atom (inr (Nonce n0))) ).

Parameters A B: agent.
Definition evs_ex := [ publicly_ChallengeRequest A B 42].
Lemma f:
    fresh_nonce A evs_ex 42 -> False.
Proof.
    unfold fresh_nonce. intro H. apply H.
    unfold evs_ex. unfold publicly_ChallengeRequest.
    unfold format_ChallengeRequest. 
    apply analz_tuple with (Xs := [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42))]) ; try firstorder.
    apply analz_tuple with (Xs := [Tuple [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42)) ] ; 
        MAC (Tuple [Atom (inl (Agent A)) ; Atom (inl (Agent B)) ; Tuple [ Atom (inl TagChallengeRequest) ; Atom (inr (Nonce 42))]])]) ; try firstorder.
    apply analz_init. unfold In. apply knows_publicly.
Qed.

Lemma fB:
    fresh_nonce B evs_ex 42.
Proof.
    unfold fresh_nonce. unfold evs_ex.
    intro H. inversion H.
    (* premier lemme : analz Empty_set = Empty_set
        deuxième lemme : knows B evs_ex = Empty_set *)
Admitted.

Inductive parts (X: msg) (H: Ensemble msg): Prop :=
    | parts_init: In msg H X -> parts X H
    | parts_tuple Xs: parts (Tuple Xs) H -> List.In X Xs -> parts X H
    | parts_mac: parts (MAC X) H -> parts X H.

Inductive used (m: msg): capture -> Prop :=
    | used_init A: parts m (init_state A) -> used m []
    | used_now ev evs: parts m (Singleton msg ev.(payload)) -> used m (ev :: evs)
    | used_later ev evs: used m evs -> used m (ev :: evs).

Definition unique m evs :=
    ~ used m evs \/ (exists pre suff ev, evs = pre ++ ev :: suff 
                        /\ ~ used m pre /\ ~ used m suff 
                        /\ m = ev.(payload)). 

Record local_state := LS {
        _PC: agent -> option nat ;
        _index: agent -> option string ;
        _nonce: agent -> nat -> bool
    }.
Definition global_state := agent -> local_state.

Definition lookup_PC (sigma: global_state) A B := (sigma A).(_PC) B.
Definition lookup_index (sigma: global_state) A B := (sigma A).(_index) B.
Definition test_nonce (sigma: global_state) A B n := (sigma A).(_nonce) B n.

Definition update_PC (sigma: global_state) A B new_pc :=
    fun A' => 
        if eqb A' A then 
            let update_new_PC B' := if eqb B' B then Some new_pc 
                        else (sigma A).(_PC) B' 
            in
            LS update_new_PC (sigma A).(_index) (sigma A).(_nonce)
        else sigma A'.

Definition update_index (sigma: global_state) A B new_index :=
    fun A' =>
        if eqb A' A then 
            let update_new_index B' := if eqb B' B then Some new_index 
                        else (sigma A).(_index) B' 
            in
            LS (sigma A).(_PC) update_new_index (sigma A).(_nonce)
        else sigma A'.

Definition update_PC_index (sigma: global_state) A B new_pc new_index :=
    update_index (update_PC sigma A B new_pc) A B new_index.
    
Definition set_nonce (sigma: global_state) A B new_nonce :=
    fun A' =>
        if eqb A' A then 
            let set_new_nonce B' := if eqb B' B then (fun n => Nat.eqb n new_nonce)
                        else (sigma A).(_nonce) B'
            in
            LS (sigma A).(_PC) (sigma A).(_index) set_new_nonce
        else sigma A'.

Definition init_global_state (seed: agent -> string): global_state := 
    fun A => LS 
        ( fun B => if eqb A B then Some 0 else None ) 
        ( fun B => (if eqb A B then Some (seed A) else None) ) 
        ( fun _ _ => false ).

Definition saved_index sigma A B index := Some index = lookup_index sigma A B.
Definition saved_PC sigma A B pc := Some pc = lookup_PC sigma A B.

Inductive Network: global_state -> capture -> Prop :=
    | Network_Attack: forall sigma evs X B,
        Network sigma evs ->
        synth (analz (knows Attacker evs)) X ->
        Network sigma ( publicly Attacker B X :: evs )
    
    | Network_init: forall sigma,
        sigma = init_global_state index_seed ->
        Network sigma []

    | Network_reset: forall sigma evs B index_B sigma1 sigma2,
        Network sigma evs -> 
        fresh_index B evs index_B ->
        sigma1 = update_index sigma B B index_B ->
        sigma2 = update_PC sigma1 B B 0 ->
        Network sigma2 ( privately_index B index_B :: evs )

    | Network_Msg: forall sigma evs A B req index_B pc_B sigma1,
        Network sigma evs -> 
        saved_index sigma B B index_B -> 
        saved_PC sigma B B pc_B ->
        sigma1 = update_PC sigma B B (pc_B + 1) ->
        Network sigma1 ( publicly_Msg B A req index_B pc_B :: evs )
    
    | Network_RespFast: forall sigma evs A B B' index_B pc_B req resp pc sigma1,
        Network sigma evs -> 
        List.In (publicly B' A (format_MAC_Msg B A req index_B pc_B)) evs ->
        saved_index sigma A B index_B ->
        saved_PC sigma A B pc -> pc < pc_B -> 
        sigma1 = update_PC sigma A B pc_B ->
        Network sigma1 ( publicly_RespFast A B req resp index_B pc_B :: evs )
        
    | Network_ChallengeRequest: forall sigma evs A B B' index_B pc_B req n0,
        Network sigma evs -> 
        List.In (publicly B' A (format_MAC_Msg B A req index_B pc_B)) evs ->
        fresh_nonce A evs n0 ->
        Network sigma 
            ( privately_nonce A n0 :: publicly_ChallengeRequest A B n0 :: evs ) 
        
    | Network_ChallengeReply: forall sigma evs A A' B n0 req index_B sigma1 sigma2 sigma3,
        Network sigma evs -> 
        List.In (publicly A' B (format_MAC_ChallengeRequest A B n0)) evs ->
        test_nonce sigma B A n0 = false ->
        fresh_index B evs index_B ->
        sigma1 = update_index sigma B B index_B ->
        sigma2 = update_PC sigma1 B B 0 ->
        sigma3 = set_nonce sigma2 B A n0 ->
        Network sigma3
            ( privately_index B index_B :: 
                publicly_ChallengeReply B A req n0 index_B 0 :: evs ) 
                        
    | Network_RespSlow: forall sigma evs A B B' n0 index_B pc_B req resp sigma1 sigma2,
        Network sigma evs -> 
        List.In (publicly_ChallengeRequest A B n0) evs ->
        List.In (publicly B' A (format_MAC_ChallengeReply B A req n0 index_B pc_B)) evs ->
        sigma1 = update_index sigma A B index_B ->
        sigma2 = update_PC sigma1 A B pc_B ->
        Network sigma2 ( publicly_RespSlow A B req resp index_B pc_B :: evs ).


(* Théorèmes montrant que les prédicats Network_Msg, Network_reset et Network_ChallengeRequest peuvent toujours se faire *)

Lemma Msg_always_possible:
    forall sigma evs B, Network sigma evs -> 
        (exists index, saved_index B B index sigma) /\ (exists pc, saved_PC B B pc sigma).
Admitted.

Theorem can_Msg:
    forall sigma evs A B req, Network sigma evs -> 
        exists sigma1 evs' index pc, Network sigma1 evs' /\ List.In (publicly_Msg B A req index pc) evs'
            /\ (exists pre, evs' = pre ++ evs).
Proof.
    intros sigma evs A B req. intro Hnetwork.
    pose proof (Msg_always_possible sigma evs B Hnetwork) as ([index Hindex] & [pc Hpc]).
    eexists. eexists. exists index. exists pc. split.
    - eapply Network_Msg ; eauto.
    - split ; try firstorder.
        exists [publicly_Msg B A req index pc]. auto.
Qed.

Lemma reset_always_possible:
    forall sigma evs B, Network sigma evs -> (exists index, fresh_index B evs index).
Admitted.

Theorem can_reset:
    forall sigma evs B, Network sigma evs -> 
        exists sigma1 evs' index, Network sigma1 evs' /\ List.In (privately_index B B index) evs' 
                /\ (exists pre, evs' = pre ++ evs).
Admitted.

Lemma ChallengeRequest_always_possible:
    forall sigma evs A B req index pc, Network sigma evs ->
        List.In ( publicly_Msg B A req index pc ) evs -> (exists n0, fresh_nonce A evs n0).
Admitted.

Theorem can_Challenge:
    forall sigma evs A B req index pc, Network sigma evs -> List.In ( publicly_Msg B A req index pc ) evs ->
        exists sigma1 evs' n0, Network sigma1 evs' /\ List.In (publicly_ChallengeRequest A B n0) evs'
            /\ (exists pre, evs' = pre ++ evs).
Admitted.

(* Théorèmes de spoofing *)

Theorem spoofing_RespFast:
    forall sigma evs A B req resp index pc,
        Network sigma evs ->
        List.In (publicly_RespFast A B req resp index pc) evs ->
        exists sigma1 evs', List.In (publicly_RespFast A B req resp index pc) evs' 
            /\ List.In (publicly Attacker A (format_MAC_Msg A B req index pc)) evs' 
            /\ Network sigma1 evs'.
Admitted.

(* Théorèmes d'unicité des messages *)

Lemma compatibiliy_knows_in: forall evs A B X,
    List.In (publicly A B X) evs -> knows Attacker evs X.
Proof.
    intros evs A B X. intro HIn.
    apply in_split in HIn as [l1 [l2 HIn]]. subst.
    induction l1.
    - simpl. apply knows_attacker.
    - rewrite <- app_comm_cons. apply knows_later. assumption.
Qed.

Theorem replay: forall sigma evs A B X, 
    Network sigma evs -> 
    List.In (publicly A B X) evs ->
    forall C, Network sigma ( publicly Attacker C X :: evs ).
Proof.
    intros sigma evs A B X. intros Hnetwork HIn. intro C.
    apply Network_Attack ; try auto.
    apply synth_init. unfold In. apply analz_init. unfold In.
    eapply compatibiliy_knows_in. eauto.
Qed.

Theorem Msg_unicity:
    forall sigma evs A B index pc req, 
        Network sigma evs ->
        unique ( format_MAC_Msg A B req index pc ) evs.
Admitted.

Theorem RespFast_unicity:
    forall sigma evs index pc A A' B B' req req' resp resp',
        Network sigma evs ->
        List.In ( publicly_RespFast A B req resp index pc ) evs ->
        List.In ( publicly_RespFast A' B' req' resp' index pc ) evs ->
        A = A' /\ B = B' /\ req = req' /\ resp = resp'.
Admitted.

Theorem ChallengeRequest_unicity:
    forall sigma evs A n0 B B',
        Network sigma evs ->
        List.In ( publicly_ChallengeRequest A B n0 ) evs ->
        List.In ( publicly_ChallengeRequest A B' n0 ) evs ->
        B = B'.
Admitted.

Theorem ChallengeReply_unicity:
    forall sigma evs n0 A A' B B' index index' pc pc' req req',
        Network sigma evs ->
        List.In ( publicly_ChallengeReply A B n0 req index pc ) evs ->
        List.In ( publicly_ChallengeReply A' B' n0 req' index' pc' ) evs ->
        A = A' /\ B = B' /\ req = req' /\ index = index' /\ pc = pc'.
Admitted.

Theorem RespSlow_unicity:
    forall sigma evs index pc A A' B B' req req' resp resp',
        Network sigma evs ->
        List.In ( publicly_RespSlow A B req resp index pc ) evs ->
        List.In ( publicly_RespSlow A' B' req' resp' index pc ) evs ->
        A = A' /\ B = B' /\ req = req' /\ resp = resp'.
Admitted.