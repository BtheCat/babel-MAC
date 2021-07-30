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

Lemma refl_eqb:
    forall A, eqb A A = true.
Admitted.

(* Messages *)

Variant public :=
    | Literal : bytes -> public 
    | Agent : agent -> public
    | PC : nat -> public 
    | TagSend : public
    | TagAccept : public 
    | TagChallengeRequest : public 
    | TagChallengeReply : public.

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

Definition format_index B index := Tuple [Atom (inl (Agent B)) ; Atom (inr (Index index))].
Definition format_Accept A B pkt index pc := Tuple [Atom (inl TagAccept) ; 
    Atom (inl (Agent A)) ; Atom (inl (Agent B)) ; Atom (inl (Literal pkt)) ; 
    Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_ChallengeAccept A B n0 index pc := Tuple [Atom (inl TagAccept) ; 
    Atom (inl (Agent A)) ; Atom (inl (Agent B)) ; Atom (inr (Nonce n0)) ; 
    Atom (inr (Index index)) ; Atom (inl (PC pc))].

Definition privately_reset A B index := privately A (format_index B index).
Definition privately_Accept A B pkt index pc := 
    privately A (format_Accept A B pkt index pc).
Definition privately_ChallengeAccept A B n0 index pc := 
    privately A (format_ChallengeAccept A B n0 index pc).

Definition format_Send pkt index pc := Tuple [Atom (inl TagSend) ; Atom (inl (Literal pkt)) ; 
    Atom (inr (Index index)) ; Atom (inl (PC pc))].
Definition format_ChallengeRequest n0 := Tuple [Atom (inl TagChallengeRequest) ; Atom (inr (Nonce n0))].
Definition format_ChallengeReply n0 index pc := Tuple [Atom (inl TagChallengeReply) ;
    Atom (inr (Nonce n0)) ; Atom (inr (Index index)) ; Atom (inl (PC pc))].

Definition format_MAC src dest msg :=
    Tuple [ msg ; MAC ( Tuple [ Atom (inl (Agent src)) ; Atom (inl (Agent dest)) ; msg ] ) ].

Definition format_MAC_Send src dest pkt index pc := 
    format_MAC src dest (format_Send pkt index pc).
Definition format_MAC_ChallengeRequest src dest n0 :=
    format_MAC src dest (format_ChallengeRequest n0).
Definition format_MAC_ChallengeReply src dest n0 index pc :=
    format_MAC src dest (format_ChallengeReply n0 index pc).

Definition publicly_Send A B pkt index pc := 
    publicly A B (format_MAC_Send A B pkt index pc).
Definition publicly_ChallengeRequest A B n0 := 
    publicly A B (format_MAC_ChallengeRequest A B n0).
Definition publicly_ChallengeReply A B n0 index pc := 
    publicly A B (format_MAC_ChallengeReply A B n0 index pc).

Definition capture := list event.

Parameter index_seed: agent -> string.
Inductive init_state: agent -> Ensemble msg :=
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

Definition unique (ev: event) evs :=
    ~ List.In ev evs \/ (exists pre suff, evs = pre ++ ev :: suff 
                        /\ ~ List.In ev pre /\ ~ List.In ev suff). 

Record local_state := LS {
        _PC: agent -> option nat ;
        _index: agent -> option string ;
        _nonce: agent -> nat -> bool
    }.
Definition global_state := agent -> local_state.

Definition lookup_PC (sigma: global_state) A B := (sigma A).(_PC) B.
Definition lookup_index (sigma: global_state) A B := (sigma A).(_index) B.
(* Definition test_nonce (sigma: global_state) A B n := (sigma A).(_nonce) B n. *)

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
    
Definition set_nonce (sigma: global_state) A B new_nonce b :=
    fun A' =>
        if eqb A' A then 
            let set_new_nonce B' := if eqb B' B then 
                            (fun n =>  if Nat.eqb n new_nonce then b else (sigma A).(_nonce) B n)
                        else (sigma A).(_nonce) B'
            in
            LS (sigma A).(_PC) (sigma A).(_index) set_new_nonce
        else sigma A'.

Definition init_global_state (seed: agent -> string): global_state := 
    fun A => LS 
        ( fun B => if eqb A B then Some 0 else None ) 
        ( fun B => (if eqb A B then Some (seed A) else None) ) 
        ( fun _ _ => false ).

(* Definition saved_index sigma A B index := Some index = lookup_index sigma A B.
Definition saved_PC sigma A B pc := Some pc = lookup_PC sigma A B. *)

Definition is_privately_reset A B ev := exists ix, ev = privately_reset A B ix.
Definition is_publicly_Send A ev := exists B pkt ix pc, ev = publicly_Send A B pkt ix pc.
Definition is_publicly_ChallengeRequest A B ev := exists n0, ev = publicly_ChallengeRequest A B n0.
Definition is_privately_ChallengeAccept A B ev := exists n ix pc, ev = privately_ChallengeAccept A B n ix pc.
Definition is_privately_Accept A B ev := exists pkt ix pc, ev = privately_Accept A B pkt ix pc.

Inductive local_index (A B: agent) (ix: string): capture -> Prop :=
    | local_index_init: 
        init_state A (format_index B ix) -> 
        local_index A B ix [] 
    | local_index_now_reset evs: 
        local_index A B ix ( privately_reset A B ix :: evs )
    | local_index_now_ChallengeReply evs n0 pc:
        local_index A B ix ( publicly_ChallengeReply A B n0 ix pc :: evs )
    | local_index_later ev evs: 
        ~ is_privately_reset A B ev -> 
        ~ is_publicly_ChallengeRequest A B ev ->
        local_index A B ix evs -> 
        local_index A B ix (ev :: evs).

Inductive saved_index (A B: agent) (ix: string): capture -> Prop :=
    | saved_index_now evs n0 pc: 
        saved_index A B ix ( privately_ChallengeAccept A B n0 ix pc :: evs )
    | saved_index_later ev evs: 
        ~ is_privately_ChallengeAccept A B ev -> 
        saved_index A B ix evs -> 
        saved_index A B ix (ev :: evs).

Inductive local_PC (A B: agent): nat -> capture -> Prop :=
    | local_PC_init:
        local_PC A B 0 []
    | local_PC_now_reset evs ix:
        local_PC A B 0 ( privately_reset A B ix :: evs )
    | local_PC_now_Send evs pc pkt ix pc':
        local_PC A B pc evs ->
        local_PC A B (pc + 1) ( publicly_Send A B pkt ix pc' :: evs )
    | local_PC_later ev evs pc: 
        ~ is_privately_reset A A ev -> 
        ~ is_publicly_Send A ev ->
        local_PC A B pc evs -> 
        local_PC A B pc (ev :: evs).

Inductive saved_PC (A B: agent): nat -> capture -> Prop :=
    | saved_PC_now_ChallengeAccept evs n0 ix pc:
        saved_PC A B pc ( privately_ChallengeAccept A B n0 ix pc :: evs )
    | saved_PC_now_Accept evs pkt ix pc:
        saved_PC A B (pc + 1) ( privately_Accept A B pkt ix pc :: evs )
    | saved_PC_later ev evs pc:
        ~ is_privately_ChallengeAccept A B ev ->
        ~ is_privately_Accept A B ev ->
        saved_PC A B pc evs ->
        saved_PC A B pc (ev :: evs).

Inductive nonce_inflight (A B: agent) (n0: nat): capture -> Prop :=
    | nonce_inflight_now evs:
        nonce_inflight A B n0 ( publicly_ChallengeRequest A B n0 :: evs )
    | nonce_inflight_later_ChallengeAccept evs n1 ix pc:
        n0 <> n1 ->
        nonce_inflight A B n0 evs ->
        nonce_inflight A B n0 ( privately_ChallengeAccept A B n1 ix pc :: evs )
    | nonce_inflight_later ev evs:
        ~ is_publicly_ChallengeRequest A B ev ->
        ~ is_privately_ChallengeAccept A B ev ->
        nonce_inflight A B n0 evs ->
        nonce_inflight A B n0 (ev :: evs).

Inductive Network: (*global_state ->*) capture -> Prop :=
    | Network_Attack: forall (* sigma *) evs X B,
        Network (* sigma *) evs ->
        synth (analz (knows Attacker evs)) X ->
        Network (* sigma *) ( publicly Attacker B X :: evs )
    
    | Network_init: (*forall sigma,
        sigma = init_global_state index_seed ->*)
        Network (* sigma *) []

    | Network_local_reset: forall (* sigma *) evs A B index_B (* sigma1 sigma2 *),
        Network (* sigma *) evs -> 
        fresh_index B evs index_B ->
        (* sigma1 = update_index sigma B B index_B ->
        sigma2 = update_PC sigma1 B B 0 -> *)
        Network (* sigma2 *) ( privately_reset B A index_B :: evs )

    (* Fix me: miss Network_saved_reset*)

    | Network_Send: forall (* sigma *) evs A B pkt index_B pc_B (* sigma1 *),
        Network (* sigma *) evs -> 
        local_index B A index_B evs -> 
        local_PC B A pc_B evs ->
        (* sigma1 = update_PC sigma B B (pc_B + 1) ->*)
        Network (* sigma1 *) ( publicly_Send B A pkt index_B pc_B :: evs )
    
    | Network_Accept: forall (* sigma *) evs A B B' index_B pc_B pkt pc (* sigma1 *),
        Network (* sigma *) evs -> 
        List.In (publicly B' A (format_MAC_Send B A pkt index_B pc_B)) evs ->
        saved_index A B index_B evs ->
        saved_PC A B pc evs -> pc < pc_B -> 
        (* sigma1 = update_PC sigma A B pc_B -> *)
        Network (* sigma1 *) ( privately_Accept A B pkt index_B pc_B :: evs )
        
    | Network_ChallengeRequest: forall (* sigma *) evs A B n0 (* sigma1 *),
        Network (* sigma *) evs -> 
        fresh_nonce A evs n0 ->
        (* sigma1 = set_nonce sigma A B n0 true -> *)
        Network (* sigma1 *)
            ( publicly_ChallengeRequest A B n0 :: evs ) 
        
    | Network_ChallengeReply: forall (* sigma *) evs A A' B n0 index_B (* sigma1 sigma2 *),
        Network (* sigma *) evs -> 
        List.In (publicly A' B (format_MAC_ChallengeRequest A B n0)) evs ->
        (* test_nonce sigma B A n0 = false ->*)
        fresh_index B evs index_B ->
        (*sigma1 = update_index sigma B B index_B ->
        sigma2 = update_PC sigma1 B B 0 -> *)
        Network (* sigma2 *)
            ( publicly_ChallengeReply B A n0 index_B 0 :: evs )
                
    | Network_ChallengeAccept: forall (* sigma *) evs A B B' n0 index_B pc_B (* sigma1 sigma2 sigma3 *),
        Network (* sigma *) evs ->
        List.In (publicly_ChallengeRequest A B n0) evs ->
        List.In (publicly B' A (format_MAC_ChallengeReply B A n0 index_B pc_B)) evs ->
        nonce_inflight A B n0 evs ->
        (* sigma1 = update_index sigma A B index_B ->
        sigma2 = update_PC sigma1 A B pc_B ->
        sigma3 = set_nonce sigma2 A B n0 false -> *)
        Network (* sigma3 *)
            ( privately_ChallengeAccept A B n0 index_B pc_B :: evs ).

Axiom R: capture -> capture -> Prop.
Definition leq_capture (evs evs': capture) := exists pre, evs' = pre ++ evs.

Lemma R_cons:
    forall ev evs,
        Network (ev :: evs) ->
        R evs (ev :: evs).
Admitted.

Lemma R_leq:
    forall evs evs',
        leq_capture evs evs' ->
        Network evs' ->
        R evs evs'.
Admitted.

Lemma R_proj:
    forall A B evs evs' ix ix' pc pc',
        R evs evs' ->
        saved_index A B ix evs ->
        saved_PC A B pc evs ->
        saved_index A B ix' evs' ->
        saved_PC A B pc' evs' ->
        ix = ix' ->
        pc <= pc'.
Admitted.

(*Lemma invariant_init:
    forall sigma sigma' evs,
        Network sigma evs ->
        Network sigma' evs ->
        R_sigma sigma sigma'.
Proof.
    (*
        On procède par induction sur evs :
        - soit on bump par 1 le pc dans sigma et sigma' donc ok
        - soit on change l'indice, si les nouveaux indices sont égaux, alors les pc sont aussi égaux, 
                sinon on a bien la relation R
        - soit on ne touche à rien
    *)
Admitted.*)

(*Lemma invariant:
    forall sigma sigma' evs evs',
        Network sigma evs ->
        leq_capture evs evs' ->
        Network sigma' evs' ->
        R_sigma sigma sigma'.
Proof.
    (*
        On procède par induction sur le prefixe pre.
        - Dans le cas de la liste vide, on s'attend à sigma = sigma'
    *)
Admitted.*)

Lemma stability:
    forall ev evs,
        Network evs ->
        List.In ev evs ->
        exists evs',
            leq_capture (ev :: evs') evs 
            /\ Network (ev :: evs').
Admitted.

Lemma Accept_Inversion:
forall evs A B pkt index pc,
    Network evs ->
    List.In (privately_Accept A B pkt index pc) evs ->
    exists pc',
        List.In (publicly_Send B A pkt index pc) evs 
        /\ saved_index A B index evs
        /\ saved_PC A B pc' evs /\ pc' < pc.
Admitted.

Lemma Accept_unicity:
    forall evs A B pkt index_B pc_B, 
        Network ( privately_Accept A B pkt index_B pc_B :: evs ) ->
        ~ (List.In ( privately_Accept A B pkt index_B pc_B ) evs).
Proof.
    intros evs A B pkt index_B pc_B. intros Hnetwork HIn.
    assert ( exists pc',
        List.In (publicly_Send B A pkt index_B pc_B) evs 
        /\ saved_index A B index_B evs
        /\ saved_PC A B pc' evs /\ pc' < pc_B ) as (pc1 & ? & ? & ? & ?). admit.
    assert ( exists pc' evs',
        leq_capture (privately_Accept A B pkt index_B pc_B :: evs') evs 
        /\ List.In (publicly_Send B A pkt index_B pc_B) evs' 
        /\ saved_index A B index_B evs'
        /\ saved_PC A B pc' evs' /\ pc' < pc_B ) as (pc' & evs' & ? & ? & ? & ? & ?). admit.
    assert ( saved_index A B index_B (privately_Accept A B pkt index_B pc_B :: evs') ). admit.
    assert ( saved_PC A B pc_B (privately_Accept A B pkt index_B pc_B :: evs') ). admit.
    assert ( R (privately_Accept A B pkt index_B pc_B :: evs') evs ).
    apply R_leq. auto. admit.
    assert ( pc_B <= pc1 ). eapply R_proj ; eauto. SearchAbout ( ?x < ?y ) .
    eapply Lt.le_not_lt ; eauto.
Admitted.


(* Théorèmes montrant que les prédicats Network_Send, Network_reset et Network_ChallengeRequest peuvent toujours se faire *)

Lemma Send_always_possible:
    forall evs A B, 
        Network evs -> 
        (exists index, local_index A B index evs) 
        /\ (exists pc, local_PC A B pc evs).
Proof.
    (*intros sigma evs B. intro Hnetwork. induction Hnetwork.
    - assumption.
    - unfold init_global_state in H. split. 
        * unfold saved_index. unfold lookup_index. subst. 
            exists (index_seed B). simpl. rewrite refl_eqb. reflexivity.
        * unfold saved_PC. unfold lookup_PC. subst.
            exists 0. simpl. rewrite refl_eqb. reflexivity.
    -*)
Admitted.

Theorem can_Send:
    forall evs A B pkt, 
        Network evs -> 
        exists evs' index pc, 
            Network evs' 
            /\ List.In (publicly_Send B A pkt index pc) evs'
            /\ (exists pre, evs' = pre ++ evs).
Proof.
    intros evs A B pkt. intro Hnetwork.
    pose proof (Send_always_possible evs B A Hnetwork) as ([index Hindex] & [pc Hpc]).
    eexists. exists index. exists pc. split.
    - eapply Network_Send ; eauto.
    - split ; try firstorder.
        exists [publicly_Send B A pkt index pc]. auto.
Qed.

(* Network_reset est peut être redondant, on commente donc le théorème et le lemme associé
Lemma reset_always_possible:
    forall sigma evs B, Network sigma evs -> (exists index, fresh_index B evs index).
Admitted.

Theorem can_reset:
    forall sigma evs B, Network sigma evs -> 
        exists sigma1 evs' index, 
            Network sigma1 evs' 
            /\ List.In (privately_reset B index) evs' 
            /\ (exists pre, evs' = pre ++ evs).
Admitted.
*)

Lemma ChallengeRequest_always_possible:
    forall evs A, 
        Network evs ->
        exists n0, fresh_nonce A evs n0.
Admitted.

Theorem can_Challenge:
    forall evs A B, 
        Network evs -> 
        exists evs' n0, 
            Network evs' 
            /\ List.In (publicly_ChallengeRequest A B n0) evs'
            /\ (exists pre, evs' = pre ++ evs).
Proof.
    intros evs A B. intro Hnetwork.
    pose proof (ChallengeRequest_always_possible evs A Hnetwork) as [n0 Hn0].
    eexists. exists n0. split.
    - eapply Network_ChallengeRequest ; eauto.
    - split ; try firstorder.
        exists [publicly_ChallengeRequest A B n0]. auto.
Qed.

Theorem liveness:
    forall evs A B pkt,
        Network evs ->
        exists evs' index pc,
            Network evs'
            /\ List.In (publicly_Send B A pkt index pc) evs' 
            /\ List.In (privately_Accept A B pkt index pc) evs'
            /\ (exists pre, evs' = pre ++ evs).
Proof.
    intros evs A B pkt. intro Hnetwork.
    (*assert ( HsavedIndex : (exists index, saved_index sigma A B index) 
        \/ lookup_index sigma A B = None ). apply saved_index_dec.
    destruct HsavedIndex as [(index, HsavedIndex) | HnotIndex].
    - assert ( HsavedPC : (exists pc, saved_PC sigma A B pc)
            \/ lookup_PC sigma A B = None ). apply saved_PC_dec.
        destruct HsavedPC as [(pc, HsavedPC) | HnotPC].
        + assert ( HcanSend : exists sigma' evs' index' pc',
                        Network sigma' evs' 
                        /\ List.In (publicly_Send B A pkt index' pc') evs' 
                        /\ exists pre, evs' = pre ++ evs ).
            eapply can_Send ; eauto.
    *)
    (* Pour démontrer ce théorème il y a 2 cas possibles :
        cas 1 : les conditions sont réunies pour accepter une requête
            alors pre = [ privately_Accept ... ; publicly_Send ... ]
        cas 2 : au moins une des conditions n'est pas valide 
            alors pre = [ privately_Accept ... ; publicly_Send ... ;
                            privately_reset ... ; publicly_ChallengeReply ... ;
                            privately_nonce ... ; publicly_ChallengeRequest ... ]
    Dans le cas 2, il faut montrer que la procédure de Challenge / Reply permet de réunir les conditions 
        pour accepter la requête.
    Ces deux cas sont les seuls à montrer car ChallengeRequest et Send peuvent toujours se faire :
        il s'agit des theoremes can_ChallengeRequest et can_Send *)
Admitted.

(* Théorèmes de spoofing *)

(* Fix me: this is not actually spoofing
Theorem spoofing_Accept:
    forall evs A B pkt index pc,
        Network evs ->
        List.In (privately_Accept A B pkt index pc) evs ->
        exists evs', 
            Network evs'
            /\ List.In (privately_Accept A B pkt index pc) evs' 
            /\ List.In (publicly Attacker A (format_MAC_Send B A pkt index pc)) evs'.
Proof.
    intros evs A B pkt index pc. intros Hnetwork HIn.
    assert (exists pc', 
                List.In ( publicly_Send B A pkt index pc ) evs
                /\ saved_index A B index evs 
                /\ saved_PC A B pc' evs /\ pc' < pc ) 
            as 
            [pc' (HinSend & (HsavedIndex & (HsavedPC & HorderPC)))]. 
    + eapply Accept_Inversion ; eauto.
    + eexists. split.
        - eapply Network_Accept ; eauto.
        - split. 
            * eapply in_eq. 
            * apply in_cons. eapply insert_attack ; eauto.
Qed.*)

(* Théorèmes d'unicité des événements *)

Lemma compatibiliy_knows_in: forall evs A B X,
    List.In (publicly A B X) evs -> knows Attacker evs X.
Proof.
    intros evs A B X. intro HIn.
    apply in_split in HIn as [l1 [l2 HIn]]. subst.
    induction l1.
    - simpl. apply knows_attacker.
    - rewrite <- app_comm_cons. apply knows_later. assumption.
Qed.

Theorem replay: forall evs A B X, 
    Network evs -> 
    List.In (publicly A B X) evs ->
    forall C, Network ( publicly Attacker C X :: evs ).
Proof.
    intros evs A B X. intros Hnetwork HIn. intro C.
    apply Network_Attack ; try auto.
    apply synth_init. unfold In. apply analz_init. unfold In.
    eapply compatibiliy_knows_in. eauto.
Qed.

Lemma distinct_index_PC_dec: 
    forall (index index': string) (pc pc': nat),
        (index = index' /\ pc = pc') \/ (index <> index' \/ pc <> pc').
Admitted.

Theorem safety:
    forall evs index pc A B pkt,
        Network evs ->
        unique ( privately_Accept A B pkt index pc ) evs.
Proof.
    intros evs index pc A B pkt. intro Hnetwork.
    unfold unique. induction Hnetwork.
    - destruct IHHnetwork as [HnotIn | [pre [suff (Hevs & (HnotInPre & HnotInSuff))]]].
        * left. apply not_in_cons. split ; easy.
        * right. exists (publicly Attacker B0 X :: pre). exists suff. split.
            + rewrite <- app_comm_cons. apply f_equal. assumption.
            + split ; try easy. apply not_in_cons. split ; easy.
    - auto.
    - destruct IHHnetwork as [HnotIn | [pre [suff (Hevs & (HnotInPre & HnotInSuff))]]].
        * left. apply not_in_cons. split ; easy.
        * right. exists (privately_reset B0 A0 index_B :: pre). exists suff. split.
            + rewrite <- app_comm_cons. apply f_equal. assumption.
            + split ; try easy. apply not_in_cons. split ; easy.
    - destruct IHHnetwork as [HnotIn | [pre [suff (Hevs & (HnotInPre & HnotInSuff))]]].
        * left. apply not_in_cons. split ; easy.
        * right. exists (publicly_Send B0 A0 pkt0 index_B pc_B :: pre). exists suff. split.
            + rewrite <- app_comm_cons. apply f_equal. assumption.
            + split ; try easy. apply not_in_cons. split ; easy.
    - assert ( Hdiscriminate : (index = index_B /\ pc = pc_B) \/ (index <> index_B \/ pc <> pc_B) ).
        apply distinct_index_PC_dec. destruct Hdiscriminate as [(HindexEq & HpcEq) | Hdistinct].
        * assert ( HeqAccept : privately_Accept A0 B0 pkt0 index_B pc_B = 
                                privately_Accept A B pkt index pc). admit.
            right. exists []. exists evs. simpl. split.
            + f_equal. subst. assumption.
            + split ; try easy. rewrite <- HeqAccept. eapply Accept_unicity. eapply Network_Accept ; eauto.
        * assert ( HdistinctAccept : privately_Accept A B pkt index pc <> 
                                    privately_Accept A0 B0 pkt0 index_B pc_B ). admit.
            destruct IHHnetwork as [HnotIn | [pre [suff (Hin & HnotInPre & HnotInSuff)]]].            
            + left. apply not_in_cons. split ; assumption.
            + right. exists (privately_Accept A0 B0 pkt0 index_B pc_B :: pre). exists suff. split.
                ++ rewrite <- app_comm_cons. apply f_equal. assumption.
                ++ split ; try easy. apply not_in_cons. split ; assumption.
    - destruct IHHnetwork as [HnotIn | [pre [suff (Hevs & (HnotInPre & HnotInSuff))]]].
        * left. apply not_in_cons. split ; try easy.
            apply not_in_cons. split ; easy.
        * right. exists (privately_nonce A0 n0 :: publicly_ChallengeRequest A0 B0 n0 :: pre). 
            exists suff. split.
            + rewrite <- app_comm_cons. rewrite <- app_comm_cons. apply f_equal. apply f_equal. assumption.
            + split ; try easy. apply not_in_cons. split ; try easy.
                apply not_in_cons. split ; easy.
    - destruct IHHnetwork as [HnotIn | [pre [suff (Hevs & (HnotInPre & HnotInSuff))]]].
        * left. apply not_in_cons. split ; try easy.
            apply not_in_cons. split ; easy.
        * right. exists (privately_reset B0 A0 index_B :: publicly_ChallengeReply B0 A0 n0 index_B 0 :: pre). 
            exists suff. split.
            + rewrite <- app_comm_cons. rewrite <- app_comm_cons. apply f_equal. apply f_equal. assumption.
            + split ; try easy. apply not_in_cons. split ; try easy.
                apply not_in_cons. split ; easy.
Admitted.

(* Théorèmes d'authenticité *)

Lemma in_inv:
    forall {A} (a b: A) (l: list A), List.In a (b :: l) -> a <> b -> List.In a l.
Admitted.

Theorem Send_authenticity:
    forall evs A A' B B' pkt index pc,
        Network evs ->
        List.In (publicly A' B' (format_MAC_Send A B pkt index pc)) evs ->
        List.In (publicly_Send A B pkt index pc) evs.
Proof.
    intros evs A A' B B' pkt index pc. intros Hnetwork HIn.
    induction Hnetwork ; try easy.
    - (* Dans le cas de Network_Attack, on doit discriminer sur X,
            - si X = format_MAC_Send A B pkt index pc alors, comme on a 
                synth (analz (knows Attacker evs)) X, on a, par définition de knows_attacker
                    List.In (publicly A B X) evs.
                Ainsi, on a List.In (publicly A B (format_MAC_Send A B pkt index pc)) evs.
                D'où le résultat pour ce cas.
            - sinon, on a alors 
                    publicly A' B' (format_MAC_Send A B pkt index pc) <> publicly Attacker B0 X
                et donc on applique l'hypothèse de récurrence
        *)
        admit.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - (* Dans le cas de Network_Send, on doit discriminer sur l'égalité des couples (index, index_B)
        et (pc, pc_B). En effet, il peut très bien y avoir d'autres messages échangés sur le réseau.
        Dans le cas où les deux couples sont égaux, on est dans le cas où le message que l'on souhaite ajouter
        avec Network_Send est celui qui nous intéresse.
        Dans le cas où au moins l'un des deux couples est différent, on est dans le cas d'un autre message,
        on applique alors l'hypothèse de récurrence *)
        assert ( Hdiscriminate : (index = index_B /\ pc = pc_B) \/ (index <> index_B \/ pc <> pc_B) ).
        apply distinct_index_PC_dec. destruct Hdiscriminate as [(HindexEq & HpcEq) | Hdistinct].
        * assert ( HeqSend : publicly_Send A B pkt index pc = 
                                publicly_Send B0 A0 pkt0 index_B pc_B). admit.
            rewrite <- HeqSend. apply in_eq.
        * assert ( HdistinctSend : publicly_Send A B pkt index pc <> 
                                publicly_Send B0 A0 pkt0 index_B pc_B). admit.
            apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy. admit.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy. 
        apply in_inv in HIn ; easy.
    - apply in_cons. apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy. 
        apply in_inv in HIn ; easy.
Admitted.

Theorem ChallengeRequest_authenticity:
    forall evs A A' B B' n0,
        Network evs ->
        List.In (publicly A' B' (format_MAC_ChallengeRequest A B n0)) evs ->
        List.In (publicly_ChallengeRequest A B n0) evs.
Proof.
    intros evs A A' B B' n0. intros Hnetwork HIn.
    induction Hnetwork ; try easy.
    - admit.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. assert ( Hdiscriminate : (n0 = n1) \/ (n0 <> n1) ). admit. 
        destruct Hdiscriminate as [HeqNonce | HdistinctNonce].
        * rewrite <- HeqNonce. assert ( HeqChallRequest : publicly_ChallengeRequest A B n0 =
                                    publicly_ChallengeRequest A0 B0 n0 ). admit.
            rewrite <- HeqChallRequest. apply in_eq.
        * assert ( HdistinctChallReq : publicly_ChallengeRequest A B n0 <>
                                        publicly_ChallengeRequest A0 B0 n1 ). admit.
            apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy.
            apply in_inv in HIn ; try easy. admit.
    - apply in_cons. apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy.
        apply in_inv in HIn ; easy.
Admitted.

Theorem ChallengeReply_authenticity:
    forall evs A A' B B' n0 index pc,
        Network evs ->
        List.In (publicly A' B' (format_MAC_ChallengeReply A B n0 index pc)) evs ->
        List.In (publicly_ChallengeReply A B n0 index pc) evs.
Proof.
    intros evs A A' B B' n0 index pc. intros Hnetwork HIn.
    induction Hnetwork ; try easy.
    - admit.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons. apply IHHnetwork. apply in_inv in HIn ; easy.
    - apply in_cons.  apply IHHnetwork. apply in_inv in HIn ; try easy.
    - apply in_cons. assert ( Hdiscriminate : (n0 = n1) \/ (n0 <> n1) ). admit.
        destruct Hdiscriminate as [HeqNonce | HdistinctNonce].
        * rewrite <- HeqNonce. assert ( HeqChallReply : publicly_ChallengeReply A B n0 index pc =
                                                        publicly_ChallengeReply B0 A0 n0 index_B 0 ). admit.
            rewrite <- HeqChallReply. apply in_eq.
        * assert ( HdistinctChallRep : publicly_ChallengeReply A B n0 index pc <>
                                        publicly_ChallengeReply B0 A0 n1 index_B 0 ). admit.
            apply in_cons. apply IHHnetwork. apply in_inv in HIn ; try easy.
            apply in_inv in HIn ; try easy. admit.
Admitted.