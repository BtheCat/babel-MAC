(*
    b -> a  : Msg | msg
    a       : event(Msg | msg)
    a -> b  : ChallengeRequest | n0 | msg
    b       : event(ChallengeRequest | n0 | msg)
    b -> a  : ChallengeReply | n0
    a       : event(ChallengeReply | n0 | msg)
    a       : accept(msg)
*)

(*
    Protocol example : Light version of Babel-Mac Protocol (version 1)
        b       : Log(Msg(a, b, msg))
        b -> a  : Msg(a, b, msg)
        a       : assert(Msg(a, b, msg))
        a       : Log(ChallengeRequest(a, b, n0, msg))
        a -> b  : ChallengeRequest(a, b, n0, msg)
        b       : assert(ChallengeRequest(a, b, n0, msg))
        b       : Log(ChallengeReply(a, b, n0))
        b -> a  : ChallengeReply(a, b, n0)
        a       : assert(ChallengeReply(a, b, n0, msg))
*)

(*
    Protocol example: Light version of Babel-Mac Protocol (version 2)
        b       : Log(Msg(a, b, msg))
        b -> a  : Literal([TagMsg]) | msg
        a       : assert(Msg(a, b, msg))
        a       : Log(ChallengeRequest(a, b, n0, msg))
        a -> b  : Literal([TagChallengeRequest]) | msg | n0
        b       : assert(ChallengeRequest(a, b, n0, msg))
        b       : Log(ChallengeReply(a, b, n0))
        b -> a  : Literal([TagChallengeReply]) | n0
        a       : assert(ChallengeReply(a, b, msg, n0))
*)

Require Import String.
Require Import Ascii.
Require Import ListSet.

Inductive term: Type :=
    | Literal (b: string)
    | Pair (a: term) (b: term).

(* Signature: Protocol Usages and Events *)

Module Type ProtocolDefs.
    Parameter nonce_usage: Type.
    Parameter pEvent: Type.
End ProtocolDefs.

Module BabelLightDefs <: ProtocolDefs.
    Parameter TagMsg: ascii.
    Parameter TagChallengeRequest: ascii.
    Parameter TagChallengeReply: ascii.
    Parameter TagsDistinct: (TagChallengeRequest <> TagChallengeReply) 
                            /\ (TagChallengeRequest <> TagMsg)
                            /\ (TagChallengeReply <> TagMsg).

    Inductive nonce_usage' :=
        | ChallengeRequest (a b msg: term)
        | ChallengeReply (a b msg: term).
    Definition nonce_usage := nonce_usage'.

    Inductive pEvent' :=
        | Msg (a b msg : term)
        | Request (a b n0 msg: term)
        | Reply (a b n0 msg: term)
        | Bad (p: term).
    Definition pEvent := pEvent'.
End BabelLightDefs.

Module Defs (PD : ProtocolDefs).
    Include PD.

    Inductive usage: Type :=
        | AdversaryGuess
        | Nonce (nu: nonce_usage).

    Inductive event: Type :=
        | New (t: term) (u: usage)
        | ProtEvent (pe: pEvent).

    (* Definition of logs, here as simple sets of events. Also, some definitions of membership and inclusion order. *)
    Definition log: Type := set event.
    Definition Logged (e: event) (L: log): Prop := set_In e L.
    Definition LoggedP (e: pEvent) (L: log): Prop := Logged (ProtEvent e) L.
    Definition leq_log (L L': log): Prop := forall e, Logged e L -> Logged e L'.

    (* Notion of stability of log-dependant predicates under addition of events to the log *)
    Definition Stable (P: log -> Prop) := forall L L', 
        leq_log L L' -> P L -> 
        P L'.
    (* General well-formedness condition stating that any given term can have at most one usage. *)
    Definition WF_Log (L: log): Prop :=
        (forall t u u',
            Logged (New t u) L ->
            Logged (New t u') L -> u = u').
End Defs.

(* Signature: Protocol Invariants *)
Module Type ProtocolInvariants (PD: ProtocolDefs).
    Include Defs PD.
    
    Parameter LogInvariant: log -> Prop.

    (* Nonce Predicate *)
    Parameter nonceComp: term -> log -> Prop.
    Parameter nonceComp_Stable: forall t, Stable (nonceComp t).

    (*Parameter canNonce : term -> term -> log -> Prop.
    Parameter canNonce_Stable: forall n m, Stable (canNonce n m).*)
End ProtocolInvariants.

Module BabelLightInvariants <: ProtocolInvariants BabelLightDefs.
    Import BabelLightDefs.
    Include Defs BabelLightDefs.

    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    Definition RequestNComp a b L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    
    Definition RequestN a b n msg L :=
        Logged (New n (Nonce (ChallengeRequest a b msg))) L.

    Definition ResponseNComp a b L := 
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    
    Definition ResponseN a b n msg L := 
        Logged (New n (Nonce (ChallengeReply a b msg))) L.
        
    Definition nonceComp n L := 
        exists a, exists b, exists msg, (RequestN a b n msg L /\ RequestNComp a b L)
            \/ (ResponseN a b n msg L /\ ResponseNComp a b L).

    Definition nonceComp_Stable:
        forall t, Stable (nonceComp t).
    Proof.
        intro t. unfold Stable. intros L L'.
        unfold leq_log. unfold nonceComp. unfold RequestN. unfold RequestNComp.
        unfold ResponseN. unfold ResponseNComp. unfold LoggedP.
        intros Hleq_log HnonceCompL. destruct HnonceCompL as (a, HnonceCompL_a).
        destruct HnonceCompL_a as (b, HnonceCompL_ab). destruct HnonceCompL_ab as (msg, HnonceCompL_abmsg).
        exists a. exists b. exists msg. firstorder.
    Qed.   

    Definition RequestAB a b n msg L :=
        Logged (New n (Nonce (ChallengeRequest a b msg))) L.

    Definition ResponseAB a b n msg L :=
        Logged (New n (Nonce (ChallengeReply a b msg))) L. 

    (*Definition ExchangeAB a b n0 msg L :=
        Logged (New n0 (Nonce_U (Challenge a b msg))) L.

    Definition ExchangeABComp p L :=
        LoggedP (Bad p) L.

    Definition nonceComp n0 L :=
        exists a, exists b, exists msg, ExchangeAB a b n0 msg L /\ ExchangeABComp a L.

    Theorem nonceComp_Stable:
        forall n0, Stable (nonceComp n0).
    Proof.
        intro n0. unfold Stable. intros L L'.
        unfold leq_log. unfold nonceComp. unfold ExchangeAB. unfold ExchangeABComp. unfold LoggedP.
        intros Hleq_log HlogL.
        destruct HlogL as (a, HlogL_a). destruct HlogL_a as (b, HlogL_ab). destruct HlogL_ab as (msg, HlogL_abmsg).
        destruct HlogL_abmsg as (HlogL_abmsg_nonce & HlogL_abmsg_bad).
        exists a. exists b. exists msg. split.
        - specialize Hleq_log with (e:=New n0 (Nonce_U (Challenge a b msg))). apply Hleq_log. assumption.
        - specialize Hleq_log with (e:=ProtEvent (Bad a)). apply Hleq_log. assumption.
    Qed.

    Definition ExchangeABPayload a b p L :=
        (exists n0, exists msg,
            p = Pair (Literal (String TagChallengeRequest EmptyString)) (Pair n0 msg) /\
            LoggedP (ChallengeRequest a b n0 msg) L
        ) \/
        (exists n0,
            p = Pair (Literal (String TagChallengeReply EmptyString)) n0 /\
            LoggedP (ChallengeReply a b n0) L
        ).
    
    Definition canNonce n p L :=
        exists a, exists b, exists msg, ExchangeAB a b n msg L /\ ExchangeABPayload a b p L.

    Theorem canNonce_Stable:
        forall n p, Stable (canNonce n p).
    Proof.
        intros n p. unfold Stable. intros L L'.
        unfold leq_log. unfold canNonce. unfold ExchangeAB. unfold ExchangeABPayload. unfold LoggedP.
        intros Hleq_log HlogL. destruct HlogL as (a, HlogL_a). destruct HlogL_a as (b, HlogL_ab). destruct HlogL_ab as (msg, HlogL_abmsg).
        exists a. exists b. exists msg.
        destruct HlogL_abmsg as (HlogL_abmsg_ExchAB & HlogL_abmsg_ExchABPayload). split.
        - specialize Hleq_log with (e:=New n (Nonce_U (Challenge a b msg))). apply Hleq_log. assumption.
        - destruct HlogL_abmsg_ExchABPayload as [HlogL_abmsg_EABP_req | HlogL_abmsg_EABP_resp].
            * left. destruct HlogL_abmsg_EABP_req as (n0, HlogL_abmsg_EABP_req_n0). 
                destruct HlogL_abmsg_EABP_req_n0 as (msg0, HlogL_abmsg_EABP_req_n0msg).
                exists n0. exists msg0. firstorder.
            * right. destruct HlogL_abmsg_EABP_resp as (n0, HlogL_abmsg_EABP_resp_n0).
                exists n0. firstorder.
    Qed.*)
End BabelLightInvariants.

Module CryptographicInvariants (PD: ProtocolDefs) (PI: ProtocolInvariants PD).
    Include PI.

    Definition GoodLog (L: log): Prop :=
        WF_Log L /\ LogInvariant L.

    Inductive level := Low | High.
    Inductive Level: level -> term -> log -> Prop :=
        | Level_AdversaryGuess: forall l bs L,
            Logged (New (Literal bs) AdversaryGuess) L ->
            Level l (Literal bs) L

        | Level_Nonce: forall l bs L nu,
            Logged (New (Literal bs) (Nonce nu)) L ->
            (l = Low -> nonceComp (Literal bs) L) ->
            Level l (Literal bs) L 

        | Level_Pair: forall l t1 t2 L,
            Level l t1 L ->
            Level l t2 L ->
            Level l (Pair t1 t2) L
            
        (*| Level_NonceU: forall l n m L,
            canNonce n m L ->
            Level l m L ->
            Level l (Nonce n m) L
        | Level_NonceU_Low: forall l n m L,
            Level Low n L ->
            Level Low m L ->
            Level l (Nonce n m) L*).
    
    Theorem Low_High: forall t L,
        Level Low t L -> Level High t L.
    Proof.
        intros t L. intro Hlow.
        induction Hlow.
        - apply Level_AdversaryGuess. assumption.
        - apply Level_Nonce with (nu:=nu) ; try assumption. easy.
        - apply Level_Pair ; assumption.
        (*- apply Level_NonceU ; assumption.
        - apply Level_NonceU_Low ; assumption.*)
    Qed.

    Theorem Level_Stable: forall l t L L',
        leq_log L L' -> Level l t L ->
        Level l t L'.
    Proof.
        intros l t L L'. intros Hleq_log HlevelL.
        induction HlevelL.
        - apply Level_AdversaryGuess. unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) AdversaryGuess)). auto.
        - apply Level_Nonce with (nu:=nu). 
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (Nonce nu))). auto.
            * intro Hllow. apply H0 in Hllow. 
                assert ( Hstable : Stable (nonceComp (Literal bs)) ). apply nonceComp_Stable. firstorder.
        - apply Level_Pair ; firstorder.
        (*- apply Level_NonceU ; try auto.
            assert ( HStable : Stable (canNonce n m) ). apply canNonce_Stable. firstorder.
        - apply Level_NonceU_Low ; firstorder.*)
    Qed.

    Theorem AbsurdDistinctUsages : forall P L t u u',
        GoodLog L ->
        u <> u' ->
        Logged (New t u) L ->
        Logged (New t u') L ->
        P.
    Proof.
        intros P L t u u'. intros HGoodLog Hu_not_u' HlogU HlogU'.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog. 
        specialize HGL_WfLog with (t:=t) (u:=u) (u':=u').
        apply HGL_WfLog in HlogU ; try assumption.
        exfalso. tauto.
    Qed.

    Theorem LowNonce_Inversion : forall L n nu,
        GoodLog L ->
        Logged (New (Literal n) (Nonce nu)) L ->
        forall l t, l = Low -> t = Literal n -> Level l t L ->
        nonceComp (Literal n) L.
    Proof.
        intros L n nu. intros HGoodLog Hlog. intros l t. intros Hlow HLit Hlevel. symmetry in HLit.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog.
        induction Hlevel ; try discriminate. 
        - exfalso. specialize HGL_WfLog with (t:=Literal n) (u:=Nonce nu) (u':=AdversaryGuess).
            apply HGL_WfLog in Hlog ; try assumption. 
            + discriminate. 
            + rewrite HLit. assumption. 
        - apply H0 in Hlow. rewrite <- HLit in Hlow. assumption.
    Qed.

    Theorem LowPair_Inversion: forall L t1 t2,
        GoodLog L ->
        forall l t, l = Low -> t = Pair t1 t2 -> Level l t L ->
        Level Low t1 L /\ Level Low t2 L.
    Proof.
        intros L t1 t2. intro HGoodLog. intros l t. intros Hlow Hterm Hlevel.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog.
        induction Hlevel ; try discriminate. 
        injection Hterm. intros Ht3 Ht0. split.
        - rewrite Hlow in Hlevel1. rewrite Ht0 in Hlevel1. assumption.
        - rewrite Hlow in Hlevel2. rewrite Ht3 in Hlevel2. assumption.
    Qed.

    (*Theorem Nonce_Inversion : forall L l n m,
        forall t, t = Nonce n m -> Level l t L ->
        canNonce n m L \/ Level Low n L.
    Proof.
        intros L l n m. intro t. intros Hnonce Hlevel.
        induction Hlevel ; try discriminate.
        - left. injection Hnonce. intros Hm0 Hn0. rewrite Hm0 in H. rewrite Hn0 in H. assumption.
        - right. injection Hnonce. intros _ Hn0. rewrite Hn0 in Hlevel1. assumption.
    Qed.*)
End CryptographicInvariants.

Import BabelLightDefs.
Include CryptographicInvariants BabelLightDefs BabelLightInvariants.
Import BabelLightInvariants.

Theorem ChallengeRequestCorrespondence: forall a b n0 msg L,
    GoodLog L -> RequestAB a b n0 msg L ->
    forall l t, l = Low -> t = Pair (Literal (String TagChallengeRequest EmptyString)) (Pair n0 msg) ->
    Level l t L -> LoggedP (Request a b n0 msg) L \/ (LoggedP (Bad a) L \/ LoggedP (Bad b) L).
Proof.
    intros a b n0 msg L. unfold RequestAB. intros HGoodLog Hrequest. intros l t. intros Hlow Hterm Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. unfold LogInvariant in HGL_LogInv.
    induction Hlevel ; try discriminate. injection Hterm. intros Ht2 Ht1.
    assert ( Hrequest_bis : Logged (New n0 (Nonce (ChallengeRequest a b msg))) L ). assumption.
    specialize HGL_LogInv with (t:=n0) (u:=Nonce (ChallengeRequest a b msg)). apply HGL_LogInv in Hrequest_bis.
    destruct Hrequest_bis as (bs, HLitn0). assert ( HnonceComp : nonceComp (Literal bs) L ).
    - apply LowNonce_Inversion with (t:=Literal bs) (l:=Low) (nu:=ChallengeRequest a b msg) ; try easy.
        + rewrite HLitn0 in Hrequest. assumption.
        + rewrite Ht2 in Hlevel2. rewrite Hlow in Hlevel2.
            assert ( Hpair : Level Low (Literal bs) L /\ Level Low msg L ).
            *  apply LowPair_Inversion with (t1:=Literal bs) (t2:=msg) (l:= Low) (t:=Pair (Literal bs) msg) ; try easy.
                rewrite HLitn0 in Hlevel2. assumption.
            * destruct Hpair as (Hpair & _). assumption.
    - unfold nonceComp in HnonceComp. destruct HnonceComp as (a0, HnonceComp_a).
        destruct HnonceComp_a as (b0, HnonceComp_ab). destruct HnonceComp_ab as (msg0, HnonceComp_abmsg).
        destruct HnonceComp_abmsg as [HNC_request | HNC_response].
        + destruct HNC_request as (HNC_request_req & HNC_request_reqComp).
            unfold RequestN in HNC_request_req. unfold RequestNComp in HNC_request_reqComp.
            rewrite HLitn0 in Hrequest. 
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce (ChallengeRequest a b msg)) (u':=Nonce (ChallengeRequest a0 b0 msg0)).
            apply HGL_WfLog in Hrequest ; try assumption. injection Hrequest. intros _ Hb Ha. 
            rewrite <- Ha in HNC_request_reqComp. rewrite <- Hb in HNC_request_reqComp.
            right. assumption.
        + destruct HNC_response as (HNC_response_resp & _). unfold ResponseN in HNC_response_resp.
            rewrite HLitn0 in Hrequest. 
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce (ChallengeRequest a b msg)) (u':=Nonce (ChallengeReply a0 b0 msg0)).
            apply HGL_WfLog in Hrequest ; try assumption. discriminate.
Qed.

Theorem ChallengeReplyCorrespondence: forall a b n0 msg L,
    GoodLog L -> ResponseAB a b n0 msg L ->
    forall l t, l = Low -> t = Pair (Literal (String TagChallengeReply EmptyString)) n0 ->
    Level l t L -> LoggedP (Reply a b n0 msg) L \/ (LoggedP (Bad a) L \/ LoggedP (Bad b) L).
Proof.
    intros a b n0 msg L. unfold ResponseAB. intros HGoodLog Hresponse. intros l t. intros Hlow Hterm Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. unfold LogInvariant in HGL_LogInv.
    induction Hlevel ; try discriminate. injection Hterm. intros Ht2 Ht1.
    assert ( Hresponse_bis : Logged (New n0 (Nonce (ChallengeReply a b msg))) L ). assumption.
    specialize HGL_LogInv with (t:=n0) (u:=Nonce (ChallengeReply a b msg)). apply HGL_LogInv in Hresponse_bis.
    destruct Hresponse_bis as (bs, HLitn0). assert ( HnonceComp : nonceComp (Literal bs) L ).
    - apply LowNonce_Inversion with (t:=Literal bs) (l:=Low) (nu:=ChallengeReply a b msg) ; try easy.
        + rewrite HLitn0 in Hresponse. assumption.
        + rewrite Hlow in Hlevel2. rewrite Ht2 in Hlevel2. rewrite HLitn0 in Hlevel2. assumption.
    - unfold nonceComp in HnonceComp. destruct HnonceComp as (a0, HnonceComp_a). 
        destruct HnonceComp_a as (b0, HnonceComp_ab). destruct HnonceComp_ab as (msg0, HnonceComp_abmsg).
        destruct HnonceComp_abmsg as [HNC_request | HNC_response].
        + destruct HNC_request as (HNC_request_req & _). unfold RequestN in HNC_request_req.
            rewrite HLitn0 in Hresponse. 
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce (ChallengeReply a b msg)) (u':=Nonce (ChallengeRequest a0 b0 msg0)).
            apply HGL_WfLog in Hresponse ; try assumption. discriminate.
        + destruct HNC_response as (HNC_response_resp & HNC_response_respComp). 
            unfold ResponseN in HNC_response_resp. unfold ResponseNComp in HNC_response_respComp. rewrite HLitn0 in Hresponse.
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce (ChallengeReply a b msg)) (u':=Nonce (ChallengeReply a0 b0 msg0)).
            apply HGL_WfLog in Hresponse ; try assumption. injection Hresponse. intros _ Hb Ha.
            rewrite <- Ha in HNC_response_respComp. rewrite <- Hb in HNC_response_respComp.
            right. assumption.
Qed.

(*Theorem ChallengeRequestCorrespondence: forall a b n0 msg L,
    GoodLog L -> ExchangeAB a b n0 msg L ->
    forall l t, l = Low -> t = Nonce n0 (Pair (Literal (String TagChallengeRequest EmptyString)) (Pair n0 msg)) ->
    Level l t L -> LoggedP (ChallengeRequest a b n0 msg) L \/ LoggedP (Bad a) L.
Proof.
    intros a b n0 msg L. unfold ExchangeAB.
    intros HGoodLog HExchangeAB. intros l t. intros Hlow Hnonce Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
    - left. injection Hnonce. intros Hm Hn. rewrite Hn in H. unfold canNonce in H.
        destruct H as (a0, Ha). destruct Ha as (b0, Hab). destruct Hab as (msg0, Habmsg).
        destruct Habmsg as (Habmsg_ExchAB & Habmsg_ExchABPayload). unfold ExchangeAB in Habmsg_ExchAB.
        specialize HGL_WfLog with (t:=n0) (u:=Nonce_U (Challenge a b msg)) (u':=Nonce_U (Challenge a0 b0 msg0)).
        apply HGL_WfLog in Habmsg_ExchAB ; try assumption. injection Habmsg_ExchAB.
        intros Hmsg Hb Ha. unfold ExchangeABPayload in Habmsg_ExchABPayload.
        destruct Habmsg_ExchABPayload as [Habmsg_EABP_req | Habmsg_EABP_resp].
        + destruct Habmsg_EABP_req as (n', Habmsg_EABP_req_n0). destruct Habmsg_EABP_req_n0 as (msg', Habmsg_EABP_req_n0msg).
            destruct Habmsg_EABP_req_n0msg as (Habmsg_EABP_req_msg & Habmsg_EABP_req_log).
            symmetry in Habmsg_EABP_req_msg. rewrite Hm in Habmsg_EABP_req_msg. injection Habmsg_EABP_req_msg.
            intros Hmsg' Hn'. rewrite Ha. rewrite Hb. rewrite Hn' in Habmsg_EABP_req_log. rewrite Hmsg' in Habmsg_EABP_req_log.
            assumption.
        + exfalso. destruct Habmsg_EABP_resp as (n', Habmsg_EABP_resp_n0).
            destruct Habmsg_EABP_resp_n0 as (Habmsg_EABP_resp_msg & _). symmetry in Habmsg_EABP_resp_msg. 
            rewrite Hm in Habmsg_EABP_resp_msg. injection Habmsg_EABP_resp_msg. intros _ Htag.
            assert ( HtagDistinct : TagChallengeRequest <> TagChallengeReply ). apply TagsDistinct. firstorder.
    - right. injection Hnonce. intros Hm Hn.
        specialize HGL_LogInv with (t:=n0) (u:=Nonce_U (Challenge a b msg)).
        assert ( Hlog : Logged (New n0 (Nonce_U (Challenge a b msg))) L ). assumption.
        apply HGL_LogInv in HExchangeAB. destruct HExchangeAB as (bs, HLitn0).
        assert ( HnonceComp : nonceComp (Literal bs) L ).
        + apply LowNonce_Inversion with (nu:=Challenge a b msg) (l:=Low) (t:=Literal bs) ; try easy.
            * rewrite HLitn0 in Hlog. assumption.
            * rewrite Hn in Hlevel1. rewrite HLitn0 in Hlevel1. assumption.
        + unfold nonceComp in HnonceComp. destruct HnonceComp as (a0, HnonceComp_a). destruct HnonceComp_a as (b0, HnonceComp_ab).
            destruct HnonceComp_ab as (msg0, HnonceComp_abmsg). destruct HnonceComp_abmsg as (HnonceComp_ExchAB & HnonceComp_ExchABComp).
            unfold ExchangeAB in HnonceComp_ExchAB. rewrite HLitn0 in Hlog. 
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce_U (Challenge a b msg)) (u':=Nonce_U (Challenge a0 b0 msg0)).
            apply HGL_WfLog in Hlog ; try assumption. injection Hlog. intros Hmsg Hb Ha.
            unfold ExchangeABComp in HnonceComp_ExchABComp. rewrite Ha. assumption.
Qed.

Theorem ChallengeReplyCorrespondence: forall a b n0 msg L,
    GoodLog L -> ExchangeAB a b n0 msg L ->
    forall l t, l = Low -> t = Nonce n0 (Pair (Literal (String TagChallengeReply EmptyString)) n0) ->
    Level l t L -> LoggedP (ChallengeReply a b n0) L \/ LoggedP (Bad a) L.
Proof.
    intros a b n0 msg L. unfold ExchangeAB. 
    intros HGoodLog HExchangeAB. intros l t. intros Hlow Hnonce Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. unfold LogInvariant in HGL_LogInv. 
    induction Hlevel ; try discriminate.
    - left. injection Hnonce. intros Hm Hn. unfold canNonce in H. destruct H as (a0, Ha).
        destruct Ha as (b0, Hab). destruct Hab as (msg0, Habmsg). destruct Habmsg as (Habmsg_ExchAB & Habmsg_ExchABPayload).
        unfold ExchangeAB in Habmsg_ExchAB. rewrite Hn in Habmsg_ExchAB.
        specialize HGL_WfLog with (t:=n0) (u:=Nonce_U (Challenge a b msg)) (u':=Nonce_U (Challenge a0 b0 msg0)).
        apply HGL_WfLog in HExchangeAB ; try assumption. injection HExchangeAB. intros Hmsg Hb Ha. unfold ExchangeABPayload in Habmsg_ExchABPayload.
        destruct Habmsg_ExchABPayload as [Habmsg_EABP_req | Habmsg_EABP_resp].
        * exfalso. destruct Habmsg_EABP_req as (n', Habmsg_EABP_req_n0). destruct Habmsg_EABP_req_n0 as (msg', Habmsg_EABP_req_n0msg).
            destruct Habmsg_EABP_req_n0msg as (Habmsg_EABP_req_msg & _). symmetry in Habmsg_EABP_req_msg.
            rewrite Hm in Habmsg_EABP_req_msg. injection Habmsg_EABP_req_msg. intros _ Htag.
            assert ( HtagDistinct : TagChallengeRequest <> TagChallengeReply ). apply TagsDistinct. tauto.
        * destruct Habmsg_EABP_resp as (n', Habmsg_EABP_resp_n0). destruct Habmsg_EABP_resp_n0 as (Habmsg_EABP_resp_msg & Habmsg_EABP_resp_log).
            symmetry in Habmsg_EABP_resp_msg. rewrite Hm in Habmsg_EABP_resp_msg. injection Habmsg_EABP_resp_msg.
            intros Hn'. rewrite Ha. rewrite Hb. rewrite Hn' in Habmsg_EABP_resp_log. assumption.
    - right. injection Hnonce. intros Hm Hn.
        specialize HGL_LogInv with (t:=n0) (u:=Nonce_U (Challenge a b msg)).
        assert ( Hlog : Logged (New n0 (Nonce_U (Challenge a b msg))) L ). assumption.
        apply HGL_LogInv in HExchangeAB. destruct HExchangeAB as (bs, HLitn0).
        assert ( HnonceComp : nonceComp (Literal bs) L ).
        + apply LowNonce_Inversion with (nu:=Challenge a b msg) (l:=Low) (t:=Literal bs) ; try easy.
            * rewrite HLitn0 in Hlog. assumption.
            * rewrite Hn in Hlevel1. rewrite HLitn0 in Hlevel1. assumption.
        + unfold nonceComp in HnonceComp. destruct HnonceComp as (a0, HnonceComp_a). destruct HnonceComp_a as (b0, HnonceComp_ab).
            destruct HnonceComp_ab as (msg0, HnonceComp_abmsg). destruct HnonceComp_abmsg as (HnonceComp_ExchAB & HnonceComp_ExchABComp).
            unfold ExchangeAB in HnonceComp_ExchAB. rewrite HLitn0 in Hlog.
            specialize HGL_WfLog with (t:=Literal bs) (u:=Nonce_U (Challenge a b msg)) (u':=Nonce_U (Challenge a0 b0 msg0)).
            apply HGL_WfLog in HnonceComp_ExchAB ; try assumption. injection HnonceComp_ExchAB. intros Hmsg Hb Ha.
            unfold ExchangeABComp in HnonceComp_ExchABComp. rewrite Ha. assumption.
Qed.

Theorem NonceSecrecy: forall a b n0 msg L,
    GoodLog L -> ExchangeAB a b n0 msg L ->
    forall l, l = Low -> Level l n0 L ->
    LoggedP (Bad a) L.
Proof.
    intros a b n0 msg L. unfold ExchangeAB.
    intros HGoodLog HExchangeAB. intro l. intros Hlow Hlevel.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. unfold LogInvariant in HGL_LogInv.
    specialize HGL_LogInv with (t:=n0) (u:=Nonce_U (Challenge a b msg)).
    assert ( HExchangeAB_bis : Logged (New n0 (Nonce_U (Challenge a b msg))) L ). assumption.
    apply HGL_LogInv in HExchangeAB_bis. destruct HExchangeAB_bis as (bs, HLitn0).
    induction n0 ; try discriminate. induction Hlevel ; try discriminate.
    - specialize HGL_WfLog with (t:=Literal bs0) (u:=Nonce_U (Challenge a b msg)) (u':=AdversaryGuess).
        apply HGL_WfLog in HExchangeAB ; try assumption. discriminate.
    - apply H0 in Hlow. unfold nonceComp in Hlow. destruct Hlow as (a', Hlow_a). destruct Hlow_a as (b', Hlow_ab).
        destruct Hlow_ab as (msg', Hlow_abmsg). destruct Hlow_abmsg as (Hlow_exchAB & Hlow_exchABComp).
        unfold ExchangeAB in Hlow_exchAB. specialize HGL_WfLog with (t:=Literal bs0) (u:=Nonce_U (Challenge a b msg)) (u':=Nonce_U (Challenge a' b' msg')).
        apply HGL_WfLog in HExchangeAB ; try assumption. injection HExchangeAB. intros Hmsg Hb Ha.
        unfold ExchangeABComp in Hlow_exchABComp. rewrite Ha. assumption.
Qed.*)