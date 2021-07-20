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
                        | hmac(k, Literal([TagChallengeRequest]) | msg | n0)
        b       : assert(ChallengeRequest(a, b, n0, msg))
        b       : Log(ChallengeReply(a, b, n0))
        b -> a  : Literal([TagChallengeReply]) | n0 
                        | hmac(k, Literal([TagChallengeReply]) | n0)
        a       : assert(ChallengeReply(a, b, msg, n0))
*)

Require Import String.
Require Import Ascii.
Require Import ListSet.

Inductive term: Type :=
    | Literal (b: string)
    | Pair (a: term) (b: term)
    | HMac (k: term) (p: term).

Module Type ProtocolDefs.
    Parameter nonce_usage: Type.
    Parameter hmac_usage: Type.
    Parameter pEvent: Type.
End ProtocolDefs.

Module BabelLightDefs <: ProtocolDefs.
    (*Parameter TagMsg: ascii.*)
    Parameter TagChallengeRequest: ascii.
    Parameter TagChallengeReply: ascii.
    Parameter TagsDistinct: (TagChallengeRequest <> TagChallengeReply) 
                            (*/\ (TagChallengeRequest <> TagMsg)
                            /\ (TagChallengeReply <> TagMsg)*).

    Inductive nonce_usage' :=
        | ChallengeRequest (a b msg: term)
        | ChallengeReply (a b msg: term).
    Definition nonce_usage := nonce_usage'.

    Inductive hmac_usage' :=
        | U_KeyAB (a b: term).
    Definition hmac_usage := hmac_usage'.
    
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
        | Nonce (nu: nonce_usage)
        | HMacKey (hu: hmac_usage).

    Inductive event: Type :=
        | New (t: term) (u: usage)
        | ProtEvent (pe: pEvent).

    Definition log: Type := set event.
    Definition Logged (e: event) (L: log): Prop := set_In e L.
    Definition LoggedP (e: pEvent) (L: log): Prop := Logged (ProtEvent e) L.
    Definition leq_log (L L': log): Prop := forall e, Logged e L -> Logged e L'.

    Definition Stable (P: log -> Prop) := forall L L', 
        leq_log L L' -> P L -> 
        P L'.
    Definition WF_Log (L: log): Prop :=
        (forall t u u',
            Logged (New t u) L ->
            Logged (New t u') L -> u = u').
End Defs.

(* Signature: Protocol Invariants *)
Module Type ProtocolInvariants (PD: ProtocolDefs).
    Include Defs PD.
    
    Parameter LogInvariant: log -> Prop.

    Parameter hmacComp : term -> log -> Prop.
    Parameter hmacComp_Stable: forall t, Stable (hmacComp t).

    Parameter canHmac : term -> term -> log -> Prop.
    Parameter canHmac_Stable: forall k n, Stable (canHmac k n).
End ProtocolInvariants.

Module BabelLightInvariants <: ProtocolInvariants BabelLightDefs.
    Import BabelLightDefs.
    Include Defs BabelLightDefs.

    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    Definition KeyAB a b k L :=
        Logged (New k (HMacKey (U_KeyAB a b))) L.
    
    (*Definition RequestN a b n L :=
        exists msg, Logged (New n (Nonce (ChallengeRequest a b msg))) L.*)
    
    Definition ResponseN a b n msg L := 
        Logged (New n (Nonce (ChallengeReply a b msg))) L.

    Definition KeyABComp a b L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.

    Definition hmacComp k L :=
        exists a, exists b, KeyAB a b k L /\ KeyABComp a b L.

    Theorem hmacComp_Stable:
        forall t, Stable (hmacComp t).
    Proof.
        intro t. unfold Stable. intros L L'.
        unfold leq_log. unfold hmacComp. unfold KeyAB. unfold KeyABComp. unfold LoggedP.
        firstorder.
    Qed.

    Definition KeyABPayload a b p L :=
        (exists n, exists msg, 
            p = Pair (Literal (String TagChallengeRequest EmptyString)) (Pair msg n) /\
            LoggedP (Request a b n msg) L) \/
        (exists n, exists msg,
            p = Pair (Literal (String TagChallengeReply EmptyString)) n /\
            LoggedP (Reply a b n msg) L).

    Definition canHmac k p L :=
        exists a, exists b, KeyAB a b k L /\ KeyABPayload a b p L.

    Theorem canHmac_Stable:
        forall k n, Stable (canHmac k n).
    Proof.
        intros k p. unfold Stable. intros L L'. unfold leq_log. unfold canHmac.
        unfold KeyAB. unfold KeyABPayload. unfold LoggedP.
        intros Hleq_log HcanHmacL. 
        destruct HcanHmacL as (a, HcanHmacL_a). destruct HcanHmacL_a as (b, HcanHmacL_ab).
        exists a. exists b. firstorder.
    Qed.
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
        
        | Level_HMacKey: forall l bs L hu,
            Logged (New (Literal bs) (HMacKey hu)) L ->
            (l = Low -> hmacComp (Literal bs) L) ->
            Level l (Literal bs) L 

        | Level_Pair: forall l t1 t2 L,
            Level l t1 L ->
            Level l t2 L ->
            Level l (Pair t1 t2) L
            
        | Level_HMac: forall l k m L,
            canHmac k m L ->
            Level l m L ->
            Level l (HMac k m) L
        | Level_HMac_Low: forall l k m L,
            Level Low k L ->
            Level Low m L ->
            Level l (HMac k m) L.
    
    Theorem Low_High: forall t L,
        Level Low t L -> Level High t L.
    Proof.
        intros t L. intro Hlow.
        induction Hlow.
        - apply Level_AdversaryGuess. assumption.
        - apply Level_HMacKey with (hu:=hu) ; try assumption. easy.
        - apply Level_Pair ; assumption.
        - apply Level_HMac ; assumption.
        - apply Level_HMac_Low ; assumption.
    Qed.

    Theorem Level_Stable: forall l t L L',
        leq_log L L' -> Level l t L ->
        Level l t L'.
    Proof.
        intros l t L L'. intros Hleq_log HlevelL.
        induction HlevelL.
        - apply Level_AdversaryGuess. unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) AdversaryGuess)). auto.
        - apply Level_HMacKey with (hu:=hu).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (HMacKey hu))). auto.
            * intro Hllow. apply H0 in Hllow.
                assert ( Hstable : Stable (hmacComp (Literal bs)) ). apply hmacComp_Stable. firstorder.
        - apply Level_Pair ; firstorder.
        - apply Level_HMac ; try auto.
            assert ( Hstable : Stable (canHmac k m) ). apply canHmac_Stable. firstorder.
        - apply Level_HMac_Low ; firstorder.
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

    Theorem LowHmacKeyLiteral_Inversion : forall L k hu,
        GoodLog L ->
        Logged (New (Literal k) (HMacKey hu)) L ->
        forall l t, l = Low -> t = Literal k -> Level l t L ->
        hmacComp (Literal k) L.
    Proof. 
        intros L k hu. intros HGoodLog Hlog. intros l t. intros Hlow HLit Hlevel. symmetry in HLit.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WL_Usage & _).
        unfold WF_Log in HGL_WL_Usage.
        induction Hlevel ; try discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=AdversaryGuess).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - apply H0 in Hlow. rewrite HLit. assumption.
    Qed.

    Theorem HMac_Inversion : forall L l k p,
        forall t, t = HMac k p -> Level l t L ->
        canHmac k p L \/ Level Low k L.
    Proof.
        intros L l k p. intro t. intros Hhmac Hlevel.
        induction Hlevel ; try discriminate.
        - injection Hhmac. intros Hm Hk0. rewrite Hm in H. rewrite Hk0 in H. auto.
        - injection Hhmac. intros _ Hk0. rewrite Hk0 in Hlevel1. auto.
    Qed.
End CryptographicInvariants.

Import BabelLightDefs.
Include CryptographicInvariants BabelLightDefs BabelLightInvariants.
Import BabelLightInvariants.

Theorem RequestCorrespondence: forall a b k n msg L,
    GoodLog L -> KeyAB a b k L ->
    forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagChallengeRequest EmptyString)) (Pair msg n))) ->
    Level l t L ->
    LoggedP (Request a b n msg) L \/
    LoggedP (Bad a) L \/ LoggedP (Bad b) L.
Proof.
    intros a b k n msg L. unfold KeyAB.
    intros HGoodLog HKeyAB. intros l t. intros Hlow Hhmac Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WL_Usage & HGL_LogInv).
    unfold WF_Log in HGL_WL_Usage.
    unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
    - left. injection Hhmac. intros Hm Hk0. rewrite Hk0 in H. unfold canHmac in H.
        destruct H as (a0, Ha). destruct Ha as (b0, Hab).
        destruct Hab as (Hkey & HkeyPayload).
        unfold KeyAB in Hkey. specialize HGL_WL_Usage with (t:=k) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
        apply HGL_WL_Usage in HKeyAB ; try assumption. injection HKeyAB. intros Hb Ha.
        unfold KeyABPayload in HkeyPayload. destruct HkeyPayload as [HKP_req | HKP_reply].
        + destruct HKP_req as (n0, HKP_req_n). destruct HKP_req_n as (msg0, HKP_req_nmsg).
            destruct HKP_req_nmsg as (HKP_req_m & HKP_req_log).
            symmetry in Hm. rewrite HKP_req_m in Hm. injection Hm. intros Hn Hmsg.
            rewrite <- Ha in HKP_req_log. rewrite <- Hb in HKP_req_log. 
            rewrite <- Hn in HKP_req_log. rewrite <- Hmsg in HKP_req_log. assumption.
        + exfalso. destruct HKP_reply as (n0, HKP_reply_n). destruct HKP_reply_n as (msg0, HKP_reply_nmsg).
            destruct HKP_reply_nmsg as (HKP_reply & _). symmetry in Hm.
            rewrite HKP_reply in Hm. injection Hm. intros _ Htag.
            assert ( HTagDistinct : TagChallengeRequest <> TagChallengeReply ). 
            apply TagsDistinct. tauto.
    - right. injection Hhmac. intros Hm Hk0. rewrite Hk0 in Hlevel1.
        specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)).
        assert ( Hlog : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
        apply HGL_LogInv in HKeyAB. destruct HKeyAB as (bs, HLitk).
        assert ( HhmacComp : hmacComp (Literal bs) L ).
        + apply LowHmacKeyLiteral_Inversion with (hu:=U_KeyAB a b) (l:=Low) (t:=Literal bs) ; try easy.
            * rewrite HLitk in Hlog. assumption.
            * rewrite HLitk in Hlevel1. assumption.
        + unfold hmacComp in HhmacComp. destruct HhmacComp as (a0, HhmacComp_a).
            destruct HhmacComp_a as (b0, HhmacComp_ab).
            destruct HhmacComp_ab as (HHC_key & HHC_keyComp).
            unfold KeyAB in HHC_key. rewrite HLitk in Hlog. 
            specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
            apply HGL_WL_Usage in Hlog ; try assumption. injection Hlog. intros Hb Ha.
            rewrite <- Ha in HHC_keyComp. rewrite <- Hb in HHC_keyComp. 
            unfold KeyABComp in HHC_keyComp. assumption.
Qed.

Theorem ResponseCorrespondence: forall a b k n msg L,
    GoodLog L -> KeyAB a b k L -> ResponseN a b n msg L ->
    forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagChallengeReply EmptyString)) n)) ->
    Level l t L ->
    LoggedP (Reply a b n msg) L \/
    LoggedP (Bad a) L \/ LoggedP (Bad b) L.
Proof.
    intros a b k n msg L. unfold KeyAB. unfold ResponseN.
    intros HGoodLog HKeyAB HrespN. intros l t. intros Hlow Hhmac Hlevel.
    assert ( HGoodLog_bis : GoodLog L ). assumption.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WL_Usage & HGL_LogInv).
    unfold WF_Log in HGL_WL_Usage. unfold LogInvariant in HGL_LogInv.
    induction Hlevel ; try discriminate.
    - left. injection Hhmac. intros Hm Hk0. rewrite Hk0 in H. unfold canHmac in H.
        destruct H as (a0, Ha). destruct Ha as (b0, Hab).
        destruct Hab as (Hkey & HkeyPayload). unfold KeyAB in Hkey.
        specialize HGL_WL_Usage with (t:=k) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
        apply HGL_WL_Usage in HKeyAB ; try assumption. injection HKeyAB. intros Hb Ha.
        unfold KeyABPayload in HkeyPayload. destruct HkeyPayload as [HKP_req | HKP_reply].
        + exfalso. destruct HKP_req as (n0, HKP_req_n). destruct HKP_req_n as (msg0, HKP_req_nmsg).
            destruct HKP_req_nmsg as (HKP_req_m & _). symmetry in Hm. rewrite HKP_req_m in Hm.
            injection Hm. intros _ Htag.
            assert ( HtagDistinct : TagChallengeRequest <> TagChallengeReply ). apply TagsDistinct.
            firstorder.
        + destruct HKP_reply as (n0, HKP_reply_n). destruct HKP_reply_n as (msg0, HKP_reply_nmsg).
            destruct HKP_reply_nmsg as (HKP_reply_m & HKP_reply_log).
            symmetry in Hm. rewrite HKP_reply_m in Hm. injection Hm. intro Hn.
