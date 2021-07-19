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
        a -> b  : Literal([TagChallengeRequest]) | msg | hmac(k, n0)
        b       : assert(ChallengeRequest(a, b, n0, msg))
        b       : Log(ChallengeReply(a, b, n0))
        b -> a  : Literal([TagChallengeReply]) | hmac(k, n0)
        a       : assert(ChallengeReply(a, b, msg, n0))
*)

Require Import String.
Require Import Ascii.
Require Import ListSet.

Inductive term: Type :=
    | Literal (b: string)
    | Pair (a: term) (b: term)
    | HMac (k: term) (p: term).

(* Signature: Protocol Usages and Events *)

Module Type ProtocolDefs.
    Parameter nonce_usage: Type.
    Parameter hmac_usage: Type.
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

    Inductive hmac_usage' :=
        | HNonce (n: term).
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
    
    Definition RequestN a b k msg L :=
        exists n, Logged (New k (HMacKey (HNonce n))) L /\ Logged (New n (Nonce (ChallengeRequest a b msg))) L.
    
    Definition ResponseN a b k msg L := 
        exists n, Logged (New k (HMacKey (HNonce n))) L /\ Logged (New n (Nonce (ChallengeReply a b msg))) L.

    Definition keyComp a b L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.

    Definition hmacComp k L :=
        exists a, exists b, exists msg, (RequestN a b k msg L \/ ResponseN a b k msg L) /\ keyComp a b L.

    Theorem hmacComp_Stable:
        forall t, Stable (hmacComp t).
    Admitted.

    Definition noncePayload a b n L :=
        (exists msg, exists p, exists k, 
            p = Pair (Literal (String TagChallengeRequest EmptyString)) (Pair msg (HMac k n)) /\
            LoggedP (Request a b n msg) L) \/
        (exists p, exists msg, exists k,
            p = Pair (Literal (String TagChallengeReply EmptyString)) (HMac k n) /\
            LoggedP (Reply a b n msg) L).

    Definition canHmac k n L :=
        exists a, exists b, exists msg, (RequestN a b k msg L \/ ResponseN a b k msg L) /\ noncePayload a b n L.

    Theorem canHmac_Stable:
        forall k n, Stable (canHmac k n).
    Proof.
        intros k n. unfold Stable. intros L L'. unfold leq_log. unfold canHmac.
        unfold RequestN. unfold ResponseN. unfold noncePayload. unfold LoggedP.
        intros Hleq_log HcanHmacL. destruct HcanHmacL as (a, HcanHmacL_a).
        destruct HcanHmacL_a as (b, HcanHmacL_ab). destruct HcanHmacL_ab as (msg, HcanHmacL_abmsg).
        exists a. exists b. exists msg. 
    Admitted.
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

        | Level_Pair: forall l t1 t2 L,
            Level l t1 L ->
            Level l t2 L ->
            Level l (Pair t1 t2) L
            
        | Level_HMac: forall l k n L,
            canHmac k n L ->
            Level l m L ->
            Level l (HMac k n).
    
    Theorem Low_High: forall t L,
        Level Low t L -> Level High t L.
    Proof.
        intros t L. intro Hlow.
        induction Hlow.
        - apply Level_AdversaryGuess. assumption.
        - apply Level_Nonce with (nu:=nu) ; try assumption. easy.
        - apply Level_Pair ; assumption.
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
End CryptographicInvariants.

Import BabelLightDefs.
Include CryptographicInvariants BabelLightDefs BabelLightInvariants.
Import BabelLightInvariants.
