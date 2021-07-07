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
    Protocol example : Light version of Babel-Mac Protocol
        b       : Log(Msg(a, b, msg))
        b -> a  : Msg(a, b, msg)
        a       : assert(Msg(a, b, msg))
        a       : Log(ChallengeRequest(a, b, n0, msg))
        a -> b  : ChallengeRequest(a, b, n0, msg)
        b       : assert(ChallengeRequest(a, b, n0, msg))
        b       : Log(ChallengeReply(a, b, n0))
        b -> a  : ChallengeReply(a, b, n0)
        a       : assert(ChallengeReply(a, b, n0))
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
    Parameter TagChallengeRequest: ascii.
    Parameter TagChallengeReply: ascii.
    Parameter TagsDistinct: TagChallengeRequest <> TagChallengeReply.

    Inductive nonce_usage' :=
        | Challenge (a b msg: term).
    Definition nonce_usage := nonce_usage'.

    Inductive pEvent' :=
        | Msg (a b msg : term)
        | ChallengeRequest (a b n0 msg: term)
        | ChallengeReply (a b n0: term)
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
End ProtocolInvariants.

Module BabelLightInvariants <: ProtocolInvariants BabelLightDefs.
    Import BabelLightDefs.
    Include Defs BabelLightDefs.

    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    Definition ExchangeAB a b n0 msg L :=
        Logged (New n0 (Nonce (Challenge a b msg))) L.

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
        - specialize Hleq_log with (e:=New n0 (Nonce (Challenge a b msg))). apply Hleq_log. assumption.
        - specialize Hleq_log with (e:=ProtEvent (Bad a)). apply Hleq_log. assumption.
    Qed.
End BabelLightInvariants.

Module CryptographicInvariants (PD: ProtocolDefs) (PI: ProtocolInvariants PD).
    Include PI.

    Definition GoodLog (L: log): Prop :=
        WF_Log L /\ LogInvariant L.

    (*
        Level predicates indicate how cryptography can be used by honest or dishonest protocol participants.
        We say that a term t is Low in log L (denotate Level Low t L) whenever it may be made known to the adversary 
            without compromising the protocol's security objectives.
        We say that a term t is High in log L whenever it can be derivated by any honest or dishonest protocol participant 
            (including the adversary).
        Intuitively, a term is truly secret if it is not Low in the current Log
    *)
    Inductive level := Low | High.
    Inductive Level: level -> term -> log -> Prop :=
        (* AdversaryGuesses are always Low *)
        | Level_AdversaryGuess: forall l bs L,
            Logged (New (Literal bs) AdversaryGuess) L ->
            Level l (Literal bs) L

        (* Nonces are Low when nonceComp holds *)
        | Level_Nonce: forall l bs L nu,
            Logged (New (Literal bs) (Nonce nu)) L ->
            (l = Low -> nonceComp (Literal bs) L) ->
            Level l (Literal bs) L 

        (* Paris are as Low as their components *)
        | Level_Pair: forall l t1 t2 L,
            Level l t1 L ->
            Level l t2 L ->
            Level l (Pair t1 t2) L.
    
    (* Generic Invariants: Low is included in High. *)
    Theorem Low_High: forall t L,
        Level Low t L -> Level High t L.
    Proof.
        intros t L. intro Hlow.
        induction Hlow.
        - apply Level_AdversaryGuess. assumption.
        - apply Level_Nonce with (nu:=nu) ; try assumption. easy. 
        - apply Level_Pair ; assumption.
    Qed.

    (* Generic Invariants: Level is stable. *)
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

    (* Generic Invariants: Distinct usages are absurd *)
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

    (* Generic Invariants: Level inversion. *)
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
        - firstorder. rewrite HLit. assumption.
    Qed.
End CryptographicInvariants.

Import BabelLightDefs.
Include CryptographicInvariants BabelLightDefs BabelLightInvariants.
Import BabelLightInvariants.
    