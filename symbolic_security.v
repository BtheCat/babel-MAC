Require Import String.
Require Import Ascii.
Require Import ListSet.

(* Symbolic models in cryptography *)
(*
        - Literal : atomic messages
        - Pair : injective pairing operation

    Primitive keyed cryptographic operators :
        - HMac (symmetric cryptographic primitive) : use to prove the origin of a message by providing evidence of knowledge 
            of a shared secret used as key. Its validity is checked by comparing the received MAC to a freshly computed one.
        - Symmetric encryption (SEnc) : protect the secrecy of a message whilst allowing principals who know the encryption
            key to retrieve the message by decrypting its encryption.

        - Sign and Enc (assymetric cryptographic primitive) : same functionalities, but use key pairs, one public and one private.
*)

Inductive term: Type :=
    | Literal (b: string)
    | Pair (a: term) (b: term)
    | HMac (k: term) (p: term)
    | SEnc (k: term) (p: term)
    | Sign (k: term) (p: term)
    | Enc (k: term) (p: term).

(* Signature: Protocol Usages and Events *)

Module Type ProtocolDefs.
    Parameter nonce_usage: Type.
    Parameters hmac_usage senc_usage: Type.
    Parameters sign_usage enc_usage: Type.
    Parameter pEvent: Type.
End ProtocolDefs.

Module RPCDefs <: ProtocolDefs.
    Parameter TagRequest: ascii.
    Parameter TagResponse: ascii.
    Parameter TagsDistinct: TagRequest <> TagResponse.

    Definition nonce_usage := False.
    Definition senc_usage := False.
    Definition sign_usage := False.
    Definition enc_usage := False.

    Inductive hmac_usage' :=
        | U_KeyAB (a b: term).
    Definition hmac_usage := hmac_usage'.

    Inductive pEvent' :=
        | Request (a b req: term)
        | Response (a b req resp: term)
        | Bad (p: term).
    Definition pEvent := pEvent'.
End RPCDefs.

(* General Usages and Events *)

Module Defs (PD : ProtocolDefs).
    Include PD.

    Inductive usage: Type :=
        | AdversaryGuess
        | Nonce (nu: nonce_usage)
        | HMacKey (hu: hmac_usage)
        | SEncKey (eu: senc_usage)
        | SignKey (su: sign_usage)
        | VerfKey (su: sign_usage)
        | EncKey (eu: enc_usage)
        | DecKey (eu: enc_usage).

    Inductive event: Type :=
        | New (t: term) (u: usage)
        | AsymPair (pk: term) (sk: term)
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
    (* General well-formedness condition stating that any given term can have at most one usage, and that the components of asymmetric
        keypairs must have the same primitive usage, and use the appropriate usage constructor. *)
    Definition WF_Log (L: log): Prop :=
        (forall t u u',
            Logged (New t u) L ->
            Logged (New t u') L -> u = u') /\
        (forall pk sk,
            Logged (AsymPair pk sk) L ->
            ((exists su,
                Logged (New pk (VerfKey su)) L /\
                Logged (New sk (SignKey su)) L) \/
            (exists eu,
                Logged (New pk (EncKey eu)) L /\
                Logged (New sk (DecKey eu)) L))).
End Defs.

(* Signature: Protocol Invariants *)
Module Type ProtocolInvariants (PD: ProtocolDefs).
    Include Defs PD.
    (* Additional well-formedness invariant on the log, meant to represent conditions enforced by the key management infrastructure
        (for example, unidirectionality of keys) *)
    Parameter LogInvariant: log -> Prop.

    (* As follow : 
        - a release primComp for each kind of primitive usage, and proofs that the release conditions are stable
        - a payload condition canPrim for each kind of primitive key usage (excluding nonces), also equipped with proofs of stability.
        Note : Assymetric cryptography is treated in the same way
    *)

    (* Nonce Predicate *)
    Parameter nonceComp: term -> log -> Prop.
    Parameter nonceComp_Stable: forall t, Stable (nonceComp t).

    (* HMAC Predicates *)
    Parameter hmacComp: term -> log -> Prop.
    Parameter hmacComp_Stable: forall t, Stable (hmacComp t).

    Parameter canHmac: term -> term -> log -> Prop.
    Parameter canHmac_Stable: forall k p, Stable (canHmac k p).

    (* SEnc Predicates *)
    Parameter sencComp: term -> log -> Prop.
    Parameter sencComp_Stable: forall t, Stable (sencComp t).

    Parameter canSEnc: term -> term -> log -> Prop.
    Parameter canSEnc_Stable: forall k p, Stable (canSEnc k p).

    (* Sign Predicates *)
    Parameter sigComp: term -> log -> Prop.
    Parameter sigComp_Stable: forall t, Stable (sigComp t).

    Parameter canSign: term -> term -> log -> Prop.
    Parameter canSign_Stable: forall k p, Stable (canSign k p).

    (* Enc Predicates *)
    Parameter encComp: term -> log -> Prop.
    Parameter encComp_Stable: forall t, Stable (encComp t).

    Parameter canEnc: term -> term -> log -> Prop.
    Parameter canEnc_Stable: forall k p, Stable (canEnc k p).
End ProtocolInvariants.

Module RPCInvariants <: ProtocolInvariants RPCDefs.
    Import RPCDefs.
    Include Defs RPCDefs.
    
    (* A-RPC: Log Invariant *)
    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    (* A-RPC: Key usage test *)
    Definition KeyAB a b k L :=
        Logged (New k (HMacKey (U_KeyAB a b))) L.

    (* A-RPC: Release Condition *)
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

    (* A-RPC: Payload Condition *)
    Definition KeyABPayload a b p L :=
        (exists req,
            p = Pair (Literal (String TagRequest EmptyString)) req /\
            LoggedP (Request a b req) L) \/
        (exists req, exists resp,
            p = Pair (Literal (String TagResponse EmptyString)) (Pair req resp) /\
            LoggedP (Response a b req resp) L).

    Definition canHmac k p L :=
        exists a, exists b, KeyAB a b k L /\ KeyABPayload a b p L.

    Theorem canHmac_Stable:
        forall k p, Stable (canHmac k p).
    Proof.
        intros k p. unfold Stable. intros L L'.
        unfold leq_log. unfold canHmac. unfold KeyAB. unfold KeyABPayload. unfold LoggedP.
        intros Hleq_log HcanHmacL.
        destruct HcanHmacL as (a, HcanHmacLa). destruct HcanHmacLa as (b, HcanHmacLab).
        destruct HcanHmacLab as (HcanHmacLab_l & HcanHmacLab_r). 
        exists a. exists b. firstorder.
    Qed.

    (* For the authenticated RPC protocol, all other usage conditions are trivially False. *)
    Definition nonceComp (_: term) (_: log) := False.
    Definition sencComp (_: term) (_: log) := False.
    Definition canSEnc (_ _: term) (_: log) := False.
    Definition sigComp (_: term) (_: log) := False.
    Definition canSign (_ _: term) (_: log) := False.
    Definition encComp (_: term) (_: log) := False.
    Definition canEnc (_ _: term) (_: log) := False.

    Theorem nonceComp_Stable: 
        forall t, Stable (nonceComp t).
    Proof. 
        firstorder.
    Qed.

    Theorem sencComp_Stable: 
        forall t, Stable (sencComp t).
    Proof. 
        firstorder. 
    Qed.

    Theorem canSEnc_Stable:
        forall k p, Stable (canSEnc k p).
    Proof.
        firstorder.
    Qed.

    Theorem sigComp_Stable:
        forall t, Stable (sigComp t).
    Proof.
        firstorder.
    Qed. 

    Theorem canSign_Stable:
        forall k p, Stable (canSign k p).
    Proof.
        firstorder.
    Qed.

    Theorem encComp_Stable:
        forall t, Stable (encComp t).
    Proof.
        firstorder.
    Qed. 

    Theorem canEnc_Stable:
        forall k p, Stable (canEnc k p).
    Proof.
        firstorder.
    Qed.
End RPCInvariants.

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
        (* HMacKeys are Low when hmacComp holds *)
        | Level_HMacKey: forall l bs L hu,
            Logged (New (Literal bs) (HMacKey hu)) L ->
            (l = Low -> hmacComp (Literal bs) L) ->
            Level l (Literal bs) L 
        (* SEncKeys are Low when sencComp holds *)
        | Level_SEncKey: forall l bs L su,
            Logged (New (Literal bs) (SEncKey su)) L ->
            (l = Low -> sencComp (Literal bs) L) ->
            Level l (Literal bs) L 
        (* SigKeys are Low when sigComp holds *)
        | Level_SigKey: forall l bs L su,
            Logged (New (Literal bs) (SignKey su)) L ->
            (l = Low -> sigComp (Literal bs) L) ->
            Level l (Literal bs) L 
        (* VerfKeys are always Low *)
        | Level_VerKey: forall l bs L su,
            Logged (New (Literal bs) (VerfKey su)) L ->
            Level l (Literal bs) L 
        (* EncKeys are always Low *)
        | Level_EncKey: forall l bs L eu,
            Logged (New (Literal bs) (EncKey eu)) L ->
            Level l (Literal bs) L 
        (* DecKeys are Low when encComp holds *)
        | Level_DecKey: forall l bs L eu,
            Logged (New (Literal bs) (DecKey eu)) L ->
            (l = Low -> encComp (Literal bs) L) ->
            Level l (Literal bs) L 

        (* Paris are as Low as their components *)
        | Level_Pair: forall l t1 t2 L,
            Level l t1 L ->
            Level l t2 L ->
            Level l (Pair t1 t2) L

        (* Honest Hmacs are as Low as their payload *)
        | Level_HMac: forall l k m L,
            canHmac k m L ->
            Level l m L ->
            Level l (HMac k m) L
        (* Dishonest Hmacs are Low *)
        | Level_HMac_Low: forall l k m L,
            Level Low k L ->
            Level Low m L ->
            Level l (HMac k m) L 

        (* Honest SEncs are Low *)
        | Level_SEnc: forall l l' k p L,
            canSEnc k p L ->
            Level l' k L ->
            Level l (SEnc k p) L 
        (* Dishonest SEncs are Low *)
        | Level_SEnc_Low: forall l k p L,
            Level Low k L ->
            Level Low p L ->
            Level l (SEnc k p) L
            
        (* Honests Sigs are as Low as their payload *)
        | Level_Sig : forall l k m L,
            canSign k m L ->
            Level l m L ->
            Level l (Sign k m) L 
        (* Dishonest Sigs are Low *)
        | Level_Sig_Low : forall l k m L,
            Level Low k L ->
            Level Low m L ->
            Level l (Sign k m) L

        (* Honest Encryptions are Low *)
        | Level_Enc : forall l k p L,
            canEnc k p L ->
            Level High p L ->
            Level l (Enc k p) L 
        (* Dishonest Encryptions are Low *)
        | Level_Enc_Low : forall l k p L,
            Level Low k L ->
            Level Low p L ->
            Level l (Enc k p) L.
    
    (* Generic Invariants: Low is included in High. *)
    Theorem Low_High: forall t L,
        Level Low t L -> Level High t L.
    Proof.
        intros t L. intro Hlow.
        induction Hlow.
        - apply Level_AdversaryGuess. assumption.
        - apply Level_Nonce with (nu:=nu) ; try assumption. easy. 
        - apply Level_HMacKey with (hu:=hu) ; try assumption. easy.
        - apply Level_SEncKey with (su:=su) ; try assumption. easy.
        - apply Level_SigKey with (su:=su) ; try assumption. easy.
        - apply Level_VerKey with (su:=su). assumption.
        - apply Level_EncKey with (eu:=eu). assumption.
        - apply Level_DecKey with (eu:=eu) ; try assumption. easy.
        - apply Level_Pair ; assumption.
        - apply Level_HMac ; assumption.
        - apply Level_HMac_Low ; assumption.
        - apply Level_SEnc with (l':=l') ; assumption.
        - apply Level_SEnc_Low ; assumption. 
        - apply Level_Sig ; assumption.
        - apply Level_Sig_Low ; assumption.
        - apply Level_Enc ; assumption.
        - apply Level_Enc_Low ; assumption.  
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
        - apply Level_HMacKey with (hu:=hu).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (HMacKey hu))). auto.
            * intro Hllow. apply H0 in Hllow.
                assert ( Hstable : Stable (hmacComp (Literal bs)) ). apply hmacComp_Stable. firstorder.
        - apply Level_SEncKey with (su:=su). 
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (SEncKey su))). auto.
            * intro Hllow. apply H0 in Hllow.
                assert ( Hstable : Stable (sencComp (Literal bs)) ). apply sencComp_Stable. firstorder.
        - apply Level_SigKey with (su:=su).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (SignKey su))). auto.
            * intro Hllow. apply H0 in Hllow.
                assert ( Hstable : Stable (sigComp (Literal bs)) ). apply sigComp_Stable. firstorder.
        - apply Level_VerKey with (su:=su). unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) (VerfKey su))). auto.
        - apply Level_EncKey with (eu:=eu). unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) (EncKey eu))). auto.
        - apply Level_DecKey with (eu:=eu).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (DecKey eu))). auto.
            * intro Hllow. apply H0 in Hllow.
                assert ( Hstable : Stable (encComp (Literal bs)) ). apply encComp_Stable. firstorder.
        - apply Level_Pair ; firstorder.
        - apply Level_HMac ; try auto.
            assert ( Hstable : Stable (canHmac k m) ). apply canHmac_Stable. firstorder.
        - apply Level_HMac_Low ; firstorder.
        - apply Level_SEnc with (l':=l') ; try auto.
            assert ( Hstable : Stable (canSEnc k p) ). apply canSEnc_Stable. firstorder.
        - apply Level_SEnc_Low ; firstorder.
        - apply Level_Sig ; try auto.
            * assert ( Hstable : Stable (canSign k m) ). apply canSign_Stable. firstorder. 
        - apply Level_Sig_Low ; firstorder.
        - apply Level_Enc ; try auto.
            assert ( Hstable : Stable (canEnc k p) ). apply canEnc_Stable. firstorder.
        - apply Level_Enc_Low ; firstorder.
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
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
        specialize HGL_WL_Usage with (t:=t) (u:=u) (u':=u').
        apply HGL_WL_Usage in HlogU ; try assumption.
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
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
        induction Hlevel ; try discriminate. 
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=AdversaryGuess).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate. 
            + rewrite HLit. assumption. 
        - firstorder. rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=HMacKey hu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=SEncKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=SignKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=VerfKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=EncKey eu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal n) (u:=Nonce nu) (u':=DecKey eu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.  
    Qed.

    Theorem LowHmacKeyLiteral_Inversion : forall L k hu,
        GoodLog L ->
        Logged (New (Literal k) (HMacKey hu)) L ->
        forall l t, l = Low -> t = Literal k -> Level l t L ->
        hmacComp (Literal k) L.
    Proof. 
        intros L k hu. intros HGoodLog Hlog. intros l t. intros Hlow HLit Hlevel. symmetry in HLit.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
        induction Hlevel ; try discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=AdversaryGuess).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=Nonce nu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - apply H0 in Hlow. rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=SEncKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=SignKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=VerfKey su).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=EncKey eu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=HMacKey hu) (u':=DecKey eu).
            apply HGL_WL_Usage in Hlog ; try assumption. 
            + discriminate.
            + rewrite HLit. assumption.
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

    Theorem SEnc_Inversion : forall L l k p,
        forall t, t = SEnc k p -> Level l t L ->
        canSEnc k p L \/ Level Low k L.
    Proof.
        intros L l k p. intro t. intros Hsenc Hlevel.
        induction Hlevel ; try discriminate.
        - injection Hsenc. intros Hp0 Hk0. rewrite Hp0 in H. rewrite Hk0 in H. auto.
        - injection Hsenc. intros _ Hk0. rewrite Hk0 in Hlevel1. auto.
    Qed.

    Theorem Sign_Inversion : forall L l k p,
        forall t, t = Sign k p -> Level l t L ->
        canSign k p L \/ Level Low k L.
    Proof.
        intros L l k p. intro t. intros Hsign Hlevel.
        induction Hlevel ; try discriminate.
        - injection Hsign. intros Hm Hk0. rewrite Hm in H. rewrite Hk0 in H. auto.
        - injection Hsign. intros _ Hk0. rewrite Hk0 in Hlevel1. auto.
    Qed.

    Theorem Enc_Inversion : forall L l k p,
        forall t, t = Enc k p -> Level l t L ->
        (canEnc k p L /\ Level High p L) \/ Level Low k L.
    Proof.
        intros L l k p. intro t. intros Henc Hlevel.
        induction Hlevel ; try discriminate.
        - injection Henc. intros Hp0 Hk0. 
            rewrite Hp0 in H. rewrite Hk0 in H. rewrite Hp0 in Hlevel. auto.
        - injection Henc. intros _ Hk0. rewrite Hk0 in Hlevel1. auto.
    Qed.
End CryptographicInvariants.

Import RPCDefs.
Include CryptographicInvariants RPCDefs RPCInvariants.
Import RPCInvariants.

(* A-RPC: Request Correspondance Theorem *)
Theorem RequestCorrespondance: forall a b k req L,
    GoodLog L -> KeyAB a b k L ->
    forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagRequest EmptyString)) req)) -> 
    Level l t L ->
    LoggedP (Request a b req) L \/
    LoggedP (Bad a) L \/ LoggedP (Bad b) L.
Proof.
    intros a b k req L. unfold KeyAB. 
    intros HGoodLog HKeyAB. intros l t. intros Hlow Hhmac Hlevel. unfold LoggedP. 
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
    unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
    - apply IHHlevel in HGL_WL_Usage ; try assumption. admit.
    - apply IHHlevel1 in HGL_WL_Usage ; try auto. admit.
Admitted.

(* A-RPC: Response Correspondance Theorem *)
Theorem ResponseCorrespondance: forall a b k req resp L,
    GoodLog L -> KeyAB a b k L ->
    forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagResponse EmptyString)) (Pair req resp))) ->
    Level l t L ->
    LoggedP (Response a b req resp) L \/
    LoggedP (Bad a) L \/ LoggedP (Bad b) L.
Proof.
    intros a b k req resp L. unfold KeyAB.
    intros HGoodLog HKeyAB. intros l t. intros Hlow Hhmac Hlevel. unfold LoggedP.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
    unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
    - apply IHHlevel in HGL_WL_Usage ; try assumption. admit.
    - apply IHHlevel1 in HGL_WL_Usage ; try auto. admit.
Admitted.

(* A-RPC: Key Secrecy Theorem *)
Theorem KeySecrecy: forall a b k L,
    GoodLog L -> KeyAB a b k L -> 
    forall l, l = Low -> Level l k L ->
    LoggedP (Bad a) L \/ LoggedP (Bad b) L.
Proof.
    intros a b k L. unfold KeyAB.
    intros HGoodLog HKeyAB. intro l. intros Hlow Hlevel. (*unfold LoggedP.*)
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
    unfold LogInvariant in HGL_LogInv. induction Hlevel.
    - 
Admitted.

(* Keyed HMAC Inversion Theorem *)
Theorem KeyedHMac_Inversion: forall hu k p L,
    GoodLog L -> Logged (New k (HMacKey hu)) L ->
    forall l t, l = High -> t = HMac k p -> Level l t L ->
    canHmac k p L \/ hmacComp k L.
Proof.
    intros hu k p L. intros HGoodLog Hlog.
    intros l t. intros Hhigh Hhmac Hlevel.
    unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
    unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & HGL_WL_Keys).
    unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - apply IHHlevel in HGL_WL_Usage ; assumption.
    - 
Admitted.