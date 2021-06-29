Require Import String.
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


Module CryptographicInvariants (PD: ProtocolDefs).
    Include ProtocolInvariants PD.

    Definition GoodLog (L: log): Prop :=
        WF_Log L /\ LogInvariant L.

    Inductive level := Low | High.
    Inductive Level: level -> term -> log -> Prop :=
        (* AdversaryGuesses are always Low *)
        | Level_AdversaryGuess: forall l bs L,
            Logged (New (Literal bs) AdversaryGuess) L ->
            Level l (Literal bs) L

        (* Nonces are Low when nonceComp holds *)
        | Level_Nonce: forall l bs L nu,
            Logged (New (Literal bs) (Nonce nu)) L ->
            (l = High \/ (l = Low -> nonceComp (Literal bs) L)) ->
            Level l (Literal bs) L 
        (* HMacKeys are Low when hmacComp holds *)
        | Level_HMacKey: forall l bs L hu,
            Logged (New (Literal bs) (HMacKey hu)) L ->
            (l = High \/ (l = Low -> hmacComp (Literal bs) L)) ->
            Level l (Literal bs) L 
        (* SEncKeys are Low when sencComp holds *)
        | Level_SEncKey: forall l bs L su,
            Logged (New (Literal bs) (SEncKey su)) L ->
            (l = High \/ (l = Low -> sencComp (Literal bs) L)) ->
            Level l (Literal bs) L 
        (* SigKeys are Low when sigComp holds *)
        | Level_SigKey: forall l bs L su,
            Logged (New (Literal bs) (SignKey su)) L ->
            (l = High \/ (l = Low -> sigComp (Literal bs) L)) ->
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
            (l = High \/ (l = Low -> encComp (Literal bs) L)) ->
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
        - apply Level_Nonce with (nu:=nu).
            * assumption.
            * left. tauto.
        - apply Level_HMacKey with (hu:=hu). 
            * assumption.
            * left. tauto.
        - apply Level_SEncKey with (su:=su).
            * assumption.
            * left. tauto.
        - apply Level_SigKey with (su:=su).
            * assumption.
            * left. tauto.
        - apply Level_VerKey with (su:=su). assumption.
        - apply Level_EncKey with (eu:=eu). assumption.
        - apply Level_DecKey with (eu:=eu).
            * assumption.
            * left. tauto.
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
            specialize Hleq_log with (e:=(New (Literal bs) AdversaryGuess)).
            apply Hleq_log in H. assumption.
        - apply Level_Nonce with (nu:=nu). 
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (Nonce nu))).
                apply Hleq_log in H. assumption.
            * destruct H0 as [H0left | H0right].
                + left. assumption.
                + right. intro Hllow. apply H0right in Hllow. 
                    assert ( Hstable : Stable (nonceComp (Literal bs)) ). apply nonceComp_Stable.
                    unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                    apply Hstable ; assumption.
        - apply Level_HMacKey with (hu:=hu).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (HMacKey hu))).
                apply Hleq_log in H. assumption.
            * destruct H0 as [H0left | H0right].
                + left. assumption.
                + right. intro Hllow. apply H0right in Hllow.
                    assert ( Hstable : Stable (hmacComp (Literal bs)) ). apply hmacComp_Stable. 
                    unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                    apply Hstable ; assumption.
        - apply Level_SEncKey with (su:=su). 
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (SEncKey su))).
                apply Hleq_log in H. assumption.
            * destruct H0 as [H0left | H0right].
                + left. assumption.
                + right. intro Hllow. apply H0right in Hllow.
                    assert ( Hstable : Stable (sencComp (Literal bs)) ). apply sencComp_Stable.
                    unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                    apply Hstable ; assumption.
        - apply Level_SigKey with (su:=su).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (SignKey su))).
                apply Hleq_log in H. assumption.
            * destruct H0 as [H0left | H0right].
                + left. assumption.
                + right. intro Hllow. apply H0right in Hllow.
                    assert ( Hstable : Stable (sigComp (Literal bs)) ). apply sigComp_Stable.
                    unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                    apply Hstable ; assumption.
        - apply Level_VerKey with (su:=su). unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) (VerfKey su))).
            apply Hleq_log in H. assumption.
        - apply Level_EncKey with (eu:=eu). unfold leq_log in Hleq_log.
            specialize Hleq_log with (e:=(New (Literal bs) (EncKey eu))).
            apply Hleq_log in H. assumption.
        - apply Level_DecKey with (eu:=eu).
            * unfold leq_log in Hleq_log.
                specialize Hleq_log with (e:=(New (Literal bs) (DecKey eu))).
                apply Hleq_log in H. assumption.
            * destruct H0 as [H0left | H0right].
                + left. assumption.
                + right. intro Hllow. apply H0right in Hllow.
                    assert ( Hstable : Stable (encComp (Literal bs)) ). apply encComp_Stable.
                    unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                    apply Hstable ; assumption.
        - apply Level_Pair.
            * apply IHHlevelL1. assumption.  
            * apply IHHlevelL2. assumption.
        - apply Level_HMac.
            * assert ( Hstable : Stable (canHmac k m) ). apply canHmac_Stable.
                unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                apply Hstable ; assumption.
            * apply IHHlevelL. assumption.
        - apply Level_HMac_Low.
            * apply IHHlevelL1. assumption.
            * apply IHHlevelL2. assumption.
        - apply Level_SEnc with (l':=l').
            * assert ( Hstable : Stable (canSEnc k p) ). apply canSEnc_Stable.
                unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                apply Hstable ; assumption.
            * apply IHHlevelL. assumption.
        - apply Level_SEnc_Low.
            * apply IHHlevelL1. assumption.
            * apply IHHlevelL2. assumption. 
        - apply Level_Sig.
            * assert ( Hstable : Stable (canSign k m) ). apply canSign_Stable. 
                unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                apply Hstable ; assumption.
            * apply IHHlevelL. assumption.
        - apply Level_Sig_Low.
            * apply IHHlevelL1. assumption.
            * apply IHHlevelL2. assumption.
        - apply Level_Enc.
            * assert ( Hstable : Stable (canEnc k p) ). apply canEnc_Stable.
                unfold Stable in Hstable. specialize Hstable with (L:=L) (L':=L').
                apply Hstable ; assumption.
            * apply IHHlevelL. assumption.
        - apply Level_Enc_Low.
            * apply IHHlevelL1. assumption.
            * apply IHHlevelL2. assumption.
    Qed.

    (* Generic Invariants: Level inversion. *)
    Theorem LowHmacKeyLiteral_Inversion : forall L k hu,
        GoodLog L ->
        Logged (New (Literal k) (HMacKey hu)) L ->
        Level Low (Literal k) L ->
        hmacComp (Literal k) L.
    Proof. 
        intros L k hu. intros HGoodLog Hlog Hlevel.
    Admitted.

    Theorem HMac_Inversion : forall L l k p,
        Level l (HMac k p) L ->
        canHmac k p L \/ Level Low k L.
    Proof.
        intros L l k p. intro Hlevel.
    Admitted.
End Levels.