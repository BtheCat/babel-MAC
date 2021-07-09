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

(*
    Protocol Example: an Authenticated RPC Protocol
        a       : Log(Request(a, b, req))
        a -> b  : req | hmac(kab, Literal([TagRequest]) | req)
        b       : assert(Request(a, b, req))
        b       : Log(Response(a, b, req, resp))
        b -> a  : resp | hmac(kab, Literal([TagResponse]) | req | resp)
        a       : assert(Response(a, b, req, resp))
*)

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

(*
    Protocol Example: Encrypted RPC Protocol
        a       : Log(Request(a, b, req))
        a       : k = keygen()
        a -> b  : senc(kab, req | k)
        b       : assert(Request(a, b, req))
        b       : Log(Response(a, b, req, resp))
        b -> a  : senc(k, resp)
        a       : assert(Response(a, b, req, resp))
*)

Module ERPCDefs <: ProtocolDefs.
    Parameter TagRequest: ascii.
    Parameter TagResponse: ascii.
    Parameter TagsDistinct: TagRequest <> TagResponse.

    Inductive nonce_usage' :=
        | U_NonceAB (a b: term).
    Definition nonce_usage := nonce_usage'.

    Inductive senc_usage' :=
        | U_SKeyAB (a b req: term).
    Definition senc_usage := senc_usage'.

    Inductive hmac_usage' :=
        | U_KeyAB (a b: term).
    Definition hmac_usage := hmac_usage'.

    Definition sign_usage := False.
    Definition enc_usage := False.

    Inductive pEvent' :=
        | Request (a b req: term)
        | Response (a b req resp: term)
        | Bad (p: term).
    Definition pEvent := pEvent'.
End ERPCDefs.

(* 
    Protocol Example: Otway-Rees Protocol 
        i       : ni = fresh()
        i -> r  : i | ni
        r       : nr = fresh()
        r -> s  : i | r | ni | nr
        s       : kir = keygen()
        s       : Log(Initiator(i, ni, kir, r))
        s       : Log(Responder(r, nr, kir, i))
        s -> r  : senc(ki, i | r | kir | ni) | senc(kr, i | r | kir | nr)
        r       : Log(Responder(i, nr, kir, r))
        r -> i  : senc(ki, i | r | kir | ni)
        i       : assert(Initiator(i, ni, kir, r))
*)

Module OtwayReesDefs <: ProtocolDefs.
    Parameter TagRequest: ascii.
    Parameter TagResponse: ascii.
    Parameter TagsDistinct: TagRequest <> TagResponse.
    
    Definition nonce_usage := False.
    Definition sign_usage := False.
    Definition enc_usage := False.

    Inductive hmac_usage' :=
        | U_KeyAB (a b: term).
    Definition hmac_usage := hmac_usage'.

    Inductive senc_usage' :=
        | U_SKeyAB (p: term).
    Definition senc_usage := senc_usage'.

    Inductive pEvent' :=
        | Request (a b req: term)
        | Response (a b req resp: term)
        | Initiator (p np kpb b: term)
        | Responder (p np kap a: term)
        | Bad (p: term).
    Definition pEvent := pEvent'.    
End OtwayReesDefs.

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
        destruct HcanHmacL as (a, HcanHmacL_a). destruct HcanHmacL_a as (b, HcanHmacL_ab).
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

Module ERPCInvariants <: ProtocolInvariants ERPCDefs.
    Import ERPCDefs.
    Include Defs ERPCDefs.

    (* E-RPC: Log Invariant *)
    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    (* E-RPC: Release Condition for Nonce *)
    Definition RequestNComp a b L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    
    Definition RequestN a b n L :=
        Logged (New n (Nonce (U_NonceAB a b))) L.

    Definition ResponseNComp a b L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.

    Definition ResponseN a b n L := 
        Logged (New n (Nonce (U_NonceAB a b))) L.

    Definition nonceComp n L :=
        exists a, exists b, (RequestN a b n L /\ RequestNComp a b L) \/ (ResponseN a b n L /\ ResponseNComp a b L).

    Theorem nonceComp_Stable:
        forall t, Stable (nonceComp t).
    Proof.
        intro t. unfold Stable. intros L L'.
        unfold leq_log. unfold nonceComp. unfold RequestN. unfold RequestNComp.
        unfold ResponseN. unfold ResponseNComp. unfold LoggedP.
        firstorder.
    Qed.

    Definition SessionKeyAB a b k req L :=
        Logged (New k (SEncKey (U_SKeyAB a b req))) L.

    Definition SessionKeyComp a b (req: term) L :=
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.

    Definition sencComp k L :=
        exists a, exists b, exists req, SessionKeyAB a b k req L /\ SessionKeyComp a b req L.

    Theorem sencComp_Stable:
        forall t, Stable (sencComp t).
    Proof.
        intro t. unfold Stable. intros L L'.
        unfold leq_log. unfold sencComp. unfold SessionKeyAB. unfold SessionKeyComp. unfold LoggedP.
        intros Hleq_log HsencCompL. 
        destruct HsencCompL as (a, HsencCompL_a). destruct HsencCompL_a as (b, HsencCompL_ab).
        destruct HsencCompL_ab as (req, HsencCompL_abreq). exists a. exists b. exists req. firstorder.
    Qed.
        
    Definition SessionKeyPayload a b req m L :=
        LoggedP (Response a b req m) L.

    Definition canSEnc k m L :=
        exists a, exists b, exists req, SessionKeyAB a b k req L /\ SessionKeyPayload a b req m L.

    Theorem canSEnc_Stable:
        forall k m, Stable (canSEnc k m).
    Proof.
        intros k m. unfold Stable. intros L L'.
        unfold leq_log. unfold canSEnc. unfold SessionKeyAB. unfold SessionKeyPayload. unfold LoggedP.
        intros Hleq_log HcanSEncL.
        destruct HcanSEncL as (a, HcanSEncL_a). destruct HcanSEncL_a as (b, HcanSEncL_ab).
        destruct HcanSEncL_ab as (req, HcanSEncL_abreq).
        exists a. exists b. exists req. firstorder.
    Qed.

    Definition KeyAB a b k L :=
        Logged (New k (HMacKey (U_KeyAB a b))) L.

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
        exists req, exists k,
            p = Pair req k /\
            SessionKeyAB a b k req L /\
            LoggedP (Request a b req) L.

    Definition canHmac k p L := 
        exists a, exists b, KeyAB a b k L /\ KeyABPayload a b p L.

    Theorem canHmac_Stable: 
        forall k p, Stable (canHmac k p).
    Proof.
        intros k p. unfold Stable. intros L L'.
        unfold leq_log. unfold canHmac. unfold KeyABPayload. unfold LoggedP.
        intros Hleq_log HcanHmacL.
        destruct HcanHmacL as (a, HcanHmacL_a). destruct HcanHmacL_a as (b, HcanHmacL_ab).
        exists a. exists b. firstorder.
    Qed.
    
    Definition sigComp (_: term) (_: log) := False.
    Definition canSign (_ _: term) (_: log) := False.
    Definition encComp (_: term) (_: log) := False.
    Definition canEnc (_ _: term) (_: log) := False.

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
End ERPCInvariants.

Module OtwayReesInvariants <: ProtocolInvariants OtwayReesDefs.
    Import OtwayReesDefs.
    Include Defs OtwayReesDefs.

    Definition LogInvariant L :=
        forall t u, Logged (New t u) L -> (exists bs, t = Literal bs).

    Definition KeyAB a b k L := 
        Logged (New k (HMacKey (U_KeyAB a b))) L.

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
        destruct HcanHmacL as (a, HcanHmacL_a). destruct HcanHmacL_a as (b, HcanHmacL_ab).
        exists a. exists b. firstorder.
    Qed.

    Definition PrinKeyAB p k L := 
        Logged (New k (SEncKey (U_SKeyAB p))) L.

    Definition PrinKeyComp p (k: term) L :=
        LoggedP (Bad p) L.

    Definition sencComp k L :=
        exists p, PrinKeyAB p k L /\ PrinKeyComp p k L.

    Theorem sencComp_Stable: 
        forall t, Stable (sencComp t).
    Proof.
        intro t. unfold Stable. intros L L'.
        unfold leq_log. unfold sencComp. unfold PrinKeyAB. unfold PrinKeyComp. unfold LoggedP.
        firstorder.
    Qed.

    Definition PrinKeyPayload p m L:= 
        (exists b, exists np, exists kpb,
            p <> b /\
            m = Pair p (Pair kpb np) /\
            KeyAB p b kpb L /\
            LoggedP (Initiator p np kpb b) L) \/
        (exists a, exists np, exists kap,
            p <> a /\
            m = Pair p (Pair kap np) /\
            KeyAB a p kap L /\
            LoggedP (Responder p np kap a) L).

    Definition canSEnc k m L := 
        exists p, PrinKeyAB p k L /\ PrinKeyPayload p m L.
    
    Theorem canSEnc_Stable:
        forall k m, Stable (canSEnc k m).
    Proof.
        intros k m. unfold Stable. intros L L'.
        unfold leq_log. unfold canSEnc. unfold PrinKeyAB. unfold PrinKeyPayload. unfold LoggedP.
        intros Hleq_log HcanSEncL. destruct HcanSEncL as (p, HcanSEncL_p).
        destruct HcanSEncL_p as (HcanSEncL_log & HcanSEncL_keys).
        exists p. split.
        - firstorder.
        - destruct HcanSEncL_keys as [HcanSEncL_keys_init | HcanSEncL_keys_resp].
            * left. destruct HcanSEncL_keys_init as (b, HcanSEncL_keys_init_b). 
                destruct HcanSEncL_keys_init_b as (np, HcanSEncL_keys_init_bnp).
                destruct HcanSEncL_keys_init_bnp as (kpb, HcanSEncL_keys_init_bnpkpb).
                exists b. exists np. exists kpb. firstorder.
            * right. destruct HcanSEncL_keys_resp as (a, HcanSEncL_keys_resp_a).
                destruct HcanSEncL_keys_resp_a as (np, HcanSEncL_keys_resp_anp).
                destruct HcanSEncL_keys_resp_anp as (kap, HcanSEncL_keys_resp_anpkap).
                exists a. exists np. exists kap. firstorder. 
    Qed.
    
    Definition nonceComp (_: term) (_: log) := False.
    Definition sigComp (_: term) (_: log) := False.
    Definition canSign (_ _: term) (_: log) := False.
    Definition encComp (_: term) (_: log) := False.
    Definition canEnc (_ _: term) (_: log) := False.

    Theorem nonceComp_Stable: 
        forall t, Stable (nonceComp t).
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
End OtwayReesInvariants.

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
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
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
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
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
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        induction Hlevel ; try discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=AdversaryGuess).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=Nonce nu).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - apply H0 in Hlow. rewrite HLit. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=SEncKey su).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=SignKey su).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=VerfKey su).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=EncKey eu).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey hu) (u':=DecKey eu).
            rewrite HLit in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
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

    Theorem LowSencKeyLiteral_Inversion: forall L k su,
        GoodLog L ->
        Logged (New (Literal k) (SEncKey su)) L ->
        forall l t, l = Low -> t = Literal k -> Level l t L ->
        sencComp (Literal k) L.
    Proof.
        intros L k su. intros HGoodLog Hlog. intros l t. intros Hlow Hlit Hlevel.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & _).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        induction Hlevel ; try discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=AdversaryGuess).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=Nonce nu).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=HMacKey hu). 
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - apply H0 in Hlow. rewrite Hlit in Hlow. assumption.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=SignKey su0).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=VerfKey su0).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=EncKey eu).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
        - exfalso. specialize HGL_WL_Usage with (t:=Literal k) (u:=SEncKey su) (u':=DecKey eu).
            rewrite Hlit in H. apply HGL_WL_Usage in Hlog ; try assumption. discriminate.
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

Module RPCTheorems.
    Import RPCDefs.
    Include CryptographicInvariants RPCDefs RPCInvariants.
    Import RPCInvariants.

    (* A-RPC: Request Correspondence Theorem *)
    Theorem RequestCorrespondence: forall a b k req L,
        GoodLog L -> KeyAB a b k L ->
        forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagRequest EmptyString)) req)) -> 
        Level l t L ->
        LoggedP (Request a b req) L \/
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    Proof.
        intros a b k req L. unfold KeyAB. 
        intros HGoodLog HKeyAB. intros l t. intros Hlow Hhmac Hlevel. 
        assert ( HGoodLog_bis : GoodLog L ). assumption.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hhmac. intros Hm Hk0. rewrite Hk0 in H. unfold canHmac in H.
            destruct H as (a0, Ha). destruct Ha as (b0, Hab). destruct Hab as (Hab_key & Hab_keyPayload).
            unfold KeyAB in Hab_key. specialize HGL_WL_Usage with (t:=k) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. injection HKeyAB. intros Hb Ha.
            unfold KeyABPayload in Hab_keyPayload. destruct Hab_keyPayload as [Hab_KP_req | Hab_KP_reqresp].
            + destruct Hab_KP_req as (req0, Hab_KP_req). destruct Hab_KP_req as (Hab_KP_req_m & Hab_KP_req_log).
                symmetry in Hm. rewrite Hab_KP_req_m in Hm. injection Hm. intro Hreq.
                rewrite Ha. rewrite Hb. rewrite Hreq. assumption.
            +  exfalso. destruct Hab_KP_reqresp as (req0, Hab_KP_req). destruct Hab_KP_req as (resp0, Hab_KP_reqresp).
                destruct Hab_KP_reqresp as (Hab_KP_reqresp_m & _). symmetry in Hm. rewrite Hab_KP_reqresp_m in Hm. 
                injection Hm. intros _ Htag.
                assert ( HtagDistinct : TagRequest <> TagResponse ). apply TagsDistinct. 
                tauto.
        - right. injection Hhmac. intros Hm Hk0.
            specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)). 
            assert ( Hlog : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
            apply HGL_LogInv in HKeyAB. destruct HKeyAB as (bs, HLitk).
            assert ( HhmacComp : hmacComp (Literal bs) L ).
            + apply LowHmacKeyLiteral_Inversion with (hu:=U_KeyAB a b) (l:=Low) (t:=Literal bs) ; try easy.
                * rewrite HLitk in Hlog. assumption.
                * rewrite Hk0 in Hlevel1. rewrite HLitk in Hlevel1. assumption.
            + unfold hmacComp in HhmacComp. destruct HhmacComp as (a0, HhmacComp_a). destruct HhmacComp_a as (b0, HhmacComp_ab).
                destruct HhmacComp_ab as (HHC_ab_key & HHC_ab_keyComp). unfold KeyAB in HHC_ab_key.
                rewrite HLitk in Hlog. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
                apply HGL_WL_Usage in HHC_ab_key ; try assumption. injection HHC_ab_key.
                intros Hb Ha. rewrite Hb. rewrite Ha. unfold KeyABComp in HHC_ab_keyComp. assumption.
    Qed.

    (* A-RPC: Response Correspondence Theorem *)
    Theorem ResponseCorrespondence: forall a b k req resp L,
        GoodLog L -> KeyAB a b k L ->
        forall l t, l = Low -> t = (HMac k (Pair (Literal (String TagResponse EmptyString)) (Pair req resp))) ->
        Level l t L ->
        LoggedP (Response a b req resp) L \/
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    Proof.
        intros a b k req resp L. unfold KeyAB.
        intros HGoodLog HKeyAB. intros l t. intros Hlow Hhmac Hlevel. 
        assert ( HGoodLog_bis : GoodLog L ). assumption.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hhmac. intros Hm Hk0. rewrite Hk0 in H. unfold canHmac in H.
            destruct H as (a0, Ha). destruct Ha as (b0, Hab). destruct Hab as (Hab_key & Hab_keyPayload).
            unfold KeyAB in Hab_key. specialize HGL_WL_Usage with (t:=k) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. injection HKeyAB. intros Hb Ha.
            unfold KeyABPayload in Hab_keyPayload. destruct Hab_keyPayload as [Hab_KP_req | Hab_KP_reqresp].
            + exfalso. destruct Hab_KP_req as (req0, hab_KP_req). destruct hab_KP_req as (Hab_KP_req_m & _).
                symmetry in Hm. rewrite Hab_KP_req_m in Hm. injection Hm. intros _ Htag.
                assert ( HtagDistinct : TagRequest <> TagResponse ). apply TagsDistinct. firstorder.
            + destruct Hab_KP_reqresp as (req0, hab_KP_req). destruct hab_KP_req as (resp0, Hab_KP_reqresp).
                destruct Hab_KP_reqresp as (Hab_KP_reqresp_m & Hab_KP_reqresp_log). symmetry in Hm. rewrite Hab_KP_reqresp_m in Hm. 
                injection Hm. intros Hresp Hreq. rewrite Ha. rewrite Hb. rewrite Hreq. rewrite Hresp. assumption.
        - right. injection Hhmac. intros Hm Hk0.
            specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)).
            assert ( Hlog : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
            apply HGL_LogInv in HKeyAB. destruct HKeyAB as (bs, HLitk).
            assert ( HhmacComp : hmacComp (Literal bs) L).
            + apply LowHmacKeyLiteral_Inversion with (hu:=U_KeyAB a b) (l:=Low) (t:=Literal bs) ; try easy.
                * rewrite HLitk in Hlog. assumption.
                * rewrite Hk0 in Hlevel1. rewrite HLitk in Hlevel1. assumption.
            + unfold hmacComp in HhmacComp. destruct HhmacComp as (a0, HhmacComp_a). destruct HhmacComp_a as (b0, HhmacComp_ab).
                destruct HhmacComp_ab as (HHC_ab_key & HHC_ab_keyComp). unfold KeyAB in HHC_ab_key.
                rewrite HLitk in Hlog. specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
                apply HGL_WL_Usage in HHC_ab_key ; try assumption. injection HHC_ab_key.
                intros Hb Ha. rewrite Hb. rewrite Ha. unfold KeyABComp in HHC_ab_keyComp. assumption. 
    Qed.

    (* A-RPC: Key Secrecy Theorem *)
    Theorem KeySecrecy: forall a b k L,
        GoodLog L -> KeyAB a b k L -> 
        forall l, l = Low -> Level l k L ->
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    Proof.
        intros a b k L. unfold KeyAB.
        intros HGoodLog HKeyAB. intro l. intros Hlow Hlevel. 
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)).
        assert ( HKeyAB_bis : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
        apply HGL_LogInv in HKeyAB_bis. destruct HKeyAB_bis as (bs, HLitk).
        induction k ; try discriminate. induction Hlevel ; try discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=AdversaryGuess) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=Nonce nu) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - apply H0 in Hlow. unfold hmacComp in Hlow. destruct Hlow as (a', Hlow_a). destruct Hlow_a as (b', Hlow_ab).
            destruct Hlow_ab as (Hab_key & Hab_keyComp). unfold KeyAB in Hab_key.
            specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a' b')).
            apply HGL_WL_Usage in Hab_key ; try assumption. injection Hab_key.
            intros Hb Ha. rewrite Ha. rewrite Hb. unfold KeyABComp in Hab_keyComp. assumption.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey su) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SignKey su) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=VerfKey su) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=EncKey eu) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=DecKey eu) (u':=HMacKey (U_KeyAB a b)).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
    Qed.

    (* Keyed HMAC Inversion Theorem *)
    Theorem KeyedHMac_Inversion: forall hu k p L,
        GoodLog L -> Logged (New k (HMacKey hu)) L ->
        forall l t, l = High -> t = HMac k p -> Level l t L ->
        canHmac k p L \/ hmacComp k L.
    Proof.
        intros hu k p L. intros HGoodLog Hlog. intros l t. intros Hhigh Hhmac Hlevel.
        assert ( HGoodLog_bis : GoodLog L ). assumption.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hhmac. intros Hm Hk0. rewrite Hm in H. rewrite Hk0 in H. assumption.
        - right. injection Hhmac. intros _ Hk0. rewrite Hk0 in Hlevel1.
            specialize HGL_LogInv with (t:=k) (u:=HMacKey hu).
            assert ( Hlog_bis : Logged (New k (HMacKey hu)) L ). assumption.
            apply HGL_LogInv in Hlog_bis. destruct Hlog_bis as (bs, HLitk).
            rewrite HLitk. apply LowHmacKeyLiteral_Inversion with (hu:=hu) (l:=Low) (t:=Literal bs) ; try easy.
            + rewrite HLitk in Hlog. assumption.
            + rewrite HLitk in Hlevel1. assumption.
    Qed.
End RPCTheorems.

Module ERPCTheorems.
    Import ERPCDefs.
    Include CryptographicInvariants ERPCDefs ERPCInvariants.
    Import ERPCInvariants.

    Theorem KeyedHMac_Inversion: forall a b p k L,
        GoodLog L -> KeyAB a b k L ->
        forall l t, l = High -> t = HMac k p -> Level l t L ->
        canHmac k p L \/ hmacComp k L.
    Proof.
        intros a b p k L. intros HGoodLog HKeyAB. intros l t. intros Hhigh Hhmac Hlevel.
        assert ( HGoodLog_bis : GoodLog L ). assumption.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hhmac. intros Hm Hk0. rewrite Hk0 in H. rewrite Hm in H. assumption.
        - right. injection Hhmac. intros Hm Hk0. rewrite Hk0 in Hlevel1.
            unfold KeyAB in HKeyAB. assert ( Hlog : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
            specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)).
            apply HGL_LogInv in HKeyAB. destruct HKeyAB as (bs, HLitk). rewrite HLitk. 
            apply LowHmacKeyLiteral_Inversion with (hu:=U_KeyAB a b) (l:=Low) (t:=Literal bs) ; try easy.
            + rewrite HLitk in Hlog. assumption.
            + rewrite HLitk in Hlevel1. assumption.
    Qed.

    Theorem RequestCorrespondence: forall a b kab req k L,
        GoodLog L -> KeyAB a b kab L ->
        forall l t, l = Low -> t = SEnc kab (Pair req k) -> Level l t L ->
        (LoggedP (Request a b req) L /\ SessionKeyAB a b k req L) \/
        (LoggedP (Bad a) L \/ LoggedP (Bad b) L).
    Proof.
        intros a b kab req k L. unfold KeyAB. intros HGoodLog HKeyAB. intros l t. intros Hlow Hsenc Hlevel.
        assert ( HGoodLog_bis : GoodLog L ). assumption.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hsenc. intros Hp Hk0. rewrite Hk0 in H.
            unfold canSEnc in H. unfold KeyAB in HKeyAB.
            destruct H as (a0, Ha). destruct Ha as (b0, Hab). destruct Hab as (req0, Habreq).
            destruct Habreq as (Habreq_sessKey & Habreq_sessKeyPayload). 
            unfold SessionKeyAB in Habreq_sessKey. unfold SessionKeyPayload in Habreq_sessKeyPayload.
            unfold SessionKeyAB. admit.
        - right. injection Hsenc. intros Hp Hk0. 
            specialize HGL_LogInv with (t:=kab) (u:=HMacKey (U_KeyAB a b)).
            assert ( Hlog : Logged (New kab (HMacKey (U_KeyAB a b))) L ). assumption.
            apply HGL_LogInv in HKeyAB. destruct HKeyAB as (bs, HLitKab).
            assert ( HhmacComp : hmacComp (Literal bs) L ).
            + apply LowHmacKeyLiteral_Inversion with (hu:=U_KeyAB a b) (l:=Low) (t:=Literal bs) ; try easy.
                * rewrite HLitKab in Hlog. assumption.
                * rewrite Hk0 in Hlevel1. rewrite HLitKab in Hlevel1. assumption.
            + unfold hmacComp in HhmacComp. destruct HhmacComp as (a0, HhmacComp_a). destruct HhmacComp_a as (b0, HhmacComp_ab).
                destruct HhmacComp_ab as (HHC_ab_key & HHC_ab_keyComp). unfold KeyAB in HHC_ab_key.
                specialize HGL_WL_Usage with (t:=Literal bs) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a0 b0)).
                rewrite HLitKab in Hlog. apply HGL_WL_Usage in Hlog ; try assumption. injection Hlog. intros Hb Ha.
                unfold KeyABComp in HHC_ab_keyComp. rewrite Hb. rewrite Ha. assumption.
    Admitted.

    Theorem ResponseCorrespondence: forall a b k req resp L,
        GoodLog L -> SessionKeyAB a b k req L ->
        forall l t, l = Low -> t = SEnc k resp -> Level l t L ->
        LoggedP (Response a b req resp) L \/ (LoggedP (Bad a) L \/ LoggedP (Bad b) L).
    Proof.
        intros a b k req resp L. intros HGoodLog HSessionKey. intros l t. intros Hlow Hsenc Hlevel.
        assert ( HGoodLog_bis : GoodLog L ). assumption. unfold SessionKeyAB in HSessionKey.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. induction Hlevel ; try discriminate.
        - left. injection Hsenc. intros Hp Hk0. rewrite Hk0 in H.
            unfold canSEnc in H. destruct H as (a0, Ha). destruct Ha as (b0, Hab). destruct Hab as (req0, Habreq).
            destruct Habreq as (Habreq_sessKey & Habreq_sessKeyPayload). unfold SessionKeyAB in Habreq_sessKey.
            specialize HGL_WL_Usage with (t:=k) (u:=SEncKey (U_SKeyAB a b req)) (u':=SEncKey (U_SKeyAB a0 b0 req0)).
            assert ( Hlog : Logged (New k (SEncKey (U_SKeyAB a b req))) L ). assumption.
            apply HGL_WL_Usage in HSessionKey ; try assumption. injection HSessionKey. intros Hreq Hb Ha.
            unfold SessionKeyPayload in Habreq_sessKeyPayload. rewrite Ha. rewrite Hb. rewrite Hreq.
            rewrite Hp in Habreq_sessKeyPayload. assumption.
        - right. injection Hsenc. intros Hp Hk0. 
            specialize HGL_LogInv with (t:=k) (u:=SEncKey (U_SKeyAB a b req)).
            assert ( Hlog : Logged (New k (SEncKey (U_SKeyAB a b req))) L ). assumption.
            apply HGL_LogInv in HSessionKey. destruct HSessionKey as (bs, HLitk).
            assert ( HsencComp : sencComp (Literal bs) L ).
            + apply LowSencKeyLiteral_Inversion with (su:=U_SKeyAB a b req) (l:=Low) (t:=Literal bs) ; try easy.
                * rewrite HLitk in Hlog. assumption.
                * rewrite Hk0 in Hlevel1. rewrite HLitk in Hlevel1. assumption.
            + unfold sencComp in HsencComp. destruct HsencComp as (a0, HsencComp_a). destruct HsencComp_a as (b0, HsencComp_ab).
                destruct HsencComp_ab as (req0, HsencComp_abreq). destruct HsencComp_abreq as (HsencComp_sessKey & HsencComp_sessKeyComp).
                unfold SessionKeyAB in HsencComp_sessKey. rewrite HLitk in Hlog.
                specialize HGL_WL_Usage with (t:=Literal bs) (u:=SEncKey (U_SKeyAB a b req)) (u':=SEncKey (U_SKeyAB a0 b0 req0)).
                apply HGL_WL_Usage in HsencComp_sessKey ; try assumption. injection HsencComp_sessKey.
                intros Hreq Hb Ha. unfold SessionKeyComp in HsencComp_sessKeyComp. rewrite Ha. rewrite Hb. assumption.
    Qed.

    Theorem KeyABSecrecy: forall a b k L,
        GoodLog L -> KeyAB a b k L -> 
        forall l, l = Low -> Level l k L ->
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    Proof.
        intros a b k L. unfold KeyAB.
        intros HGoodLog HKeyAB. intro l. intros Hlow Hlevel.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. specialize HGL_LogInv with (t:=k) (u:=HMacKey (U_KeyAB a b)).
        assert ( HKeyAB_bis : Logged (New k (HMacKey (U_KeyAB a b))) L ). assumption.
        apply HGL_LogInv in HKeyAB_bis. destruct HKeyAB_bis as (bs, HLitk).
        induction k ; try discriminate. induction Hlevel ; try discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=AdversaryGuess).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=Nonce nu).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - apply H0 in Hlow. unfold hmacComp in Hlow. destruct Hlow as (a', Hlow_a). destruct Hlow_a as (b', Hlow_ab).
            destruct Hlow_ab as (Hab_key & Hab_keyComp). unfold KeyAB in Hab_key. 
            specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=HMacKey (U_KeyAB a' b')).
            apply HGL_WL_Usage in Hab_key ; try assumption. injection Hab_key. intros Hb Ha.
            rewrite Hb. rewrite Ha. unfold KeyABComp in Hab_keyComp. assumption.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=SEncKey su).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=SignKey su).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=VerfKey su).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=EncKey eu).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=HMacKey (U_KeyAB a b)) (u':=DecKey eu).
            apply HGL_WL_Usage in HKeyAB ; try assumption. discriminate.
    Qed.

    Theorem SessionKeySecrecy: forall a b req k L,
        GoodLog L -> SessionKeyAB a b k req L ->
        forall l, l = Low -> Level l k L ->
        LoggedP (Bad a) L \/ LoggedP (Bad b) L.
    Proof.
        intros a b req k L. unfold SessionKeyAB.
        intros HGoodLog HSessionKey. intro l. intros Hlow Hlevel.
        unfold GoodLog in HGoodLog. destruct HGoodLog as (HGL_WfLog & HGL_LogInv).
        unfold WF_Log in HGL_WfLog. destruct HGL_WfLog as (HGL_WL_Usage & _).
        unfold LogInvariant in HGL_LogInv. specialize HGL_LogInv with (t:=k) (u:=SEncKey (U_SKeyAB a b req)).
        assert ( HSessionKey_bis : Logged (New k (SEncKey (U_SKeyAB a b req))) L ). assumption.
        apply HGL_LogInv in HSessionKey_bis. destruct HSessionKey_bis as (bs, HLitk).
        induction k ; try discriminate. induction Hlevel ; try discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=AdversaryGuess).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=Nonce nu).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=HMacKey hu).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - apply H0 in Hlow. unfold sencComp in Hlow. destruct Hlow as (a', Hlow_a). destruct Hlow_a as (b', Hlow_ab).
            destruct Hlow_ab as (req', Hlow_abreq). destruct Hlow_abreq as (Habreq_sessKey & Habreq_sessKeyComp).
            unfold SessionKeyAB in Habreq_sessKey. specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=SEncKey (U_SKeyAB a' b' req')).
            apply HGL_WL_Usage in Habreq_sessKey ; try assumption. injection Habreq_sessKey. intros Hreq Hb Ha.
            rewrite Ha. rewrite Hb. unfold SessionKeyComp in Habreq_sessKeyComp. assumption.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=SignKey su).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=VerfKey su).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=EncKey eu).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
        - specialize HGL_WL_Usage with (t:=Literal bs0) (u:=SEncKey (U_SKeyAB a b req)) (u':=DecKey eu).
            apply HGL_WL_Usage in HSessionKey ; try assumption. discriminate.
    Qed.
End ERPCTheorems.
