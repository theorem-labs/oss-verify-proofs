(** * ZReproQ6M — the generic fetch-vs-hdecode instrument (LEN-chain
    layer 1).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    PRODUCING DIRECTION, root-only tables: from an OWNERSHIP hypothesis
    on every root index ([zr_root_own] — the entry at [i] is the
    canonical entry of the symbol whose codeword prefixes [i]'s
    spelling, advertised at its true length, all codes fitting the
    root), a successful [inf_fetch] YIELDS the [hdecode] equation on the
    same stream.  This is the pull-loop-inclusive complement to
    [DecodeBridge.inf_fetch_agrees] (which is entry-side and Buffered):
    the early-stop worry — the fetch stopping at a padded index before
    the codeword is buffered — is refuted by prefix-freeness: an entry
    that stops the loop has [c_bits <= bits], so its codeword lies
    inside the REAL bits and prefixes the true stream.

    CONSUMERS: the fixed-leg LEN chain (lenfix root 9 / distfix root 5,
    every code fits); an earlier development run's [zr_codes_fetch_bridge] at CT_CODES
    (root 7, max code 7).  The dyn LENS/DISTS chase (codes past the
    root) is a LATER extension, not this file.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate ZBitsBridge
  DecodeBridge.
(* Require WITHOUT Import: ZReproQ6A defines its own [br_stream], a
   duplicate of [ZBitsBridge.br_stream]; importing it would shadow the
   bridge constant this file's statements are in.  [br_wf_dropbits]'s
   statement mentions only shared ZBitsIn constants, so qualified use is
   safe. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6A.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** Ownership of every root index by a root-fitting canonical codeword. *)
Definition zr_root_own (T : ztbl) (root : Z) (lens : list nat)
           (maxBits : nat) (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    exists sym cw,
      code_for lens maxBits sym = Some cw
      /\ Z.of_nat (length cw) <= root
      /\ T i = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw)
      /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw.

Lemma zr_fetch_go_hdecode :
  forall (T : ztbl) (root : Z) (lens : list nat) (maxBits : nat)
         (ent : nat -> Code),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    forall f b, br_wf b ->
      match inf_fetch_go f T root b with
      | FetchOk h b' =>
          exists sym cw,
            code_for lens maxBits sym = Some cw
            /\ h = ent sym
            /\ c_bits h = Z.of_nat (length cw)
            /\ br_stream b' = br_stream b
            /\ br_wf b'
            /\ c_bits h <= br_bits b'
            /\ hdecode (code_table lens maxBits) (br_stream b')
               = Some (sym, br_stream (br_dropbits (c_bits h) b'))
      | FetchLeave b' => br_stream b' = br_stream b /\ br_wf b'
      | FetchFuel => True
      end.
Proof.
  intros T root lens maxBits ent Hroot HV Hown.
  induction f as [|f IH]; intros b Hwf; cbn [inf_fetch_go]; [exact I|].
  cbv zeta.
  destruct (Hown (br_bits_of root b)
              (br_bits_of_in_range root b ltac:(lia)))
    as (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref).
  destruct (Z.leb_spec (c_bits (T (br_bits_of root b))) (br_bits b))
    as [Hle|Hgt].
  - (* stop: the owner's codeword is inside the real bits *)
    rewrite HTi in Hle. rewrite Hcb in Hle.
    assert (Hfp : cw = firstn (length cw) (br_stream b)).
    { rewrite <- (Nat2Z.id (length cw)).
      rewrite <- (br_index_spells_stream (Z.of_nat (length cw)) root b)
        by (destruct Hwf as (Hb & _); lia).
      rewrite Nat2Z.id.
      rewrite <- (firstn_write_bits (Z.to_nat root) (length cw)
                    (br_bits_of root b)) by lia.
      symmetry. exact Hpref. }
    set (rest := skipn (length cw) (br_stream b)).
    assert (Hsplit : br_stream b = cw ++ rest).
    { unfold rest. rewrite Hfp at 1.
      rewrite <- Hfp. rewrite Hfp at 1. apply eq_sym, firstn_skipn. }
    exists sym, cw.
    split; [exact Hcf|].
    split; [exact HTi|].
    split; [rewrite HTi; exact Hcb|].
    split; [reflexivity|].
    split; [exact Hwf|].
    split; [rewrite HTi, Hcb; lia|].
    rewrite HTi, Hcb.
    assert (Hdrop : br_stream (br_dropbits (Z.of_nat (length cw)) b)
                    = rest).
    { rewrite br_stream_dropbits
        by (destruct Hwf as (_ & Hh & _); lia).
      rewrite Nat2Z.id. reflexivity. }
    rewrite Hdrop, Hsplit.
    exact (hdecode_complete nat Nat.eq_dec (code_table lens maxBits)
             cw sym rest (code_table_prefix_free lens maxBits HV)
             (proj2 (code_table_In_iff lens maxBits sym cw) Hcf)).
  - (* pull: below the owner's length, so bits <= root - 1 <= 14 *)
    rewrite HTi, Hcb in Hgt.
    assert (H31 : br_bits b <= 31) by lia.
    destruct (br_pullbyte b) as [b1|] eqn:HP.
    + pose proof (br_wf_pullbyte b b1 Hwf H31 HP) as Hwf1.
      pose proof (br_stream_pullbyte b b1 Hwf HP) as Hs1.
      specialize (IH b1 Hwf1).
      destruct (inf_fetch_go f T root b1) as [h' b'|b'|] eqn:HG;
        [| |exact I].
      * destruct IH as (sym' & cw' & C1 & C2 & C3 & C4 & C5 & C6 & C7).
        exists sym', cw'.
        split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
        split; [rewrite C4; exact Hs1|].
        split; [exact C5|]. split; [exact C6|]. exact C7.
      * destruct IH as (S1 & S2).
        split; [rewrite S1; exact Hs1 | exact S2].
    + split; [reflexivity | exact Hwf].
Qed.

Theorem zr_fetch_hdecode :
  forall (T : ztbl) (root : Z) (lens : list nat) (maxBits : nat)
         (ent : nat -> Code) (b : BR),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    br_wf b ->
    match inf_fetch T root b with
    | FetchOk h b' =>
        exists sym cw,
          code_for lens maxBits sym = Some cw
          /\ h = ent sym
          /\ c_bits h = Z.of_nat (length cw)
          /\ br_stream b' = br_stream b
          /\ br_wf b'
          /\ c_bits h <= br_bits b'
          /\ hdecode (code_table lens maxBits) (br_stream b')
             = Some (sym, br_stream (br_dropbits (c_bits h) b'))
    | FetchLeave b' => br_stream b' = br_stream b /\ br_wf b'
    | FetchFuel => True
    end.
Proof.
  intros T root lens maxBits ent b Hroot HV Hown Hwf.
  exact (zr_fetch_go_hdecode T root lens maxBits ent Hroot HV Hown
           (S (Z.to_nat (br_have b))) b Hwf).
Qed.

Print Assumptions zr_fetch_hdecode.

(** ** Layer 2a: [inf_decode] in producing form, pointer-free tables.

    Both fixed tables and CT_CODES have no sub-table pointers, so
    [inf_decode] is the fetch plus one drop; the [sub] guard is
    discharged per instantiation from the entry classification. *)
Theorem zr_decode_hdecode_root :
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (maxBits : nat) (ent : nat -> Code) (b : BR),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    (forall sym cw, code_for lens maxBits sym = Some cw ->
                    sub (ent sym) = false) ->
    br_wf b ->
    match inf_decode sub T root b with
    | DecOk h b' nb =>
        exists sym cw,
          code_for lens maxBits sym = Some cw
          /\ h = ent sym
          /\ nb = c_bits h
          /\ c_bits h = Z.of_nat (length cw)
          /\ br_wf b'
          /\ hdecode (code_table lens maxBits) (br_stream b)
             = Some (sym, br_stream b')
    | DecLeave b' => br_stream b' = br_stream b /\ br_wf b'
    | DecFuel => True
    end.
Proof.
  intros sub T root lens maxBits ent b Hroot HV Hown Hsub Hwf.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode T root lens maxBits ent b Hroot HV Hown Hwf)
    as HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|]; [| exact HF | exact I].
  destruct HF as (sym & cw & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  rewrite C2, (Hsub sym cw C1).
  exists sym, cw.
  split; [exact C1|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [rewrite <- C2; exact C3|].
  split.
  { apply ZReproQ6A.br_wf_dropbits; [exact C5|].
    rewrite <- C2. lia. }
  rewrite <- C4, <- C2. exact C7.
Qed.

Print Assumptions zr_decode_hdecode_root.
