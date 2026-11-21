(** * ZReproQ6T — the TWO-LEVEL fetch/decode instrument (dyn chase,
    LEN-chain layer 1'), SCRATCH against the zr_two_own strawman sent to
    ; the predicate may adjust at their fit-check.

    OWNER: model-rt lane.  Extends ZReproQ6M's root-only producing
    instrument to tables WITH sub-table pointers: a root fetch landing on
    a pointer entry chases [inf_fetch2] into the child window, and the
    composite [inf_decode] IS [hdecode] at the canonical code — the
    codeword being the root index's spelling extended by the child bits.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From Stdlib Require Znumtheory.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate ZBitsBridge
  DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The strawman two-level ownership predicate (message to an earlier development run,
    2026-08-20): every root index is a LEAF owned by a root-fitting
    canonical codeword, or a POINTER whose child window is owned by
    canonical codewords extending the root index's spelling. *)
Definition zr_two_own (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    (exists sym cw, code_for lens 15%nat sym = Some cw
       /\ Z.of_nat (length cw) <= root
       /\ T i = ent sym
       /\ c_bits (ent sym) = Z.of_nat (length cw)
       /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw)
    \/ (c_bits (T i) = root
        /\ 1 <= c_op (T i) <= 15 - root
        /\ 2 ^ root <= c_val (T i)
        /\ (forall j, 0 <= j < 2 ^ c_op (T i) ->
             exists sym cw, code_for lens 15%nat sym = Some cw
               /\ root < Z.of_nat (length cw) <= root + c_op (T i)
               /\ T (c_val (T i) + j) = ent sym
               /\ c_bits (ent sym) = Z.of_nat (length cw) - root
               /\ firstn (length cw)
                    (write_bits (Z.to_nat root) i
                     ++ write_bits (Z.to_nat (c_op (T i))) j) = cw)).

(* ==========================================================================
   1.  Two-slab spelling: [rb + k] buffered bits spell the stream's
       first [rb + k] bits as root-index spelling ++ child-bits spelling,
       where the child bits are exactly the machine's
       [shiftr (br_bits_of (rb + k) b) rb].
   ========================================================================== *)

Lemma zr_bits_of_mod_low : forall rb n b,
  0 <= rb <= n ->
  (br_bits_of n b) mod 2 ^ rb = br_bits_of rb b.
Proof.
  intros rb n b [H0 H1].
  unfold br_bits_of. rewrite !Z.shiftl_1_l.
  replace (Z.land (br_hold b) (2 ^ rb - 1))
    with ((br_hold b) mod 2 ^ rb)
    by (rewrite <- Z.land_ones by lia; f_equal; rewrite Z.ones_equiv; lia).
  replace (Z.land (br_hold b) (2 ^ n - 1))
    with ((br_hold b) mod 2 ^ n)
    by (rewrite <- Z.land_ones by lia; f_equal; rewrite Z.ones_equiv; lia).
  rewrite <- Znumtheory.Zmod_div_mod.
  all: try reflexivity;
       try (apply Z.pow_pos_nonneg; lia);
       try (exists (2 ^ (n - rb)); rewrite <- Z.pow_add_r by lia;
            f_equal; lia).
Qed.

Lemma zr_spell_two : forall rb k b,
  0 < rb -> 0 <= k -> rb + k <= br_bits b -> br_wf b ->
  firstn (Z.to_nat (rb + k)) (ZBitsBridge.br_stream b)
  = write_bits (Z.to_nat rb) (br_bits_of rb b)
    ++ write_bits (Z.to_nat k) (Z.shiftr (br_bits_of (rb + k) b) rb).
Proof.
  intros rb k b Hrb Hk Hle Hwf.
  rewrite <- (br_index_spells_stream (rb + k) (rb + k) b) by lia.
  change (write_bits (Z.to_nat (rb + k)) (br_bits_of (rb + k) b))
    with (zwrite (rb + k) (br_bits_of (rb + k) b)).
  rewrite (zwrite_cut rb (rb + k) (br_bits_of (rb + k) b)) by lia.
  replace (rb + k - rb) with k by lia.
  unfold zwrite.
  rewrite (zr_bits_of_mod_low rb (rb + k) b) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

(* ==========================================================================
   2.  The child fetch's pull loop preserves the stream (the
       [inf_fetch_go_stream] analog for [inf_fetch2]) — shape-independent
       of the ownership predicate: only a uniform entry-bits bound feeds
       the pull-safety arithmetic.
   ========================================================================== *)

Lemma zr_fetch2_go_stream : forall (f : nat) (t : ztbl) (lst : Code) (b : BR)
                                   (h : Code) (b' : BR),
  br_wf b ->
  0 <= c_bits lst ->
  (forall i, 0 <= c_bits (t i)) ->
  (forall i, c_bits lst + c_bits (t i) <= 32) ->
  inf_fetch2_go f t lst b = FetchOk h b' ->
  ZBitsBridge.br_stream b' = ZBitsBridge.br_stream b
  /\ br_wf b'
  /\ c_bits lst + c_bits h <= br_bits b'
  /\ h = t (c_val lst
            + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)).
Proof.
  induction f as [|f IH]; intros t lst b h b' Hwf Hlb Hnn Hb32 H;
    cbn [inf_fetch2_go] in H; [discriminate|].
  destruct (Z.leb_spec
              (c_bits lst
               + c_bits (t (c_val lst
                   + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b)
                              (c_bits lst))))
              (br_bits b)) as [Hle|Hgt].
  - injection H as <- <-.
    split; [reflexivity|]. split; [exact Hwf|].
    split; [exact Hle | reflexivity].
  - destruct (br_pullbyte b) as [b1|] eqn:HP; [|discriminate].
    assert (H31 : br_bits b <= 31).
    { pose proof (Hnn (c_val lst
        + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))).
      pose proof (Hb32 (c_val lst
        + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))).
      lia. }
    pose proof (br_wf_pullbyte b b1 Hwf H31 HP) as Hwf1.
    pose proof (ZBitsBridge.br_stream_pullbyte b b1 Hwf HP) as Hs1.
    destruct (IH t lst b1 h b' Hwf1 Hlb Hnn Hb32 H) as (S1 & S2 & S3 & S4).
    split; [rewrite S1; exact Hs1|].
    split; [exact S2|].
    split; [exact S3 | exact S4].
Qed.

Lemma zr_fetch2_stream : forall (t : ztbl) (lst : Code) (b : BR)
                                (h : Code) (b' : BR),
  br_wf b ->
  0 <= c_bits lst ->
  (forall i, 0 <= c_bits (t i)) ->
  (forall i, c_bits lst + c_bits (t i) <= 32) ->
  inf_fetch2 t lst b = FetchOk h b' ->
  ZBitsBridge.br_stream b' = ZBitsBridge.br_stream b
  /\ br_wf b'
  /\ c_bits lst + c_bits h <= br_bits b'
  /\ h = t (c_val lst
            + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)).
Proof.
  intros t lst b h b' Hwf Hlb Hnn Hb32 H.
  exact (zr_fetch2_go_stream (S (Z.to_nat (br_have b))) t lst b h b'
           Hwf Hlb Hnn Hb32 H).
Qed.

Print Assumptions zr_spell_two.
Print Assumptions zr_fetch2_stream.
