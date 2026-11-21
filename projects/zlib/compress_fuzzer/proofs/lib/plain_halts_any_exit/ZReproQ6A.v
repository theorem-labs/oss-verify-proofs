(** * ZReproQ6A — Q6 leg (a): the bit-reader's declarative stream view.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  Q6 (the
    general inflater face) stage 1.  The soundness walk's clause 1 is a
    correspondence between the model's bit reader and a declarative bit
    stream; this file names that view and proves the four facts every arm
    leg consumes:

      [br_stream b] = the unconsumed bits, LSB-first — exactly the
      refinement shape ZBitsIn.v's own §-comment describes ("the low
      [br_bits] bits of [br_hold], then [bytes_bits (br_bytes b)]").

    - [br_stream_pullbyte]: PULLBYTE is a no-op at stream level.
    - [br_read_agree]: BITS(n)+DROPBITS(n) IS [read_bits n] — the model's
      read and the declarative decoder's read return the same value and
      the same remainder.  This is the atom [dec_blk]-vs-arm agreement
      reduces to.
    - [br_wf] preservation for both, and the NEEDBITS loop ([inf_nb])
      preserving the stream while establishing [n <= br_bits].

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The view.
   ========================================================================== *)

Definition br_stream (b : BR) : list bool :=
  zwrite (br_bits b) (br_hold b) ++ bytes_bits (br_bytes b).

Lemma br_stream_length : forall b,
  br_wf b ->
  Z.of_nat (length (br_stream b)) = br_bits b + 8 * br_have b.
Proof.
  intros b (Hb & _ & Hv & _). unfold br_stream.
  rewrite length_app, bytes_bits_length, br_bytes_length.
  unfold zwrite. rewrite write_bits_length. lia.
Qed.

(* ==========================================================================
   2.  PULLBYTE: wf-preserving (below the 32-bit read ceiling), stream
       no-op.
   ========================================================================== *)

Lemma br_wf_pullbyte : forall b b',
  br_wf b -> br_bits b <= 31 ->
  br_pullbyte b = Some b' -> br_wf b'.
Proof.
  intros b b' (Hb & Hh & Hv & Hr) Hceil H.
  unfold br_pullbyte in H.
  destruct (Z.eqb_spec (br_have b) 0); [discriminate|].
  injection H as <-.
  unfold br_wf; cbn [br_bits br_hold br_have br_in].
  rewrite Z.shiftl_1_l in *.
  pose proof (Hr (br_next b)) as Hbyte.
  assert (Hpos : 0 < 2 ^ br_bits b) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hup : br_hold b + br_in b (br_next b) * 2 ^ br_bits b
                < 2 ^ (br_bits b + 8)).
  { rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia. }
  assert (Hm : 0 <= br_in b (br_next b) * 2 ^ br_bits b) by nia.
  repeat split; try lia;
    try (match goal with |- context [br_in b ?k] =>
           specialize (Hr k); lia end).
Qed.

Lemma br_stream_pullbyte : forall b b',
  br_wf b -> br_pullbyte b = Some b' ->
  br_stream b' = br_stream b.
Proof.
  intros b b' Hwf H.
  pose proof Hwf as (Hb & Hh & Hv & Hr).
  pose proof (br_bytes_pullbyte b b' ltac:(lia) H) as EBY.
  unfold br_pullbyte in H.
  destruct (Z.eqb_spec (br_have b) 0); [discriminate|].
  injection H as <-.
  unfold br_stream; cbn [br_bits br_hold].
  rewrite EBY, bytes_bits_cons.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_1_l in Hh.
  rewrite (zwrite_split (br_bits b) 8 (br_hold b) (br_in b (br_next b)))
    by lia.
  assert (Hbyte : byte_bits (br_in b (br_next b))
                  = zwrite 8 (br_in b (br_next b))).
  { rewrite <- byte_bits_zwrite. f_equal. unfold u8.
    rewrite Z.mod_small; [reflexivity | apply Hr]. }
  rewrite Hbyte.
  now rewrite <- app_assoc.
Qed.

(* ==========================================================================
   3.  The read agreement: BITS + DROPBITS is [read_bits].
   ========================================================================== *)

Lemma br_wf_dropbits : forall n b,
  br_wf b -> 0 <= n <= br_bits b ->
  br_wf (br_dropbits n b).
Proof.
  intros n b (Hb & Hh & Hv & Hr) Hn.
  unfold br_wf, br_dropbits; cbn [br_bits br_hold br_have br_in].
  rewrite Z.shiftl_1_l in *.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hpos : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  repeat split; try lia;
    try (apply Z.div_pos; lia);
    try (apply Z.div_lt_upper_bound; [lia|];
         rewrite <- Z.pow_add_r by lia;
         replace (n + (br_bits b - n)) with (br_bits b) by lia; lia);
    try (match goal with |- context [br_in b ?k] =>
           specialize (Hr k); lia end).
Qed.

Lemma br_read_agree : forall n b,
  br_wf b -> 0 <= n <= br_bits b ->
  read_bits (Z.to_nat n) (br_stream b)
  = Some (br_bits_of n b, br_stream (br_dropbits n b)).
Proof.
  intros n b (Hb & Hh & Hv & Hr) Hn.
  unfold br_stream, br_bits_of, br_dropbits;
    cbn [br_bits br_hold br_bytes br_have br_next br_in].
  rewrite Z.shiftl_1_l in *.
  rewrite (zwrite_cut n (br_bits b) (br_hold b)) by lia.
  rewrite <- app_assoc.
  unfold zwrite at 1.
  rewrite read_bits_write_bits
    by (replace (Z.of_nat (Z.to_nat n)) with n by lia;
        apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  f_equal. f_equal.
  - replace (2 ^ n - 1) with (Z.ones n)
      by (rewrite Z.ones_equiv; lia).
    now rewrite Z.land_ones by lia.
  - now rewrite Z.shiftr_div_pow2 by lia.
Qed.

(* ==========================================================================
   4.  NEEDBITS ([inf_nb]): stream no-op, wf-preserving, establishes the
       bit floor.  [n <= 32] is the C's read ceiling ([NEEDBITS(32)] is
       the largest call), which keeps [br_bits <= 39] through the pulls.
   ========================================================================== *)

Lemma inf_nb_go_ok : forall f n b b',
  br_wf b -> 0 <= n <= 32 ->
  inf_nb_go f n b = NBOk b' ->
  br_stream b' = br_stream b /\ br_wf b' /\ n <= br_bits b'.
Proof.
  induction f as [|f IH]; intros n b b' Hwf Hn H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb_spec (br_bits b) n); [discriminate|].
    injection H as <-. auto.
  - destruct (Z.ltb_spec (br_bits b) n).
    + destruct (br_pullbyte b) as [b1|] eqn:EP; [|discriminate].
      assert (Hwf1 : br_wf b1)
        by (apply (br_wf_pullbyte b b1); [exact Hwf | lia | exact EP]).
      destruct (IH n b1 b' Hwf1 Hn H) as (Hs & Hw & Hbits).
      rewrite Hs. rewrite (br_stream_pullbyte b b1 Hwf EP). auto.
    + injection H as <-. auto.
Qed.

Lemma inf_nb_ok : forall n b b',
  br_wf b -> 0 <= n <= 32 ->
  inf_nb n b = NBOk b' ->
  br_stream b' = br_stream b /\ br_wf b' /\ n <= br_bits b'.
Proof.
  intros n b b' Hwf Hn H. unfold inf_nb in H.
  exact (inf_nb_go_ok (Z.to_nat n) n b b' Hwf Hn H).
Qed.

(* ==========================================================================
   5.  Control.  One concrete reader state, both operations, byte-exact:
       reading 3 bits from hold 0b101 with byte 0xA5 pending agrees with
       the declarative read on the concatenated stream.
   ========================================================================== *)

Example zr_q6a_control :
  let b := {| br_in := zlist [165]; br_have := 1; br_next := 0;
              br_hold := 5; br_bits := 3 |} in
  read_bits 3%nat (br_stream b)
  = Some (br_bits_of 3 b, br_stream (br_dropbits 3 b))
  /\ br_bits_of 3 b = 5.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions br_read_agree.
Print Assumptions inf_nb_ok.
