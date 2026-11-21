(** * Bridge.BrFlush — pair D10 of PAIRS.md: [flush_pending], S5 vs RT.

    The dequeue side of the pending queue, and the first bridge that touches
    the STREAM.  S5's [flush_pending] ([Z/DeflateLz.v:289]) runs [bi_flush],
    copies [min(pending, avail_out)] bytes from [pending_buf[pending_out]] into
    the call's reversed output list, advances [pending_out], and resets it to
    0 once the queue is empty; RT's ([Spec/PngModel/Deflate.v:544]) moves the
    same count from the head of [bw_out] onto the end of the cumulative
    [zs_out].

    The relation [fp_rel s t pre] adds three stream conjuncts to [bw_rel]:
    RT's cumulative output is [pre] (the output of earlier calls; [] for
    compress_fuzzer's one-call compress) followed by S5's output of this
    call, and the two [avail_out]/[total_out] fields agree.  The premises are
    the ones the C's integer types impose: [avail_out >= 0], the queue fits a
    [uInt], and [total_out] does not wrap.

    S5's state updates are handled with the projection-over-setter database
    databases of [Bridge/S5Fields.v], never by unfolding a setter. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelDefl BrBits S5Fields.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  Slice and stream kit                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma slice_nat_firstn : forall {A} n k (a : parr A) o,
  (k <= n)%nat -> arr_slice_nat a o k = firstn k (arr_slice_nat a o n).
Proof.
  induction n as [|n IH]; intros k a o Hk.
  - replace k with O by lia. reflexivity.
  - destruct k as [|k]; [reflexivity|].
    cbn [arr_slice_nat firstn]. f_equal. apply IH. lia.
Qed.

Lemma slice_nat_skipn : forall {A} n k (a : parr A) o,
  (k <= n)%nat -> arr_slice_nat a (o + Z.of_nat k) (n - k) = skipn k (arr_slice_nat a o n).
Proof.
  induction n as [|n IH]; intros k a o Hk.
  - replace k with O by lia. reflexivity.
  - destruct k as [|k].
    + change (Z.of_nat 0) with 0. cbn [skipn]. rewrite Z.add_0_r, Nat.sub_0_r. reflexivity.
    + cbn [arr_slice_nat skipn]. replace (S n - S k)%nat with (n - k)%nat by lia.
      replace (o + Z.of_nat (S k)) with ((o + 1) + Z.of_nat k) by lia.
      apply IH. lia.
Qed.

Lemma slice_firstn : forall (a : arr) o k n,
  0 <= k <= n -> arr_slice a o k = firstn (Z.to_nat k) (arr_slice a o n).
Proof. intros a o k n Hk. unfold arr_slice. apply slice_nat_firstn. lia. Qed.

Lemma slice_skipn : forall (a : arr) o k n,
  0 <= k <= n -> arr_slice a (o + k) (n - k) = skipn (Z.to_nat k) (arr_slice a o n).
Proof.
  intros a o k n Hk. unfold arr_slice.
  replace (Z.to_nat (n - k)) with (Z.to_nat n - Z.to_nat k)%nat by lia.
  replace (o + k) with (o + Z.of_nat (Z.to_nat k)) by lia.
  apply slice_nat_skipn. lia.
Qed.

Lemma cs_output_emit : forall st l,
  DeflateState.cs_output (DeflateState.cs_emit st l) = DeflateState.cs_output st ++ l.
Proof.
  intros st l. unfold DeflateState.cs_output, DeflateState.cs_emit, DeflateState.cset_out_rev.
  cbn [DeflateState.cs_out_rev]. rewrite !rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive.
  reflexivity.
Qed.

Lemma cs_output_cset_avail_out : forall x v,
  DeflateState.cs_output (DeflateState.cset_avail_out x v) = DeflateState.cs_output x.
Proof. reflexivity. Qed.
Lemma cs_output_cset_total_out : forall x v,
  DeflateState.cs_output (DeflateState.cset_total_out x v) = DeflateState.cs_output x.
Proof. reflexivity. Qed.
Lemma cs_avail_out_emit : forall x l,
  DeflateState.cs_avail_out (DeflateState.cs_emit x l) = DeflateState.cs_avail_out x.
Proof. reflexivity. Qed.
Lemma cs_total_out_emit : forall x l,
  DeflateState.cs_total_out (DeflateState.cs_emit x l) = DeflateState.cs_total_out x.
Proof. reflexivity. Qed.
Global Hint Rewrite cs_output_emit cs_avail_out_emit cs_total_out_emit : s5c_emit.
Global Hint Rewrite cs_output_cset_avail_out : s5c_avail_out.
Global Hint Rewrite cs_output_cset_total_out : s5c_total_out.

(** The setters [flush_pending] uses, and nothing else. *)
Ltac fp_fields :=
  autorewrite with s5f_pending s5f_strm s5f_pending_out s5c_emit s5c_avail_out s5c_total_out.

(* ------------------------------------------------------------------------- *)
(* 2.  The relation and the bridge                                           *)
(* ------------------------------------------------------------------------- *)

Definition fp_rel (s : DeflateState.deflate_state) (t : Deflate.DSt) (pre : list Z) : Prop :=
  bw_rel s (PngModel.Trees.ts_bw (Deflate.d_ts t))
  /\ Deflate.zs_out (Deflate.d_strm t) = pre ++ DeflateState.cs_output (DeflateState.ds_strm s)
  /\ Deflate.zs_availout (Deflate.d_strm t) = DeflateState.cs_avail_out (DeflateState.ds_strm s)
  /\ Deflate.zs_totalout (Deflate.d_strm t) = DeflateState.cs_total_out (DeflateState.ds_strm s).

(** The integer-type premises: [avail_out] is a [uInt], the pending buffer is
    addressable by a [uInt] count, [total_out] is a [uLong] that does not wrap. *)
Definition fp_ok (s : DeflateState.deflate_state) : Prop :=
  0 <= DeflateState.cs_avail_out (DeflateState.ds_strm s)
  /\ arr_len (DeflateState.ds_pending_buf s) < 2 ^ 32
  /\ 0 <= DeflateState.cs_total_out (DeflateState.ds_strm s)
  /\ DeflateState.cs_total_out (DeflateState.ds_strm s) + arr_len (DeflateState.ds_pending_buf s) < 2 ^ 64.

Theorem br_flush_pending : forall s t pre,
  fp_rel s t pre -> flush_room s -> fp_ok s ->
  fp_rel (DeflateLz.flush_pending s) (Deflate.flush_pending t) pre.
Proof.
  intros s t pre (Hbw & Hout & Hav & Htot) Hfr (Hav0 & Hlen32 & Htot0 & Htot64).
  destruct (br_bi_flush s _ Hbw Hfr) as (Hbw1 & Ho1 & Hl1 & Hs1).
  unfold DeflateLz.flush_pending, Deflate.flush_pending. cbv zeta.
  unfold Z.Trees.tr_flush_bits, PngModel.Trees.tr_flush_bits.
  change (PngModel.Trees.ts_bw (PngModel.Trees.set_bw (ZBitsOut.bw_flush (PngModel.Trees.ts_bw (Deflate.d_ts t)))
                                                       (Deflate.d_ts t)))
    with (ZBitsOut.bw_flush (PngModel.Trees.ts_bw (Deflate.d_ts t))).
  rewrite Hs1, Hav.
  revert Hbw1 Ho1 Hl1 Hs1.
  generalize (Z.Trees.bi_flush s) as s1.
  generalize (ZBitsOut.bw_flush (PngModel.Trees.ts_bw (Deflate.d_ts t))) as b1.
  intros b1 s1 Hbw1 Ho1 Hl1 Hs1.
  destruct Hbw1 as ((Hpo & Hp & Hin & Hsl) & Hb & Hv).
  assert (HlenP : Chunk.zlen (ZBitsOut.bw_out b1) = DeflateState.ds_pending s1).
  { rewrite <- Hsl. change Chunk.zlen with (@zlength Z). rewrite arr_slice_length. lia. }
  rewrite HlenP.
  rewrite (wrap32_id (DeflateState.ds_pending s1)) by lia.
  remember (if DeflateState.cs_avail_out (DeflateState.ds_strm s) <? DeflateState.ds_pending s1
            then DeflateState.cs_avail_out (DeflateState.ds_strm s) else DeflateState.ds_pending s1) as L eqn:HL'.
  assert (HL : 0 <= L <= DeflateState.ds_pending s1 /\ L <= DeflateState.cs_avail_out (DeflateState.ds_strm s))
    by (subst L; destruct (Z.ltb_spec (DeflateState.cs_avail_out (DeflateState.ds_strm s)) (DeflateState.ds_pending s1)); lia).
  destruct (Z.eqb_spec L 0) as [L0|L0].
  - (* nothing moves *)
    unfold fp_rel. cbn [Deflate.d_ts Deflate.d_strm Deflate.setD_ts PngModel.Trees.ts_bw PngModel.Trees.set_bw].
    split; [exact (conj (conj Hpo (conj Hp (conj Hin Hsl))) (conj Hb Hv))|].
    rewrite Hs1. split; [exact Hout|]. split; [exact Hav | exact Htot].
  - (* L bytes move *)
    assert (Hpre : arr_slice (DeflateState.ds_pending_buf s1) (DeflateState.ds_pending_out s1) L
                   = firstn (Z.to_nat L) (ZBitsOut.bw_out b1))
      by (rewrite <- Hsl; apply slice_firstn; lia).
    assert (Hsuf : arr_slice (DeflateState.ds_pending_buf s1) (DeflateState.ds_pending_out s1 + L)
                             (DeflateState.ds_pending s1 - L)
                   = skipn (Z.to_nat L) (ZBitsOut.bw_out b1))
      by (rewrite <- Hsl; apply slice_skipn; lia).
    assert (Hw64 : wrap64 (DeflateState.cs_total_out (DeflateState.ds_strm s) + L)
                   = DeflateState.cs_total_out (DeflateState.ds_strm s) + L)
      by (apply wrap64_id; lia).
    assert (Hlen : length (ZBitsOut.bw_out b1) = Z.to_nat (DeflateState.ds_pending s1)).
    { rewrite <- Hsl. unfold arr_slice. apply arr_slice_nat_length. }
    unfold fp_rel, bw_rel, pend_rel.
    fp_fields.
    destruct (Z.eqb_spec (DeflateState.ds_pending s1 - L) 0) as [E|E];
      cbv beta iota; fp_fields;
      cbn [Deflate.d_ts Deflate.d_strm Deflate.setD_ts Deflate.setD_strm
           Deflate.setZ_out Deflate.setZ_availout Deflate.setZ_totalout
           Deflate.zs_out Deflate.zs_availout Deflate.zs_totalout
           PngModel.Trees.ts_bw PngModel.Trees.set_bw
           ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid];
      rewrite ?Hs1, ?Hw64.
    + (* the queue empties: pending_out resets to 0 *)
      split; [split; [|split; [exact Hb | exact Hv]]|].
      * split; [lia|]. split; [lia|]. split; [lia|].
        rewrite E. rewrite skipn_all2 by lia. reflexivity.
      * rewrite Hpre, Hout, <- app_assoc. split; [reflexivity|]. split; [reflexivity|]. rewrite Htot. reflexivity.
    + split; [split; [|split; [exact Hb | exact Hv]]|].
      * split; [lia|]. split; [lia|]. split; [lia|]. exact Hsuf.
      * rewrite Hpre, Hout, <- app_assoc. split; [reflexivity|]. split; [reflexivity|]. rewrite Htot. reflexivity.
Qed.

Print Assumptions br_flush_pending.
