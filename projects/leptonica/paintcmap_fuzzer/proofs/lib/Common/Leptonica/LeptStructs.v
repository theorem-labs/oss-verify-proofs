(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec StepTac StoreOk MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import WalksLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma zbv_plus1 : forall a, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !u_Z2bv_mod. change (bv_unsigned (1 : bv 64)) with 1.
  rewrite bv_wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

Lemma bytes_at_rdn : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at m a bs -> rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs. revert a. induction bs as [|b bs IH]; intros a Ha Hn HB; [reflexivity|].
  cbn [length] in Hn. cbn [length rdn].
  pose proof (HB 0 ltac:(cbn [length]; lia)) as H0. rewrite Z.add_0_r in H0. change (Z.to_nat 0) with 0%nat in H0. cbn [nth] in H0. rewrite H0.
  rewrite zbv_plus1.
  rewrite (IH (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. rewrite (HB (i + 1)) by (cbn [length]; lia).
  f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma bytes_at_app : forall m a bs1 bs2, bytes_at m a (bs1 ++ bs2) <-> bytes_at m a bs1 /\ bytes_at m (a + Z.of_nat (length bs1)) bs2.
Proof.
  intros m a bs1 bs2. unfold bytes_at. rewrite length_app. split.
  - intros H. split.
    + intros i Hi. rewrite H by lia. f_equal. rewrite app_nth1 by lia. reflexivity.
    + intros i Hi. replace (a + Z.of_nat (length bs1) + i) with (a + (Z.of_nat (length bs1) + i)) by lia.
      rewrite H by lia. f_equal. rewrite app_nth2 by lia. f_equal. lia.
  - intros [H1 H2] i Hi. destruct (Z_lt_ge_dec i (Z.of_nat (length bs1))).
    + rewrite H1 by lia. f_equal. rewrite app_nth1 by lia. reflexivity.
    + replace (a + i) with (a + Z.of_nat (length bs1) + (i - Z.of_nat (length bs1))) by lia.
      rewrite H2 by lia. f_equal. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma bytes_at_sub : forall m a bs (off n : nat), (off + n <= length bs)%nat ->
  bytes_at m a bs -> bytes_at m (a + Z.of_nat off) (firstn n (skipn off bs)).
Proof.
  intros m a bs off n Hle HB.
  rewrite <- (firstn_skipn off bs) in HB. apply bytes_at_app in HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn n (skipn off bs)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

Lemma bytes_at_field : forall m a bs (off n : nat), 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (off + n <= length bs)%nat -> bytes_at m a bs ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat off)) n = Some (firstn n (skipn off bs)).
Proof.
  intros m a bs off n Ha Hn Hle HB.
  pose proof (bytes_at_sub m a bs off n Hle HB) as HS.
  assert (L : length (firstn n (skipn off bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  pose proof (bytes_at_rdn m (a + Z.of_nat off) (firstn n (skipn off bs)) ltac:(lia) ltac:(rewrite L; lia) HS) as R.
  rewrite L in R. exact R.
Qed.

Lemma bytes_at_frame : forall m m' a bs, bytes_at m a bs ->
  (forall x : word, a <= u x < a + Z.of_nat (length bs) -> m' x = m x) -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at m' a bs.
Proof. intros m m' a bs HB HF Ha Hn i Hi. rewrite HF by (rewrite u_Z2bv by lia; lia). apply HB. exact Hi. Qed.

Lemma bytes_at_wbytes_out : forall m a bs (wa : word) ws, bytes_at m a bs ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> u wa + Z.of_nat (length ws) <= 2 ^ 64 ->
  (a + Z.of_nat (length bs) <= u wa \/ u wa + Z.of_nat (length ws) <= a) ->
  bytes_at (wbytes m wa ws) a bs.
Proof.
  intros m a bs wa ws HB Ha Hn Hw Hd. apply (bytes_at_frame m); [exact HB | | exact Ha | exact Hn].
  intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma bytes_at_wbytes_in : forall m a bs (off : nat) ws, bytes_at m a bs ->
  0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 -> (off + length ws <= length bs)%nat ->
  bytes_at (wbytes m (Z_to_bv 64 (a + Z.of_nat off)) ws) a (firstn off bs ++ ws ++ skipn (off + length ws) bs).
Proof.
  intros m a bs off ws HB Ha Hn Hle.
  assert (L1 : length (firstn off bs) = off) by (rewrite length_firstn; lia).
  assert (U : bv_unsigned (Z_to_bv 64 (a + Z.of_nat off)) = a + Z.of_nat off) by (rewrite u_Z2bv by lia; reflexivity).
  apply bytes_at_app. split; [|apply bytes_at_app; split].
  - pose proof HB as HB1. rewrite <- (firstn_skipn off bs) in HB1. apply bytes_at_app in HB1 as [HB1 _].
    apply (bytes_at_wbytes_out m a (firstn off bs) _ ws HB1 Ha); rewrite ?L1, ?U; lia.
  - rewrite L1. intros i Hi. rewrite wbytes_inside; rewrite ?U, ?u_Z2bv by lia; [|lia|lia]. f_equal. f_equal. lia.
  - rewrite L1. pose proof HB as HB2. rewrite <- (firstn_skipn (off + length ws) bs) in HB2. apply bytes_at_app in HB2 as [_ HB2].
    rewrite length_firstn, Nat.min_l in HB2 by lia.
    replace (a + Z.of_nat off + Z.of_nat (length ws)) with (a + Z.of_nat (off + length ws)) by lia.
    apply (bytes_at_wbytes_out m _ _ _ ws HB2); rewrite ?length_skipn, ?U; lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros : forall m a (n : nat), (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
  bytes_at m a (repeat (Z_to_bv 8 0) n).
Proof. intros m a n H i Hi. rewrite repeat_length in Hi. rewrite H by lia. f_equal. rewrite nth_repeat. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w2b_Z : forall (k : nat) z, 0 <= z < 2 ^ 64 -> word_to_le_bytes k (Z_to_bv 64 z) = Z_to_le_bytes k z.
Proof. intros k z Hz. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma lez_u : forall (k : nat) z, (k <= 8)%nat -> 0 <= z < 2 ^ (8 * Z.of_nat k) -> bytes_le_to_Z (Z_to_le_bytes k z) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros k z Hk Hz. rewrite bytes_le_Z_to_le by lia. rewrite Z.mod_small by lia.
  assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record pixv := PIXV {
  p_w : Z; p_h : Z; p_d : Z; p_spp : Z; p_wpl : Z; p_rc : Z; p_xres : Z; p_yres : Z; p_fmt : Z; p_spec : Z;
  p_text : Z; p_cmap : Z; p_data : Z }.

Definition pix_bytes (v : pixv) : list byte :=
  Z_to_le_bytes 4 (p_w v) ++ Z_to_le_bytes 4 (p_h v) ++ Z_to_le_bytes 4 (p_d v) ++ Z_to_le_bytes 4 (p_spp v) ++
  Z_to_le_bytes 4 (p_wpl v) ++ Z_to_le_bytes 4 (p_rc v) ++ Z_to_le_bytes 4 (p_xres v) ++ Z_to_le_bytes 4 (p_yres v) ++
  Z_to_le_bytes 4 (p_fmt v) ++ Z_to_le_bytes 4 (p_spec v) ++
  Z_to_le_bytes 8 (p_text v) ++ Z_to_le_bytes 8 (p_cmap v) ++ Z_to_le_bytes 8 (p_data v).

Lemma pix_bytes_len : forall v, length (pix_bytes v) = 64%nat.
Proof. intros v. reflexivity. Qed.

(* [comment removed for export] *)
Record pix_wf (v : pixv) : Prop := PIXWF {
  wf_w : 0 <= p_w v < 2 ^ 31; wf_h : 0 <= p_h v < 2 ^ 31; wf_d : 0 <= p_d v < 2 ^ 31; wf_spp : 0 <= p_spp v < 2 ^ 31;
  wf_wpl : 0 <= p_wpl v < 2 ^ 31; wf_rc : 0 <= p_rc v < 2 ^ 31; wf_xres : 0 <= p_xres v < 2 ^ 31; wf_yres : 0 <= p_yres v < 2 ^ 31;
  wf_fmt : 0 <= p_fmt v < 2 ^ 31; wf_spec : 0 <= p_spec v < 2 ^ 31;
  wf_text : 0 <= p_text v < 2 ^ 64; wf_cmap : 0 <= p_cmap v < 2 ^ 64; wf_data : 0 <= p_data v < 2 ^ 64 }.

Definition PIXat (m : word -> option byte) (p : Z) (v : pixv) : Prop :=
  0 <= p /\ p + 64 < 2 ^ 64 /\ pix_wf v /\ bytes_at m p (pix_bytes v).

Definition pix0 : pixv := PIXV 0 0 0 0 0 0 0 0 0 0 0 0 0.
Lemma pix0_wf : pix_wf pix0. Proof. constructor; cbn; lia. Qed.
Lemma pix_bytes_0 : pix_bytes pix0 = repeat (Z_to_bv 8 0) 64.
Proof. reflexivity. Qed.

Lemma PIXat_zero : forall m p, 0 <= p -> p + 64 < 2 ^ 64 ->
  (forall i, 0 <= i < 64 -> m (Z_to_bv 64 (p + i)) = Some (Z_to_bv 8 0)) -> PIXat m p pix0.
Proof.
  intros m p Hp Hn HZ. split; [lia|]. split; [lia|]. split; [apply pix0_wf|]. rewrite pix_bytes_0. apply bytes_at_zeros. exact HZ.
Qed.

Lemma PIXat_frame : forall m m' p v, PIXat m p v -> (forall x : word, p <= u x < p + 64 -> m' x = m x) -> PIXat m' p v.
Proof.
  intros m m' p v (Hp & Hn & WF & HB) HF. split; [lia|]. split; [lia|]. split; [exact WF|].
  apply (bytes_at_frame m); [exact HB | rewrite pix_bytes_len; exact HF | lia | rewrite pix_bytes_len; cbn; lia].
Qed.

Lemma PIXat_out : forall m p v (wa : word) ws, PIXat m p v -> u wa + Z.of_nat (length ws) <= 2 ^ 64 ->
  (p + 64 <= u wa \/ u wa + Z.of_nat (length ws) <= p) -> PIXat (wbytes m wa ws) p v.
Proof.
  intros m p v wa ws HP Hw Hd. apply (PIXat_frame m); [exact HP|]. intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma PIXat_defined : forall m p v (x : word), PIXat m p v -> p <= u x < p + 64 -> m x <> None.
Proof.
  intros m p v x (Hp & Hn & _ & HB) Hx.
  pose proof (HB (u x - p) ltac:(rewrite pix_bytes_len; cbn; lia)) as E.
  replace (Z_to_bv 64 (p + (u x - p))) with x in E by (apply bv_eq; rewrite u_Z2bv by lia; lia). rewrite E. discriminate.
Qed.

(* [comment removed for export] *)
Local Ltac fld HP off n :=
  let H := fresh in
  lazymatch type of HP with PIXat ?m ?p ?v =>
  destruct HP as (?Hp & ?Hn & ?WF & ?HB);
  pose proof (bytes_at_field m p (pix_bytes v) off n ltac:(lia) ltac:(rewrite pix_bytes_len; cbn; lia) ltac:(rewrite pix_bytes_len; cbn; lia) HB) as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H; rewrite ?Z.add_0_r in H; exact H end.

Lemma PIX_rd_w : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 p) 4 = Some (Z_to_le_bytes 4 (p_w v)).
Proof. intros m p v HP. fld HP 0%nat 4%nat. Qed.
Lemma PIX_rd_h : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 4)) 4 = Some (Z_to_le_bytes 4 (p_h v)).
Proof. intros m p v HP. fld HP 4%nat 4%nat. Qed.
Lemma PIX_rd_d : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 8)) 4 = Some (Z_to_le_bytes 4 (p_d v)).
Proof. intros m p v HP. fld HP 8%nat 4%nat. Qed.
Lemma PIX_rd_spp : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 12)) 4 = Some (Z_to_le_bytes 4 (p_spp v)).
Proof. intros m p v HP. fld HP 12%nat 4%nat. Qed.
Lemma PIX_rd_wpl : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 16)) 4 = Some (Z_to_le_bytes 4 (p_wpl v)).
Proof. intros m p v HP. fld HP 16%nat 4%nat. Qed.
Lemma PIX_rd_rc : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 20)) 4 = Some (Z_to_le_bytes 4 (p_rc v)).
Proof. intros m p v HP. fld HP 20%nat 4%nat. Qed.
Lemma PIX_rd_fmt : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 32)) 4 = Some (Z_to_le_bytes 4 (p_fmt v)).
Proof. intros m p v HP. fld HP 32%nat 4%nat. Qed.
Lemma PIX_rd_spec : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 36)) 4 = Some (Z_to_le_bytes 4 (p_spec v)).
Proof. intros m p v HP. fld HP 36%nat 4%nat. Qed.
Lemma PIX_rd_text : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 40)) 8 = Some (Z_to_le_bytes 8 (p_text v)).
Proof. intros m p v HP. fld HP 40%nat 8%nat. Qed.
Lemma PIX_rd_cmap : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 48)) 8 = Some (Z_to_le_bytes 8 (p_cmap v)).
Proof. intros m p v HP. fld HP 48%nat 8%nat. Qed.
Lemma PIX_rd_data : forall m p v, PIXat m p v -> rdn segs m (Z_to_bv 64 (p + 56)) 8 = Some (Z_to_le_bytes 8 (p_data v)).
Proof. intros m p v HP. fld HP 56%nat 8%nat. Qed.

(* [comment removed for export] *)
Definition set_w (v : pixv) z := PIXV z (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_h (v : pixv) z := PIXV (p_w v) z (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_d (v : pixv) z := PIXV (p_w v) (p_h v) z (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_spp (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) z (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_wpl (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) z (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_rc (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) z (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_fmt (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) z (p_spec v) (p_text v) (p_cmap v) (p_data v).
Definition set_spec (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) z (p_text v) (p_cmap v) (p_data v).
Definition set_text (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) z (p_cmap v) (p_data v).
Definition set_cmap (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) z (p_data v).
Definition set_data (v : pixv) z := PIXV (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_rc v) (p_xres v) (p_yres v) (p_fmt v) (p_spec v) (p_text v) (p_cmap v) z.

Local Ltac wr HP off k z SET :=
  lazymatch type of HP with PIXat ?m ?p ?v =>
  destruct HP as (?Hp & ?Hn & ?WF & ?HB);
  split; [lia|]; split; [lia|]; split; [destruct WF; constructor; cbn; lia|];
  let H := fresh in
  pose proof (bytes_at_wbytes_in m p (pix_bytes v) off (Z_to_le_bytes k z) HB ltac:(lia) ltac:(rewrite pix_bytes_len; cbn; lia)
                ltac:(rewrite pix_bytes_len, length_Z_to_le_bytes; cbn; lia)) as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H; rewrite ?Z.add_0_r in H;
  rewrite w2b_Z by lia; exact H end.

Lemma PIX_wr_w : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_w v z).
Proof. intros m p v z HP Hz. wr HP 0%nat 4%nat z set_w. Qed.
Lemma PIX_wr_h : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 4)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_h v z).
Proof. intros m p v z HP Hz. wr HP 4%nat 4%nat z set_h. Qed.
Lemma PIX_wr_d : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 8)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_d v z).
Proof. intros m p v z HP Hz. wr HP 8%nat 4%nat z set_d. Qed.
Lemma PIX_wr_spp : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 12)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_spp v z).
Proof. intros m p v z HP Hz. wr HP 12%nat 4%nat z set_spp. Qed.
Lemma PIX_wr_wpl : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 16)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_wpl v z).
Proof. intros m p v z HP Hz. wr HP 16%nat 4%nat z set_wpl. Qed.
Lemma PIX_wr_rc : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_rc v z).
Proof. intros m p v z HP Hz. wr HP 20%nat 4%nat z set_rc. Qed.
Lemma PIX_wr_fmt : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 32)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_fmt v z).
Proof. intros m p v z HP Hz. wr HP 32%nat 4%nat z set_fmt. Qed.
Lemma PIX_wr_spec : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 31 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 36)) (word_to_le_bytes 4 (Z_to_bv 64 z))) p (set_spec v z).
Proof. intros m p v z HP Hz. wr HP 36%nat 4%nat z set_spec. Qed.
Lemma PIX_wr_text : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 64 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 40)) (word_to_le_bytes 8 (Z_to_bv 64 z))) p (set_text v z).
Proof. intros m p v z HP Hz. wr HP 40%nat 8%nat z set_text. Qed.
Lemma PIX_wr_cmap : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 64 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 48)) (word_to_le_bytes 8 (Z_to_bv 64 z))) p (set_cmap v z).
Proof. intros m p v z HP Hz. wr HP 48%nat 8%nat z set_cmap. Qed.
Lemma PIX_wr_data : forall m p v z, PIXat m p v -> 0 <= z < 2 ^ 64 ->
  PIXat (wbytes m (Z_to_bv 64 (p + 56)) (word_to_le_bytes 8 (Z_to_bv 64 z))) p (set_data v z).
Proof. intros m p v z HP Hz. wr HP 56%nat 8%nat z set_data. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record cmapv := CMAPV { c_arr : Z; c_d : Z; c_nalloc : Z; c_n : Z; c_pad : Z }.

Definition cmap_bytes (v : cmapv) : list byte :=
  Z_to_le_bytes 8 (c_arr v) ++ Z_to_le_bytes 4 (c_d v) ++ Z_to_le_bytes 4 (c_nalloc v) ++ Z_to_le_bytes 4 (c_n v) ++ Z_to_le_bytes 4 (c_pad v).

Lemma cmap_bytes_len : forall v, length (cmap_bytes v) = 24%nat.
Proof. intros v. reflexivity. Qed.

Record cmap_wf (v : cmapv) : Prop := CMAPWF {
  cf_arr : 0 <= c_arr v < 2 ^ 64; cf_d : 0 <= c_d v < 2 ^ 31; cf_nalloc : 0 <= c_nalloc v < 2 ^ 31; cf_n : 0 <= c_n v < 2 ^ 31;
  cf_pad : 0 <= c_pad v < 2 ^ 31 }.

Definition CMAPat (m : word -> option byte) (c : Z) (v : cmapv) : Prop :=
  0 <= c /\ c + 24 < 2 ^ 64 /\ cmap_wf v /\ bytes_at m c (cmap_bytes v).

Definition cmap0 : cmapv := CMAPV 0 0 0 0 0.
Lemma cmap_bytes_0 : cmap_bytes cmap0 = repeat (Z_to_bv 8 0) 24.
Proof. reflexivity. Qed.

Lemma CMAPat_zero : forall m c, 0 <= c -> c + 24 < 2 ^ 64 ->
  (forall i, 0 <= i < 24 -> m (Z_to_bv 64 (c + i)) = Some (Z_to_bv 8 0)) -> CMAPat m c cmap0.
Proof.
  intros m c Hc Hn HZ. split; [lia|]. split; [lia|]. split; [constructor; cbn; lia|]. rewrite cmap_bytes_0. apply bytes_at_zeros. exact HZ.
Qed.

Lemma CMAPat_frame : forall m m' c v, CMAPat m c v -> (forall x : word, c <= u x < c + 24 -> m' x = m x) -> CMAPat m' c v.
Proof.
  intros m m' c v (Hc & Hn & WF & HB) HF. split; [lia|]. split; [lia|]. split; [exact WF|].
  apply (bytes_at_frame m); [exact HB | rewrite cmap_bytes_len; exact HF | lia | rewrite cmap_bytes_len; cbn; lia].
Qed.

Lemma CMAPat_out : forall m c v (wa : word) ws, CMAPat m c v -> u wa + Z.of_nat (length ws) <= 2 ^ 64 ->
  (c + 24 <= u wa \/ u wa + Z.of_nat (length ws) <= c) -> CMAPat (wbytes m wa ws) c v.
Proof.
  intros m c v wa ws HP Hw Hd. apply (CMAPat_frame m); [exact HP|]. intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma CMAPat_defined : forall m c v (x : word), CMAPat m c v -> c <= u x < c + 24 -> m x <> None.
Proof.
  intros m c v x (Hc & Hn & _ & HB) Hx.
  pose proof (HB (u x - c) ltac:(rewrite cmap_bytes_len; cbn; lia)) as E.
  replace (Z_to_bv 64 (c + (u x - c))) with x in E by (apply bv_eq; rewrite u_Z2bv by lia; lia). rewrite E. discriminate.
Qed.

Local Ltac cfld HP off n :=
  let H := fresh in
  lazymatch type of HP with CMAPat ?m ?p ?v =>
  destruct HP as (?Hp & ?Hn & ?WF & ?HB);
  pose proof (bytes_at_field m p (cmap_bytes v) off n ltac:(lia) ltac:(rewrite cmap_bytes_len; cbn; lia) ltac:(rewrite cmap_bytes_len; cbn; lia) HB) as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H; rewrite ?Z.add_0_r in H; exact H end.

Lemma CMAP_rd_arr : forall m c v, CMAPat m c v -> rdn segs m (Z_to_bv 64 c) 8 = Some (Z_to_le_bytes 8 (c_arr v)).
Proof. intros m c v HP. cfld HP 0%nat 8%nat. Qed.
Lemma CMAP_rd_d : forall m c v, CMAPat m c v -> rdn segs m (Z_to_bv 64 (c + 8)) 4 = Some (Z_to_le_bytes 4 (c_d v)).
Proof. intros m c v HP. cfld HP 8%nat 4%nat. Qed.
Lemma CMAP_rd_nalloc : forall m c v, CMAPat m c v -> rdn segs m (Z_to_bv 64 (c + 12)) 4 = Some (Z_to_le_bytes 4 (c_nalloc v)).
Proof. intros m c v HP. cfld HP 12%nat 4%nat. Qed.
Lemma CMAP_rd_n : forall m c v, CMAPat m c v -> rdn segs m (Z_to_bv 64 (c + 16)) 4 = Some (Z_to_le_bytes 4 (c_n v)).
Proof. intros m c v HP. cfld HP 16%nat 4%nat. Qed.

Definition cset_arr (v : cmapv) z := CMAPV z (c_d v) (c_nalloc v) (c_n v) (c_pad v).
Definition cset_d (v : cmapv) z := CMAPV (c_arr v) z (c_nalloc v) (c_n v) (c_pad v).
Definition cset_nalloc (v : cmapv) z := CMAPV (c_arr v) (c_d v) z (c_n v) (c_pad v).
Definition cset_n (v : cmapv) z := CMAPV (c_arr v) (c_d v) (c_nalloc v) z (c_pad v).

Local Ltac cwr HP off k z :=
  lazymatch type of HP with CMAPat ?m ?p ?v =>
  destruct HP as (?Hp & ?Hn & ?WF & ?HB);
  split; [lia|]; split; [lia|]; split; [destruct WF; constructor; cbn; lia|];
  let H := fresh in
  pose proof (bytes_at_wbytes_in m p (cmap_bytes v) off (Z_to_le_bytes k z) HB ltac:(lia) ltac:(rewrite cmap_bytes_len; cbn; lia)
                ltac:(rewrite cmap_bytes_len, length_Z_to_le_bytes; cbn; lia)) as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H; rewrite ?Z.add_0_r in H;
  rewrite w2b_Z by lia; exact H end.

Lemma CMAP_wr_arr : forall m c v z, CMAPat m c v -> 0 <= z < 2 ^ 64 ->
  CMAPat (wbytes m (Z_to_bv 64 c) (word_to_le_bytes 8 (Z_to_bv 64 z))) c (cset_arr v z).
Proof. intros m c v z HP Hz. cwr HP 0%nat 8%nat z. Qed.
Lemma CMAP_wr_d : forall m c v z, CMAPat m c v -> 0 <= z < 2 ^ 31 ->
  CMAPat (wbytes m (Z_to_bv 64 (c + 8)) (word_to_le_bytes 4 (Z_to_bv 64 z))) c (cset_d v z).
Proof. intros m c v z HP Hz. cwr HP 8%nat 4%nat z. Qed.
Lemma CMAP_wr_nalloc : forall m c v z, CMAPat m c v -> 0 <= z < 2 ^ 31 ->
  CMAPat (wbytes m (Z_to_bv 64 (c + 12)) (word_to_le_bytes 4 (Z_to_bv 64 z))) c (cset_nalloc v z).
Proof. intros m c v z HP Hz. cwr HP 12%nat 4%nat z. Qed.
Lemma CMAP_wr_n : forall m c v z, CMAPat m c v -> 0 <= z < 2 ^ 31 ->
  CMAPat (wbytes m (Z_to_bv 64 (c + 16)) (word_to_le_bytes 4 (Z_to_bv 64 z))) c (cset_n v z).
Proof. intros m c v z HP Hz. cwr HP 16%nat 4%nat z. Qed.

(* [comment removed for export] *)
Lemma rdn_bytes_at : forall m (a : Z) bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (a + i)) <> None) ->
  rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> bytes_at m a bs.
Proof.
  intros m a bs. revert a. induction bs as [|b bs IH]; intros a Ha Hn Hdef R i Hi; [cbn in Hi; lia|].
  cbn [length] in Hn, Hi, Hdef. rewrite Nat2Z.inj_succ in Hn, Hi, Hdef. cbn [length rdn] in R.
  destruct (m (Z_to_bv 64 a)) as [b0|] eqn:E0.
  - destruct (rdn segs m (Z_to_bv 64 a + 1) (length bs)) as [rest|] eqn:ER; [|discriminate].
    injection R as Eb Ers. subst b0 rest.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + rewrite Z.add_0_r. cbn. exact E0.
    + rewrite zbv_plus1 in ER.
      pose proof (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros j Hj; replace (a + 1 + j) with (a + (j + 1)) by lia; apply Hdef; lia) ER (i - 1) ltac:(lia)) as X.
      replace (a + 1 + (i - 1)) with (a + i) in X by lia. rewrite X. f_equal.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
  - exfalso. pose proof (Hdef 0 ltac:(lia)) as D. rewrite Z.add_0_r in D. exact (D E0).
Qed.

Lemma CMAPat_set_n : forall m m' c v n, CMAPat m c v -> 0 <= n < 2 ^ 31 ->
  (forall x : word, c <= u x < c + 24 -> ~ (c + 16 <= u x < c + 20) -> m' x = m x) ->
  (forall x : word, c <= u x < c + 24 -> m' x <> None) ->
  rdn segs m' (Z_to_bv 64 (c + 16)) 4 = Some (Z_to_le_bytes 4 n) -> CMAPat m' c (cset_n v n).
Proof.
  intros m m' c v n (Hc & Hn64 & WF & HB) Hn FR DEF R. split; [lia|]. split; [lia|]. split; [destruct WF; constructor; cbn; lia|].
  unfold cmap_bytes. cbn [c_arr c_d c_nalloc c_n c_pad cset_n].
  unfold cmap_bytes in HB.
  apply bytes_at_app in HB as [H1 HB]. apply bytes_at_app in HB as [H2 HB]. apply bytes_at_app in HB as [H3 HB]. apply bytes_at_app in HB as [H4 H5].
  rewrite !length_Z_to_le_bytes in *. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.add] in *.
  Ltac fixaddr K := match goal with |- bytes_at _ ?a _ => replace a with K by (rewrite ?length_Z_to_le_bytes; cbn; lia) end.
  Ltac fixhyp H K := match type of H with bytes_at _ ?a _ => replace a with K in H by (rewrite ?length_Z_to_le_bytes; cbn; lia) end.
  fixhyp H2 (c + 8). fixhyp H3 (c + 12). fixhyp H4 (c + 16). fixhyp H5 (c + 20).
  apply bytes_at_app; split; [|apply bytes_at_app; split; [|apply bytes_at_app; split; [|apply bytes_at_app; split]]].
  - eapply bytes_at_frame; [exact H1 | | lia | rewrite length_Z_to_le_bytes; cbn; lia]. rewrite length_Z_to_le_bytes. cbn. intros x Hx. apply FR; lia.
  - fixaddr (c + 8). eapply bytes_at_frame; [exact H2 | | lia | rewrite length_Z_to_le_bytes; cbn; lia]. rewrite length_Z_to_le_bytes. cbn. intros x Hx. apply FR; lia.
  - fixaddr (c + 12). eapply bytes_at_frame; [exact H3 | | lia | rewrite length_Z_to_le_bytes; cbn; lia]. rewrite length_Z_to_le_bytes. cbn. intros x Hx. apply FR; lia.
  - fixaddr (c + 16). apply (rdn_bytes_at m' (c + 16) (Z_to_le_bytes 4 n)); rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | | exact R].
    cbn. intros i Hi. apply DEF. rewrite u_Z2bv by lia. lia.
  - fixaddr (c + 20). eapply bytes_at_frame; [exact H5 | | lia | rewrite length_Z_to_le_bytes; cbn; lia]. rewrite length_Z_to_le_bytes. cbn. intros x Hx. apply FR; lia.
Qed.

End WithSegs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
