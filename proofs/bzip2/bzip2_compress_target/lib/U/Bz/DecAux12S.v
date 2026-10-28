(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU11 BzDOKS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12S.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma zh16_nth_lo : forall a n i, 0 <= i -> 2 * i + 2 <= n -> nth_error (zh16 a n) (Z.to_nat (2 * i)) = Some (Z_to_bv 8 (zget a i mod 256)).
Proof.
  intros a n i Hi Hn. unfold zh16. rewrite tab_nth by lia. f_equal.
  replace (2 * i / 2) with i by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  replace (2 * i) with (i * 2) by lia. rewrite Z_mod_mult. cbn [Z.mul Z.pow Z.pow_pos Pos.iter]. rewrite Z.div_1_r. symmetry. apply Z_to_bv8_mod256.
Qed.
Lemma zh16_nth_hi : forall a n i, 0 <= i -> 2 * i + 2 <= n -> nth_error (zh16 a n) (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 8 (zget a i / 256)).
Proof.
  intros a n i Hi Hn. unfold zh16. rewrite tab_nth by lia. f_equal.
  replace ((2 * i + 1) / 2) with i by (rewrite Z.mul_comm, Z.add_comm, Z.div_add by lia; cbn; lia).
  replace ((2 * i + 1) mod 2) with 1 by (rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; reflexivity).
  reflexivity.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.
  (* [comment removed for export] *)
  Lemma zh16_read2 : forall segs m A a n i ad, u8arr segs m A (zh16 a n) -> 0 <= i -> 2 * i + 2 <= n -> 0 <= zget a i < 65536 ->
    ad = wa (A + 2 * i) -> ov_read_bytes segs m ad 2 = Some (le2 (Z_to_bv 64 (zget a i))).
  Proof.
    intros segs m A a n i ad H Hi Hn Hv ->.
    rewrite (u8arr_read2 segs m A (zh16 a n) i _ _ _ H (zh16_nth_lo a n i Hi Hn) (zh16_nth_hi a n i Hi Hn) Hi eq_refl).
    rewrite R16_value by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma zh16_read_lo : forall segs m A a n i ad, u8arr segs m A (zh16 a n) -> 0 <= i -> 2 * i + 2 <= n ->
    ad = wa (A + 2 * i) -> ov_read_bytes segs m ad 1 = Some [Z_to_bv 8 (zget a i mod 256)].
  Proof.
    intros segs m A a n i ad H Hi Hn ->.
    exact (u8arr_read segs m A (zh16 a n) (2 * i) _ _ H (zh16_nth_lo a n i Hi Hn) ltac:(lia) eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma dpureF_set_cftabCopy : forall cx b0 pl J d s a, dpureF cx b0 pl J d s -> dpureF cx b0 pl J (d_set_cftabCopy d a) s.
  Proof.
    intros cx b0 pl J d s a DP. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. destruct d; cbn in *. exact RP.
  Qed.
  Lemma dpureF_set_ll4 : forall cx b0 pl J d s i v, dpureF cx b0 pl J d s -> 0 <= v < 256 ->
    dpureF cx b0 pl J (d_set_ll4 d (zset (d_ll4 d) i v)) s.
  Proof.
    intros cx b0 pl J d s i v DP Hv. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. destruct d; cbn in *. decompose [and] RP.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      intros k. rewrite zget_zset. destruct (k =? i); [lia| auto].
  Qed.
End ACeilS1.

(* [comment removed for export] *)
Lemma land_le_lit : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= b.
Proof. intros a b Ha Hb. split; [apply Z.land_nonneg; lia| apply land_le_r'; lia]. Qed.
Lemma nib_even_range : forall old n, 0 <= old < 256 -> 0 <= n < 16 -> 0 <= Z.lor (Z.land old 240) n < 256.
Proof.
  intros old n Ho Hn. apply (lor_lt_pow2 _ _ 8); [| lia]. pose proof (land_le_lit old 240 ltac:(lia) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sv32_zw32_12 : forall a n i, 0 <= i < n -> - 2^31 <= zget a i < 2^31 -> sv32 (zw32 a n) i = zget a i.
Proof.
  intros a n i Hi Hr. rewrite (sv32_nth (zw32 a n) i (Z_to_bv 64 (zget a i))) by (apply zw32_nth; lia).
  apply sv32_lit. exact Hr.
Qed.
Lemma iif_zw32 : forall cf indx,
  (forall i, 0 <= i < 257 -> 0 <= zget cf i < 2^31) ->
  index_into_f indx (sv32 (zw32 cf 257)) = indexIntoF indx cf.
Proof.
  intros cf indx R. rewrite indexIntoF_eq. apply index_into_f_ext.
  intros i Hi. apply sv32_zw32_12; [lia|]. pose proof (R i ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma smallF_cftab_range : forall L d sym unz a b, smallF L d sym unz a b ->
  forall i, 0 <= i < 257 -> 0 <= zget (d_cftab d) i <= sv_nblock L.
Proof.
  intros L d sym unz a b SF i Hi. cps_destruct SF as (_ & _ & _ & ORIG & _ & NB9 & HIST & SYMB & _ & CFP & _).
  rewrite CFP by lia.
  pose proof (psum_range sym unz (Z.to_nat (sv_nblock L)) ltac:(intros k Hk; apply SYMB; lia) HIST i ltac:(lia)). lia.
Qed.
Lemma dout_ok_sft_nr : forall L d sym unz a b j5 k0 tp2, smallF L d sym unz a b -> d_rand d = 0 -> 1 <= d_bs100k d <= 9 ->
  1 <= sv_nblock L -> 0 <= k0 < 256 -> 0 <= tp2 < 4294967296 ->
  dout_ok (d_set_sv (sft_nr d k0 tp2) (sv_set_j (sv_set_i L (d_origPtr d)) j5)).
Proof.
  intros L d sym unz a b j5 k0 tp2 SF R BSN NB1 K0R TPR. pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
  cps_destruct SF as (TS & SM1 & HDR & ORIG & _).
  unfold dout_ok, sft_nr. unfold tset, hdr_ok in *. destruct d; destruct L; cbn -[Z.mul] in *.
  unfold crc_init in *. repeat match goal with |- _ /\ _ => split end; try lia.
  intros _. exact CFR.
Qed.
Lemma dout_ok_sft_r : forall L d sym unz a b j5 k0 tp2, smallF L d sym unz a b -> d_rand d = 1 -> 1 <= d_bs100k d <= 9 ->
  1 <= sv_nblock L -> 0 <= k0 < 256 -> 0 <= tp2 < 4294967296 ->
  dout_ok (d_set_sv (sft_r d k0 tp2) (sv_set_j (sv_set_i L (d_origPtr d)) j5)).
Proof.
  intros L d sym unz a b j5 k0 tp2 SF R BSN NB1 K0R TPR. pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
  cps_destruct SF as (TS & SM1 & HDR & ORIG & _).
  unfold dout_ok, sft_r. unfold tset, hdr_ok in *. destruct d; destruct L; cbn -[Z.mul] in *.
  unfold crc_init in *. repeat match goal with |- _ /\ _ => split end; try lia.
  intros _. exact CFR.
Qed.
