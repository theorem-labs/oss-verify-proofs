(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0F_bzd_out.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section Set8.
  Variable d : dst.
  Variables oc ol nu k0 tp rn rt cb : Z.
  Notation D := (set8 d oc ol nu k0 tp rn rt cb).

  Lemma d_set_out_ch_set8 : forall v, d_set_out_ch D v = set8 d v ol nu k0 tp rn rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_out_len_set8 : forall v, d_set_out_len D v = set8 d oc v nu k0 tp rn rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_nused_set8 : forall v, d_set_nused D v = set8 d oc ol v k0 tp rn rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_k0_set8 : forall v, d_set_k0 D v = set8 d oc ol nu v tp rn rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_tPos_set8 : forall v, d_set_tPos D v = set8 d oc ol nu k0 v rn rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_rNToGo_set8 : forall v, d_set_rNToGo D v = set8 d oc ol nu k0 tp v rt cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_rTPos_set8 : forall v, d_set_rTPos D v = set8 d oc ol nu k0 tp rn v cb.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.
  Lemma d_set_cbcrc_set8 : forall v, d_set_cbcrc D v = set8 d oc ol nu k0 tp rn rt v.
  Proof. intros v. destruct d; cbv; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma d_out_ch_set8 : d_out_ch D = oc. Proof. destruct d; reflexivity. Qed.
  Lemma d_out_len_set8 : d_out_len D = ol. Proof. destruct d; reflexivity. Qed.
  Lemma d_nused_set8 : d_nused D = nu. Proof. destruct d; reflexivity. Qed.
  Lemma d_k0_set8 : d_k0 D = k0. Proof. destruct d; reflexivity. Qed.
  Lemma d_tPos_set8 : d_tPos D = tp. Proof. destruct d; reflexivity. Qed.
  Lemma d_rNToGo_set8 : d_rNToGo D = rn. Proof. destruct d; reflexivity. Qed.
  Lemma d_rTPos_set8 : d_rTPos D = rt. Proof. destruct d; reflexivity. Qed.
  Lemma d_cbcrc_set8 : d_cbcrc D = cb. Proof. destruct d; reflexivity. Qed.
  Lemma d_sv_set8 : d_sv D = d_sv d. Proof. destruct d; reflexivity. Qed.
  Lemma d_cftab_set8 : d_cftab D = d_cftab d. Proof. destruct d; reflexivity. Qed.
  Lemma d_small_set8 : d_small D = d_small d. Proof. destruct d; reflexivity. Qed.
  Lemma d_rand_set8 : d_rand D = d_rand d. Proof. destruct d; reflexivity. Qed.
  Lemma d_bs100k_set8 : d_bs100k D = d_bs100k d. Proof. destruct d; reflexivity. Qed.
  Lemma d_ll16_set8 : d_ll16 D = d_ll16 d. Proof. destruct d; reflexivity. Qed.
  Lemma d_ll4_set8 : d_ll4 D = d_ll4 d. Proof. destruct d; reflexivity. Qed.
  Lemma d_tt_set8 : d_tt D = d_tt d. Proof. destruct d; reflexivity. Qed.
  Lemma blk_cap_set8 : blk_cap D = blk_cap d. Proof. destruct d; reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma get_ll_set8 : forall i, get_ll D i = get_ll d i. Proof. intros i. destruct d; reflexivity. Qed.
  Lemma rand_mask_set8 : rand_mask D = (if rn =? 1 then 1 else 0). Proof. destruct d; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pwd_set8 : pwd D = set8 d oc (ol - 1) nu k0 tp rn rt (crc_update cb oc).
  Proof. destruct d; reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma gsSN_set8 : gsSN D = (indexIntoF tp (d_cftab d), set8 d oc ol nu k0 (get_ll d tp) rn rt cb).
  Proof. destruct d; reflexivity. Qed.
End Set8.

Lemma pws_smod : forall d s out av tout, pws d (smod s out av tout) = smod s (d_out_ch d :: out) (av - 1) (tout + 1).
Proof. intros. reflexivity. Qed.
Lemma s_avail_out_smod : forall s out av tout, s_avail_out (smod s out av tout) = av.
Proof. intros. reflexivity. Qed.
Lemma s_out_smod : forall s out av tout, s_out (smod s out av tout) = out.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Create HintDb set8db.
#[global] Hint Rewrite d_set_out_ch_set8 d_set_out_len_set8 d_set_nused_set8 d_set_k0_set8 d_set_tPos_set8
  d_set_rNToGo_set8 d_set_rTPos_set8 d_set_cbcrc_set8
  d_out_ch_set8 d_out_len_set8 d_nused_set8 d_k0_set8 d_tPos_set8 d_rNToGo_set8 d_rTPos_set8 d_cbcrc_set8
  d_sv_set8 d_cftab_set8 d_small_set8 d_rand_set8 d_bs100k_set8 d_ll16_set8 d_ll4_set8 d_tt_set8 blk_cap_set8
  get_ll_set8 rand_mask_set8 pwd_set8 gsSN_set8 pws_smod s_avail_out_smod s_out_smod : set8db.
Ltac s8 := autorewrite with set8db.
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zx16_of_Z : forall z, (0 <= z < 2^16)%Z -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le1_sx32_lit : forall k, le1 (sx32 (Z_to_bv 64 k)) = [Z_to_bv 8 k].
Proof.
  intros k. unfold sx32. rewrite le1_lit.
  f_equal. apply Z_to_bv8_mod. change (2^8)%Z with 256%Z.
  rewrite <- (mod_pow2_mod256 (bv_unsigned _) 32) by lia.
  rewrite <- (mod_pow2_mod256 k 32) by lia. change (2^32)%Z with M32.
  rewrite low32_lit, swrap32_mod32, low32_lit. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
  Context {ACEIL__ : ACeil}.
  Variable segs : list Segment.

  Lemma zh16_nth : forall a n k, 0 <= k < n ->
    nth_error (zh16 a n) (Z.to_nat k) = Some (Z_to_bv 8 (zget a (k / 2) / 2 ^ (8 * (k mod 2)))).
  Proof. intros a n k Hk. unfold zh16. rewrite tab_nth by lia. reflexivity. Qed.

  Lemma zh16_read2 : forall m A a n i ad, u8arr segs m A (zh16 a n) -> 0 <= i -> 2 * i + 2 <= n ->
    0 <= zget a i < 65536 -> ad = wa (A + 2 * i) ->
    ov_read_bytes segs m ad 2 = Some (le2 (Z_to_bv 64 (zget a i))).
  Proof.
    intros m A a n i ad H Hi Hn Hv ->.
    pose proof (zh16_nth a n (2 * i) ltac:(lia)) as N0. pose proof (zh16_nth a n (2 * i + 1) ltac:(lia)) as N1.
    replace (2 * i / 2) with i in N0 by (symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia).
    replace ((2 * i) mod 2) with 0 in N0 by (symmetry; rewrite Z.mul_comm; apply Z.mod_mul; lia).
    replace ((2 * i + 1) / 2) with i in N1 by (symmetry; rewrite Z.mul_comm, Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
    replace ((2 * i + 1) mod 2) with 1 in N1 by (symmetry; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity).
    cbn [Z.mul Pos.mul Z.pow Z.pow_pos Pos.iter] in N0, N1. rewrite Z.div_1_r in N0.
    rewrite (BzWalkArith2.u8arr_read2 segs m A (zh16 a n) i _ _ _ H N0 N1 Hi eq_refl).
    f_equal. f_equal. f_equal.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * 1)) with 256.
    rewrite (Z.mod_small (zget a i / 256) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.div_mod (zget a i) 256 ltac:(lia)). lia.
  Qed.
End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sv32_zw32 : forall a n i, 0 <= i < n -> - 2^31 <= zget a i < 2^31 -> sv32 (zw32 a n) i = zget a i.
Proof.
  intros a n i Hi Hr. rewrite (sv32_nth (zw32 a n) i (Z_to_bv 64 (zget a i))) by (apply zw32_nth; lia).
  apply sv32_lit. exact Hr.
Qed.
Lemma index_into_f_zw32 : forall cf indx,
  (forall i, 0 <= i < 257 -> 0 <= zget cf i < 2^31) ->
  index_into_f indx (sv32 (zw32 cf 257)) = indexIntoF indx cf.
Proof.
  intros cf indx R. rewrite indexIntoF_eq. apply index_into_f_ext.
  intros i Hi. apply sv32_zw32; [lia|]. pose proof (R i ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma K_PM_fold : forall f d oc ol nu k0 tp rn rt cb s out av tout,
  (if av =? 0 then (0, set8 d oc ol nu k0 tp rn rt cb, smod s out av tout)
   else K_PH f (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout))
  = K_PM f (set8 d oc ol nu k0 tp rn rt cb) (smod s out av tout).
Proof. intros. rewrite K_PM_eq. reflexivity. Qed.
