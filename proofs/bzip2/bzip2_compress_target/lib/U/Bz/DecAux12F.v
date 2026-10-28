(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12F.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma rnums_words_model12 : map bv_unsigned rnums_words = rNums_list.
Proof. vm_compute. reflexivity. Qed.
Lemma rnums_words_tbl12 : forall i, (0 <= i < 512)%Z -> wnth rnums_words i = Z_to_bv 64 (rNums i).
Proof.
  intros i Hi. unfold rNums. rewrite <- rnums_words_model12. unfold wnth.
  rewrite <- (Z_to_bv_bv_unsigned (nth (Z.to_nat i) rnums_words (Z_to_bv 64 0))). f_equal.
  change 0%Z with (bv_unsigned (Z_to_bv 64 0)) at 2. rewrite map_nth. reflexivity.
Qed.
Lemma rnums_words_nth12 : forall i, (0 <= i < 512)%Z -> nth_error rnums_words (Z.to_nat i) = Some (Z_to_bv 64 (rNums i)).
Proof.
  intros i Hi. rewrite <- rnums_words_tbl12 by lia. apply nth_error_wnth; [lia|]. rewrite rnums_words_length. lia.
Qed.

(* [comment removed for export] *)
Lemma dout_ok_aft_nr : forall L d sym tt0, dinv_AFT L d sym tt0 -> d_rand d = 0 -> 1 <= d_bs100k d <= 9 ->
  dout_ok (d_set_sv (aft_nr d) (sv_set_i L (sv_nblock L))).
Proof.
  intros L d sym tt0 DI R BSN. cps_pose (dinv_AFT_facts L d sym tt0 DI) as (TP & ALL28 & ALL32).
  cps_destruct DI as (Hi & ORIG & NB1 & NB9 & HDR & TS & SM & _).
  pose proof (ALL32 (aft_tp d)) as W32.
  unfold aft_nr, aft_w. set (tp := aft_tp d) in *. clearbody tp. set (w := zget (d_tt d) tp) in *. clearbody w.
  assert (K0R : 0 <= Z.land w 255 < 256).
  { split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (TPR2 : 0 <= Z.shiftr w 8 < 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  unfold dout_ok, hdr_ok, tset in *. destruct d; cbn -[Z.pow Z.mul Z.land Z.shiftr] in *.
  unfold crc_init in *. repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma dout_ok_aft_r : forall L d sym tt0, dinv_AFT L d sym tt0 -> d_rand d = 1 -> 1 <= d_bs100k d <= 9 ->
  dout_ok (d_set_sv (aft_r d) (sv_set_i L (sv_nblock L))).
Proof.
  intros L d sym tt0 DI R BSN. cps_pose (dinv_AFT_facts L d sym tt0 DI) as (TP & ALL28 & ALL32).
  cps_destruct DI as (Hi & ORIG & NB1 & NB9 & HDR & TS & SM & _).
  pose proof (ALL32 (aft_tp d)) as W32.
  unfold aft_r, aft_w. set (tp := aft_tp d) in *. clearbody tp. set (w := zget (d_tt d) tp) in *. clearbody w.
  assert (K0R : 0 <= Z.land w 255 < 256).
  { split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (TPR2 : 0 <= Z.shiftr w 8 < 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  unfold dout_ok, hdr_ok, tset in *. destruct d; cbn -[Z.pow Z.mul Z.land Z.shiftr] in *.
  unfold crc_init in *. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
