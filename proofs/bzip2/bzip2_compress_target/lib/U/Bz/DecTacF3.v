(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.
  Variable segs : list Segment.

  Lemma Z_to_bv8_eq_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
  Proof. intros x y E. rewrite <- (Z_to_bv8_mod256 x), <- (Z_to_bv8_mod256 y), E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma zh16_write2 : forall m A a n i (w : word), u8arr segs m A (zh16 a n) -> 0 <= i -> 2 * i + 2 <= n ->
    u8arr segs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (zh16 (zset a i (bv_unsigned w mod 65536)) n).
  Proof.
    intros m A a n i w H Hi Hn.
    pose proof (u8arr_writeN segs m A (zh16 a n) (2 * i) (le2 w) H ltac:(lia) ltac:(rewrite length_le2, zh16_length_nat; lia)) as W.
    unfold zh16 in W |- *. erewrite tab_upd_bytes in W; [exact W| lia| rewrite length_le2; lia| |].
    - intros k Hk. rewrite length_le2 in Hk. rewrite le2_unsigned.
      pose proof (bv_unsigned_in_range 64 w) as R.
      destruct k as [|[|k]]; [| | lia]; cbn [nth_error Z.of_nat Pos.of_succ_nat]; f_equal.
      + replace (2 * i + Z.of_nat 0) with (i * 2) by lia. rewrite Z.div_mul, Z_mod_mult by lia.
        rewrite zget_zset_same. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
        apply Z_to_bv8_eq_mod. replace 65536 with (256 * 256) by reflexivity.
        rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z_mod_plus_full, Z.mod_mod by lia. reflexivity.
      + replace (2 * i + Z.of_nat 1) with (1 + i * 2) by lia. rewrite Z_div_plus, Z_mod_plus_full by lia.
        change (1 / 2 + i) with (0 + i). rewrite Z.add_0_l. change (1 mod 2) with 1.
        rewrite zget_zset_same. change (2 ^ (8 * 1)) with 256.
        apply Z_to_bv8_eq_mod.
        pose proof (Z.div_mod (bv_unsigned w) 65536 ltac:(lia)) as DM.
        pose proof (Z.mod_pos_bound (bv_unsigned w) 65536 ltac:(lia)) as MB.
        set (q := bv_unsigned w / 65536) in DM. set (r := bv_unsigned w mod 65536) in DM, MB |- *.
        rewrite DM. replace (65536 * q + r) with (r + (q * 256) * 256) by lia. rewrite Z_div_plus by lia.
        rewrite Z_mod_plus_full. reflexivity.
    - intros j Hj Hnot. rewrite length_le2 in Hnot. cbn beta. rewrite zget_zset_other; [reflexivity|].
      intros E. apply Hnot. pose proof (Z.div_mod j 2 ltac:(lia)). pose proof (Z.mod_pos_bound j 2 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dpureF_set_tt : forall cx b0 pl J d s k uc, dpureF cx b0 pl J d s -> 0 <= uc < 2 ^ 32 ->
    dpureF cx b0 pl J (d_set_tt d (zset (d_tt d) k uc)) s.
  Proof.
    intros cx b0 pl J d s k uc DP Huc. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. cps_destruct RP as (R1 & R2 & R3 & R4 & R5).
      split; [| tauto]. intros i. rewrite zget_zset. destruct (i =? k); [lia| apply R1].
  Qed.
  Lemma dpureF_set_ll16 : forall cx b0 pl J d s k uc, dpureF cx b0 pl J d s -> 0 <= uc < 2 ^ 16 ->
    dpureF cx b0 pl J (d_set_ll16 d (zset (d_ll16 d) k uc)) s.
  Proof.
    intros cx b0 pl J d s k uc DP Huc. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. cps_destruct RP as (R1 & R2 & R3 & R4 & R5).
      split; [exact R1|]. split; [| tauto]. intros i. rewrite zget_zset. destruct (i =? k); [lia| apply R2].
  Qed.
  Lemma dpureF_set_unzftab : forall cx b0 pl J d s a, dpureF cx b0 pl J d s -> dpureF cx b0 pl J (d_set_unzftab d a) s.
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
    - unfold drep in *. dmodel_cbn. exact RP.
  Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac zw32_sw ARR i v tacv :=
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
    let SO := fresh "SO" in
    pose proof (u32arr_store_ok sg mm A (zw32 a n) i _ ARR ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
    step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?ga (le4 ?x)) _) =>
      let H := fresh "ARR" in
      pose proof (zw32_write sg mm A a n i x v ARR ltac:(lia) ltac:(tacv)) as H;
      let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
      replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
      clear ARR; store_done; rename H into ARR
    end; try clear SO; zsimp; bz32l
  end end.

(* [comment removed for export] *)
Ltac zh16_sh ARR i :=
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ARR with u8arr _ _ ?A (zh16 ?a ?n) =>
    let SO := fresh "SO" in
    pose proof (u8arr_storeN_ok sg mm A (zh16 a n) (2 * i)%Z 2%nat _ ARR ltac:(lia) ltac:(rewrite zh16_length_nat; lia) eq_refl) as SO;
    step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?ga (le2 ?x)) _) =>
      let H := fresh "ARR" in
      pose proof (zh16_write2 sg mm A a n i x ARR ltac:(lia) ltac:(lia)) as H;
      let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
      replace (wa (A + 2 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
      clear ARR; store_done; rename H into ARR
    end; try clear SO; zsimp; bz32l
  end end.
