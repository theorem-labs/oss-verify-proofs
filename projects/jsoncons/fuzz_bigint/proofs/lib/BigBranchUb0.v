(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec Ub0_code_21248_21b5c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section Br.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.

  Lemma bru_21a84_tk : forall R, getr R (17%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21b2c%bv : word) mem rom) (@mkst fx R (0x21b44%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x21b44%bv : word) with (btgt (0x21b2c%bv : word) (bv_signed (24%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_bne_tk RSEGS R _ mem rom _ 17%bv 0%bv _ F_21b2c eq_refl D_21b2c).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.
  Lemma bru_21a84_ft : forall R, getr R (17%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21b2c%bv : word) mem rom) (@mkst fx R (0x21b30%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x21b30%bv : word) with (v_addi (0x21b2c%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_bne_ft RSEGS R _ mem rom _ 17%bv 0%bv _ F_21b2c eq_refl D_21b2c).
    rewrite getr_zero, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
  Qed.

  Lemma bru_212bc_tk : forall R, getr R (10%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21364%bv : word) mem rom) (@mkst fx R (0x213a4%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x213a4%bv : word) with (btgt (0x21364%bv : word) (bv_signed (64%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_beq_tk RSEGS R _ mem rom _ 10%bv 0%bv _ F_21364 eq_refl D_21364).
    rewrite getr_zero, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
  Qed.
  Lemma bru_212bc_ft : forall R, getr R (10%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21364%bv : word) mem rom) (@mkst fx R (0x21368%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x21368%bv : word) with (v_addi (0x21364%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_beq_ft RSEGS R _ mem rom _ 10%bv 0%bv _ F_21364 eq_refl D_21364).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.

  Lemma bru_212f8_tk : forall R, getr R (10%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x213a0%bv : word) mem rom) (@mkst fx R (0x2136c%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x2136c%bv : word) with (btgt (0x213a0%bv : word) (bv_signed (8140%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_bne_tk RSEGS R _ mem rom _ 10%bv 0%bv _ F_213a0 eq_refl D_213a0).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.
  Lemma bru_212f8_ft : forall R, getr R (10%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x213a0%bv : word) mem rom) (@mkst fx R (0x213a4%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x213a4%bv : word) with (v_addi (0x213a0%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_bne_ft RSEGS R _ mem rom _ 10%bv 0%bv _ F_213a0 eq_refl D_213a0).
    rewrite getr_zero, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma br_any : forall R (pc : word) w c rs1 rs2 (imm : bv 13),
    fetch_word RSEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
    msteps RSEGS (@mkst fx R pc mem rom)
                 (@mkst fx R (if branch_taken c (getr R rs1) (getr R rs2) then btgt pc (bv_signed imm) else v_addi pc 4) mem rom).
  Proof.
    intros R pc w c rs1 rs2 imm Hf He Hd.
    destruct (branch_taken c (getr R rs1) (getr R rs2)) eqn:Hb.
    - eapply mst_step; [reflexivity | exact (step_branch_tk_gen RSEGS R pc mem rom w c rs1 rs2 imm Hf He Hd Hb) | apply mst_refl].
    - eapply mst_step; [reflexivity | exact (step_branch_ft_gen RSEGS R pc mem rom w c rs1 rs2 imm Hf He Hd Hb) | apply mst_refl].
  Qed.
End Br.
