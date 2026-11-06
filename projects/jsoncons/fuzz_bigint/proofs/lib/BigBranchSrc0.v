(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec Src0_code_20088_210bc Src0_code_21134_21d54.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.

Section Br.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.

  Local Ltac fin := apply mst_refl || (eapply mst_step; [reflexivity | | apply mst_refl]).

  Lemma br_2155c_tk : forall R, getr R (15%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21604%bv : word) mem rom) (@mkst fx R (0x21618%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x21618%bv : word) with (btgt (0x21604%bv : word) (bv_signed (20%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_bne_tk RSEGS R _ mem rom _ 15%bv 0%bv _ F_21604 eq_refl D_21604).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.
  Lemma br_2155c_ft : forall R, getr R (15%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x21604%bv : word) mem rom) (@mkst fx R (0x21608%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x21608%bv : word) with (v_addi (0x21604%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_bne_ft RSEGS R _ mem rom _ 15%bv 0%bv _ F_21604 eq_refl D_21604).
    rewrite getr_zero, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
  Qed.

  Lemma br_20ec8_tk : forall R, getr R (12%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x20f70%bv : word) mem rom) (@mkst fx R (0x20f9c%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x20f9c%bv : word) with (btgt (0x20f70%bv : word) (bv_signed (44%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_beq_tk RSEGS R _ mem rom _ 12%bv 0%bv _ F_20f70 eq_refl D_20f70).
    rewrite getr_zero, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
  Qed.
  Lemma br_20ec8_ft : forall R, getr R (12%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x20f70%bv : word) mem rom) (@mkst fx R (0x20f74%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x20f74%bv : word) with (v_addi (0x20f70%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_beq_ft RSEGS R _ mem rom _ 12%bv 0%bv _ F_20f70 eq_refl D_20f70).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.

  Lemma br_20ef0_tk : forall R, getr R (13%bv : reg) <> Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x20f98%bv : word) mem rom) (@mkst fx R (0x20f7c%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x20f7c%bv : word) with (btgt (0x20f98%bv : word) (bv_signed (8164%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
    eapply (step_bne_tk RSEGS R _ mem rom _ 13%bv 0%bv _ F_20f98 eq_refl D_20f98).
    rewrite getr_zero. unfold c_eq. apply bv_eqb_neq. exact H.
  Qed.
  Lemma br_20ef0_ft : forall R, getr R (13%bv : reg) = Z_to_bv 64 0 ->
    msteps RSEGS (@mkst fx R (0x20f98%bv : word) mem rom) (@mkst fx R (0x20f9c%bv : word) mem rom).
  Proof.
    intros R H. eapply mst_step; [reflexivity | |apply mst_refl].
    replace (0x20f9c%bv : word) with (v_addi (0x20f98%bv : word) 4) by (apply bv_eq; reflexivity).
    eapply (step_bne_ft RSEGS R _ mem rom _ 13%bv 0%bv _ F_20f98 eq_refl D_20f98).
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
