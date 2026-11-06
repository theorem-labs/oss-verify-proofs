(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanRegionPoisoned AsanNodesRP AsanSmear AsanNodesRPSound AsanPlanImages.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Asan_code_88000_89000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgA.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac krem := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => let X := fresh "X" in set (X := v) | |- _ => idtac end.

Section FPW_1. Context {fx : PropExec.FPState}.

  Theorem as_maxva_block : forall regs (mem rom : word -> option byte) (x : word),
    getr regs 10 = x ->
    exists regs',
      msteps SEGS (mkst regs (0x890ac : word) mem rom) (mkst regs' (0x8911c : word) mem rom)
      /\ getr regs' 10 = fst (mv_smear x) /\ getr regs' 15 = snd (mv_smear x)
      /\ getr regs' 11 = Z_to_bv 64 RPN.MV_C55 /\ getr regs' 12 = Z_to_bv 64 RPN.MV_C33
      /\ getr regs' 13 = Z_to_bv 64 RPN.MV_C0F /\ getr regs' 14 = Z_to_bv 64 RPN.MV_C01
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
  Proof.
    intros regs mem rom x H10.
    eexists. split.
    -
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_890ac eq_refl D_890ac)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_890b0 eq_refl D_890b0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_890b4 eq_refl D_890b4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_890b8 eq_refl D_890b8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_890bc eq_refl D_890bc)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_890c0 eq_refl D_890c0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_890c4 eq_refl D_890c4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_890c8 eq_refl D_890c8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_890cc eq_refl D_890cc)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_890d0 eq_refl D_890d0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_890d4 eq_refl D_890d4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_890d8 eq_refl D_890d8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_890dc eq_refl D_890dc)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_890e0 eq_refl D_890e0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_890e4 eq_refl D_890e4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_890e8 eq_refl D_890e8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_890ec eq_refl D_890ec)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_890f0 eq_refl D_890f0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_890f4 eq_refl D_890f4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_890f8 eq_refl D_890f8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_890fc eq_refl D_890fc)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89100 eq_refl D_89100)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89104 eq_refl D_89104)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89108 eq_refl D_89108)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_8910c eq_refl D_8910c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89110 eq_refl D_89110)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89114 eq_refl D_89114)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89118 eq_refl D_89118)). gr. krem.   (* [comment removed for export] *)
    apply mst_refl.
    - gr. subst. unfold mv_smear, smw. repeat split; try reflexivity.
      intros r N10 N11 N12 N13 N14 N15.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.

  Theorem as_maxva_spec : mv_spec SEGS RPN.RP_ASAN.
  Proof.
    intros mem rom x regs H10.
    destruct (as_maxva_block regs mem rom x ltac:(replace (10 : bv 5) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact H10))
      as (regs' & Hms & P).
    exists regs'. split.
    - cbn [RPN.mv_entry RPN.mv_exit RPN.RP_ASAN].
      match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
        replace (Z_to_bv 64 0x890ac) with p by (apply bv_eq; reflexivity);
        replace (Z_to_bv 64 0x8911c) with q by (apply bv_eq; reflexivity) end.
      exact Hms.
    - revert P.
      replace (Z_to_bv 5 10) with (10 : bv 5) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 11) with (11 : bv 5) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 12) with (12 : bv 5) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 13) with (13 : bv 5) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 14) with (14 : bv 5) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 15) with (15 : bv 5) by (apply bv_eq; reflexivity).
      intros P. exact P.
  Qed.
End FPW_1.
