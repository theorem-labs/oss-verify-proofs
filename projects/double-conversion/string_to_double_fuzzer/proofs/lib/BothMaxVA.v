(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanRegionPoisoned AsanNodesRP AsanSmear AsanNodesRPSound BothPlanImages.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Both_code_89000_8a000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgB.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac krem := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => let X := fresh "X" in set (X := v) | |- _ => idtac end.

Section FPW_1. Context {fx : PropExec.FPState}.

  Theorem both_maxva_block : forall regs (mem rom : word -> option byte) (x : word),
    getr regs 10 = x ->
    exists regs',
      msteps SEGS (mkst regs (0x891f0 : word) mem rom) (mkst regs' (0x89260 : word) mem rom)
      /\ getr regs' 10 = fst (mv_smear x) /\ getr regs' 15 = snd (mv_smear x)
      /\ getr regs' 11 = Z_to_bv 64 RPN.MV_C55 /\ getr regs' 12 = Z_to_bv 64 RPN.MV_C33
      /\ getr regs' 13 = Z_to_bv 64 RPN.MV_C0F /\ getr regs' 14 = Z_to_bv 64 RPN.MV_C01
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
  Proof.
    intros regs mem rom x H10.
    eexists. split.
    -
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_891f0 eq_refl D_891f0)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_891f4 eq_refl D_891f4)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_891f8 eq_refl D_891f8)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_891fc eq_refl D_891fc)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_89200 eq_refl D_89200)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89204 eq_refl D_89204)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_89208 eq_refl D_89208)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_8920c eq_refl D_8920c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_89210 eq_refl D_89210)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_89214 eq_refl D_89214)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89218 eq_refl D_89218)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_8921c eq_refl D_8921c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_89220 eq_refl D_89220)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_89224 eq_refl D_89224)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_89228 eq_refl D_89228)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_8922c eq_refl D_8922c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_89230 eq_refl D_89230)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_89234 eq_refl D_89234)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_89238 eq_refl D_89238)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_8923c eq_refl D_8923c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89240 eq_refl D_89240)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89244 eq_refl D_89244)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89248 eq_refl D_89248)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_8924c eq_refl D_8924c)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89250 eq_refl D_89250)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_89254 eq_refl D_89254)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_89258 eq_refl D_89258)). gr. krem.   (* [comment removed for export] *)
    mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_8925c eq_refl D_8925c)). gr. krem.   (* [comment removed for export] *)
    apply mst_refl.
    - gr. subst. unfold mv_smear, smw. repeat split; try reflexivity.
      intros r N10 N11 N12 N13 N14 N15.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.

  Theorem both_maxva_spec : mv_spec SEGS RPN.RP_BOTH.
  Proof.
    intros mem rom x regs H10.
    destruct (both_maxva_block regs mem rom x ltac:(replace (10 : bv 5) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact H10))
      as (regs' & Hms & P).
    exists regs'. split.
    - cbn [RPN.mv_entry RPN.mv_exit RPN.RP_BOTH].
      match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
        replace (Z_to_bv 64 0x891f0) with p by (apply bv_eq; reflexivity);
        replace (Z_to_bv 64 0x89260) with q by (apply bv_eq; reflexivity) end.
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
