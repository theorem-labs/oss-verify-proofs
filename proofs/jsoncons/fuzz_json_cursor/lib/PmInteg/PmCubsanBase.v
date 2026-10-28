(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp KillFree VmLimitFrame.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PmLibSpecs PmFinal PmFinalSan Pm10DrvLibL.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmTop Require TopGlueC.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmLibInstC.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require PmLibSpecs_u PmFinal_u PmFinalSan_u Pm10DrvLibL_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require TopGlueC_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmInteg Require PmLibInstC_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmCubsanBase.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Abbreviation SRC := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Abbreviation TGT := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).

(* Plain image (source side): the facts PmCasanBase and PmCbothBase use. *)
Let Lay0F : word -> lib_layout := fun sp => TopGlueC.TopGlueC.Lay0 (bv_unsigned sp).
Let LS0F : word -> lib_statics := fun _ => PmLibSpecs.PMS.pm_statics.
Lemma DLL0 : forall sp, valid_sp sp -> Pm10DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst10.L0 (bv_unsigned sp)).
Proof. intros sp Hsp. apply TopGlueC.TopGlueC.Lay0_drv. Qed.
Lemma LIB0 : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F sp) PmFinal.cfg0 (PmHeapInst10.HI0 (bv_unsigned sp)) (LS0F sp).
Proof. intros sp Hsp. apply (TopGlueC.TopGlueC.Lay0_iface (bv_unsigned sp) _ PmLibInstC.PmLibInstC.scr_ok (PmLibInstC.PmLibInstC.lib_spec0 sp Hsp)). Qed.
Lemma LX0 : forall sp, valid_sp sp -> Pm10DrvLibL.lib_exit_ok (LS0F sp).
Proof. intros sp Hsp. apply TopGlueC.TopGlueC.pm_exit_ok. Qed.
Lemma BUD0 : PmFinal.budget0_ok Lay0F.
Proof. exact TopGlueC.TopGlueC.Lay0_budget. Qed.

(* Ubsan image (target side): the same facts, from the twin of the plain proof on the ubsan image. *)
Let Lay0F_u : word -> lib_layout := fun sp => TopGlueC_u.TopGlueC.Lay0 (bv_unsigned sp).
Let LS0F_u : word -> lib_statics := fun _ => PmLibSpecs_u.PMS.pm_statics.
Lemma DLL0_u : forall sp, valid_sp sp -> Pm10DrvLibL_u.drv_lib_layout (Lay0F_u sp) (PmHeapInst10_u.L0 (bv_unsigned sp)).
Proof. intros sp Hsp. apply TopGlueC_u.TopGlueC.Lay0_drv. Qed.
Lemma LIB0_u : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F_u sp) PmFinal_u.cfg0 (PmHeapInst10_u.HI0 (bv_unsigned sp)) (LS0F_u sp).
Proof. intros sp Hsp. apply (TopGlueC_u.TopGlueC.Lay0_iface (bv_unsigned sp) _ PmLibInstC_u.PmLibInstC.scr_ok (PmLibInstC_u.PmLibInstC.lib_spec0 sp Hsp)). Qed.
Lemma LX0_u : forall sp, valid_sp sp -> Pm10DrvLibL_u.lib_exit_ok (LS0F_u sp).
Proof. intros sp Hsp. apply TopGlueC_u.TopGlueC.pm_exit_ok. Qed.
Lemma BUD0_u : PmFinal_u.budget0_ok Lay0F_u.
Proof. exact TopGlueC_u.TopGlueC.Lay0_budget. Qed.

(* Target half: the plain source half's proof, run on the ubsan image, at the shipped target budget. *)
Lemma ubsan_half : forall en_t inp,
  valid_entry TGT en_t inp -> valid_input_abort inp ->
  PmFinalSan.half_ok PmFinal.cfg0 TGT ShippedBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp)).
Proof.
  intros en_t inp Hen Hvalid.
  exact (PmFinalSan_u.src11_half_big Lay0F_u LS0F_u DLL0_u LIB0_u LX0_u BUD0_u ShippedBudgets.lim_target en_t inp Hen Hvalid nbr_limit_target).
Qed.

Theorem base_abort : strong_universal_error_free_T_scfg_budgets_abort PmFinal.cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target SRC TGT.
Proof. exact (PmFinalSan.shipped_base_of_target_half Lay0F LS0F DLL0 LIB0 LX0 BUD0 TGT ubsan_half). Qed.
End FPX_1.
End PmCubsanBase.
