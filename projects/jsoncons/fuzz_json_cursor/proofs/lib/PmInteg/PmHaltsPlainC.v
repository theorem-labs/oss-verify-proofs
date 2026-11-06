(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp L5Defs L5Core PmLibDefs PmLibSpecs PmCurSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmFinal PmHalts.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmTop Require TopGlueC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmLibInstC.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmHaltsPlainC.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Abbreviation SRC := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).

Theorem halts_of_lib : forall SS, SS <= 54224 ->
  (forall sp, valid_sp sp -> @PMCS.lib_spec_c TopGlueC.TopGlueC.cfg0P (PmHeapInst10.L0 (bv_unsigned sp)) (PmHeapInst10.HI0 (bv_unsigned sp)) SS (TopGlueC.TopGlueC.Lay0 (bv_unsigned sp))) ->
  halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit PmHalts.CODES SRC.
Proof.
  intros SS HSS LIB.
  apply (PmHalts.halts_csrc (fun sp => TopGlueC.TopGlueC.Lay0 (bv_unsigned sp)) (fun _ => PMS.pm_statics)).
  - intros sp Hsp. apply TopGlueC.TopGlueC.Lay0_drv.
  - intros sp Hsp. apply (TopGlueC.TopGlueC.Lay0_iface (bv_unsigned sp) SS HSS (LIB sp Hsp)).
  - intros sp Hsp. apply TopGlueC.TopGlueC.pm_exit_ok.
  - exact TopGlueC.TopGlueC.Lay0_budget.
Qed.

Theorem halts_plain : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] SRC.
Proof. exact (halts_of_lib _ PmLibInstC.PmLibInstC.scr_ok PmLibInstC.PmLibInstC.lib_spec0). Qed.
End FPX_1.
End PmHaltsPlainC.
