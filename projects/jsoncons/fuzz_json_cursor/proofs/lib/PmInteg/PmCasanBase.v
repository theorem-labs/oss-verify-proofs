(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp L5Defs L5Core PmLibDefs PmLibSpecs PmCurSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct HeapIfaceA HeapIfaceANull PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout Pm8ArtIfaceInst Pm8ArtIfaceInstX
  PmLibDefsA PmLibSpecsA PmCurSpecsA PmLibAssemblyCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmFinal Pm10DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmCasanFinal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmTop Require TopGlueC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmLibInstC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmCasanLibTop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmCasanBase.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Abbreviation SRC := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Abbreviation TGT := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).

Let LIBTOP := PmCasanLibTop.PmCasanLibTop.libtop.
Let LIBA := ASMC.la4 PmCasanFinal.cfg0 art_IL art_ILX art_IL_ok art_ILX_ok LIBTOP.

Let Lay0F : word -> lib_layout := fun sp => TopGlueC.TopGlueC.Lay0 (bv_unsigned sp).
Let LS0F : word -> lib_statics := fun _ => PMS.pm_statics.
Lemma DLL0 : forall sp, valid_sp sp -> Pm10DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst10.L0 (bv_unsigned sp)).
Proof. intros sp Hsp. apply TopGlueC.TopGlueC.Lay0_drv. Qed.
Lemma LIB0 : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F sp) PmFinal.cfg0 (PmHeapInst10.HI0 (bv_unsigned sp)) (LS0F sp).
Proof. intros sp Hsp. apply (TopGlueC.TopGlueC.Lay0_iface (bv_unsigned sp) _ PmLibInstC.PmLibInstC.scr_ok (PmLibInstC.PmLibInstC.lib_spec0 sp Hsp)). Qed.
Lemma LX0 : forall sp, valid_sp sp -> Pm10DrvLibL.lib_exit_ok (LS0F sp).
Proof. intros sp Hsp. apply TopGlueC.TopGlueC.pm_exit_ok. Qed.
Lemma BUD0 : PmFinal.budget0_ok Lay0F.
Proof. exact TopGlueC.TopGlueC.Lay0_budget. Qed.

Theorem base_scfg : strong_universal_error_free_T_scfg PmCasanFinal.cfg0 SRC TGT.
Proof. exact (fuzz_json_cursor_asan_base_scfg ASMC.LayC8 ASMC.LStC8 ASMC.la1 ASMC.la2 ASMC.la3 LIBA Lay0F LS0F DLL0 LIB0 LX0 BUD0). Qed.

Theorem base_abort : strong_universal_error_free_T_scfg_budgets_abort PmCasanFinal.cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC TGT.
Proof. exact (fuzz_json_cursor_asan_base_abort ASMC.LayC8 ASMC.LStC8 ASMC.la1 ASMC.la2 ASMC.la3 LIBA Lay0F LS0F DLL0 LIB0 LX0 BUD0). Qed.
End FPX_1.
End PmCasanBase.
