(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/jsoncons/fuzz_json_cursor/proofs/lib/PmInteg/PmHaltsAsanC.v at 874e3397a35 and ported to the ubsan image; the exiting half is Pm10HeapBridge_u.src0_realizes_spec_heap_lim at target_alloc_limit, with the Lay0F_u/LS0F_u instances copied from PmInteg/PmCubsanBase.v at the same commit, in place of the ASan PmCasanFinal.pm_casan_tgt half. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp KillFree VmLimitFrame HaltsBridge HaltsSpec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmFinal Pm10DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Common.LimSim Require Import LimSimSys.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U Require PmLibSpecs_u PmFinal_u Pm10DrvLibL_u Pm10HeapBridge_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require TopGlueC_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmInteg Require PmLibInstC_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmHaltsUbsanC.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Abbreviation TGT := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).

Definition CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma codes_0 : In (exit_code 0) CODES.  Proof. left. reflexivity. Qed.
Lemma codes_2 : In (exit_code 2) CODES.  Proof. right. left. reflexivity. Qed.

(* Ubsan image: the facts PmCubsanBase instantiates, from the twin of the plain proof. *)
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

Lemma must_exit_cfg0_big : forall en inp, valid_entry TGT en inp -> valid_input inp ->
  must_exit_in_scfg PmFinal.cfg0 CODES TGT target_alloc_limit en inp.
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid.
  pose proof (Pm10HeapBridge_u.src0_realizes_spec_heap_lim PmFinal_u.cfg0 eq_refl eq_refl Lay0F_u LS0F_u DLL0_u LIB0_u LX0_u BUD0_u target_alloc_limit) as TGT0.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _).
  eapply (srealizes_must_exit_init_fo _ PmFinal.cfg0 CODES).
  - exact (TGT0 sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds).
  - apply Safe_init_big. exact nbr_limit_target.
  - reflexivity.
  - apply HaltsSpec.codes_ok_spec; [exact codes_0 | exact codes_2].
  - apply HaltsSpec.nokill_spec.
Qed.

Theorem halts_ubsan : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] TGT.
Proof.
  apply (halts_allowed_of_must_exit_wb forced_only_cfg). { apply forced_only_cfg_least. }
  intros en inp Hen Hvalid Hwb.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg _ TGT target_alloc_limit ShippedBudgets.lim_source en inp).
  - cbv. discriminate.
  - exact Hwb.
  - apply (must_exit_in_scfg_forced_only PmFinal.cfg0). exact (must_exit_cfg0_big en inp Hen Hvalid).
Qed.
End FPX_1.
End PmHaltsUbsanC.
