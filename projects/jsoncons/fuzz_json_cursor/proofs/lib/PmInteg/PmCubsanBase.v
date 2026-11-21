(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added base_scfg, the unbudgeted strong_universal_error_free_T_scfg for the ubsan image; its proof text is copied from projects/jsoncons/fuzz_json_cursor/proofs/lib/PmCasanFinal.v:119-138 at theorem-labs/oss-verify-proofs@c5665593c2d8, with the ubsan target half Pm10HeapBridge_u.src0_realizes_spec_heap_lim in place of pm_casan_tgt. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (walks lifted to the run's segments): changed base_scfg; internal commit ids in comments replaced by public commits or removed. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp KillFree VmLimitFrame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmLibSpecs PmFinal PmFinalSan Pm10DrvLibL Pm10HeapBridge.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmTop Require TopGlueC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require PmLibInstC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U Require PmLibSpecs_u PmFinal_u PmFinalSan_u Pm10DrvLibL_u Pm10HeapBridge_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require TopGlueC_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmInteg Require PmLibInstC_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Common.Cfg Require SRomStable.
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

Theorem base_scfg : strong_universal_error_free_T_scfg PmFinal.cfg0 SRC TGT.
Proof.
  pose proof (Pm10HeapBridge.src0_realizes_spec_heap_lim PmFinal.cfg0 eq_refl eq_refl Lay0F LS0F DLL0 LIB0 LX0 BUD0 source_alloc_limit) as SRC0.
  pose proof (Pm10HeapBridge_u.src0_realizes_spec_heap_lim PmFinal_u.cfg0 eq_refl eq_refl Lay0F_u LS0F_u DLL0_u LIB0_u LX0_u BUD0_u target_alloc_limit) as TGT0.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  (* each entry's 5th conjunct is the launch; valid_input is read through the model's BY-NAME
     accessors, for Pm10DrvMain(_u)'s src_realizes_stmt2_lim (.. Hmb Hvl Hlau Hargv Henvp Hfs
     Hcreds Hcr) *)
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [_ Halau]]]].
  pose proof (valid_input_argv _ Hvalid) as Hargv. pose proof (valid_input_envp _ Hvalid) as Henvp.
  pose proof (valid_input_fs _ Hvalid) as Hfs. pose proof (valid_input_creds _ Hvalid) as Hcreds.
  pose proof (valid_input_launch _ Hvalid) as Hvl. pose proof (valid_input_channel_reader _ Hvalid) as Hcr.
  specialize (SRC0 rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hcr).
  specialize (TGT0 asp abrk amb arnd inp Hasp Habrk Hamb Hvl Halau Hargv Henvp Hfs Hcreds Hcr).
  (* both walks are over the binaries' own segments; the run reads them with the run's vDSO
     appended, so [SRomStable.srun_init] lifts each ([vdso_image] [None] by computation) *)
  apply (SRomStable.srun_init PmFinal.cfg0 Plain.M.loaded_segments inp rsp rmb _ _ _ _ _ _ eq_refl) in SRC0.
  apply (SRomStable.srun_init PmFinal_u.cfg0 Ubsan.M.loaded_segments inp asp amb _ _ _ _ _ _ eq_refl) in TGT0.
  split; [| split].
  - eapply srealizes_error_free_big; [exact SRC0 | exact nbr_limit_source].
  - eapply srealizes_error_free_big; [exact TGT0 | exact nbr_limit_target].
  - intro tr.
    rewrite (srealizes_traces_iff_big PmFinal.cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC0 nbr_limit_source).
    rewrite (srealizes_traces_iff_big PmFinal.cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT0 nbr_limit_target).
    reflexivity.
Qed.
End FPX_1.
End PmCubsanBase.
