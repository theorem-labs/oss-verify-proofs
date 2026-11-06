(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp
  VmLimitFrame NoSpinSite HaltsBridge HaltsSpec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm10DrvLibL Pm10HeapBridge PmFinal Pm10NoSpin.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation IMG_csrc :=
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Abbreviation IMG_cub :=
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).

Definition CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma codes_0 : In (exit_code 0) CODES.  Proof. left. reflexivity. Qed.
Lemma codes_2 : In (exit_code 2) CODES.  Proof. right. left. reflexivity. Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Section Src.

  Variable Lay0F : word -> lib_layout.
  Variable LS0F : word -> lib_statics.
  Hypothesis DLL0 : forall sp, valid_sp sp -> Pm10DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst10.L0 (bv_unsigned sp)).
  Hypothesis LIB0 : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F sp) PmFinal.cfg0 (PmHeapInst10.HI0 (bv_unsigned sp)) (LS0F sp).
  Hypothesis LX0 : forall sp, valid_sp sp -> Pm10DrvLibL.lib_exit_ok (LS0F sp).
  Hypothesis BUD0 : PmFinal.budget0_ok Lay0F.

  Theorem halts_csrc : halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit CODES IMG_csrc.
  Proof.
    apply (halts_allowed_of_must_exit PmFinal.cfg0).
    intros [sp brk mb rnd] inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hrsp [Hrbrk [Hrmb Hrfit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _).
    eapply (srealizes_must_exit_init _ PmFinal.cfg0 CODES).
    - exact (Pm10HeapBridge.src0_realizes_spec_heap_lim PmFinal.cfg0 eq_refl eq_refl Lay0F LS0F DLL0 LIB0 LX0 BUD0 source_alloc_limit
               sp brk mb rnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
    - apply Safe_init_big. exact nbr_limit_source.
    - exact Pm10NoSpin.src11_no_spin_site.
    - apply HaltsSpec.codes_ok_spec; [exact codes_0 | exact codes_2].
    - apply HaltsSpec.nokill_spec.
  Qed.
End Src.

End FPX_1.
