(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp LibIfaceFpW
  VmLimitFrame Scfg HaltsBridge Spec BigintSpec PhiExtract SpecG Pm6NoSpin Pm6DrvLibL Pm6DrvG.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvMainW_s34 Pm6HeapBridgeW_s34.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_s34.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmPhiX16.
Abbreviation IMG_xsrc :=
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
Definition CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma codes_0 : In (exit_code 0) CODES.  Proof. left. reflexivity. Qed.
Lemma codes_2 : In (exit_code 2) CODES.  Proof. right. left. reflexivity. Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Section Src.
  Variable Lay0F : word -> lib_layout.
  Variable LS0F : word -> lib_statics.
  Variable PHI : list byte -> Prop.
  Hypothesis DLL0 : forall sp, valid_sp sp -> Pm6DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst6_s34.L0 (bv_unsigned sp)).
  Hypothesis LIOKW0 : forall sp, valid_sp sp -> lib_iface_ok_fpw (Lay0F sp) cfg0 (PmHeapInst6_s34.HI0 (bv_unsigned sp)) (LS0F sp) PHI.
  Hypothesis LX0 : forall sp, valid_sp sp -> Pm6DrvLibL.lib_exit_ok (LS0F sp).
  Hypothesis BUD0 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    Pm6DrvG.cred (PmHeapInst6_s34.L0 (bv_unsigned sp))
      (PmHeapInst6_s34.KPM + 4 * fst (ll_credit (Lay0F sp) n)) (n + PmHeapInst6_s34.BOV + 4 * snd (ll_credit (Lay0F sp) n)) 0
      (debit (PmHeapInst6_s34.L0 (bv_unsigned sp)) (PmHeapInst6_s34.K0, PmHeapInst6_s34.B0) 65536).

  (* [comment removed for export] *)
  Lemma srealizes_specG_init : forall lim sp brk mb rnd inp,
    lim <= 2 ^ 34 ->
    valid_entry IMG_xsrc (mkEntry sp brk mb rnd) inp -> valid_input_abort inp ->
    srealizes Plain.M.loaded_segments cfg0
      (init_config Plain.M.loaded_segments Plain.M.init_pc
                   Plain.M.phdrs sp brk mb rnd lim inp)
      (specG (fun d => PHI (Pm6DrvD.payload d)) (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp brk mb rnd inp Hlim Hen Hvalid.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hrsp [Hrbrk [Hrmb Hrfit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _).
    exact (Pm6HeapBridgeW_s34.src0_realizes_specG_heap_lim cfg0 eq_refl eq_refl Lay0F LS0F PHI DLL0 LIOKW0 LX0 BUD0 lim Hlim
             sp brk mb rnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
  Qed.

  (* [comment removed for export] *)
  Theorem phi_xsrc_at : forall lim sp brk mb rnd inp a0 path data,
    lim <= 2 ^ 34 ->
    valid_entry IMG_xsrc (mkEntry sp brk mb rnd) inp -> valid_input_abort inp ->
    ~ run_scfg_budget_refused cfg0 IMG_xsrc lim (mkEntry sp brk mb rnd) inp ->
    in_argv inp = [a0; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
    fs_lookup (in_fs inp) path = Some data -> SpecG.hdr_okD data ->
    PHI (Pm6DrvD.payload data).
  Proof.
    intros lim sp brk mb rnd inp a0 path data Hlim Hen Hvalid Hwb Hargv Hlen Hne Hnd Hlk Hhdr.
    pose proof (srealizes_specG_init lim sp brk mb rnd inp Hlim Hen Hvalid) as Hsrz. rewrite Hargv in Hsrz.
    apply (phi_extract_after Plain.M.loaded_segments cfg0 CODES _ _ SpecG.t0 (PHI (Pm6DrvD.payload data)) Hsrz).
    - apply Safe_init_within_budget. exact Hwb.
    - exact Pm6NoSpin.src11_no_spin_site.
    - reflexivity.
    - apply (codes_ok_specG CODES codes_0 codes_2).
    - apply nokill_specG.
    - exact (specG_t0 (fun d => PHI (Pm6DrvD.payload d)) a0 path (in_fs inp) data Hlen Hne Hnd Hlk Hhdr).
    - exact t0_no_halt.
    - exact (guard_after_specG (fun d => PHI (Pm6DrvD.payload d)) a0 path (in_fs inp) data Hlen Hne Hnd Hlk Hhdr).
  Qed.
End Src.
End FPX_1.
End PmPhiX16.
