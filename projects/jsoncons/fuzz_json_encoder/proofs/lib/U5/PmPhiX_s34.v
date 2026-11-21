(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (walks lifted to the run's segments): changed phi_xsrc_at, srealizes_specG_init. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp LibIfaceFpW
  VmLimitFrame Scfg HaltsBridge Spec BigintSpec PhiExtract SpecG Pm6NoSpin Pm6DrvLibL Pm6DrvG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvMainW_s34 Pm6HeapBridgeW_s34.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_s34.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.Common.Cfg Require SRomStable.
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
    (* LPS 727298f3: [valid_entry]'s fifth conjunct is the launch, and [valid_input_abort]
       has sixteen conjuncts; the source walk reads the launch and the channel reader. *)
    destruct Hen as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & _ & Hcreds & _ & _ & _ & _ & _ & _ & Hvl & Hcr & _ & _).
    exact (Pm6HeapBridgeW_s34.src0_realizes_specG_heap_lim cfg0 eq_refl eq_refl Lay0F LS0F PHI DLL0 LIOKW0 LX0 BUD0 lim Hlim
             sp brk mb rnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hcr).
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
    (* the run reads the binary's segments with the vDSO pair appended ([Run.run_segments],
       LPS 727298f3), which is the configuration the budget premise speaks about *)
    apply (SRomStable.srun_init cfg0 Plain.M.loaded_segments inp sp mb _ _ _ _ _ _ eq_refl) in Hsrz.
    apply (phi_extract_after (run_segments Plain.M.loaded_segments inp sp mb) cfg0 CODES _ _ SpecG.t0 (PHI (Pm6DrvD.payload data)) Hsrz).
    - apply Safe_init_within_budget. exact Hwb.
    - intros _ Hal. cbv in Hal. discriminate Hal.
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
