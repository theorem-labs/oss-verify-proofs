(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_s34 PmHeapClosed6_s34.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec StoreOk HeapIface LibIface LibIfaceFp LibIfaceFpW Pm6DrvLib Pm6DrvLibL Pm6DrvG Pm6DrvMain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvMainW_s34 Pm6HeapBridge_s34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FPX_1.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hfs : sc_fs scfg = true.
#[local] Existing Instance PropExec.fx0.

Section WithLibW.
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  Variable PHI : list byte -> Prop.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0 (bv_unsigned sp)).
  Hypothesis LIokWF : forall sp, valid_sp sp -> lib_iface_ok_fpw (LayF sp) scfg (HI0 (bv_unsigned sp)) (LStF sp) PHI.
  Hypothesis LXokF : forall sp, valid_sp sp -> lib_exit_ok (LStF sp).
  Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    cred (L0 (bv_unsigned sp)) (KPM + 4 * fst (ll_credit (LayF sp) n)) (n + BOV + 4 * snd (ll_credit (LayF sp) n)) 0
         (debit (L0 (bv_unsigned sp)) (K0, B0) 65536).

  Theorem src0_realizes_specG_heap_lim : forall lim, (lim <= 2 ^ 34)%Z -> src_realizes_stmtG_lim scfg PHI lim.
  Proof.
    intros lim0 Hlim0.
    apply (src0_realizes_specG_lim scfg (fun sp => L0 (bv_unsigned sp)) (fun sp => HI0 (bv_unsigned sp)) LayF LStF (K0, B0)).
    - intros sp Hsp. apply HI0_ok_closed. exact Halloc.
    - exact (drv_layout_L0).
    - exact DLLF.
    - exact LIokWF.
    - exact LXokF.
    - intros lim sp a0s path envp uid hw rdraw tid regs mem brk mbase Hlim Hsp Hbrk Hmb Hva Hve Htid ME.
      exact (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem Hva Hve Hsp Htid ME brk mbase lim Hlim Hbrk Hmb).
    - exact Hfs.
    - exact Hbudget.
    - exact Hlim0.
  Qed.
End WithLibW.
End FPX_1.
