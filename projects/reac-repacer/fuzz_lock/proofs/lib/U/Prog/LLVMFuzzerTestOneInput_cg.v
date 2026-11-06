(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_gcg.v, with its module paths changed; 18 of its 41 lines of code are new or changed and 17 lines of the source are left out. *)
(* The crash-free twin of LLVMFuzzerTestOneInput_g.v: from the SRcf contract of fuzz_lock.ubsan's
   LLVMFuzzerTestOneInput to U/Prog/AgreeRet.v's lib_contract_cgr for the return lock_ret, as
   libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v (25e3d17bdb50) does for its harness
   function. The post is the one of LLVMFuzzerTestOneInput_g.v (llvm_post_gr); only realizes becomes
   crealizes. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet AgreeRet check_no_overread_c check_lookup_c
  lt_cf_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_g.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma crz_conseq : forall c T T', crealizes B c T -> t_eq T T' -> crealizes B c T'.
Proof. intros c T T' (H1 & H2) E. split; [exact (rz_conseq (ms_segs B) c T T' H1 E) | exact H2]. Qed.

Theorem llvm_cg_of_sr :
  LLVMFuzzerTestOneInput_sr_contract_cf B API ->
  LLVMFuzzerTestOneInput_contract_cg B API.
Proof.
  intros SRC BI (LK & LR & LD) j Hj ra empty stk Hk Hra.
  unfold lib_contract_cgr.
  intros L A regs mem md p n pl b K Hpre GI Hrelro Hro Htask Hfrm HK.
  destruct BI as (Hsegs & BI'). pose proof Hro as Hro'. rewrite Hsegs in Hro'.
  assert (BI : llvm_binds B API) by exact (conj Hsegs BI').
  destruct Hpre as (Hlp & Hn & Hd & Hres & Hroom & Hsn & Hfd & Hfs & Hch & Hsp).
  apply (crz_conseq _ (K (LL (lock_ret pl) (m_fs md) []))); [| apply t_eq_sym, LK].
  pose proof (SRC BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hlp Hn Hd Hsn Hsp
    Hres (LR b n Hroom) Hro' Hrelro GI Hfrm) as HSR.
  apply HSR.
  intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & Hsk & Hr & Hp & Hro2 & _).
  apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc|]. split; [exact Hf|]. split; [| exact I].
  rewrite <- Hsegs in Hro2.
  apply llvm_post_gr; [exact Hfs | exact Hpost | exact Hsk | exact Hro2 | rewrite LD; exact Hr | exact Hp].
Qed.

End G.
