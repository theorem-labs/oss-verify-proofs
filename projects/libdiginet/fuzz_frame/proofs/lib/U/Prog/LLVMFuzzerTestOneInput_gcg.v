(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_gcg.v
   at bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1; module path only. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/U/Prog/LLVMFuzzerTestOneInput_gcg.v, with its module paths changed; 1 line of the source is left out. *)
(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_gcg.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i YK15_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_g LLVMFuzzerTestOneInput_cfb.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_g_of_sr_cf :
  LLVMFuzzerTestOneInput_sr_contract_cf B API ->
  LLVMFuzzerTestOneInput_contract_cg B API.
Proof.
  intros SRC BI (LK & LR & LD) j Hj ra empty stk Hk Hra.
  unfold lib_contract_cg.
  intros L A regs mem md p n pl b K Hpre GI Hrelro Hro Htask Hfrm HK.
  destruct BI as (Hsegs & BI'). pose proof Hro as Hro'. rewrite Hsegs in Hro'.
  assert (BI : llvm_binds B API) by exact (conj Hsegs BI').
  destruct Hpre as (Hlp & Hn & Hd & Hres & Hroom & Hsn & Hfd & Hfs & Hch & Hsp).
  assert (HC : crealizes B (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
                 (K (LL 0 (m_fs md) []))).
  { apply (SRC BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hlp Hn Hd Hsn Hsp
      Hres (LR b n Hroom) Hro' Hrelro GI Hfrm).
    intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & Hsk & Hr & Hp & Hro2 & _).
    apply HK. exists fx', L', A', regs', mem', md'.
    split; [exact Hc|]. split; [exact Hf|]. split; [| exact I].
    rewrite <- Hsegs in Hro2.
    apply llvm_post_g; [exact Hfs | exact Hpost | exact Hsk | exact Hro2 | rewrite LD; exact Hr | exact Hp]. }
  exact (crz_conseq B _ _ _ HC (t_eq_sym _ _ (LK pl (m_fs md) K))).
Qed.

End G.
