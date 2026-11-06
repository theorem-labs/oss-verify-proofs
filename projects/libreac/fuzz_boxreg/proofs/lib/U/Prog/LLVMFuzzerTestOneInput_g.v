From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma llvm_post_g : forall stk L A regs mem md p n b L' A' regs' mem' md',
  Fs.fs_sorted (m_fs md) = true ->
  lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' ->
  sink_none B mem' md' ->
  ro_agree (ms_segs B) mem' ->
  res_ok_slots A' (lib_delta n b) ->
  (forall i, 0 <= i < n -> mbyte (ms_segs B) mem' (p + i) = mbyte (ms_segs B) mem (p + i)) ->
  lib_post_g B API llvm_G stk L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md p n b L' A' regs' mem' md' Hs
    (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12) Hsk Hro Hr Hp.
  unfold lib_post_g.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj _ (conj H8 (conj H9 (conj _ (conj _
    (conj H11 (conj H12 (conj eq_refl (conj eq_refl (conj Hs (conj Hsk (conj Hro (conj Hr Hp))))))))))))))))))).
  - exists vm', (m_fds md), (m_statpins md). split; [|reflexivity].
    rewrite Hmd. exact (with_vmmaps_os_upd vm' md).
  - intros a Ha Hso Hc He Hg. exact (H10 a Ha Hso Hc He Hg).
  - intros a (lo & len & Hin & _). destruct Hin.
Qed.

Theorem llvm_g_of_sr :
  LLVMFuzzerTestOneInput_sr_contract B API ->
  LLVMFuzzerTestOneInput_contract B API.
Proof.
  intros SRC BI (LK & LR & LD) j Hj ra empty stk Hk Hra.
  unfold lib_contract_g.
  intros L A regs mem md p n pl b K Hpre GI Hrelro Hro Htask Hfrm HK.
  destruct BI as (Hsegs & BI'). pose proof Hro as Hro'. rewrite Hsegs in Hro'.
  assert (BI : llvm_binds B API) by exact (conj Hsegs BI').
  destruct Hpre as (Hlp & Hn & Hd & Hres & Hroom & Hsn & Hfd & Hfs & Hch & Hsp).
  apply (rz_conseq (ms_segs B) _ (K (LL 0 (m_fs md) []))); [| apply t_eq_sym, LK].
  pose proof (SRC BI j Hj ra empty stk Hk Hra L A regs mem md p n b Hlp Hsn Hsp
    Hres (LR b n Hroom) Hro' Hrelro GI Hfrm) as HSR.
  apply HSR.
  intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & Hsk & Hr & Hp & Hro2 & _).
  apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc|]. split; [exact Hf|]. split; [| exact I].
  rewrite <- Hsegs in Hro2.
  apply llvm_post_g; [exact Hfs | exact Hpost | exact Hsk | exact Hro2 | rewrite LD; exact Hr | exact Hp].
Qed.

End G.
