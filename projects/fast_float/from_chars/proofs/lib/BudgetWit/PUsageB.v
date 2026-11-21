(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from PUsage.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec DriverCfg FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain RefStartup RefStartupDefs PUsageCert PUsage1 PUsage2 PUsage3 PUsage4 Spec.
Import ListNotations.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PUsage.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import PUsage1B PUsage2B PUsage3B PUsage4B Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.
Theorem usage_path_b : forall inp mbase entry sp0 brk tid rdraw regs mem model,
  valid_sp sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  entry_stack_fits sp0 (in_argv inp) (in_envp inp) -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry inp mbase entry sp0 rdraw tid regs mem -> length (in_argv inp) <> 2%nat ->
  m_halted model = None -> m_vm_lazy model = [] -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  m_channel_reader model = true ->
  Rzb.rzb PSEGS DriverCfg.DCFG (mkCfg (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)) model)
           (t_die (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Proof.
  intros inp mbase entry sp0 brk tid rdraw regs mem model Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc Hh Hl Hfd2 Hrd2.
  apply (PUsage1B.usage_A_b inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc model Hh Hl).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  refine (PUsage2B.usage_B_b inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc model Hh Hl Hfd2 Hrd2 (TEXIT model) _ _ E1 ms1 Ha1 Hd1 Hrom1 Hmf1).
  - intros E' ms' Ha' Hd' Hrom' Hmf' _. exact (PUsage3B.usage_Cb_b inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc model Hh Hl Hfd2 Hrd2 E' ms' Ha' Hd' Hrom' Hmf').
  - intros E' ms' Ha' Hd' Hrom' Hmf' Hwin HK. exact (PUsage4B.usage_Ca_b inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc model Hh Hl Hfd2 Hrd2 E' ms' Ha' Hd' Hrom' Hmf' Hwin HK).
Qed.
