(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec DriverCfg FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require RefStartup RefStartupDefs POpenCert PUsage3 PCant1 PCant2 PCant3 PCant4 Spec.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.PUsage3 OSSVerify.Proofs.fast_float.from_chars.lib.PCant1 OSSVerify.Proofs.fast_float.from_chars.lib.PCant2 OSSVerify.Proofs.fast_float.from_chars.lib.PCant3 OSSVerify.Proofs.fast_float.from_chars.lib.PCant4 OSSVerify.Proofs.fast_float.from_chars.lib.Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* LPS 08b1429: the statement takes the launch ([inp], [mbase], [entry], [brk]) instead of
   argv/envp/uid/hwcap, as PDrvMain's Handoff and POpenCert's Handoff2 sections do.
   [entry_stack_fits] is kept so the statement is unchanged, now over [in_argv]/[in_envp]. *)
Theorem cant_open : forall inp mbase entry sp0 brk tid rdraw regs mem model,
  valid_sp sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  entry_stack_fits sp0 (in_argv inp) (in_envp inp) -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry inp mbase entry sp0 rdraw tid regs mem -> length (in_argv inp) = 2%nat ->
  m_halted model = None -> m_vm_lazy model = [] -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  m_channel_reader model = true ->
  forall E2 ms2, agree 200 (E_main inp sp0 (ed_top rdraw) tid (canary rdraw) regs) E2 -> sden PSEGS E2 U_oe ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  (forall x, outside (E_main inp sp0 (ed_top rdraw) tid (canary rdraw) regs) (s_rgs P_main2) x -> ms_mem ms2 x = mem x) ->
  realizes PSEGS (mkCfg ms2 model) (t_die (msg_cannot_open (nth 1 (in_argv inp) [])) (m_fs model)).
Proof.
  intros inp mbase entry sp0 brk tid rdraw regs mem model Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc2 Hh Hl Hfd2 Hrd2 E2 ms2 Ha2 Hd2 Hrom2 Hmf2.
  refine (cant_A inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau ME Hargc2 model Hh Hl _ _ E2 ms2 Ha2 Hd2 Hrom2 Hmf2).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  refine (cant_B inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc2 model Hh Hl Hfd2 Hrd2 (TEXIT model) _ _ E1 ms1 Ha1 Hd1 Hrom1 Hmf1).
  - intros E' ms' Ha' Hd' Hrom' Hmf' _. exact (cant_Cb inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 model Hh Hl Hfd2 Hrd2 E' ms' Ha' Hd' Hrom' Hmf').
  - intros E' ms' Ha' Hd' Hrom' Hmf' Hwin HK. exact (cant_Ca inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 model Hh Hl Hfd2 Hrd2 E' ms' Ha' Hd' Hrom' Hmf' Hwin HK).
Qed.
