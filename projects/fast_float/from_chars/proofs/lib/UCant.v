(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec DriverCfg FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UbStartup UbStartupDefs UOpenCert UUsage3 UCant1 UCant2 UCant3 UCant4 Spec.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert OSSVerify.Proofs.fast_float.from_chars.lib.UUsage3 OSSVerify.Proofs.fast_float.from_chars.lib.UCant1 OSSVerify.Proofs.fast_float.from_chars.lib.UCant2 OSSVerify.Proofs.fast_float.from_chars.lib.UCant3 OSSVerify.Proofs.fast_float.from_chars.lib.UCant4 OSSVerify.Proofs.fast_float.from_chars.lib.Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem cant_open : forall sp0 av ev uid tid hw rdraw regs mem model,
  valid_sp sp0 -> valid_argv av -> valid_envp ev -> entry_stack_fits sp0 av ev -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 av ev uid tid hw rdraw regs mem -> length av = 2%nat ->
  m_halted model = None -> m_vm_lazy model = [] -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  forall E2 ms2, agree 200 (E_main sp0 av ev tid (canary rdraw) regs) E2 -> sden PSEGS E2 U_oe ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  (forall x, outside (E_main sp0 av ev tid (canary rdraw) regs) (s_rgs P_main2) x -> ms_mem ms2 x = mem x) ->
  realizes PSEGS (mkCfg ms2 model) (t_die (msg_cannot_open (nth 1 av [])) (m_fs model)).
Proof.
  intros sp0 av ev uid tid hw rdraw regs mem model Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfd2 E2 ms2 Ha2 Hd2 Hrom2 Hmf2.
  refine (cant_A sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 model Hh Hl _ _ E2 ms2 Ha2 Hd2 Hrom2 Hmf2).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  refine (cant_B sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Hfits Htid ME Hargc2 model Hh Hl Hfd2 (TEXIT model) _ _ E1 ms1 Ha1 Hd1 Hrom1 Hmf1).
  - intros E' ms' Ha' Hd' Hrom' Hmf' _. exact (cant_Cb sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 model Hh Hl Hfd2 E' ms' Ha' Hd' Hrom' Hmf').
  - intros E' ms' Ha' Hd' Hrom' Hmf' Hwin HK. exact (cant_Ca sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 model Hh Hl Hfd2 E' ms' Ha' Hd' Hrom' Hmf' Hwin HK).
Qed.
