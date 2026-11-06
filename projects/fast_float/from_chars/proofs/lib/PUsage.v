(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec DriverCfg FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain RefStartup RefStartupDefs PUsageCert PUsage1 PUsage2 PUsage3 PUsage4 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem usage_path : forall sp0 av ev uid tid hw rdraw regs mem model,
  valid_sp sp0 -> valid_argv av -> valid_envp ev -> entry_stack_fits sp0 av ev -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 av ev uid tid hw rdraw regs mem -> length av <> 2%nat ->
  m_halted model = None -> m_vm_lazy model = [] -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  realizes PSEGS (mkCfg (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)) model)
           (t_die (msg_usage (nth 0 av [])) (m_fs model)).
Proof.
  intros sp0 av ev uid tid hw rdraw regs mem model Hsp Hva Hve Hfits Htid ME Hargc Hh Hl Hfd2.
  apply (usage_A sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc model Hh Hl).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1.
  refine (usage_B sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Hfits Htid ME Hargc model Hh Hl Hfd2 (TEXIT model) _ _ E1 ms1 Ha1 Hd1 Hrom1 Hmf1).
  - intros E' ms' Ha' Hd' Hrom' Hmf' _. exact (usage_Cb sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc model Hh Hl Hfd2 E' ms' Ha' Hd' Hrom' Hmf').
  - intros E' ms' Ha' Hd' Hrom' Hmf' Hwin HK. exact (usage_Ca sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc model Hh Hl Hfd2 E' ms' Ha' Hd' Hrom' Hmf' Hwin HK).
Qed.
