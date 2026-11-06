(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YP0n.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YP0n_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM00 YP0n YO0d YK15_cfw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import SlotAgree.
Import ListNotations.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_chk1_silent : forall regs pc mem rom model eff m' T,
m_halted model = None -> m_vm_lazy model = [] ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= CheckOk m' [] ->
m_halted m' = None -> m_vm_lazy m' = [] ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model
= CheckOk m2 evs2 -> eff2 = eff /\ m2 = m' /\ evs2 = []) ->
crealizes B (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4)
(effmem mem eff) rom) m') T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model eff m' T Hh Hlz Hal Hok Hh' Hlz' Huniq Hc.
eapply (crz_silent1_sys B (pend_at regs pc mem rom) model (getr regs 17)); [reflexivity | exact Hal | |].
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) unit tt
(fun _ => eff) (fun _ => m') (fun _ => []) Hh eq_refl
(fun _ => Hok) (fun _ => Hh') (fun _ => Hlz')).
+ intros eff2 m2 evs2 H2. exists tt. apply Huniq. exact H2.
+ intros []. apply nonspurious_of_unique. intros eff2 m2 evs2 Hs2.
apply check_syscall_ok_iff in Hs2. apply Huniq in Hs2 as (-> & _ & _). reflexivity.
- cbn. rewrite adv_pend. exact Hc.
Qed.
Lemma crz_ret_only_silent : forall regs pc mem rom model r m' T,
m_halted model = None -> m_vm_lazy model = [] ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only eff r m' []) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
crealizes B (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model r m' T Hh Hlz Hal Hchk Hh' Hlz' Hc.
apply (crz_chk1_silent regs pc mem rom model (mkEffect r [] []) m' T Hh Hlz Hal).
- rewrite Hchk. apply check_ret_only_self.
- exact Hh'.
- exact Hlz'.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_uniq. exact H2.
- cbn [eff_ret]. rewrite effmem_ret_only. exact Hc.
Qed.
Lemma crz_exit_at : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
crealizes B (mkCfg (pend_at regs pc mem rom) model)
(t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof using.
intros regs pc mem rom model Hh Hlz Hx8.
rewrite <- (pend_gpr0 regs pc mem rom).
apply (crz_exit B (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl Hx8).
Qed.
Lemma crz_exit_small : forall regs pc mem rom model (c : word),
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
getr regs 10 = c -> (bv_unsigned c < 256)%Z ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_exit c (m_fs model)).
Proof using.
intros regs pc mem rom model c Hh Hlz Hx8 Hc Hsmall.
rewrite <- (land_255_small c Hsmall), <- Hc. apply crz_exit_at; assumption.
Qed.
Lemma crz_ioctl_winsz : forall regs pc mem rom model fd e T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 29%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
(forall rd wr : bool, e <> FdUrandom) ->
cmd32 (getr regs 11) = TIOCGWINSZ ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk Hnd Hcmd Hc.
apply (crz_ret_only_silent regs pc mem rom model (errno_ret ENOTTY) model T Hh Hlz ltac:(rewrite Hno; reflexivity)).
- intro eff. rewrite chk29 by exact Hno. rewrite Hfd, H32, Hcmd. unfold check_ioctl.
rewrite Hlk. change (tty_only_request TIOCGWINSZ) with true. destruct e; try reflexivity. exfalso; eapply (Hnd true true); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
End g.
