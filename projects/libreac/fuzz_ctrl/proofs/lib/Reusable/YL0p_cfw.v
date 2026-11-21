(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0p.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0p_cfw.v, with its module paths changed; 2 of its 47 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_knock's port of its copy of this file (changed usage_hyp_cf, cannot_open_hyp_cf, read_error_hyp_cf). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YH00 YH01 YH03 YN3e YL0k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0d YH02 YL0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition usage_hyp_cf : Prop :=
forall (sp brk mbase tid : word) (rnd : EntryDraw) (inp : ProcInput) ms model,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(length (in_argv inp) <> 2)%nat ->
st_ok src0segs (E_main sp inp tid rnd) (add_cond ss_main_f (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
crealizes src0_msyms (mkCfg ms model) (diag (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Definition cannot_open_hyp_cf : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) regs mem model e,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
0 < bv_unsigned tid < 4194304 ->
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
0 < e < 4096 ->
crealizes src0_msyms
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Definition read_error_hyp_cf : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) (E : env) ms model,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
0 < bv_unsigned tid < 4194304 ->
Z.of_nat (length path) <= 60 ->
env_agree 10 (E_main sp inp tid rnd) E ->
st_ok src0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
crealizes src0_msyms (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
End a.
