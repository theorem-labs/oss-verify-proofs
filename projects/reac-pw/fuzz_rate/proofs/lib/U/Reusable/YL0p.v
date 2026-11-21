(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0p.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack change of cgif/cgif_file_fuzzer's copy, keeping this unit's ProcInput-owned E_main/runs_main, nullary ss_main_f, src0 names and module paths; the launch's ProcInput, mmap base and entry draw; the launch's string area with the exec file name). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YH00 YH01 YH03 YN3e YL0k.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
(* These three Props connect YL0y/YL0w/YL0x to YL0q/YL0n/YL0j.  The donor replaces
   [entry_stack_fits] by [valid_launch], [entry_launch_ok_va] and [valid_input], and
   takes the two-element argv as an equation on [in_argv inp] (donor YL0p.v:18-67).
   Here [E_main] and [runs_main] already read argv, envp, execfn and top from [inp]/[rnd];
   [forget_rs] keeps [ss_main_f] nullary, so the donor's extra layout arguments are absent. *)
Definition usage_hyp : Prop :=
forall (sp brk mbase tid : word) (rnd : EntryDraw) (inp : ProcInput) ms model,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
st_ok src0segs (E_main sp inp tid rnd)
(add_cond ss_main_f (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes src0segs (mkCfg ms model) (diag (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Definition cannot_open_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) regs mem model e,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 ->
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
0 < e < 4096 ->
realizes src0segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Definition read_error_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) (E : env) ms model,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 ->
Z.of_nat (length path) <= 60 ->
env_agree 10 (E_main sp inp tid rnd) E ->
st_ok src0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes src0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
End a.
