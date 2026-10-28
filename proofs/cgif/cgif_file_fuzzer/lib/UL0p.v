(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH01 UH03 UN3e UL0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition usage_hyp : Prop :=
forall sp argv envp tid rnd ms model,
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> (length argv <> 2)%nat ->
st_ok ubs0segs (E_main sp argv envp tid rnd) (add_cond ss_main_f (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp argv envp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_usage (nth 0 argv [])) (m_fs model)).
Definition cannot_open_hyp : Prop :=
forall sp a0 path envp tid rnd regs mem model e,
valid_sp sp -> valid_argv [a0; path] -> valid_envp envp -> entry_stack_fits sp [a0; path] envp ->
0 < bv_unsigned tid < 4194304 ->
regs_ok (E_main sp [a0; path] envp tid rnd) (ss_regs ss_open) regs ->
mem_ok ubs0segs (E_main sp [a0; path] envp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp [a0; path] envp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp [a0; path] envp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
0 < e < 4096 ->
realizes ubs0segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom ubs0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Definition read_error_hyp : Prop :=
forall sp a0 path envp tid rnd (E : env) ms model,
valid_sp sp -> valid_argv [a0; path] -> valid_envp envp -> entry_stack_fits sp [a0; path] envp ->
0 < bv_unsigned tid < 4194304 ->
Z.of_nat (length path) <= 60 ->
env_agree 10 (E_main sp [a0; path] envp tid rnd) E ->
st_ok ubs0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] envp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
End a.
