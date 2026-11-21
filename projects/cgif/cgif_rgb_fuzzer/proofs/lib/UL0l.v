(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the three hypotheses usage_hyp, cannot_open_hyp and read_error_hyp are stated over the run: its ProcInput and execfn string, the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits, the entry draw's top in runs_main, and the run's CONFIG_RSEQ-indexed states, the open-failure arm's being the flag-free ss_open_c). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UO3p UL0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
(* #38: the interface between UL0r/UL0s/UL0t, which prove these, and UL0m/UL0f,
   which consume them.  [E_main] takes the run and its execfn string, and
   [runs_main] the entry draw's top (UO3p.v); [entry_stack_fits] no longer
   fixes the stack image, so its place is taken by the launch premises UO3p's
   Section f takes; the states are those of the run's own CONFIG_RSEQ flag,
   except the open-failure arm's, which is the flag-free [ss_open_c] (UL0g). *)
Definition usage_hyp : Prop :=
forall (sp brk mbase tid : word) (rnd : EntryDraw) (inp : ProcInput) ms model,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(length (in_argv inp) <> 2)%nat ->
st_ok ubs2segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd)
(add_cond (ss_main false (kb_rseq (in_kernel inp))) (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs2segs (mkCfg ms model) (diag (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Definition cannot_open_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) regs mem model e,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
0 < bv_unsigned tid < 4194304 ->
regs_ok (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_regs ss_open_c) regs ->
mem_ok ubs2segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) mem (ss_mem ss_open_c) ->
facts_ok (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_facts ss_open_c) ->
runs_at (bv_unsigned sp) mem (runs_main true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp) rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
0 < e < 4096 ->
realizes ubs2segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open_c)) 4) mem (seg_rom ubs2segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Definition read_error_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) (E : env) ms model,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
0 < bv_unsigned tid < 4194304 ->
Z.of_nat (length path) <= 60 ->
env_agree 10 (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) E ->
st_ok ubs2segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp) rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs2segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
End a.
