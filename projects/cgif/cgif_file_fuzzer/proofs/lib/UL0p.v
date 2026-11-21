(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN): changed usage_hyp, cannot_open_hyp, read_error_hyp. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH01 UH03 UN3e UL0k.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* These three Props are the interface between UL0y/UL0w/UL0x, which prove them, and
   UL0q/UL0n/UL0j, which consume them.  All three are restated for the revision:
   [E_main] gained [inp] and [efn] (UN3e.v:69-71); [runs_main] takes the entry draw's TOP
   rather than the draw (UN3e.v:103-108); [ss_main_f] is indexed by the run's rseq flag
   (UN3e.v:149) and is pinned here to the rseq-OFF state, which is the WEAKER of the two
   (the bridge for a general flag is [UL0k.st_ok_main_rs]); and
   [entry_stack_fits], which no longer determines the stack image, is REPLACED by the three
   premises UN3e's Section f takes (UN3e.v:189-194).  The two-element argv cases take it as
   an EQUATION on [in_argv inp], because the layout facts are stated over [inp]
   (YP08.v:494). *)
Definition usage_hyp : Prop :=
forall (sp brk mbase tid : word) (rnd : EntryDraw) (inp : ProcInput) ms model,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
st_ok ubs0segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd)
(add_cond (ss_canon false) (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms)
(runs_main (kb_rseq (in_kernel inp)) false sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
Definition cannot_open_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) regs mem model e,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 ->
regs_ok (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_regs ss_open) regs ->
mem_ok ubs0segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp)) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
0 < e < 4096 ->
realizes ubs0segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom ubs0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Definition read_error_hyp : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word)
(rnd : EntryDraw) (E : env) ms model,
valid_sp sp -> in_argv inp = [a0; path] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 ->
Z.of_nat (length path) <= 60 ->
env_agree 10 (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) E ->
st_ok ubs0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp)) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
End a.
