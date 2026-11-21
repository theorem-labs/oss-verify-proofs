(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/U1UsageTop.v for the budget-premise witness: the same proofs over BudgetWit.SRealizes.srealizes, the released srealizes with a no-allocation-call check at each node; only module paths change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec ShapeAlg ArgvEnv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit Require Import SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import U1Start U1Usage.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

(* LPS 727298f3: the start-up hands the run's own input [inp]; the driver Sections name it as
   [mkProcInputC] of its ambient record [amb_of inp].  The entry state reads the input only
   through projections the two share; [in_fs] of the second is [fs_seed_tmp (in_fs inp) []],
   which computes to [in_fs inp] ([State.fs_seed_tmp_nil]). *)
Lemma main_entry_C : forall sp rnd inp mbase tid regs mem,
  main_entry sp rnd inp mbase tid regs mem ->
  main_entry sp rnd (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
    mbase tid regs mem.
Proof. intros sp rnd inp mbase tid regs mem []. constructor; assumption. Qed.

Theorem u1_usage_top : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (* LPS 727298f3: [u1_startup] takes the launch facts, and the usage line is a write
     to the launch's channel ([Run.valid_input]'s launch and reader clauses). *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  in_channel_reader inp = true ->
  length (in_argv inp) <> 2%nat ->
  srealizes Ubsan.M.loaded_segments
           (init_config Ubsan.M.loaded_segments
              Ubsan.M.init_pc Ubsan.M.phdrs
              sp brk mbase rnd lim inp)
           (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hva Hve Hfit Hvl Hlau Hrd Hargc.
  apply u1_startup; try assumption.
  intros tid regs mem Htid ME.
  exact (@ref_usage_w fx0 (amb_of inp) sp (in_argv inp) (in_envp inp) tid rnd regs mem brk mbase
           (in_fs inp) (in_stdin inp) lim Hva Hve Hsp Htid (main_entry_C sp rnd inp mbase tid regs mem ME)
           Hrd Hargc).
Qed.
