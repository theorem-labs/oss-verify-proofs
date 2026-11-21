(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ShapeAlg Spec U0FuzzStmt.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP0 Require Import U0MainH.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP0 Require U0TrH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* port727 (): S8MainH's launch premises (valid_launch, LOK, the channel reader) in place of
   entry_stack_fits; the realizes stays the chain's own (over rsegs) until the (A) bridge's form is ruled. *)
Theorem u0_realizes_spec_h :
  forall sp brk mbase (draw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    (* port727: the launch premises, as the corollary below and S0MainH *)
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp -> in_channel_reader inp = true ->
    realizes (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof. exact (u0_realizes_spec_tp (fun RCx rc => U0TrH.target_phase_h (RCa1 := RCx) (rc := rc))). Qed.

Corollary u0_realizes_spec_hs :
  (forall RCx : RunCtx, @u0_fuzz_stmt RCx) ->  (* the statement for every run *)
  forall sp brk mbase (draw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp -> in_channel_reader inp = true ->
    realizes (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof. intros _. exact u0_realizes_spec_h. Qed.
