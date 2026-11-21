(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import ShapeAlg Spec S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.MrP9 Require Import S9MainH.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.MrP9 Require S9TrH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* S8MainH's launch premises (valid_launch, LOK, the channel reader) in place of
   entry_stack_fits; the realizes stays the chain's own (over rsegs) until the (A) bridge's form is ruled. *)
Theorem s9_realizes_spec_hs :
  (forall RCx : RunCtx, @zlib_u2_contract_S9 RCx) ->  (* the library contract for every run *)
  forall sp brk mbase (draw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp -> in_channel_reader inp = true ->
    realizes (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw source_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof. intros CS. exact (s9_realizes_spec_tp (fun RCx rc => S9TrH.target_phase_h (RCa1 := RCx) (rc := rc) (CS RCx))). Qed.
