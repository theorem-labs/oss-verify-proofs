(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require Import U8MainH.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require U8TrH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* a worker port727 (): S8MainH's launch premises (valid_launch, LOK, the channel reader) in place of
   entry_stack_fits; the realizes stays the chain's own (over rsegs) until the (A) bridge's form is ruled. *)
Theorem u8_realizes_spec_hs :
  (forall RCx : RunCtx, @zlib_u2_contract_U8 RCx) ->  (* a worker (A1): the library contract for every run *)
  forall sp brk mbase (draw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp -> in_channel_reader inp = true ->
    realizes (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof. intros C. exact (u8_realizes_spec_tp (fun RCx rc => U8TrH.target_phase_h (RCa1 := RCx) (rc := rc) (C RCx))). Qed.  (* a worker (A1) *)
