(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: plain_realizes_closed over the run's segment list (run_segments), with the launch facts valid_launch, entry_launch_ok_va and the channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import MainDefs RefStartupDefs TargetRun RefTop.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg HeapCeil HeapSecret Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import HeapMF_iface BJIface BJIfaceStr BJIfaceLL BJIfaceTop BJIfaceObjL L_top.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import EhIface EhGlue EhClosed EhChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require Import PlainTop.
Import ListNotations.
Open Scope Z_scope.

Section Open.
  (* [comment removed for export] *)
  Lemma FZ_plain : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @BJIfaceLL.llvm_fuzz_stmt2 HCEIL (@MallocMF.HMF HCEIL HSEC) (@EHG.E HCEIL HSEC).
  Proof.
    intros HCEIL HSEC.
    exact (@llvm_fuzz_all HCEIL (@MallocMF.HMF HCEIL HSEC) (@EHG.E HCEIL HSEC)
             (@EHC.heap_mf_hyps_plain HCEIL HSEC) (@EHC.bj_ehtabs_plain HCEIL HSEC)
             (EHA.L_chain_above (@MallocMF.HMF HCEIL HSEC))).
  Qed.

  Theorem plain_halts_closed :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source exit_codes_02 PLAIN.
  Proof. exact (plain_halts FZ_plain). Qed.

  (* LPS 727298f3 port: as [PlainTop.plain_realizes_spec_lim] states it: the walk is over the
     run's segment list ([Run.run_segments]), and the launch facts [valid_launch],
     [entry_launch_ok_va] and the channel reader, which [Run.valid_input] and [Run.valid_entry]
     give, are premises. *)
  Theorem plain_realizes_closed :
    forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
      valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 34 <= lim ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
      valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
      realizes (run_segments RSEGS inp sp mbase)
        (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc RPH sp brk mbase rnd lim inp)
        (spec (in_argv inp) (in_fs inp)).
  Proof. exact (plain_realizes_spec_lim FZ_plain). Qed.
End Open.
