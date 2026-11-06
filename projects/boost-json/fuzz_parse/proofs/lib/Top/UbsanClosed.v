(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainDefs RefStartupDefs TargetRun RefTop.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg HeapCeil HeapSecret Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs HeapMF_iface MallocMF MallocMF_floor.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJIface BJIfaceStr BJIfaceEsc BJIfaceLL BJIfaceTop BJHeapFloor L_top.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhIface EhGlue EhClosed EhChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Top Require Import UbsanTop.
Import ListNotations.
Open Scope Z_scope.

Section Open.
  (* [comment removed for export] *)

  Lemma HFL_ubsan : forall (HCEIL : HeapCeil) (HSEC : HeapSecret), heap_floor (@MallocMF.HMF HCEIL HSEC).
  Proof. intros HCEIL HSEC. unfold heap_floor. intros s LB m b HP Hb. exact (HMF_block_floor s LB m b HP Hb). Qed.

  Lemma FZ_ubsan : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @BJIfaceLL.llvm_fuzz_stmt2 HCEIL (@MallocMF.HMF HCEIL HSEC) (@EHG.E HCEIL HSEC).
  Proof.
    intros HCEIL HSEC.
    exact (@llvm_fuzz_all HCEIL (@MallocMF.HMF HCEIL HSEC) (@EHG.E HCEIL HSEC)
             (@EHC.heap_mf_hyps_ubsan HCEIL HSEC) (@EHC.bj_ehtabs_ubsan HCEIL HSEC) (HFL_ubsan HCEIL HSEC)
             (EHA.L_chain_above (@MallocMF.HMF HCEIL HSEC))).
  Qed.

  Theorem ubsan_halts_closed :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source exit_codes_02 UBSAN.
  Proof. exact (ubsan_halts FZ_ubsan). Qed.

  Theorem ubsan_realizes_closed :
    forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
      valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 34 <= lim ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
      realizes RSEGS (init_config RSEGS Ubsan.M.init_pc RPH sp brk mbase rnd lim inp)
               (spec (in_argv inp) (in_fs inp)).
  Proof. exact (ubsan_realizes_spec_lim FZ_ubsan). Qed.
End Open.
