(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RefNodes.v: the set_tid_address (96) and exit nodes restated over BudgetWit.Rzb.rzb, with the no-allocation check at the set_tid_address node *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes StoreOk AgentLib Agenxn8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Agenxn8.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb Agenxn8B NodesB.

Section WithSegs.
Variable segs : list Segment.
Lemma rzb_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rzb_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rzb_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] | eapply nonalloc_no; [reflexivity | rewrite H17; reflexivity] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma rzb_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  rzb segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rzb_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rzb_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
End WithSegs.
