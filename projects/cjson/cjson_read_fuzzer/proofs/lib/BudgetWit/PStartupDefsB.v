(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from PStartupDefs.v (modules Nodes, AgentNodes, StartupNodes): rz_cases, rz_sys and rz_set_tid restated over BudgetWit.Rzb.rzb, with their released proofs; rzb_cases also takes the grant check of its node. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: rzb_cases also takes RomBase.sys_rob for its node, and rzb_set_tid gives it by RomBase.sys_rob_memfree, as rz_set_tid does. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim WallSim MmapSim AllocSim PropExec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RomBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.FileSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StoreOk.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.AgentNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.

(** [Nodes.rz_cases], with the grant check of the node. *)
Lemma rzb_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> RomBase.sys_rob segs c ->
  grant_ok c ->
  (forall i, rzb segs (nx i) (T i)) ->
  rzb segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hg Hc.
  apply (rzb_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rzb_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hg Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

End WithSegs.

(** [AgentNodes.rz_sys]. *)
Lemma rzb_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  rzb segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rzb_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

Section WithSegs2.
Variable segs : list Segment.

(** [StartupNodes.rz_set_tid]: set_tid_address is call 96, off the
    allocation numbers. *)
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
                    | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
                    | eapply RomBase.sys_rob_memfree; [reflexivity | rewrite H17, (u64_lit 96) by lia; exact RomBase.memfree_96]
                    | apply (grant_ok_no _ _ (getr regs 17) 96); [reflexivity | rewrite H17; apply u64_lit; lia | reflexivity] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

End WithSegs2.
