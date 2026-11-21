(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from RefNodes.v's rz_set_tid for the budget-premise witness: the released statement over BudgetWit.Rzb.realizes, proved by hand because the released proof is a replayed term that builds the node through Nodes.rz_cases, which over Rzb also takes the node's no-allocation check. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the node's check takes the system-call robustness premise (sys_rob). *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes Gap04 RefNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.AgNB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : list Segment.
Context {SC : StepCfg}.

(** [set_tid_address] (96): the ecall step, then one node whose children are
    the tids the kernel may return ([RefNodes.node_set_tid]); 96 has no
    injecting arm and is no allocation number, so the node passes the check. *)
Lemma rz_set_tid : forall regs pc mem rom model (K : TSet) (w : bv 32),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid : word, (0 < bv_unsigned tid < Fork.PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Ht0 HK.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; reflexivity).
  set (ms := epend regs pc mem rom (getr regs 17)).
  set (t1 := exist _ (Z_to_bv 64 1) one_tid_ok : tid_I).
  apply (rz_conseq segs (mkCfg ms model) (t_alt (fun _ : tid_I => K))).
  - apply (rz_cases segs (mkCfg ms model) tid_I
             (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model))
             (fun _ => K) t1).
    + apply (node_set_tid segs ms model (getr regs 17)); [exact Hh | exact Hlazy | reflexivity | exact Hno | exact Ht0].
    + apply (nonalloc_no segs ms model (getr regs 17));
        [ reflexivity | rewrite Hno; vm_compute; reflexivity | rewrite Hno; vm_compute; reflexivity
        | eapply RomBase.sys_rob_memfree; [reflexivity | rewrite Hno; exact RomBase.memfree_96] ].
    + intros [t Ht]. cbn [proj1_sig]. unfold ms. rewrite adv_set_epend. apply HK. exact Ht.
  - intros tr. split.
    + intros [_ H]. exact H.
    + intros H. exists t1. exact H.
Qed.

End WithSegs.
