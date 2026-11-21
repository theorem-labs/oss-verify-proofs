(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/Nodes.v (rz_ret_only_copyins_silent, rz_cases), Common/ShapeNodes.v (rz_ecall) and Common/RefNodesMF.v (rz_set_tid_ms, rz_set_tid_at), restated over the budget carrier rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the read-only-backing premise sys_rob of rzb_ret_only_copyins_silent and rzb_cases, given by rob_auto at the set_tid node; import of Cfg.RomBase). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  AsanCeil SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg ShapeNodes Nodes StoreOk AgentLib SpecConsts RefNodes PureModel AllocRefusal CfgStep.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import RefNodesMF.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Cfg Require Import RomBase.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.BudgetWit Require Import Rzb.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma rzb_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  rzb segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hna Hrob Hchk Hh' Hlazy Hc.
  eapply rzb_silent1;
    [eapply (Nodes.node_ret_only_copyins segs); eassumption | exact Hrob
    | exact (nalloc_ok_sysno ms model x8 _ Hsvc eq_refl Hna) | exact Hc].
Qed.

Lemma rzb_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> sys_rob segs c ->
  nalloc_ok c ->
  (forall i, rzb segs (nx i) (T i)) ->
  rzb segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hna Hc.
  apply (rzb_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rzb_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hna Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (rzb_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(** [RefNodesMF.rz_set_tid_ms]: the node is set_tid_address (96). *)
Lemma rzb_set_tid_ms : forall ms model x8 T,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     rzb segs (mkCfg (advance_past_svc (set_gpr0 ms tid)) (with_tid tid model)) T) ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Htid Hk.
  apply (rzb_conseq segs _ (t_alt (fun _ : tid_I => T)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rzb_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                    | eapply node_set_tid; [exact Hh | exact Hlazy | exact Hsvc | exact Hno | exact Htid] | rob_auto
                    | exact (nalloc_ok_sysno ms model x8 96 Hsvc Hno eq_refl) |].
  intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.
End WithSegs.

Section EcallAt.
Context {fx : FPState}.

(** [ShapeNodes.rz_ecall]: an instruction node. *)
Lemma rzb_ecall : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  rzb segs (mkCfg (ecall_st regs pc mem rom) model) T ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy Hf He Hc.
  eapply rzb_step; [exact Hh | exact Hlazy | reflexivity
                   | eapply step_ecall_st; eassumption | exact Hc].
Qed.

Variable segs : list Segment.

(** [RefNodesMF.rz_set_tid_at]. *)
Lemma rzb_set_tid_at : forall regs (pc : word) mem rom model w T,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) T) ->
  rzb segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hp HF HE H17 Htid Hk.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rzb_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rzb_set_tid_ms segs (ecall_st regs pc mem rom) model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | exact H17 | exact Htid |].
  intros tid Ht. rewrite adv_setgpr0_st. apply Hk. exact Ht.
Qed.
End EcallAt.
