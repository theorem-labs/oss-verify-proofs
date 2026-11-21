(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from Nodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob at the rzb nodes, as Nodes.v asks it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SimInv ExitSim CatSim FileSim ShapeAlg.
Import ListNotations.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Nodes.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RomBase.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Section WithSegs.
Variable segs : list Segment.
Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [Nodes.halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold Nodes.halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold Nodes.halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.
Lemma sstep_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.
Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy. split.
  - intros i. apply (sstep_of_check ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.
Lemma rzb_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  Rzb.grant_ok segs (mkCfg ms model) ->
  Rzb.rzb segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  Rzb.rzb segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hrob Hchk Hh' Hlazy Hg Hc.
  eapply Rzb.rzb_silent1; [eapply node_ret_only_copyins; eassumption | exact Hrob | exact Hg | exact Hc].
Qed.
Lemma rzb_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  Rzb.grant_ok segs c ->
  (forall i, Rzb.rzb segs (nx i) (T i)) ->
  Rzb.rzb segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hg Hc.
  apply (Rzb.rzb_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (Rzb.rzb_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hg Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (Rzb.rzb_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (Rzb.rzb_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.
End WithSegs.
