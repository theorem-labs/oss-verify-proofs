From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK0i YK15 YM06.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Exec RegisterBridge Regs6ss.
Import ListNotations.

Inductive mat_le : Model -> Model -> Prop :=
| mat_refl : forall m, mat_le m m
| mat_step : forall m acc m' m'',
    materialize_model_accesses m acc = Some m' -> mat_le m' m'' -> mat_le m m''.

Lemma mat_le_trans : forall m1 m2 m3, mat_le m1 m2 -> mat_le m2 m3 -> mat_le m1 m3.
Proof.
  intros m1 m2 m3 H12. induction H12 as [m | m acc m' m'' Hm H IH]; intros H23; [exact H23 |].
  exact (mat_step m acc m' m3 Hm (IH H23)).
Qed.

Lemma mat_le_frame : forall m m', mat_le m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m /\
  m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\ m_lim m' = m_lim m.
Proof.
  intros m m' H. induction H as [m | m acc m1 m2 Hm H IH].
  - repeat split.
  - destruct (materialize_model_accesses_frame m acc m1 Hm) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    destruct IH as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    repeat split; congruence.
Qed.

Lemma mat_le_halted : forall m m', mat_le m m' -> m_halted m' = m_halted m.
Proof.
  intros m m' H. destruct (mat_le_frame m m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

Section Lift.
Variable segs : list Segment.

Lemma acct_cases : forall ms model ms',
  RiscvSemantics.step segs ms = MachineOk ms' ->
  (exists acc model', materialize_model_accesses model acc = Some model' /\
     mi_account_step segs ms model = MachineOk (ms', model'))
  \/ (exists report, RiscvSemantics.step_accesses segs ms = MachineOk report /\
     materialize_model_accesses model (@accessed_ranges _ report) = None).
Proof.
  intros ms model ms' Hstep.
  pose proof (RiscvSemantics.drop_step_accesses segs ms) as Hdrop.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Hacc; cbn in Hdrop;
    rewrite Hstep in Hdrop; try discriminate.
  injection Hdrop as Hv.
  destruct (materialize_model_accesses model (@accessed_ranges _ report)) as [model'|] eqn:Hm.
  - left. exists (@accessed_ranges _ report), model'. split; [exact Hm |].
    rewrite Hv. reflexivity.
  - right. exists report. split; [reflexivity | exact Hm].
Qed.

Lemma node_instr_lazy : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' model' Hh Hsvc Ha.
  apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc |]. split.
  - intros []. exact (sstep_instr segs ms model ms' model' Hh Hsvc Ha).
  - intros e st Hss. exists tt.
    inversion Hss; subst; try congruence.
    match goal with H : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Ha in H; injection H as <- <- end.
    split; reflexivity.
Qed.

Lemma rz_step_lazy : forall ms model ms' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  (forall model', mat_le model model' -> realizes segs (mkCfg ms' model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hsvc Hstep K.
  destruct (acct_cases ms model ms' Hstep) as [(acc & model' & Hm & Ha) | (report & Hr & Hn)].
  - eapply rz_silent1; [exact (node_instr_lazy ms model ms' model' Hh Hsvc Ha) |].
    apply K. exact (mat_step model acc model' model' Hm (mat_refl model')).
  - apply rz_cut. unfold budget_refused_at. split; [exact Hh |]. left. split; [exact Hsvc |].
    exists report. split; [exact Hr | exact Hn].
Qed.

Lemma rz_msteps_lazy : forall ms ms' model T,
  m_halted model = None ->
  msteps segs ms ms' ->
  (forall model', mat_le model model' -> realizes segs (mkCfg ms' model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hms. revert model Hh.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros model Hh K.
  - apply K. apply mat_refl.
  - apply (rz_step_lazy ms model ms1 T Hh Hsvc Hstep). intros model1 H1.
    apply IH; [rewrite (mat_le_halted model model1 H1); exact Hh |].
    intros model2 H2. apply K. exact (mat_le_trans model model1 model2 H1 H2).
Qed.

Lemma exec_msteps : forall ms final, Exec.msteps segs ms final -> msteps segs ms final.
Proof.
  intros ms final H. induction H as [ms|ms mid final [HS HV] HT IH].
  - constructor.
  - econstructor; eassumption.
Qed.

Lemma evt_SR_lazy : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None ->
  (forall ms' md', Q ms' -> mat_le md md' -> SR segs (mkCfg ms' md') P) ->
  SR segs (mkCfg ms md) P.
Proof.
  intros ms Q md P [final [Hs HQ]] Hh K T HK.
  apply (rz_msteps_lazy ms final md T Hh (exec_msteps ms final Hs)).
  intros md' Hle. exact (K final md' HQ Hle T HK).
Qed.

Lemma evt_SR_canon_lazy : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None ->
  (forall ms' md', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> mat_le md md' -> SR segs (mkCfg ms' md') P) ->
  SR segs (mkCfg ms md) P.
Proof.
  intros ms Q md P H Hh K.
  exact (evt_SR_lazy ms _ md P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh K).
Qed.

End Lift.
