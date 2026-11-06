(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad MemImageType RiscvSemantics Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record spec_frame_facts : Prop := {
  (* [comment removed for export] *)
  sff_frame : forall L i m o,
    Inv m ->
    syscall_spec i m o ->
    alloc_budget_refused_b i m = false ->
    alloc_budget_refused_b i (m_relim L m) = false ->
    syscall_spec i (m_relim L m) (o_relim L o);
  (* [comment removed for export] *)
  sff_limit : forall i m x m' evs,
    syscall_spec i m (Ok x m' evs) -> m_limit m' = m_limit m;
  (* [comment removed for export] *)
  sff_gate_mono : forall L L' i m,
    (L <= L')%Z ->
    alloc_budget_refused_b i (m_relim L m) = false ->
    alloc_budget_refused_b i (m_relim L' m) = false;
  (* [comment removed for export] *)
  sff_inv : forall i m x m' evs,
    syscall_spec i m (Ok x m' evs) -> Inv m -> Inv m'
}.

Lemma inv_materialize : forall m acc m', materialize_model_accesses m acc = Some m' -> Inv m -> Inv m'.
Proof.
  intros m acc m' H HI. destruct (materialize_model_accesses_frame m acc m' H) as (_ & Hv & _).
  unfold Inv in *. rewrite Hv. exact HI.
Qed.

Lemma refusal_b_relim : forall L i m r, refusal_b i (m_relim L m) r = refusal_b i m r.
Proof. reflexivity. Qed.

Section Bridge.
Variable FF : spec_frame_facts.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma gate_up : forall L i m,
  (L <= m_limit m)%Z ->
  alloc_budget_refused_b i (m_relim L m) = false -> alloc_budget_refused_b i m = false.
Proof.
  intros L i m Hle Hg. pose proof (sff_gate_mono FF L (m_limit m) i m Hle Hg) as HG.
  rewrite m_relim_eta in HG. exact HG.
Qed.

Lemma spec_down : forall L i m o,
  Inv m ->
  (L <= m_limit m)%Z ->
  syscall_spec i m o ->
  alloc_budget_refused_b i (m_relim L m) = false ->
  syscall_spec i (m_relim L m) (o_relim L o).
Proof. intros L i m o HI Hle H Hg. exact (sff_frame FF L i m o HI H (gate_up L i m Hle Hg) Hg). Qed.

Lemma spec_up : forall L i m o,
  Inv m ->
  (L <= m_limit m)%Z ->
  syscall_spec i (m_relim L m) o ->
  alloc_budget_refused_b i (m_relim L m) = false ->
  syscall_spec i m (o_relim (m_limit m) o).
Proof.
  intros L i m o HI Hle H Hg.
  pose proof (sff_frame FF (m_limit m) i (m_relim L m) o (proj2 (Inv_relim L m) HI) H Hg) as HF.
  rewrite m_relim_idem, m_relim_eta in HF. apply HF.
  exact (gate_up L i m Hle Hg).
Qed.

Lemma spurious_relim_iff : forall L i m eff,
  Inv m ->
  (L <= m_limit m)%Z ->
  alloc_budget_refused_b i (m_relim L m) = false ->
  (spurious_refusal_cfg cfg i (m_relim L m) eff <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros L i m eff HI Hle Hg. unfold spurious_refusal_cfg. rewrite refusal_b_relim.
  split; intros (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)); (split; [exact Hoff | split; [exact Hr |]]).
  - exists eff', (m_relim (m_limit m) m'), evs'. split; [| rewrite refusal_b_relim in Hnr; exact Hnr].
    exact (spec_up L i m _ HI Hle Hs Hg).
  - exists eff', (m_relim L m'), evs'. split; [| rewrite refusal_b_relim; exact Hnr].
    exact (spec_down L i m _ HI Hle Hs Hg).
Qed.

(* [comment removed for export] *)
Definition quiet (c : config) : Prop := ~ budget_refused_at segs c.

Lemma quiet_gate : forall ms m x8,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  quiet (mkCfg ms m) -> alloc_budget_refused_b (sys_input segs ms x8) m = false.
Proof.
  intros ms m x8 Hh Hp Hq.
  destruct (alloc_budget_refused_b (sys_input segs ms x8) m) eqn:E; [| reflexivity].
  exfalso. apply Hq. split; [exact Hh |]. right. exists x8. split; [exact Hp |]. left. exact E.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_up_next : forall L c evs c1,
  Inv (cfg_model c) ->
  (L <= m_limit (cfg_model c))%Z ->
  quiet (c_relim L c) ->
  sstep_cfg segs cfg (c_relim L c) evs (SNext c1) ->
  exists c', sstep_cfg segs cfg c evs (SNext c') /\ c1 = c_relim L c' /\ m_limit (cfg_model c') = m_limit (cfg_model c).
Proof.
  intros L [ms m] evs c1 HI Hle Hq H. unfold c_relim in *. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; clear H.
  - (* [comment removed for export] *)
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report | |] eqn:Est; try discriminate.
    destruct (materialize_model_accesses (m_relim L m) (@accessed_ranges _ report)) as [m1 |] eqn:Em; try discriminate.
    match goal with Hx : MachineOk _ = MachineOk _ |- _ => injection Hx as <- <- end.
    pose proof (materialize_relim_up L (m_limit m) m _ _ Em Hle) as Hup. rewrite m_relim_eta in Hup.
    exists (mkCfg (@access_value _ report) (m_relim (m_limit m) m1)). split; [| split].
    + apply sstep_cfg_instr; [assumption | assumption |].
      unfold mi_account_step. rewrite Est, Hup. reflexivity.
    + cbn [cfg_ms cfg_model]. rewrite m_relim_idem.
      rewrite (m_relim_same L m1); [reflexivity |].
      rewrite (materialize_limit _ _ _ Em). reflexivity.
    + cbn [cfg_model]. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hh : m_halted (m_relim L m) = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ (m_relim L m) (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_up L _ m _ HI Hle Hs Hg) as HU; cbn [o_relim] in HU;
      pose proof (sff_limit FF _ _ _ _ _ Hs) as HL1 end.
    rewrite m_limit_relim in HL1.
    match goal with Hm : materialize_model_accesses ?mm _ = Some ?m2 |- _ =>
      pose proof (materialize_limit _ _ _ Hm) as HL2;
      assert (Hm' : materialize_model_accesses (m_relim L mm) (syscall_effect_accesses eff) = Some m2)
        by (rewrite (m_relim_same L mm HL1); exact Hm);
      pose proof (materialize_relim_up L (m_limit m) mm _ _ Hm' Hle) as Hup end.
    exists (mkCfg (advance_past_svc (apply_effect ms eff)) (m_relim (m_limit m) model'')). split; [| split].
    + eapply sstep_cfg_syscall; [assumption | eassumption | exact HU | | | exact Hup].
      * intros Hsp. match goal with Hn : ~ spurious_refusal_cfg _ _ _ _ |- _ => apply Hn end.
        apply (spurious_relim_iff L _ m eff HI Hle Hg). exact Hsp.
      * assumption.
    + cbn [cfg_ms cfg_model]. rewrite m_relim_idem. rewrite (m_relim_same L model''); [reflexivity |].
      rewrite HL2. exact HL1.
    + cbn [cfg_model]. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hh : m_halted (m_relim L m) = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ (m_relim L m) (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_up L _ m _ HI Hle Hs Hg) as HU; cbn [o_relim] in HU;
      pose proof (sff_limit FF _ _ _ _ _ Hs) as HL1 end.
    rewrite m_limit_relim in HL1.
    exists (mkCfg ms (m_relim (m_limit m) model')). split; [| split].
    + change (m_fs model') with (m_fs (m_relim (m_limit m) model')).
      eapply sstep_cfg_exit; [assumption | eassumption | exact HU | assumption | assumption].
    + cbn [cfg_ms cfg_model]. rewrite m_relim_idem. rewrite (m_relim_same L model' HL1). reflexivity.
    + cbn [cfg_model]. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hh : m_halted (m_relim L m) = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ (m_relim L m) (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_up L _ m _ HI Hle Hs Hg) as HU; cbn [o_relim] in HU;
      pose proof (sff_limit FF _ _ _ _ _ Hs) as HL1 end.
    rewrite m_limit_relim in HL1.
    exists (mkCfg ms (m_relim (m_limit m) model')). split; [| split].
    + change (m_fs model') with (m_fs (m_relim (m_limit m) model')).
      eapply sstep_cfg_killed; [assumption | eassumption | exact HU | assumption].
    + cbn [cfg_ms cfg_model]. rewrite m_relim_idem. rewrite (m_relim_same L model' HL1). reflexivity.
    + cbn [cfg_model]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_up_error : forall L c evs,
  Inv (cfg_model c) ->
  (L <= m_limit (cfg_model c))%Z ->
  quiet (c_relim L c) ->
  sstep_cfg segs cfg (c_relim L c) evs SError ->
  exists evs', sstep_cfg segs cfg c evs' SError.
Proof.
  intros L [ms m] evs HI Hle Hq H. unfold c_relim in *. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; clear H.
  - (* [comment removed for export] *)
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report | |] eqn:Est; try discriminate.
    + destruct (materialize_model_accesses (m_relim L m) (@accessed_ranges _ report)) as [m1 |] eqn:Em; try discriminate.
      exfalso. apply Hq. split; [assumption |]. left. split; [assumption |]. exists report. split; [exact Est | exact Em].
    + exists []. apply sstep_cfg_instr_fault; [assumption | assumption |]. unfold mi_account_step. rewrite Est. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report | |] eqn:Est; try discriminate.
    + destruct (materialize_model_accesses (m_relim L m) (@accessed_ranges _ report)); discriminate.
    + exists []. apply sstep_cfg_instr_unmodeled; [assumption | assumption |]. unfold mi_account_step. rewrite Est. reflexivity.
  - (* [comment removed for export] *)
    exfalso. apply Hq. split; [assumption |]. right. eexists. split; [eassumption |]. right.
    eexists _, _, _. split; [eassumption | split; eassumption].
  - (* [comment removed for export] *)
    match goal with Hh : m_halted (m_relim L m) = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ (m_relim L m) Unmodeled |- _ =>
      pose proof (spec_up L _ m _ HI Hle Hs Hg) as HU; cbn [o_relim] in HU end.
    exists []. eapply sstep_cfg_syscall_unmodeled; [assumption | eassumption | exact HU].
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_down : forall L c evs c',
  Inv (cfg_model c) ->
  (L <= m_limit (cfg_model c))%Z ->
  quiet (c_relim L c) ->
  sstep_cfg segs cfg c evs (SNext c') ->
  exists evs1 st1, sstep_cfg segs cfg (c_relim L c) evs1 st1.
Proof.
  intros L [ms m] evs c' HI Hle Hq H. unfold c_relim in *. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; clear H.
  - (* [comment removed for export] *)
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report | |] eqn:Est; try discriminate.
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1 |] eqn:Em; try discriminate.
    destruct (materialize_relim_down L m _ _ Em) as [Hn | Hs].
    + exfalso. apply Hq. split; [assumption |]. left. split; [assumption |]. exists report. split; [exact Est | exact Hn].
    + eexists _, _. apply sstep_cfg_instr; [assumption | assumption |]. unfold mi_account_step. rewrite Est, Hs. reflexivity.
  - (* [comment removed for export] *)
    match goal with Hh : m_halted m = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ m (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_down L _ m _ HI Hle Hs Hg) as HD; cbn [o_relim] in HD end.
    match goal with Hm : materialize_model_accesses ?mm _ = Some ?m2 |- _ =>
      destruct (materialize_relim_down L mm _ _ Hm) as [Hn | Hs2] end.
    + exfalso. apply Hq. split; [assumption |]. right. eexists. split; [eassumption |]. right.
      eexists _, _, _. split; [exact HD | split; [assumption | exact Hn]].
    + eexists _, _. eapply sstep_cfg_syscall; [assumption | eassumption | exact HD | | assumption | exact Hs2].
      intros Hsp. match goal with Hn : ~ spurious_refusal_cfg _ _ _ _ |- _ => apply Hn end.
      apply (spurious_relim_iff L _ m eff HI Hle Hg). exact Hsp.
  - (* [comment removed for export] *)
    match goal with Hh : m_halted m = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ m (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_down L _ m _ HI Hle Hs Hg) as HD; cbn [o_relim] in HD end.
    eexists _, _. eapply sstep_cfg_exit; [assumption | eassumption | exact HD | eassumption | eassumption].
  - (* [comment removed for export] *)
    match goal with Hh : m_halted m = None, Hp : ms_svc_pending ms = Some ?x |- _ =>
      pose proof (quiet_gate ms (m_relim L m) x Hh Hp Hq) as Hg end.
    match goal with Hs : syscall_spec _ m (Ok ?e ?mm ?ev) |- _ =>
      pose proof (spec_down L _ m _ HI Hle Hs Hg) as HD; cbn [o_relim] in HD end.
    eexists _, _. eapply sstep_cfg_killed; [assumption | eassumption | exact HD | eassumption].
Qed.

(* [comment removed for export] *)
Lemma never_refused_quiet : forall c, ~ reaches_budget_refused_cfg segs cfg c -> quiet c.
Proof. intros c H Hb. apply H. exists [], c. split; [apply star_cfg_refl | exact Hb]. Qed.
Lemma never_refused_step : forall c evs c',
  ~ reaches_budget_refused_cfg segs cfg c -> sstep_cfg segs cfg c evs (SNext c') ->
  ~ reaches_budget_refused_cfg segs cfg c'.
Proof.
  intros c evs c' H Hs (tr & c2 & Hstar & Hb). apply H.
  exists (evs ++ tr), c2. split; [eapply star_cfg_step; eassumption | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma inv_step : forall c evs c', Inv (cfg_model c) -> sstep_cfg segs cfg c evs (SNext c') -> Inv (cfg_model c').
Proof.
  intros [ms m] evs c' HI H. cbn [cfg_ms cfg_model] in *. inversion H; subst; clear H; cbn [cfg_model].
  - unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report | |] eqn:Est; try discriminate.
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1 |] eqn:Em; try discriminate.
    match goal with Hx : MachineOk _ = MachineOk _ |- _ => injection Hx as <- <- end.
    exact (inv_materialize _ _ _ Em HI).
  - match goal with Hs : syscall_spec _ m (Ok _ ?mm _), Hm : materialize_model_accesses ?mm _ = Some _ |- _ =>
      exact (inv_materialize _ _ _ Hm (sff_inv FF _ _ _ _ _ Hs HI)) end.
  - match goal with Hs : syscall_spec _ m (Ok _ _ _) |- _ => exact (sff_inv FF _ _ _ _ _ Hs HI) end.
  - match goal with Hs : syscall_spec _ m (Ok _ _ _) |- _ => exact (sff_inv FF _ _ _ _ _ Hs HI) end.
Qed.

(* [comment removed for export] *)
Theorem must_exit_in_at_cfg_lower_limit : forall S c,
  must_exit_in_at_cfg cfg segs S c ->
  forall L, Inv (cfg_model c) -> (L <= m_limit (cfg_model c))%Z ->
  ~ reaches_budget_refused_cfg segs cfg (c_relim L c) ->
  must_exit_in_at_cfg cfg segs S (c_relim L c).
Proof.
  intros S c H. induction H as [c code Hh Hin Hk | c Hh Hex Hne Hall IH]; intros L HI Hle Hnr.
  - apply (must_exit_in_at_cfg_halted cfg segs S (c_relim L c) code); [exact Hh | exact Hin | exact Hk].
  - pose proof (never_refused_quiet _ Hnr) as Hq.
    apply must_exit_in_at_cfg_running.
    + exact Hh.
    + destruct Hex as (evs & st & Hst). destruct st as [c' |].
      * exact (sstep_cfg_down L c evs c' HI Hle Hq Hst).
      * exfalso. exact (Hne evs Hst).
    + intros evs Herr. destruct (sstep_cfg_up_error L c evs HI Hle Hq Herr) as (evs' & He). exact (Hne evs' He).
    + intros evs c1 Hst.
      destruct (sstep_cfg_up_next L c evs c1 HI Hle Hq Hst) as (c' & Hs' & -> & Hl').
      apply (IH evs c' Hs' L); [exact (inv_step c evs c' HI Hs') | rewrite Hl'; exact Hle |].
      exact (never_refused_step _ _ _ Hnr Hst).
Qed.

End Bridge.

(* [comment removed for export] *)
Lemma init_config_relim : forall segs pc ph sp brk0 mb rnd L L' inp,
  init_config segs pc ph sp brk0 mb rnd L inp = c_relim L (init_config segs pc ph sp brk0 mb rnd L' inp).
Proof. reflexivity. Qed.

Theorem must_exit_in_scfg_lower_limit : forall (FF : spec_frame_facts) cfg S img L L' en inp,
  (L <= L')%Z ->
  must_exit_in_scfg cfg S img L' en inp ->
  ~ run_scfg_budget_refused cfg img L en inp ->
  must_exit_in_scfg cfg S img L en inp.
Proof.
  intros FF cfg S [segs pc ph] L L' [sp brk0 mb rnd] inp Hle H Hnr.
  cbn [must_exit_in_scfg run_scfg_budget_refused] in *.
  rewrite (init_config_relim segs pc ph sp brk0 mb rnd L L' inp).
  apply (must_exit_in_at_cfg_lower_limit FF segs cfg S _ H L).
  - unfold Inv. cbn. constructor.
  - cbn. exact Hle.
  - rewrite <- (init_config_relim segs pc ph sp brk0 mb rnd L L' inp). exact Hnr.
Qed.

Theorem halts_allowed_lower_limit : forall (FF : spec_frame_facts) cfg S img L L',
  (L <= L')%Z ->
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in_scfg cfg S img L' en inp) ->
  halts_allowed_T_scfg_budgets cfg L S img.
Proof.
  intros FF cfg S img L L' Hle H en inp Hen Hinp Hb.
  exact (must_exit_in_scfg_lower_limit FF cfg S img L L' en inp Hle (H en inp Hen Hinp) Hb).
Qed.
