(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied into libreac/fuzz_ctrl; LimSim imports renamed *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Common.LimSim Require Import LimSim LimSimMm LimSimArms LimSimMv LimSimWf LimSimSys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

Section Steps.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.

Ltac halt_tac H := first [ exact H | rewrite relim_halted; exact H | cbn [cfg_model cfg_ms]; rewrite relim_halted; exact H ].
Ltac kill_tac H := first [ exact H | rewrite relim_killed; exact H | cbn [cfg_model cfg_ms]; rewrite relim_killed; exact H ].

(* [comment removed for export] *)
Lemma step_down_exact : forall ms m evs st,
  MOK L0 m -> MV_OK m -> ~ budget_refused_at segs (mkCfg ms (relim L m)) ->
  sstep_cfg segs cfg (mkCfg ms m) evs st ->
  match st with
  | SNext c' => exists ms' m0, c' = mkCfg ms' m0 /\ MOK L0 m0 /\
                  sstep_cfg segs cfg (mkCfg ms (relim L m)) evs (SNext (mkCfg ms' (relim L m0)))
  | SError => sstep_cfg segs cfg (mkCfg ms (relim L m)) evs SError
  end.
Proof.
  intros ms m evs st HM MV NB Hs.
  remember (mkCfg ms m) as c eqn:Ec.
  destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
                 | ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
    injection Ec as -> ->.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [|discriminate].
    injection Ha as <- <-.
    destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
    + assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
      destruct (materialize_relim_up L m _ _ HLE' Emat1) as (m0' & Emat0 & ->).
      rewrite Emat0 in Emat. injection Emat as ->.
      exists (@access_value _ report), m0. split; [reflexivity|]. split; [unfold MOK; rewrite (materialize_limit _ _ _ Emat0); exact HM|].
      apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
    + exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|  |discriminate].
    + destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [discriminate|].
      destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
      * assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
        destruct (materialize_relim_up L m _ _ HLE' Emat1) as (m0' & Emat0 & _). rewrite Emat0 in Emat. discriminate Emat.
      * exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
    + apply sstep_cfg_instr_fault; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate|discriminate|].
    apply sstep_cfg_instr_unmodeled; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
    + assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
      destruct (materialize_relim_up L mm' _ _ HLE' Emat1) as (m0' & Hmat0 & ->).
      rewrite Hmat0 in Hmat. injection Hmat as ->.
      exists (advance_past_svc (apply_effect ms eff)), mm''. split; [reflexivity|].
      split; [unfold MOK; rewrite (materialize_limit _ _ _ Hmat0); exact HM0|].
      eapply sstep_cfg_syscall; [halt_tac Hh | exact Hp | exact Hsp0 | | halt_tac Hh' | exact Emat1].
      intros SP. apply Hnsp. exact (spurious_relim_down cfg L0 L HLE _ _ _ HM SP).
    + exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
      exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
    + assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
      destruct (materialize_relim_up L mm' _ _ HLE' Emat1) as (m0' & Hmat0 & _). rewrite Hmat0 in Hmat. discriminate Hmat.
    + exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
      exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    exists ms, mm'. split; [reflexivity|]. split; [exact HM0|].
    rewrite <- (relim_fs L mm').
    eapply sstep_cfg_exit; [halt_tac Hh | exact Hp | exact Hsp0 | halt_tac Hh' | kill_tac Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    exists ms, mm'. split; [reflexivity|]. split; [exact HM0|].
    rewrite <- (relim_fs L mm').
    eapply sstep_cfg_killed; [halt_tac Hh | exact Hp | exact Hsp0 | kill_tac Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
    eapply sstep_cfg_syscall_unmodeled; [halt_tac Hh | exact Hp | exact Hsp0].
Qed.

End Steps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Runs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.

Definition RINV (c : config) : Prop :=
  MOK L0 (cfg_model c) /\ WF (cfg_model c) /\ ~ reaches_budget_refused_cfg segs cfg (relim_cfg L c).

Lemma RINV_big_step : forall c evs c', RINV c -> sstep_cfg segs cfg c evs (SNext c') ->
  RINV c' /\ sstep_cfg segs cfg (relim_cfg L c) evs (SNext (relim_cfg L c')).
Proof.
  intros [ms m] evs c' (HM & HW & NR) Hs. cbn in HM, HW.
  pose proof (step_down_exact segs cfg L0 L HLE ms m evs (SNext c') HM (MV_OK_wf _ HW) (not_reaches_here segs cfg _ NR) Hs)
    as (ms' & m0 & -> & HM0 & Hs'). cbn in Hs'.
  split; [|exact Hs'].
  split; [exact HM0|]. split; [exact (sstep_cfg_WF segs cfg _ _ _ Hs HW)|].
  exact (not_reaches_step segs cfg _ _ _ NR Hs').
Qed.

Lemma RINV_small_step : forall c evs cs', RINV c -> sstep_cfg segs cfg (relim_cfg L c) evs (SNext cs') ->
  exists c', cs' = relim_cfg L c' /\ RINV c' /\ sstep_cfg segs cfg c evs (SNext c').
Proof.
  intros [ms m] evs cs' (HM & HW & NR) Hs. cbn in HM, HW. unfold relim_cfg in Hs. cbn in Hs.
  destruct (step_up segs cfg L0 L HLE ms m evs (SNext cs') HM (MV_OK_wf _ HW) (not_reaches_here segs cfg _ NR) Hs)
    as (ms' & m0 & Hs0 & -> & HM0).
  exists (mkCfg ms' m0). split; [reflexivity|]. split; [|exact Hs0].
  split; [exact HM0|]. split; [exact (sstep_cfg_WF segs cfg _ _ _ Hs0 HW)|].
  exact (not_reaches_step segs cfg _ _ _ NR Hs).
Qed.

Lemma star_down : forall c tr c', star_cfg segs cfg c tr c' -> RINV c ->
  RINV c' /\ star_cfg segs cfg (relim_cfg L c) tr (relim_cfg L c').
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hstar IH]; intros R.
  - split; [exact R | apply star_cfg_refl].
  - destruct (RINV_big_step _ _ _ R Hs) as (R2 & Hs'). destruct (IH R2) as (R3 & Hstar').
    split; [exact R3|]. eapply star_cfg_step; [exact Hs' | exact Hstar'].
Qed.

Lemma star_up : forall cs tr cs', star_cfg segs cfg cs tr cs' -> forall c, cs = relim_cfg L c -> RINV c ->
  exists c', cs' = relim_cfg L c' /\ RINV c' /\ star_cfg segs cfg c tr c'.
Proof.
  intros cs tr cs' H. induction H as [cs | cs1 evs cs2 tr cs3 Hs Hstar IH]; intros c -> R.
  - exists c. split; [reflexivity|]. split; [exact R | apply star_cfg_refl].
  - destruct (RINV_small_step _ _ _ R Hs) as (c2 & -> & R2 & Hs0).
    destruct (IH c2 eq_refl R2) as (c3 & -> & R3 & Hstar0).
    exists c3. split; [reflexivity|]. split; [exact R3|]. eapply star_cfg_step; [exact Hs0 | exact Hstar0].
Qed.

Theorem obs_trace_relim : forall c tr, RINV c ->
  obs_trace_cfg segs cfg (relim_cfg L c) tr <-> obs_trace_cfg segs cfg c tr.
Proof.
  intros c tr R. split.
  - intros (tr' & cs' & Hstar & Hp). destruct (star_up _ _ _ Hstar c eq_refl R) as (c' & _ & _ & Hstar0).
    exists tr', c'. split; [exact Hstar0 | exact Hp].
  - intros (tr' & c' & Hstar & Hp). destruct (star_down _ _ _ Hstar R) as (_ & Hstar').
    exists tr', (relim_cfg L c'). split; [exact Hstar' | exact Hp].
Qed.

Theorem reaches_error_relim : forall c, RINV c ->
  reaches_error_cfg segs cfg (relim_cfg L c) <-> reaches_error_cfg segs cfg c.
Proof.
  intros c R. split.
  - intros (tr & cs' & evs & Hstar & Herr). destruct (star_up _ _ _ Hstar c eq_refl R) as ([ms m] & -> & (HM & HW & NR) & Hstar0).
    exists tr, (mkCfg ms m), evs. split; [exact Hstar0|].
    exact (step_up segs cfg L0 L HLE ms m evs SError HM (MV_OK_wf _ HW) (not_reaches_here segs cfg _ NR) Herr).
  - intros (tr & [ms m] & evs & Hstar & Herr). destruct (star_down _ _ _ Hstar R) as ((HM & HW & NR) & Hstar').
    exists tr, (relim_cfg L (mkCfg ms m)), evs. split; [exact Hstar'|].
    exact (step_down_exact segs cfg L0 L HLE ms m evs SError HM (MV_OK_wf _ HW) (not_reaches_here segs cfg _ NR) Herr).
Qed.
End Runs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RINV_init : forall segs cfg pc ph sp brk0 mbase rnd Lbig Lsmall inp,
  source_within_budget_scfg cfg Lsmall (mkImage segs pc ph) (mkEntry sp brk0 mbase rnd) inp ->
  RINV segs cfg Lbig Lsmall (init_config segs pc ph sp brk0 mbase rnd Lbig inp).
Proof.
  intros segs cfg pc ph sp brk0 mbase rnd Lbig Lsmall inp NB.
  split; [apply init_config_limit|]. split; [apply init_config_WF|].
  unfold source_within_budget_scfg, run_scfg_budget_refused in NB.
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in NB. exact NB.
Qed.

Theorem run_scfg_relim_traces : forall cfg img (Lbig Lsmall : Z) en inp,
  Lsmall <= Lbig -> source_within_budget_scfg cfg Lsmall img en inp ->
  trace_equiv (bh_traces (run_scfg cfg img Lsmall en inp)) (bh_traces (run_scfg cfg img Lbig en inp)).
Proof.
  intros cfg [segs pc ph] Lbig Lsmall [sp brk0 mbase rnd] inp HLE NB tr. cbn.
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp).
  apply (obs_trace_relim segs cfg Lbig Lsmall HLE). exact (RINV_init segs cfg pc ph sp brk0 mbase rnd Lbig Lsmall inp NB).
Qed.

Theorem run_scfg_relim_errors : forall cfg img (Lbig Lsmall : Z) en inp,
  Lsmall <= Lbig -> source_within_budget_scfg cfg Lsmall img en inp ->
  (bh_errors (run_scfg cfg img Lsmall en inp) <-> bh_errors (run_scfg cfg img Lbig en inp)).
Proof.
  intros cfg [segs pc ph] Lbig Lsmall [sp brk0 mbase rnd] inp HLE NB. cbn.
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp).
  apply (reaches_error_relim segs cfg Lbig Lsmall HLE). exact (RINV_init segs cfg pc ph sp brk0 mbase rnd Lbig Lsmall inp NB).
Qed.

Theorem run_scfg_relim_error_free_unkilled : forall cfg img (Lbig Lsmall : Z) en inp,
  Lsmall <= Lbig -> source_within_budget_scfg cfg Lsmall img en inp ->
  error_free_unkilled (run_scfg cfg img Lbig en inp) -> error_free_unkilled (run_scfg cfg img Lsmall en inp).
Proof.
  intros cfg img Lbig Lsmall en inp HLE NB [EF NK]. split.
  - intros E. apply EF. apply (run_scfg_relim_errors cfg img Lbig Lsmall en inp HLE NB). exact E.
  - intros (tr & sig & fs & Htr & Hin). apply NK. exists tr, sig, fs. split; [|exact Hin].
    apply (run_scfg_relim_traces cfg img Lbig Lsmall en inp HLE NB). exact Htr.
Qed.

(* [comment removed for export] *)
Theorem strong_equiv_ef_budgets_scfg_relim_source : forall cfg (Lbig Lsmall Lt : Z) src tgt en_s en_t inp,
  Lsmall <= Lbig -> source_within_budget_scfg cfg Lsmall src en_s inp ->
  error_free_unkilled (run_scfg cfg src Lbig en_s inp) ->
  error_free_unkilled (run_scfg cfg tgt Lt en_t inp) ->
  trace_equiv (bh_traces (run_scfg cfg src Lbig en_s inp)) (bh_traces (run_scfg cfg tgt Lt en_t inp)) ->
  error_free_unkilled (run_scfg cfg src Lsmall en_s inp) /\
  error_free_unkilled (run_scfg cfg tgt Lt en_t inp) /\
  trace_equiv (bh_traces (run_scfg cfg src Lsmall en_s inp)) (bh_traces (run_scfg cfg tgt Lt en_t inp)).
Proof.
  intros cfg Lbig Lsmall Lt src tgt en_s en_t inp HLE NB EFs EFt TE.
  split; [exact (run_scfg_relim_error_free_unkilled cfg src Lbig Lsmall en_s inp HLE NB EFs)|].
  split; [exact EFt|].
  intros tr. rewrite (run_scfg_relim_traces cfg src Lbig Lsmall en_s inp HLE NB tr). apply TE.
Qed.
