(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YQ02.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YQ00 YQ03 YQ04 YQ06 YQ05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Set Default Proof Mode "Classic".
Section a.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.
Definition relim_to (st : step_to) : step_to :=
match st with SNext c' => SNext (relim_cfg L c') | SError => SError end.
Ltac halt_tac H := first [ exact H | rewrite relim_halted; exact H | cbn [cfg_model cfg_ms]; rewrite relim_halted; exact H ].
Ltac kill_tac H := first [ exact H | rewrite relim_killed; exact H | cbn [cfg_model cfg_ms]; rewrite relim_killed; exact H ].
Lemma step_down_sim : forall ms m evs st,
MOK L0 m -> MV_OK m -> ~ budget_refused_at segs (mkCfg ms (relim L m)) ->
sstep_cfg segs cfg (mkCfg ms m) evs st ->
sstep_cfg segs cfg (mkCfg ms (relim L m)) evs (relim_to st)
/\ match st with SNext c' => MOK L0 (cfg_model c') | SError => True end.
Proof.
intros ms m evs st HM MV NB Hs.
remember (mkCfg ms m) as c eqn:Ec.
destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
| ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
injection Ec as -> ->; cbn [relim_to relim_cfg cfg_ms cfg_model].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [|discriminate].
injection Ha as <- <-.
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
+ pose proof (materialize_relim_down L m _ _ Emat ltac:(rewrite Emat1; discriminate)) as E1. rewrite Emat1 in E1. injection E1 as ->.
split; [| unfold MOK; rewrite (materialize_limit _ _ _ Emat); exact HM].
apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
+ exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [| |discriminate].
+ destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [discriminate|]. exfalso.
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
* assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
destruct (materialize_relim_up L m _ _ HLE' Emat1) as (m0' & E0 & _). rewrite E0 in Emat. discriminate Emat.
* apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
+ split; [|exact I]. apply sstep_cfg_instr_fault; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate|discriminate|].
split; [|exact I]. apply sstep_cfg_instr_unmodeled; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
-
pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
+ pose proof (materialize_relim_down L mm' _ _ Hmat ltac:(rewrite Emat1; discriminate)) as E1. rewrite Emat1 in E1. injection E1 as ->.
split; [| unfold MOK; rewrite (materialize_limit _ _ _ Hmat); exact HM0].
eapply sstep_cfg_syscall; [halt_tac Hh | exact Hp | exact Hsp0 | | halt_tac Hh' | exact Emat1].
intros SP. apply Hnsp. exact (spurious_relim_down cfg L0 L HLE _ _ _ HM G SP).
+ exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
-
pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
+ assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
destruct (materialize_relim_up L mm' _ _ HLE' Emat1) as (m0' & Hmat0 & _). rewrite Hmat0 in Hmat. discriminate Hmat.
+ exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
-
pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
split; [|exact HM0]. rewrite <- (relim_fs L mm').
eapply sstep_cfg_exit; [halt_tac Hh | exact Hp | exact Hsp0 | halt_tac Hh' | kill_tac Hk].
-
pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
split; [|exact HM0]. rewrite <- (relim_fs L mm').
eapply sstep_cfg_killed; [halt_tac Hh | exact Hp | exact Hsp0 | kill_tac Hk].
-
pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
split; [|exact I]. eapply sstep_cfg_syscall_unmodeled; [halt_tac Hh | exact Hp | exact Hsp0].
Qed.
Definition INV (c : config) : Prop :=
MOK L0 (cfg_model c) /\ WF (cfg_model c) /\ ~ reaches_budget_refused_cfg segs cfg (relim_cfg L c).
Lemma INV_step : forall c evs c', INV c -> sstep_cfg segs cfg c evs (SNext c') ->
sstep_cfg segs cfg (relim_cfg L c) evs (SNext (relim_cfg L c')) /\ INV c'.
Proof.
intros [ms m] evs c' (HM & HW & NR) Hs. cbn [cfg_model] in HM, HW.
pose proof (step_down_sim ms m evs (SNext c') HM (MV_OK_wf m HW) (not_reaches_here segs cfg _ NR) Hs) as [Hs' HM']. cbn [relim_to] in Hs'.
split; [exact Hs'|]. split; [exact HM'|]. split; [exact (sstep_cfg_WF segs cfg _ _ _ Hs HW) | exact (not_reaches_step segs cfg _ _ _ NR Hs')].
Qed.
Lemma star_down : forall c tr c', star_cfg segs cfg c tr c' -> INV c ->
star_cfg segs cfg (relim_cfg L c) tr (relim_cfg L c') /\ INV c'.
Proof.
intros c tr c' Hst. induction Hst as [c | c1 evs c2 tr c3 Hs Hst IH]; intros HI.
- split; [apply star_cfg_refl | exact HI].
- destruct (INV_step _ _ _ HI Hs) as [Hs' HI2]. destruct (IH HI2) as [Hst' HI3].
split; [eapply star_cfg_step; [exact Hs' | exact Hst'] | exact HI3].
Qed.
Lemma star_up : forall c0 tr c1, star_cfg segs cfg c0 tr c1 ->
forall c, c0 = relim_cfg L c -> INV c ->
exists c', star_cfg segs cfg c tr c' /\ c1 = relim_cfg L c' /\ INV c'.
Proof.
intros c0 tr c1 Hst. induction Hst as [c0 | c0 evs c2 tr c3 Hs Hst IH]; intros [ms m] -> (HM & HW & NR).
- exists (mkCfg ms m). split; [apply star_cfg_refl | split; [reflexivity | exact (conj HM (conj HW NR))]].
- cbn [cfg_model] in HM, HW.
destruct (step_up segs cfg L0 L HLE ms m evs (SNext c2) HM (MV_OK_wf m HW) (not_reaches_here segs cfg _ NR) Hs) as (ms' & m0 & Hs0 & -> & HM0).
assert (HI2 : INV (mkCfg ms' m0)).
{ split; [exact HM0|]. split; [exact (sstep_cfg_WF segs cfg _ _ _ Hs0 HW) | exact (not_reaches_step segs cfg _ _ _ NR Hs)]. }
destruct (IH (mkCfg ms' m0) eq_refl HI2) as (c' & Hst0 & -> & HI3).
exists c'. split; [eapply star_cfg_step; [exact Hs0 | exact Hst0] | split; [reflexivity | exact HI3]].
Qed.
Theorem obs_trace_relim_iff : forall c tr, INV c -> (obs_trace_cfg segs cfg (relim_cfg L c) tr <-> obs_trace_cfg segs cfg c tr).
Proof.
intros c tr HI. split; intros (tr' & c1 & Hst & Hpre).
- destruct (star_up _ _ _ Hst c eq_refl HI) as (c' & Hst' & _ & _). exists tr', c'. split; [exact Hst' | exact Hpre].
- destruct (star_down _ _ _ Hst HI) as [Hst' _]. exists tr', (relim_cfg L c1). split; [exact Hst' | exact Hpre].
Qed.
Theorem reaches_error_relim_iff : forall c, INV c -> (reaches_error_cfg segs cfg (relim_cfg L c) <-> reaches_error_cfg segs cfg c).
Proof.
intros c HI. split; intros (tr & c1 & evs & Hst & Herr).
- destruct (star_up _ _ _ Hst c eq_refl HI) as ([ms m] & Hst' & -> & (HM & HW & NR)). cbn [cfg_model] in HM, HW.
exists tr, (mkCfg ms m), evs. split; [exact Hst'|].
exact (step_up segs cfg L0 L HLE ms m evs SError HM (MV_OK_wf m HW) (not_reaches_here segs cfg _ NR) Herr).
- destruct (star_down _ _ _ Hst HI) as [Hst' (HM & HW & NR)]. destruct c1 as [ms m]. cbn [cfg_model] in HM, HW.
exists tr, (relim_cfg L (mkCfg ms m)), evs. split; [exact Hst'|].
exact (proj1 (step_down_sim ms m evs SError HM (MV_OK_wf m HW) (not_reaches_here segs cfg _ NR) Herr)).
Qed.
Theorem reaches_unmodeled_relim : forall c, INV c -> reaches_unmodeled_cfg segs cfg (relim_cfg L c) -> reaches_unmodeled_cfg segs cfg c.
Proof.
intros c HI (tr & c1 & Hst & Hun).
destruct (star_up _ _ _ Hst c eq_refl HI) as ([ms m] & Hst' & -> & (HM & HW & NR)). cbn [cfg_model] in HM, HW.
exists tr, (mkCfg ms m). split; [exact Hst'|]. unfold unmodeled_at in Hun |- *. cbn [cfg_ms cfg_model relim_cfg] in Hun |- *.
destruct Hun as (Hh & [(Hp & Ha) | (x8 & Hp & Hsp)]); rewrite relim_halted in Hh.
- split; [exact Hh|]. left. split; [exact Hp|].
unfold mi_account_step in Ha |- *.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|reflexivity].
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)); discriminate.
- split; [exact Hh|]. right. exists x8. split; [exact Hp|].
destruct (syscall_spec_dir L0 L HLE true _ m HM (not_refused_mark segs L ms m x8 (not_reaches_here segs cfg _ NR) Hh Hp) ltac:(discriminate) _ Hsp)
as ([|] & Hsp0 & R); cbn in R; [contradiction | exact Hsp0].
Qed.
End a.
Section b.
Variable cfg : SpuriousCfg.
Variable img : Image.
Variables Lbig Lsmall : Z.
Variable en : ExecEntry.
Variable inp : ProcInput.
Hypothesis HLE : Lsmall <= Lbig.
Hypothesis NB : ~ run_scfg_budget_refused cfg img Lsmall en inp.
Let segs := match img with mkImage s _ _ => s end.
Let cbig : config := match img, en with mkImage s pc ph, mkEntry sp brk0 mbase rnd => init_config s pc ph sp brk0 mbase rnd Lbig inp end.
Lemma csmall_eq : match img, en with mkImage s pc ph, mkEntry sp brk0 mbase rnd => init_config s pc ph sp brk0 mbase rnd Lsmall inp end = relim_cfg Lsmall cbig.
Proof. subst cbig. destruct img, en. reflexivity. Qed.
Lemma INV_init : INV segs cfg Lbig Lsmall cbig.
Proof.
split; [subst cbig segs; destruct img, en; reflexivity|].
split; [subst cbig segs; destruct img, en; apply init_config_WF|].
intros R. apply NB. unfold run_scfg_budget_refused. subst cbig segs. destruct img as [s pc ph], en as [sp brk0 mbase rnd].
exact R.
Qed.
Theorem run_relim_trace_equiv : trace_equiv (bh_traces (run_scfg cfg img Lsmall en inp)) (bh_traces (run_scfg cfg img Lbig en inp)).
Proof.
pose proof INV_init as HI. pose proof csmall_eq as E. intros tr. unfold run_scfg. subst cbig segs.
destruct img as [s pc ph], en as [sp brk0 mbase rnd]. cbn [bh_traces]. rewrite E.
exact (obs_trace_relim_iff s cfg Lbig Lsmall HLE _ tr HI).
Qed.
Theorem run_relim_errors_iff : bh_errors (run_scfg cfg img Lsmall en inp) <-> bh_errors (run_scfg cfg img Lbig en inp).
Proof.
pose proof INV_init as HI. pose proof csmall_eq as E. unfold run_scfg. subst cbig segs.
destruct img as [s pc ph], en as [sp brk0 mbase rnd]. cbn [bh_errors]. rewrite E.
exact (reaches_error_relim_iff s cfg Lbig Lsmall HLE _ HI).
Qed.
Theorem run_relim_error_free : error_free (run_scfg cfg img Lbig en inp) -> error_free (run_scfg cfg img Lsmall en inp).
Proof. intros H E. apply H. apply run_relim_errors_iff. exact E. Qed.
Theorem run_relim_modeled : modeled (run_scfg cfg img Lbig en inp) -> modeled (run_scfg cfg img Lsmall en inp).
Proof.
pose proof INV_init as HI. pose proof csmall_eq as E. unfold modeled, run_scfg. subst cbig segs.
destruct img as [s pc ph], en as [sp brk0 mbase rnd]. cbn [bh_unmodeled]. rewrite E.
intros H U. apply H. exact (reaches_unmodeled_relim s cfg Lbig Lsmall HLE _ HI U).
Qed.
End b.
