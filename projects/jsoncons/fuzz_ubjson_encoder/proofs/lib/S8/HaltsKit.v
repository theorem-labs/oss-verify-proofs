(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ExitSim CatSim ShapeAlg DivergeSim SpinAlg Spec BigintSpec KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition exit_codes_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> forall code fs, In (ExitEv code fs) tr -> In code S.

Lemma exit_codes_in_t_eq : forall S T T', t_eq T T' -> exit_codes_in S T -> exit_codes_in S T'.
Proof. intros S T T' Heq H tr Htr code fs Hin. refine (H tr _ code fs Hin). apply Heq; exact Htr. Qed.

Lemma kill_free_t_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.

Lemma exit_codes_in_branch : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exit_codes_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exit_codes_in S (T i).
Proof.
  intros S I evs T i H tr Htr code fs Hin.
  refine (H (evs i ++ tr) _ code fs _); [| apply in_app_iff; right; exact Hin].
  exists i. right. exists tr. split; [reflexivity | exact Htr].
Qed.

Lemma kill_free_branch : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kill_free (t_alt (fun i => t_emit (evs i) (T i))) -> kill_free (T i).
Proof.
  intros I evs T i H tr Htr.
  assert (HF : Forall ev_not_kill (evs i ++ tr)).
  { apply H. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
  apply Forall_app in HF as [_ HF]. exact HF.
Qed.

Lemma node_evs_trace : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  T i [] -> t_alt (fun i => t_emit (evs i) (T i)) (evs i).
Proof.
  intros I evs T i H0. exists i. right. exists []. split; [rewrite app_nil_r; reflexivity | exact H0].
Qed.

Lemma exit_codes_in_t_exit : forall S code fs, In code S -> exit_codes_in S (t_exit code fs).
Proof.
  intros S code fs Hin tr Htr c' fs' Hc.
  unfold t_exit, t_emit, t_nil in Htr.
  assert (Hc' : In (ExitEv c' fs') [ExitEv code fs]).
  { destruct Htr as [Hp | (tr' & -> & ->)].
    - exact (in_is_prefix _ _ _ Hp Hc).
    - rewrite app_nil_r in Hc. exact Hc. }
  destruct Hc' as [Hc' | []]. injection Hc' as -> _. exact Hin.
Qed.

Lemma exit_codes_in_emit_writes : forall S ch s T,
  exit_codes_in S T -> exit_codes_in S (t_emit (Spec.W ch s) T).
Proof.
  intros S ch s T H tr Htr code fs Hin.
  destruct Htr as [Hp | (tr' & -> & HT)].
  - exfalso. assert (Hin' : In (ExitEv code fs) (Spec.W ch s)) by exact (in_is_prefix _ _ _ Hp Hin).
    unfold Spec.W in Hin'. apply in_map_iff in Hin' as (b & Hb & _). discriminate Hb.
  - apply in_app_iff in Hin as [Hin | Hin].
    + exfalso. unfold Spec.W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb.
    + exact (H tr' HT code fs Hin).
Qed.

Lemma exit_codes_in_alt2 : forall S A B, exit_codes_in S A -> exit_codes_in S B -> exit_codes_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [Htr | Htr]; [exact (HA tr Htr) | exact (HB tr Htr)]. Qed.

Lemma exit_codes_in_die : forall S msg fs, In (Spec.exit_code 2) S -> exit_codes_in S (Spec.t_die msg fs).
Proof. intros S msg fs H2. unfold Spec.t_die. apply exit_codes_in_emit_writes. apply exit_codes_in_t_exit. exact H2. Qed.

Section SpecCodes.
Context {fx : PropExec.FPState} {bmK : BMode}.
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in02_0 : In (Spec.exit_code 0) codes02. Proof. left. reflexivity. Qed.
Lemma in02_2 : In (Spec.exit_code 2) codes02. Proof. right. left. reflexivity. Qed.

Lemma exit_codes_in_t_body : forall data fs, exit_codes_in codes02 (BigintSpec.t_body data fs).
Proof.
  intros data fs. unfold BigintSpec.t_body.
  repeat first [ apply exit_codes_in_die; apply in02_2
               | apply exit_codes_in_emit_writes
               | apply exit_codes_in_t_exit; apply in02_0
               | match goal with |- exit_codes_in _ (if ?c then _ else _) => destruct c end
               | match goal with |- exit_codes_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma exit_codes_in_spec : forall argv fs, exit_codes_in codes02 (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply exit_codes_in_die; apply in02_2
               | apply exit_codes_in_t_body
               | apply exit_codes_in_alt2
               | apply exit_codes_in_t_exit; apply in02_0
               | match goal with |- exit_codes_in _ (if ?c then _ else _) => destruct c end
               | match goal with |- exit_codes_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
End SpecCodes.

Section WithSegs.
Variable segs : list Segment.

Lemma m_halted_of_proc : forall m m', m_proc m' = m_proc m -> m_halted m' = m_halted m.
Proof. intros m m' H. unfold m_halted. rewrite H. reflexivity. Qed.

Lemma sstep_cfg_into_halted : forall cfg c evs c' code,
  sstep_cfg segs cfg c evs (SNext c') ->
  m_halted (cfg_model c') = Some code ->
  (m_killed (cfg_model c') = None /\ exists evs0 fs, evs = evs0 ++ [ExitEv code fs])
  \/ (exists evs0 sig fs, evs = evs0 ++ [KillEv sig fs]).
Proof.
  intros cfg c evs c' code Hss Hh.
  inversion Hss; subst; cbn [cfg_model] in Hh.
  -   exfalso.
    match goal with [ H : mi_account_step _ _ _ = MachineOk _ |- _ ] =>
      pose proof (mi_account_step_model_frame _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  -   exfalso.
    match goal with [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
      pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  -   left. split; [assumption |].
    match goal with [ H : m_halted ?m = Some ?c0 |- _ ] => idtac end.
    assert (code0 = code) by congruence. subst. eexists _, _. reflexivity.
  -   right. eexists _, _, _. reflexivity.
Qed.

Definition reach_fo (c0 c : config) : Prop := exists tr, star_cfg segs forced_only_cfg c0 tr c.

Lemma reach_fo_refl : forall c0, reach_fo c0 c0.
Proof. intros c0. exists []. apply star_cfg_refl. Qed.

Lemma star_cfg_snoc : forall cfg c0 tr c evs c',
  star_cfg segs cfg c0 tr c -> sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c0 (tr ++ evs) c'.
Proof.
  intros cfg c0 tr c evs c' Hstar Hss. induction Hstar as [c1 | c1 evs1 c2 tr2 c3 Hs Hst IH].
  - cbn. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | exact (IH Hss)].
Qed.

Lemma reach_fo_step : forall c0 c evs c',
  reach_fo c0 c -> sstep_cfg segs forced_only_cfg c evs (SNext c') -> reach_fo c0 c'.
Proof. intros c0 c evs c' (tr & Hstar) Hss. exists (tr ++ evs). eapply star_cfg_snoc; eassumption. Qed.

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity |].
    exfalso. apply H. eexists _, _, _. split; [exact Hspec | exact Hr].
Qed.

Lemma fo_progress : forall cfg c evs st,
  sstep_cfg segs cfg c evs st -> exists evs' st', sstep_cfg segs forced_only_cfg c evs' st'.
Proof.
  intros cfg [ms model] evs st Hss.
  eapply sstep_cfg_progress; [| eapply sstep_cfg_sub; exact Hss].
  intros x8 _. apply refusal_decided_classic.
Qed.

Section Master.
Variable scfgD : SpuriousCfg.
Context {fx : PropExec.FPState} {bmK : BMode}.
Hypothesis BMON : bm_on = true.
Variable S : list word.
Variable c0 : config.
Hypothesis NOREFUSE : forall c, reach_fo c0 c -> ~ budget_refused_at segs c.

Theorem srealizes_must_exit_fo : forall c T,
  srealizes0 segs scfgD c T ->
  reach_fo c0 c ->
  exit_codes_in S T ->
  kill_free T ->
  (forall code, m_halted (cfg_model c) = Some code -> In code S /\ m_killed (cfg_model c) = None) ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh Hmode | c T T' H IH Heq | c T Hon Hbr HT0];
    intros Hreach HE HK Hhalt.
  -
    destruct Hnode as [Hcomp Hsound].
    assert (Hnh : m_halted (cfg_model c) = None).
    { exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)). }
    apply must_exit_in_at_cfg_running.
    + exact Hnh.
    + destruct (fo_progress _ _ _ _ (Hcomp i0)) as (evs' & st' & Hfo). eexists _, _. exact Hfo.
    + intros evs' Herr.
      destruct (Hsound evs' SError (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Herr)) as (i & _ & Habs).
      discriminate Habs.
    + intros evs' c' Hfo.
      destruct (Hsound evs' (SNext c') (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Hfo)) as (i & -> & Hc').
      injection Hc' as Ec. subst c'.
      apply (IH i).
      * eapply reach_fo_step; eassumption.
      * eapply exit_codes_in_branch; exact HE.
      * eapply kill_free_branch; exact HK.
      * intros code Hcode.
        pose proof (srealizes0_nonempty _ _ _ _ (Hcont i)) as H0.
        pose proof (node_evs_trace I evs T i H0) as Htr.
        destruct (sstep_cfg_into_halted _ _ _ _ _ Hfo Hcode) as [(Hk & evs0 & fs & Hevs) | (evs0 & sig & fs & Hevs)].
        { split; [| exact Hk]. apply (HE (evs i) Htr code fs). rewrite Hevs. apply in_app_iff. right. left. reflexivity. }
        { exfalso. pose proof (HK (evs i) Htr) as HF. rewrite Hevs in HF.
          apply Forall_app in HF as [_ HF]. inversion HF as [| x l Hx _]; subst. exact Hx. }
  -
    destruct (m_halted (cfg_model c)) as [code |] eqn:Hc; [| congruence].
    destruct (Hhalt code eq_refl) as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  -
    exfalso. rewrite BMON in Hmode. discriminate Hmode.
  -
    apply IH; [exact Hreach | eapply exit_codes_in_t_eq; [apply t_eq_sym; exact Heq | exact HE]
              | eapply kill_free_t_eq; [apply t_eq_sym; exact Heq | exact HK] | exact Hhalt].
  -
    exfalso. exact (NOREFUSE c Hreach Hbr).
Qed.
End Master.
End WithSegs.

Section Top.
Context {fx : PropExec.FPState} {bmK : BMode}.
Hypothesis BMON : bm_on = true.

Lemma noref_of_within_budget : forall segs pc ph sp brk0 mb rnd lim inp,
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  forall c, reach_fo segs (init_config segs pc ph sp brk0 mb rnd lim inp) c -> ~ budget_refused_at segs c.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp Hnb c (tr & Hstar) Hbr.
  apply Hnb. cbn [run_scfg_budget_refused]. exists tr, c. split; [exact Hstar | exact Hbr].
Qed.

Theorem srealizes_init_must_exit : forall scfgD segs pc ph sp brk0 mb rnd lim inp S T,
  srealizes0 segs scfgD (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  exit_codes_in S T -> kill_free T ->
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros scfgD segs pc ph sp brk0 mb rnd lim inp S T Hs HE HK Hnb.
  cbn [must_exit_in_scfg].
  eapply (srealizes_must_exit_fo segs scfgD BMON S _ (noref_of_within_budget _ _ _ _ _ _ _ _ _ Hnb)).
  - exact Hs.
  - apply reach_fo_refl.
  - exact HE.
  - exact HK.
  - intros code Hh. exfalso. unfold init_config in Hh. cbn [cfg_model] in Hh. rewrite m_halted_init_model in Hh. discriminate Hh.
Qed.
End Top.
