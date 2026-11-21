(** * Lib.RegsEquivFO — register-map equivalence over the filtered step relation

    [Lib.RegsEquiv] shows that two machine states with extensionally equal register maps take the same
    [Run.sstep] steps.  The filtered relation [Run.sstep_cfg cfg] adds one premise to the syscall
    steps, the outcome not being a spurious refusal of [sys_input segs ms x8]; [RegsEquiv.sys_input_eqv]
    says that input is the same for equivalent states, so the same transfer holds, here for every
    configuration.  Ends in [must_exit_in_at_cfg_init_ms], the filtered twin of
    [HaltsEqv.must_exit_in_at_init_ms], and the behaviour transfer [init_behaviour_eqv_cfg]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Lib Require Import PropExec MState RegsEquiv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_eqv_fo : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc0 & Hsvc & _ & _ & _ & _).
  pose proof (sys_input_eqv segs) as Hsi.
  inversion Hst; subst.
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|].
    split; [exact Hres| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; unfold ms_pc in *; congruence| exact I].
  - (* the three vDSO arms of sstep_cfg (Run.v l.2248-2284), no filter premise *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + apply (sstep_cfg_vdso_call segs cfg ms' mo fn n eff model' model'' evs);
        [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
        | rewrite <- (Hsi ms ms' _ Heqv); assumption| assumption| assumption| assumption].
    + split; [apply vd_post_eqv; exact Heqv| reflexivity].  (* this lineage's RegsEquiv names it vd_post_eqv *)
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_cfg_vdso_materialization_fault segs cfg ms' mo fn n eff model' evs0);
      [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
      | rewrite <- (Hsi ms ms' _ Heqv); assumption| assumption| assumption| assumption].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_cfg_vdso_unmodeled segs cfg ms' mo fn); [assumption| congruence| exact E| unfold ms_pc in *; congruence|].
    match goal with Hu : vdso_call_unmodeled _ ms mo fn |- _ =>
      destruct Hu as [Hu0 | [(n0 & Hn & Hs) | (n0 & eff0 & mo0 & evs1 & Hn & Hs & Hr)]] end;
      [left; exact Hu0
      | right; left; exists n0; rewrite <- (Hsi ms ms' _ Heqv); split; assumption
      | right; right; exists n0, eff0, mo0, evs1; rewrite <- (Hsi ms ms' _ Heqv); repeat split; assumption].
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (Hsi ms ms' x8 Heqv); assumption
        | rewrite <- (Hsi ms ms' x8 Heqv); assumption | assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (Hsi ms ms' x8 Heqv); assumption
      | rewrite <- (Hsi ms ms' x8 Heqv); assumption | assumption| assumption].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (Hsi ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs cfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (Hsi ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x8);
      [assumption| congruence| rewrite <- (Hsi ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv_fo : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv_fo ms ms'); assumption.
Qed.

Lemma star_eqv_fo : forall c tr c1, star_cfg segs cfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs cfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstep_cfg_eqv_fo c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

Lemma obs_trace_eqv_fo : forall c c' tr, cfg_eqv c c' ->
  obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv_fo c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_eqv_fo : forall c c', cfg_eqv c c' ->
  reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Herr).
  destruct (star_eqv_fo c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv_fo c1 c1' evs SError H1 Herr) as (X' & Hst' & HX).
  destruct X' as [c2'|]; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

Lemma reaches_unmodeled_eqv_fo : forall c c', cfg_eqv c c' ->
  reaches_unmodeled_cfg segs cfg c -> reaches_unmodeled_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hu).
  destruct (star_eqv_fo c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| exact (unmodeled_at_eqv segs c1 c1' H1 Hu)].
Qed.

Lemma all_traces_error_eqv_fo : forall c, all_traces_error_cfg segs cfg c ->
  forall c', cfg_eqv c c' -> all_traces_error_cfg segs cfg c'.
Proof.
  intros c H. induction H as [c Hprog Hnext IH]; intros c' Heqv.
  constructor.
  - destruct Hprog as (evs & to & Hst).
    destruct (sstep_cfg_eqv_fo c c' evs to Heqv Hst) as (X' & Hst' & _). eauto.
  - intros evs c2' Hst'.
    destruct (sstep_cfg_eqv_fo c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
    destruct X as [c2|]; simpl in HX; [|contradiction].
    apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

Theorem behaviour_eqv_fo : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> obs_trace_cfg segs cfg (mkCfg ms' mo) tr) /\
  (reaches_error_cfg segs cfg (mkCfg ms mo) <-> reaches_error_cfg segs cfg (mkCfg ms' mo)) /\
  (all_traces_error_cfg segs cfg (mkCfg ms mo) <-> all_traces_error_cfg segs cfg (mkCfg ms' mo)) /\
  (reaches_unmodeled_cfg segs cfg (mkCfg ms mo) <-> reaches_unmodeled_cfg segs cfg (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [| split; [| split]]; [intros tr|..]; split; intros H.
  - exact (obs_trace_eqv_fo _ _ tr H1 H).
  - exact (obs_trace_eqv_fo _ _ tr H2 H).
  - exact (reaches_error_eqv_fo _ _ H1 H).
  - exact (reaches_error_eqv_fo _ _ H2 H).
  - exact (all_traces_error_eqv_fo _ H _ H1).
  - exact (all_traces_error_eqv_fo _ H _ H2).
  - exact (reaches_unmodeled_eqv_fo _ _ H1 H).
  - exact (reaches_unmodeled_eqv_fo _ _ H2 H).
Qed.

(* the launch arguments of (pc ph sp mbase draw inp), as in RegsEquiv. *)
Theorem init_behaviour_eqv_cfg : forall pc ph sp mbase draw inp mo,
  let c0 := mkCfg (init_machine_state segs pc ph sp mbase draw inp) mo in
  let c0' := mkCfg (init_ms segs pc ph sp mbase draw inp) mo in
  (forall tr, obs_trace_cfg segs cfg c0 tr <-> obs_trace_cfg segs cfg c0' tr) /\
  (reaches_error_cfg segs cfg c0 <-> reaches_error_cfg segs cfg c0') /\
  (all_traces_error_cfg segs cfg c0 <-> all_traces_error_cfg segs cfg c0') /\
  (reaches_unmodeled_cfg segs cfg c0 <-> reaches_unmodeled_cfg segs cfg c0').
Proof. intros. apply behaviour_eqv_fo. apply init_machine_state_eqv. Qed.

Lemma must_exit_in_at_cfg_eqv : forall S c, must_exit_in_at_cfg cfg segs S c ->
  forall c', cfg_eqv c c' -> must_exit_in_at_cfg cfg segs S c'.
Proof.
  intros S c H. induction H as [c code Hh Hin Hk | c Hh Hprog Hnoerr Hnext IH]; intros c' Heqv.
  - pose proof Heqv as [_ Hmo].
    apply (must_exit_in_at_cfg_halted cfg segs S c' code); [rewrite <- Hmo; exact Hh | exact Hin | rewrite <- Hmo; exact Hk].
  - pose proof Heqv as [_ Hmo].
    apply must_exit_in_at_cfg_running.
    + rewrite <- Hmo. exact Hh.
    + destruct Hprog as (evs & st & Hst).
      destruct (sstep_cfg_eqv_fo c c' evs st Heqv Hst) as (X' & Hst' & _). exists evs, X'. exact Hst'.
    + intros evs Herr'.
      destruct (sstep_cfg_eqv_fo c' c evs SError (cfg_eqv_sym _ _ Heqv) Herr') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [contradiction|]. exact (Hnoerr evs Hst).
    + intros evs c2' Hst'.
      destruct (sstep_cfg_eqv_fo c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [|contradiction].
      apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

Lemma must_exit_in_at_cfg_init_ms : forall S pc ph sp mbase draw inp mo,
  must_exit_in_at_cfg cfg segs S (mkCfg (init_ms segs pc ph sp mbase draw inp) mo) ->
  must_exit_in_at_cfg cfg segs S (mkCfg (init_machine_state segs pc ph sp mbase draw inp) mo).
Proof.
  intros S pc ph sp mbase draw inp mo H.
  apply (must_exit_in_at_cfg_eqv S _ H). split; [| reflexivity].
  apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.

End WithSegs.
