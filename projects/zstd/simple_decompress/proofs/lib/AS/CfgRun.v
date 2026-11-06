From Stdlib Require Import List Lia Bool ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Export Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Lemma errno_ret_in_eq : forall es r, errno_ret_in es r = ret_in_errnos es r.
Proof.
  intros es r.
  unfold errno_ret_in, ret_in_errnos.
  exact eq_refl.
Qed.

Lemma spec_step_ok_refuted : forall i model eff m' ev effg mg evg,
  injected_family_off ACFG i = true ->
  syscall_spec i model (Ok effg mg evg) ->
  refusal_b i model (eff_ret effg) = false ->
  refusal_b i model (eff_ret eff) = true ->
  m_halted m' = None ->
  ~ spec_step_ok i model (Ok eff m' ev).
Proof.
  intros i model eff m' ev effg mg evg Hoff Hsg Hnr Hr Hh'.
  cbv [spec_step_ok].
  intro Hk. specialize (Hk Hh').
  apply Hk. unfold spurious_refusal_cfg.
  refine (conj Hoff (conj Hr _)).
  now exists effg, mg, evg.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs ACFG c e st -> m_halted (cfg_model c) = None.
Proof.
  intros c e st Hss.
  destruct Hss; match goal with h : m_halted _ = None |- _ => exact h end.
Qed.

Lemma star_cfg_one : forall c e c',
  sstep_cfg segs ACFG c e (SNext c') -> star_cfg segs ACFG c e c'.
Proof.
  intros c e c' Hss.
  pose proof (@star_cfg_step segs ACFG c e c' [] c' Hss (@star_cfg_refl segs ACFG c')) as K.
  rewrite app_nil_r in K. exact K.
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs ACFG c1 t1 c2 -> star_cfg segs ACFG c2 t2 c3 -> star_cfg segs ACFG c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 Hfirst.
  revert t2 c3.
  elim Hfirst.
  - intros c t2 c3 Hk. exact Hk.
  - intros a ev b tr d Hab _ Hrec t2 c3 Hk.
    rewrite <- app_assoc.
    apply (@star_cfg_step segs ACFG a ev b (tr ++ t2) c3 Hab).
    apply Hrec. exact Hk.
Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs ACFG c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hs.
  revert Hh.
  destruct Hs as [x | x ev y tr0 z Hxy Hyz]; intro Hh.
  - auto.
  - destruct (Hh (sstep_cfg_halted_none _ _ _ Hxy)).
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs ACFG c [].
Proof.
  intro c. hnf.
  refine (ex_intro _ nil (ex_intro _ c (conj (@star_cfg_refl segs ACFG c) I))).
Qed.

Lemma obs_trace_cfg_prefix_closed : forall c0 tr tr',
  obs_trace_cfg segs ACFG c0 tr -> is_prefix tr' tr -> obs_trace_cfg segs ACFG c0 tr'.
Proof.
  intros c0 tr tr' Hobs Hpre.
  destruct Hobs as [full Hrest]. destruct Hrest as [c [Hst Hfp]].
  exists full. exists c. split.
  - assumption.
  - apply (is_prefix_trans tr' tr full Hpre Hfp).
Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs ACFG c tr c' -> Inv c'.
Proof.
  intros c tr c' HI Hs.
  revert HI.
  elim Hs.
  - intros x Hx. exact Hx.
  - intros x ev y tr0 z Hxy _ Hrec Hx. apply Hrec. exact (Hstep x ev y Hx Hxy).
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs ACFG c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c HI Hre.
  destruct Hre as [tr [c' [evs [Hst Herr]]]].
  apply (Hnoerr c' evs).
  - exact (star_cfg_inv Inv Hstep c tr c' HI Hst).
  - exact Herr.
Qed.

End WithSegs.

Lemma no_error_modeled_scfg :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error_cfg segs ACFG (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run_scfg ACFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros * Hne Hu.
  apply Hne.
  exact (reaches_unmodeled_cfg_reaches_error_cfg segs ACFG
           (init_config segs pc ph sp brk0 mb rnd lim inp) Hu).
Qed.

Lemma no_error_error_free_scfg :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error_cfg segs ACFG (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.error_free (run_scfg ACFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros * Hne.
  hnf. cbv [run_scfg bh_errors].
  exact Hne.
Qed.
