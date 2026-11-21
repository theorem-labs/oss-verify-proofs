(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimTransfer.v at commit theorem-labs/oss-verify-proofs@c5665593c2d8, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim and nothing else. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the step lemma sstep_fit covers the vDSO call arm of sstep, the transfer lim_transfer_scfg runs over run_segments, with this file's own comments on these changes, and the cited source commit is named by its public id. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs RiscvSemantics MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim Require Import LimBase LimMm LimSpec LimMove LimFit LimRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma down216_fit : forall L i m,
  vm_fit (m_vmmaps m) -> (L <= mlim m)%Z -> bv_unsigned (in_sysno i) = 216%Z -> down216 L i m.
Proof.
  intros L i m Hf HL E R (eff & m' & evs & Hs & Hnr).
  rewrite (mark_216 _ _ E) in R.
  apply (syscall_spec_216 _ _ _ E) in Hs.
  destruct (mremap_at_down L i m _ _ _ _ Hf HL R _ Hs) as [Ha _]. cbn [omap] in Ha.
  exists eff, (setL L m'), evs. split; [apply (syscall_spec_216 _ _ _ E); exact Ha | exact Hnr].
Qed.

(* [comment removed for export] *)
Theorem syscall_spec_down_fit : forall L i m o,
  vm_fit (m_vmmaps m) -> (L <= mlim m)%Z -> alloc_budget_refused_b i (setL L m) = false ->
  syscall_spec i m o -> syscall_spec i (setL L m) (omap L o) /\ opres m o.
Proof.
  intros L i m o Hf HL R Ho.
  destruct (Z.eq_dec (bv_unsigned (in_sysno i)) 216) as [E|E].
  - rewrite (mark_216 _ _ E) in R. apply (syscall_spec_216 _ _ _ E) in Ho.
    destruct (mremap_at_down L i m _ _ _ _ Hf HL R _ Ho) as [Ha Hb].
    split; [apply (syscall_spec_216 _ _ _ E); exact Ha | exact Hb].
  - exact (syscall_spec_down L i m o HL R E Ho).
Qed.

Definition cfg_fit (c : config) : Prop := vm_fit (m_vmmaps (cfg_model c)).

Lemma sstep_fit : forall segs c evs c', cfg_fit c -> sstep segs c evs (SNext c') -> cfg_fit c'.
Proof.
  intros segs c evs c' Hf Hss. unfold cfg_fit in *.
  (* [sstep] ([c0dd863a:theories/LinuxProcessSem/Run.v:686]) has 11 constructors, with the
     three vDSO arms at slots 4-6 (instr, instr_fault, instr_unmodeled, vdso_call,
     vdso_materialization_fault, vdso_unmodeled, syscall, syscall_materialization_fault,
     exit, killed, syscall_unmodeled).  The two SError vdso arms cannot unify
     with this lemma's [SNext c'] index and discharge themselves; [vdso_call] concludes
     [SNext] and is the one goal they add.  Binders spelled as the sites in
     [Asan/SpinAlgCfg.v:384/:438/:490] spell them. *)
  inversion Hss as
    [ ms0 m0 ms1 m1 Hh Hsvc Hacc
    | | | ms0 m0 fn n eff m1 m2 evs0 Hh Hsvc Hacc1 Hfn Hn Hs Hef Hh1 Hmat
    | | | ms0 m0 x8 eff m1 m2 evs0 Hh Hsvc Hs Hh1 Hmat
    | | ms0 m0 x8 eff m1 evs0 code Hh Hsvc Hs Hh1 Hk1
    | ms0 m0 x8 eff m1 evs0 sig Hh Hsvc Hs Hk1 | ]; subst; cbn [cfg_model] in *.
  - destruct (mi_account_step_model_frame segs ms0 m0 ms1 m1 Hacc) as (_ & Hv & _). rewrite Hv. exact Hf.
  - (* vdso_call: the model it leaves is [with_vdso_bump m2], and the vDSO setters rebuild the
       vDSO view and nothing else ([State.m_vmmaps_with_vdso_bump] at [75d69e00:theories/LinuxProcessSem/State.v:5048],
       proved by [reflexivity]), so this closes exactly as the syscall arm below does. *)
    rewrite ?m_vmmaps_with_vdso_bump.
    exact (materialize_fit m1 _ m2 (syscall_spec_fit _ _ _ _ _ Hf Hs) Hmat).
  - exact (materialize_fit m1 _ m2 (syscall_spec_fit _ _ _ _ _ Hf Hs) Hmat).
  - exact (syscall_spec_fit _ _ _ _ _ Hf Hs).
  - exact (syscall_spec_fit _ _ _ _ _ Hf Hs).
Qed.

Lemma init_config_fit : forall segs pc ph sp brk0 mbase rnd lim inp,
  cfg_fit (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof. intros. unfold cfg_fit, init_config. cbn [cfg_model]. apply init_model_fit. Qed.

(* [comment removed for export] *)
Theorem lim_transfer_fit : forall cfg segs S L c,
  cfg_fit c -> (L <= mlim (cfg_model c))%Z ->
  must_exit_in_at_cfg cfg segs S c ->
  ~ reaches_budget_refused_cfg segs cfg (cfgL L c) ->
  must_exit_in_at_cfg cfg segs S (cfgL L c).
Proof.
  intros cfg segs S L c Hf HL Hbig Hnr.
  apply (lim_transfer_at segs cfg S L cfg_fit).
  - intros c1 evs c2 H1 Hss. exact (sstep_fit segs c1 evs c2 H1 (sstep_cfg_sub segs cfg _ _ _ Hss)).
  - intros ms m x8 H1 _ _ E HL1. apply down216_fit; [exact H1 | exact HL1 | exact E].
  - exact Hbig.
  - exact Hf.
  - exact HL.
  - exact Hnr.
Qed.

(* [comment removed for export] *)
Theorem lim_transfer_init : forall cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big,
  (lim_small <= lim_big)%Z ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_big inp) ->
  ~ reaches_budget_refused_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_small inp) ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_small inp).
Proof.
  intros cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle Hbig Hnr.
  rewrite <- (init_config_cfgL segs pc ph sp brk0 mbase rnd lim_big lim_small inp).
  apply lim_transfer_fit.
  - apply init_config_fit.
  - rewrite init_config_mlim. exact Hle.
  - exact Hbig.
  - rewrite init_config_cfgL. exact Hnr.
Qed.

(* [comment removed for export] *)
Corollary lim_transfer_scfg : forall cfg S img en inp lim_small lim_big,
  (lim_small <= lim_big)%Z ->
  must_exit_in_scfg cfg S img lim_big en inp ->
  ~ run_scfg_budget_refused cfg img lim_small en inp ->
  must_exit_in_scfg cfg S img lim_small en inp.
Proof.
  intros cfg S [segs pc ph] [sp brk0 mbase rnd] inp lim_small lim_big Hle Hbig Hnr.
  cbn [must_exit_in_scfg run_scfg_budget_refused] in *.
  (* LPS 727298f3: the run's segments are [run_segments segs inp sp mbase]. *)
  exact (lim_transfer_init cfg (run_segments segs inp sp mbase) S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle Hbig Hnr).
Qed.
