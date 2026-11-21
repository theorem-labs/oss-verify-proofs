(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimTransfer.v at commit theorem-labs/oss-verify-proofs@f92feaf8b7e6, with its module paths changed to libpcap/fuzz_pcap. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 by taking openssl/bndiv's ported copy of Lib/LimTransfer.v whole, with its module paths changed to libpcap/fuzz_pcap: sstep_fit covers the vDSO-call arm, and lim_transfer_scfg reads the run over run_segments; internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs RiscvSemantics MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require Import LimBase LimMm LimSpec LimMove LimFit LimRun.
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
  (* [sstep] carries eleven constructors at 75d69e00
     (theories/LinuxProcessSem/Run.v:645, vDSO arms at :683, :699, :714).
     Only the five that conclude [SNext] leave a goal: instr (slot 1),
     vdso_call (slot 4), syscall (slot 7), exit (slot 9), killed (slot 10). *)
  inversion Hss as
    [ ms0 m0 ms1 m1 Hh Hsvc Hacc
    |
    |
    | ms0 m0 fn n eff m1 m2 evs0 Hh Hsvc Hacc Hvf Hsn Hs Hef Hh1 Hmat
    |
    |
    | ms0 m0 x8 eff m1 m2 evs0 Hh Hsvc Hs Hh1 Hmat
    |
    | ms0 m0 x8 eff m1 evs0 code Hh Hsvc Hs Hh1 Hk1
    | ms0 m0 x8 eff m1 evs0 sig Hh Hsvc Hs Hk1
    | ]; subst; cbn [cfg_model] in *.
  - destruct (mi_account_step_model_frame segs ms0 m0 ms1 m1 Hacc) as (_ & Hv & _). rewrite Hv. exact Hf.
  - (* vDSO call.  The successor's model is [with_vdso_bump] of the
       materialized model, and [State.with_vdso] rebuilds the VM subsystem
       keeping [m_vmmaps] (State.v:5031-5036 at 75d69e00), so the frame fact
       [m_vmmaps_with_vdso_bump] (State.v:5048) holds BY REFLEXIVITY, so the
       syscall arm's own term is already of the goal's type up to conversion.
       Deliberately NOT a [rewrite]: [rewrite] matches SYNTACTICALLY and would
       fail the moment the goal reached [m_vmmaps] through a fold or a flag
       specialisation, while [exact] works up to conversion (rule 11c).  Do not
       "tidy" a rewrite back in here. *)
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
  (* LPS 727298f3: [must_exit_in_scfg] and [run_scfg_budget_refused] read the run
     against [run_segments segs inp sp mbase] (the binary's segments and the vDSO pair),
     and [lim_transfer_init] holds for any segment list. *)
  exact (lim_transfer_init cfg (run_segments segs inp sp mbase) S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle Hbig Hnr).
Qed.
