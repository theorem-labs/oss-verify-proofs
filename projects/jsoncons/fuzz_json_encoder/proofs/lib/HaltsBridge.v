(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim VmLimitFrame SpinAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable S : list word.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition codes_ok (T : TSet) : Prop :=
  forall tr code fs, T tr -> In (ExitEv code fs) tr -> In code S.

(* [comment removed for export] *)
Definition nokill (T : TSet) : Prop :=
  forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.

(* [comment removed for export] *)
Definition halt_ok (c : config) : Prop :=
  m_halted (cfg_model c) = None \/
  (exists code, m_halted (cfg_model c) = Some code /\ In code S /\ m_killed (cfg_model c) = None).

Lemma codes_ok_eq : forall T T', t_eq T T' -> codes_ok T' -> codes_ok T.
Proof. intros T T' Heq H tr code fs Htr Hin. apply (H tr code fs); [apply (proj1 (Heq tr)); exact Htr | exact Hin]. Qed.

Lemma nokill_eq : forall T T', t_eq T T' -> nokill T' -> nokill T.
Proof. intros T T' Heq H tr sig fs Htr. apply (H tr sig fs). apply (proj1 (Heq tr)). exact Htr. Qed.

Lemma t_alt_emit_member : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i tr,
  T i tr -> t_alt (fun j => t_emit (evs j) (T j)) (evs i ++ tr).
Proof. intros I evs T i tr H. exists i. right. exists tr. split; [reflexivity | exact H]. Qed.

Lemma codes_ok_child : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  codes_ok (t_alt (fun j => t_emit (evs j) (T j))) -> codes_ok (T i).
Proof.
  intros I evs T i H tr code fs Htr Hin. apply (H (evs i ++ tr) code fs).
  - apply t_alt_emit_member. exact Htr.
  - apply in_app_iff. right. exact Hin.
Qed.

Lemma nokill_child : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  nokill (t_alt (fun j => t_emit (evs j) (T j))) -> nokill (T i).
Proof.
  intros I evs T i H tr sig fs Htr Hin. apply (H (evs i ++ tr) sig fs).
  - apply t_alt_emit_member. exact Htr.
  - apply in_app_iff. right. exact Hin.
Qed.

(* [comment removed for export] *)
Theorem srealizes_must_exit : forall c T,
  srealizes segs scfg c T ->
  Safe segs scfg c ->
  ~ spin_site_present segs ->
  halt_ok c -> codes_ok T -> nokill T ->
  must_exit_in_at_cfg scfg segs S c.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                 | c Hsite Hspin Hh | c T T' H IH Heq | c T Hbr Hlt HT0];
    intros Hsafe Hns Hhalt Hcodes Hnk.
  - (* [comment removed for export] *)
    destruct Hnode as [Hsteps Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hsteps i0)).
    + exists (evs i0), (SNext (nx i0)). exact (Hsteps i0).
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss. destruct (Hsound e (SNext c') Hss) as (i & He & Heq).
      injection Heq as Hc'. subst c' e.
      assert (HTi : t_alt (fun j => t_emit (evs j) (T j)) (evs i)).
      { rewrite <- (app_nil_r (evs i)). apply t_alt_emit_member. exact (srealizes_nonempty _ _ _ _ (Hcont i)). }
      apply IH.
      * exact (Safe_step _ _ _ _ _ Hsafe (Hsteps i)).
      * exact Hns.
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ (Hsteps i))
          as [Hn | [(evs0 & code & He & Hc & Hk) | (evs0 & sig & He & Hk)]].
        -- left. exact Hn.
        -- right. exists code. split; [exact Hc | split; [| exact Hk]].
           apply (Hcodes (evs i) code (m_fs (cfg_model (nx i))) HTi).
           rewrite He. apply in_app_iff. right. left. reflexivity.
        -- exfalso. apply (Hnk (evs i) sig (m_fs (cfg_model (nx i))) HTi).
           rewrite He. apply in_app_iff. right. left. reflexivity.
      * exact (codes_ok_child I evs T i Hcodes).
      * exact (nokill_child I evs T i Hnk).
  - (* [comment removed for export] *)
    destruct Hhalt as [Hn | (code & Hc & Hin & Hk)]; [congruence |].
    exact (must_exit_in_at_cfg_halted _ _ _ _ code Hc Hin Hk).
  - (* [comment removed for export] *)
    exfalso. exact (Hns Hsite).
  - (* [comment removed for export] *)
    apply IH; [exact Hsafe | exact Hns | exact Hhalt | exact (codes_ok_eq _ _ Heq Hcodes) | exact (nokill_eq _ _ Heq Hnk)].
  - (* [comment removed for export] *)
    exfalso. exact (Safe_not_refused _ _ _ Hsafe Hbr Hlt).
Qed.

(* [comment removed for export] *)
Theorem srealizes_must_exit_down : forall cfg1 c T,
  cfg_le cfg1 scfg ->
  srealizes segs scfg c T ->
  decided_from cfg1 segs c ->
  Safe segs cfg1 c ->
  ~ spin_site_present segs ->
  halt_ok c -> codes_ok T -> nokill T ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 c T Hle H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                 | c Hsite Hspin Hh | c T T' H IH Heq | c T Hbr Hlt HT0];
    intros Hdec Hsafe Hns Hhalt Hcodes Hnk.
  - destruct Hnode as [Hsteps Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hsteps i0)).
    + destruct c as [ms model].
      apply (sstep_cfg_progress segs cfg1 ms model (evs i0) (SNext (nx i0))).
      * intros x8 Hsvc. exact (Hdec [] (mkCfg ms model) x8 (star_refl _ _) Hsvc).
      * exact (sstep_cfg_sub _ _ _ _ _ (Hsteps i0)).
    + intros e Herr. destruct (Hsound e SError (sstep_cfg_mono _ _ _ _ _ _ Hle Herr)) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss1. pose proof (sstep_cfg_mono _ _ _ _ _ _ Hle Hss1) as Hss.
      destruct (Hsound e (SNext c') Hss) as (i & He & Heq).
      injection Heq as Hc'. subst c' e.
      assert (HTi : t_alt (fun j => t_emit (evs j) (T j)) (evs i)).
      { rewrite <- (app_nil_r (evs i)). apply t_alt_emit_member. exact (srealizes_nonempty _ _ _ _ (Hcont i)). }
      apply IH.
      * exact (decided_from_step _ _ _ _ _ _ Hdec Hss1).
      * exact (Safe_step _ _ _ _ _ Hsafe Hss1).
      * exact Hns.
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ (Hsteps i))
          as [Hn | [(evs0 & code & He & Hc & Hk) | (evs0 & sig & He & Hk)]].
        -- left. exact Hn.
        -- right. exists code. split; [exact Hc | split; [| exact Hk]].
           apply (Hcodes (evs i) code (m_fs (cfg_model (nx i))) HTi).
           rewrite He. apply in_app_iff. right. left. reflexivity.
        -- exfalso. apply (Hnk (evs i) sig (m_fs (cfg_model (nx i))) HTi).
           rewrite He. apply in_app_iff. right. left. reflexivity.
      * exact (codes_ok_child I evs T i Hcodes).
      * exact (nokill_child I evs T i Hnk).
  - destruct Hhalt as [Hn | (code & Hc & Hin & Hk)]; [congruence |].
    exact (must_exit_in_at_cfg_halted _ _ _ _ code Hc Hin Hk).
  - exfalso. exact (Hns Hsite).
  - apply IH; [exact Hdec | exact Hsafe | exact Hns | exact Hhalt | exact (codes_ok_eq _ _ Heq Hcodes) | exact (nokill_eq _ _ Heq Hnk)].
  - exfalso. exact (Safe_not_refused _ _ _ Hsafe Hbr Hlt).
Qed.

Theorem srealizes_must_exit_init_down : forall cfg1 pc ph sp brk0 mbase rnd lim inp T,
  cfg_le cfg1 scfg ->
  srealizes segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
  decided_from cfg1 segs (init_config segs pc ph sp brk0 mbase rnd lim inp) ->
  Safe segs cfg1 (init_config segs pc ph sp brk0 mbase rnd lim inp) ->
  ~ spin_site_present segs ->
  codes_ok T -> nokill T ->
  must_exit_in_scfg cfg1 S (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp.
Proof.
  intros cfg1 pc ph sp brk0 mbase rnd lim inp T Hle Hsr Hdec Hsafe Hns Hc Hk.
  cbn [must_exit_in_scfg].
  apply (srealizes_must_exit_down cfg1 _ T Hle Hsr Hdec Hsafe Hns); [| exact Hc | exact Hk].
  left. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem srealizes_must_exit_init : forall pc ph sp brk0 mbase rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
  Safe segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp) ->
  ~ spin_site_present segs ->
  codes_ok T -> nokill T ->
  must_exit_in_scfg scfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp.
Proof.
  intros pc ph sp brk0 mbase rnd lim inp T Hsr Hsafe Hns Hc Hk.
  cbn [must_exit_in_scfg].
  apply (srealizes_must_exit _ T Hsr Hsafe Hns); [| exact Hc | exact Hk].
  left. reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hs.
    destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
    exfalso. apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided]. apply decided_from_classic. Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_down : forall cfg1 cfg2 S img lim en inp,
  cfg_le cfg1 cfg2 ->
  must_exit_in_scfg cfg2 S img lim en inp ->
  must_exit_in_scfg cfg1 S img lim en inp.
Proof.
  intros cfg1 cfg2 S img lim en inp Hle H.
  exact (must_exit_in_scfg_mono _ _ _ _ _ _ _ Hle (run_decided_classic cfg1 img lim en inp) H).
Qed.

Lemma must_exit_in_scfg_forced_only : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  must_exit_in_scfg forced_only_cfg S img lim en inp.
Proof. intros cfg S img lim en inp H. exact (must_exit_in_scfg_down _ _ _ _ _ _ _ (forced_only_cfg_least cfg) H). Qed.

(* [comment removed for export] *)
Lemma halts_allowed_of_must_exit : forall cfg lim S img,
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in_scfg cfg S img lim en inp) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S img.
Proof.
  intros cfg lim S img H en inp Hen Hinp _.
  exact (must_exit_in_scfg_forced_only cfg S img lim en inp (H en inp Hen Hinp)).
Qed.

(* [comment removed for export] *)
Lemma halts_allowed_of_must_exit_wb : forall cfg lim S img,
  cfg_le forced_only_cfg cfg ->
  (forall en inp, valid_entry img en inp -> valid_input inp ->
                 source_within_budget_scfg forced_only_cfg lim img en inp ->
                 must_exit_in_scfg cfg S img lim en inp) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S img.
Proof.
  intros cfg lim S img _ H en inp Hen Hinp Hwb.
  exact (must_exit_in_scfg_forced_only cfg S img lim en inp (H en inp Hen Hinp Hwb)).
Qed.
