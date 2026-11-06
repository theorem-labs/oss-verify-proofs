(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib.Logic Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition ev_exits_in (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv c _ => In c S
  | KillEv _ _ => False
  | _ => True
  end.

Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (ev_exits_in S) tr.

Lemma exits_in_nil : forall S, exits_in S t_nil.
Proof. intros S tr ->. constructor. Qed.

Lemma exits_in_emit : forall S e T,
  Forall (ev_exits_in S) e -> exits_in S T -> exits_in S (t_emit e T).
Proof.
  intros S e T He HT tr [Hp | (tr' & -> & Htr')].
  - eapply is_prefix_Forall; eassumption.
  - apply Forall_app. split; [exact He | apply HT; exact Htr'].
Qed.

Lemma exits_in_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof.
  intros S code fs Hin. apply exits_in_emit; [| apply exits_in_nil].
  constructor; [exact Hin | constructor].
Qed.

Lemma Forall_exits_in_writes : forall S ch (l : list byte),
  Forall (ev_exits_in S) (map (WriteEv ch) l).
Proof. intros S ch l. induction l; cbn; constructor; [exact I | assumption]. Qed.

Lemma Forall_exits_in_reads : forall S ch (l : list byte),
  Forall (ev_exits_in S) (map (ReadEv ch) l).
Proof. intros S ch l. induction l; cbn; constructor; [exact I | assumption]. Qed.

Lemma exits_in_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, exits_in S (f i)) -> exits_in S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.

Lemma exits_in_alt2 : forall S A B,
  exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [H | H]; [apply HA | apply HB]; exact H. Qed.

Lemma exits_in_t_eq : forall S T T',
  t_eq T T' -> exits_in S T -> exits_in S T'.
Proof. intros S T T' Heq H tr Htr. apply H, Heq, Htr. Qed.

Lemma ev_exits_in_mono : forall S1 S2 e,
  (forall c, In c S1 -> In c S2) -> ev_exits_in S1 e -> ev_exits_in S2 e.
Proof. intros S1 S2 [| | |] Hsub H; cbn in *; auto. Qed.

Lemma exits_in_mono : forall S1 S2 T,
  (forall c, In c S1 -> In c S2) -> exits_in S1 T -> exits_in S2 T.
Proof.
  intros S1 S2 T Hsub H tr Htr.
  apply Forall_impl with (P := ev_exits_in S1); [| exact (H tr Htr)].
  intros e. apply ev_exits_in_mono. exact Hsub.
Qed.

(* [comment removed for export] *)
Lemma exits_only_exits_in : forall code S T,
  In code S -> exits_only code T -> exits_in S T.
Proof.
  intros code S T Hin H tr Htr.
  apply Forall_impl with (P := ev_exits_with code); [| exact (H tr Htr)].
  intros [| | |] He; cbn in *; auto. subst. exact Hin.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem realizes_cfg_must_exit_in : forall S c T,
  realizes_cfg cfg segs c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros S c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hrun Hex.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hrun.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
      inversion Heq2; subst c'. clear Heq2.
      assert (Hevs : Forall (ev_exits_in S) (evs i)).
      { apply Hex. exists i. left. apply is_prefix_refl. }
      destruct (m_halted (cfg_model (nx i))) as [code' |] eqn:Hh'.
      * destruct (sstep_cfg_next_halts_by_exit segs cfg c (evs i) (nx i) Hss)
          as [Hnone | [(evs0 & code1 & Hev & Hh1 & Hk1) | (evs0 & sig & Hev & Hk1)]].
        { rewrite Hh' in Hnone. discriminate Hnone. }
        { rewrite Hev in Hevs. apply Forall_app in Hevs as [_ Hlast].
          inversion Hlast as [| ? ? Hc _]; subst. cbn in Hc.
          eapply must_exit_in_at_cfg_halted; [exact Hh1 | exact Hc | exact Hk1]. }
        { exfalso. rewrite Hev in Hevs. apply Forall_app in Hevs as [_ Hlast].
          inversion Hlast as [| ? ? Hc _]; subst. exact Hc. }
      * apply (IH i Hh').
        intros tr Htr.
        assert (HF : Forall (ev_exits_in S) (evs i ++ tr)).
        { apply Hex. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        apply Forall_app in HF as [_ HF]. exact HF.
  - contradiction.
  - apply IH; [exact Hrun |]. eapply exits_in_t_eq; [apply t_eq_sym; exact Heq | exact Hex].
Qed.

End WithCfg.

(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
    as [Hex | Hno].
  - left. exact Hex.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity |].
    exfalso. apply Hno. exists eff', m', evs'. split; [exact Hspec | exact Hr].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof.
  intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic.
Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided].
  apply decided_from_classic.
Qed.

(* [comment removed for export] *)
Lemma must_exit_in_at_cfg_forced_only : forall cfg segs S c,
  must_exit_in_at_cfg cfg segs S c ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros cfg segs S c H.
  exact (must_exit_in_at_cfg_mono forced_only_cfg cfg segs S c
           (forced_only_cfg_least cfg) (decided_from_classic _ _ _) H).
Qed.

Lemma must_exit_in_scfg_forced_only : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  must_exit_in_scfg forced_only_cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp H.
  exact (must_exit_in_scfg_mono forced_only_cfg cfg S img lim en inp
           (forced_only_cfg_least cfg) (run_decided_classic _ _ _ _ _) H).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma realizes_cfg_must_exit_in_scfg : forall cfg S img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  exits_in S T ->
  must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S [segs pc ph] lim [sp brk0 mbase rnd] inp T H Hex.
  cbn [must_exit_in_scfg].
  exact (realizes_cfg_must_exit_in cfg segs S _ T H eq_refl Hex).
Qed.

(* [comment removed for export] *)
Lemma realizes_cfg_must_exit_in_forced_only : forall cfg S img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  exits_in S T ->
  must_exit_in_scfg forced_only_cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp T H Hex.
  apply (must_exit_in_scfg_forced_only cfg).
  eapply realizes_cfg_must_exit_in_scfg; eassumption.
Qed.

(* [comment removed for export] *)
Theorem halts_of_realizes_cfg :
  forall (cfg : SpuriousCfg) (lim : Z) (S : list word) (img : Image),
  (forall en inp,
     valid_entry img en inp ->
     valid_input inp ->
     source_within_budget_scfg forced_only_cfg lim img en inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T
       /\ exits_in S T) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S img.
Proof.
  intros cfg lim S img H en inp Hen Hinp Hb.
  destruct (H en inp Hen Hinp Hb) as (T & HR & Hex).
  eapply realizes_cfg_must_exit_in_forced_only; eassumption.
Qed.

Corollary halts_of_realizes_cfg_nopremise :
  forall (cfg : SpuriousCfg) (lim : Z) (S : list word) (img : Image),
  (forall en inp,
     valid_entry img en inp ->
     valid_input inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T
       /\ exits_in S T) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S img.
Proof.
  intros cfg lim S img H. apply (halts_of_realizes_cfg cfg).
  intros en inp Hen Hinp _. exact (H en inp Hen Hinp).
Qed.
