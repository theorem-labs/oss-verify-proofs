(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List ZArith Lia Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import Monad Specs
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ev_good (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv code _ => In code S
  | KillEv _ _ => False
  | _ => True
  end.

Definition trace_good (S : list word) (tr : list event) : Prop :=
  forall e, In e tr -> ev_good S e.

Definition shape_good (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> trace_good S tr.

Lemma trace_good_app_l : forall S a b, trace_good S (a ++ b) -> trace_good S a.
Proof. intros S a b H e He. apply H. apply in_app_iff. left; exact He. Qed.

Lemma trace_good_app_r : forall S a b, trace_good S (a ++ b) -> trace_good S b.
Proof. intros S a b H e He. apply H. apply in_app_iff. right; exact He. Qed.

Lemma shape_good_eq : forall S T T', t_eq T T' -> shape_good S T -> shape_good S T'.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.

Lemma shape_good_emit_inv : forall S evs T,
  T [] -> shape_good S (t_emit evs T) -> trace_good S evs /\ shape_good S T.
Proof.
  intros S evs T Hne H. split.
  - apply (trace_good_app_l S evs []). apply H. right. exists []. split; [reflexivity | exact Hne].
  - intros tr Htr. apply (trace_good_app_r S evs tr). apply H. right. exists tr. split; [reflexivity | exact Htr].
Qed.

Lemma shape_good_alt_inv : forall S (I : Type) (f : I -> TSet) i,
  shape_good S (t_alt f) -> shape_good S (f i).
Proof. intros S I f i H tr Htr. apply H. exists i. exact Htr. Qed.

(* [comment removed for export] *)
Lemma shape_good_nil : forall S, shape_good S t_nil.
Proof. intros S tr Htr e He. unfold t_nil in Htr. subst tr. destruct He. Qed.

Lemma is_prefix_In' : forall (l1 l2 : list event) e, is_prefix l1 l2 -> In e l1 -> In e l2.
Proof.
  intros l1 l2 e Hp. revert l2 Hp. induction l1 as [|x l1 IH]; intros l2 Hp Hin; [destruct Hin|].
  destruct l2 as [|y l2]; [inversion Hp|]. inversion Hp; subst.
  destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; eauto].
Qed.

Lemma shape_good_emit : forall S evs T,
  trace_good S evs -> shape_good S T -> shape_good S (t_emit evs T).
Proof.
  intros S evs T He HT tr [Hp | (tr' & -> & Htr')] e Hin.
  - apply He. eapply is_prefix_In'; eauto.
  - apply in_app_iff in Hin as [Hin|Hin]; [apply He; exact Hin | exact (HT tr' Htr' e Hin)].
Qed.

Lemma shape_good_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, shape_good S (f i)) -> shape_good S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.

Lemma shape_good_alt2 : forall S A B, shape_good S A -> shape_good S B -> shape_good S (t_alt2 A B).
Proof. intros S A B HA HB tr [H|H]; [exact (HA tr H) | exact (HB tr H)]. Qed.

Lemma shape_good_exit : forall S code fs, In code S -> shape_good S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply shape_good_emit; [|apply shape_good_nil].
  intros e [<-|[]]. exact Hin.
Qed.

Lemma trace_good_writes : forall S ch (s : list byte), trace_good S (map (WriteEv ch) s).
Proof.
  intros S ch s e Hin. apply in_map_iff in Hin as (b & <- & _). exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma sstep_cfg_cases : forall cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_halted (cfg_model c') = None
  \/ (exists code evs0 fs, m_halted (cfg_model c') = Some code /\ m_killed (cfg_model c') = None
                          /\ evs = evs0 ++ [ExitEv code fs])
  \/ (exists sig evs0 fs, evs = evs0 ++ [KillEv sig fs]).
Proof.
  intros cfg c evs c' H. inversion H; subst; cbn [cfg_model].
  - left.
    match goal with
    | [ K : mi_account_step _ _ _ = MachineOk _, K0 : m_halted ?mo = None |- _ ] =>
        pose proof (mi_account_step_model_frame segs _ _ _ _ K) as (_ & _ & _ & _ & _ & Hp & _);
        unfold m_halted; rewrite Hp; exact K0
    end.
  - left.
    match goal with
    | [ K : materialize_model_accesses ?m1 _ = Some _, K0 : m_halted ?m1 = None |- _ ] =>
        pose proof (materialize_model_accesses_frame _ _ _ K) as (_ & _ & _ & _ & _ & Hp & _);
        unfold m_halted; rewrite Hp; exact K0
    end.
  - right; left.
    match goal with
    | [ K : m_halted ?m1 = Some ?code, K2 : m_killed ?m1 = None |- context [?evs0 ++ [ExitEv _ _]] ] =>
        exists code, evs0, (m_fs m1); repeat split; assumption
    end.
  - right; right.
    match goal with
    | [ |- context [?evs0 ++ [KillEv ?sig (m_fs ?m1)]] ] => exists sig, evs0, (m_fs m1); reflexivity
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_ok (S : list word) (c : config) : Prop :=
  m_halted (cfg_model c) = None
  \/ exists code, m_halted (cfg_model c) = Some code /\ In code S /\ m_killed (cfg_model c) = None.

Lemma realizes_must_exit_in_gen : forall S c T,
  realizes segs c T -> shape_good S T -> leaf_ok S c ->
  must_exit_in_at_cfg the_scfg segs S c.
Proof.
  intros S c T Hrz. induction Hrz as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hgood Hleaf.
  - destruct Hnode as [Hcan Hall].
    assert (Hrun : m_halted (cfg_model c) = None).
    { pose proof (Hcan i0) as Hs. inversion Hs; subst; cbn [cfg_model]; assumption. }
    apply must_exit_in_at_cfg_running.
    + exact Hrun.
    + exists (evs i0), (SNext (nx i0)). exact (Hcan i0).
    + intros evs0 Herr. destruct (Hall _ _ Herr) as (i & _ & Habs). discriminate Habs.
    + intros evs0 c' Hs. destruct (Hall _ _ Hs) as (i & -> & Heq). inversion Heq; subst c'.
      pose proof (shape_good_alt_inv S I (fun i => t_emit (evs i) (T i)) i Hgood) as Hgi. cbn beta in Hgi.
      destruct (shape_good_emit_inv S (evs i) (T i) (realizes_nonempty segs _ _ (Hcont i)) Hgi) as [Hevs HTi].
      apply (IH i HTi).
      destruct (sstep_cfg_cases _ _ _ _ (Hcan i)) as [Hn | [(code & evs1 & fs & Hh & Hk & Hev) | (sig & evs1 & fs & Hev)]].
      * left. exact Hn.
      * right. exists code. split; [exact Hh|]. split; [|exact Hk].
        assert (Hin : In (ExitEv code fs) (evs i)) by (rewrite Hev; apply in_app_iff; right; left; reflexivity).
        exact (Hevs _ Hin).
      * exfalso. assert (Hin : In (KillEv sig fs) (evs i)) by (rewrite Hev; apply in_app_iff; right; left; reflexivity).
        exact (Hevs _ Hin).
  - destruct Hleaf as [Hn | (code & Hc & Hin & Hk)]; [congruence|].
    exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hc Hin Hk).
  - apply IH; [| exact Hleaf]. eapply shape_good_eq; [apply t_eq_sym; exact Heq | exact Hgood].
Qed.

Theorem realizes_must_exit_in : forall S pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  shape_good S T ->
  must_exit_in_scfg the_scfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros S pc ph sp brk0 mb rnd lim inp T Hrz Hgood. cbn [must_exit_in_scfg].
  eapply realizes_must_exit_in_gen; [exact Hrz | exact Hgood |].
  left. reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs',
              Specs.syscall_spec i m (Monad.Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H|H].
  - left. exact H.
  - right. intros eff' m' evs' Hs.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity|].
    exfalso. apply H. exists eff', m', evs'. split; [exact Hs | exact Hr].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mb rnd] inp. cbn. apply decided_from_classic. Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_down : forall cfg1 cfg2 S img lim en inp,
  cfg_le cfg1 cfg2 ->
  must_exit_in_scfg cfg2 S img lim en inp ->
  must_exit_in_scfg cfg1 S img lim en inp.
Proof.
  intros cfg1 cfg2 S img lim en inp Hle H.
  exact (must_exit_in_scfg_mono _ _ _ _ _ _ _ Hle (run_decided_classic _ _ _ _ _) H).
Qed.
