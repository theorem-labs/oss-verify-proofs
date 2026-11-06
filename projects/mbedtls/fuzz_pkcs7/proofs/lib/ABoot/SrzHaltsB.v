(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib.Logic Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ShapeAlg SpinAlg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Lemma snoc_or_nil {A} : forall (l : list A), l = [] \/ exists l' y, l = l' ++ [y].
Proof.
  induction l as [| x l IH]; [left; reflexivity | right].
  destruct IH as [-> | (l' & y & ->)]; [exists [], x; reflexivity | exists (x :: l'), y; reflexivity].
Qed.

Lemma snoc_eq_app {A} : forall (tr l1 l2 : list A) (x : A),
  tr ++ [x] = l1 ++ l2 ->
  (l2 = [] /\ l1 = tr ++ [x]) \/ (exists l2', l2 = l2' ++ [x] /\ tr = l1 ++ l2').
Proof.
  intros tr l1 l2 x H. destruct (snoc_or_nil l2) as [-> | (l2' & y & ->)].
  - left. rewrite app_nil_r in H. split; [reflexivity | symmetry; exact H].
  - right. rewrite app_assoc in H. apply app_inj_tail in H as [-> <-]. exists l2'. split; reflexivity.
Qed.

Lemma is_prefix_exists {A} : forall (a l : list A), is_prefix a l -> exists m, l = a ++ m.
Proof.
  induction a as [| x a IH]; intros l H; [exists l; reflexivity |].
  destruct l as [| y l]; cbn in H; [contradiction |]. destruct H as [<- H].
  destruct (IH l H) as (m & ->). exists m. reflexivity.
Qed.

Lemma is_prefix_snoc_In {A} : forall (tr l : list A) (x : A), is_prefix (tr ++ [x]) l -> In x l.
Proof.
  intros tr l x H. destruct (is_prefix_exists _ _ H) as (m & ->).
  rewrite <- app_assoc. apply in_or_app. right. cbn. left. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits_in (S : list word) (T : TSet) : Prop :=
  (forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S)
  /\ (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])).

(* [comment removed for export] *)
Definition evs_exits_in (S : list word) (evs : list event) : Prop :=
  (forall code fs, In (ExitEv code fs) evs -> In code S)
  /\ (forall sig fs, ~ In (KillEv sig fs) evs).

Lemma exits_in_t_eq : forall S T T', t_eq T T' -> exits_in S T -> exits_in S T'.
Proof.
  intros S T T' Heq [HE HK]. split.
  - intros tr code fs H. apply (HE tr code fs). apply (proj2 (Heq _)). exact H.
  - intros tr sig fs H. apply (HK tr sig fs). apply (proj2 (Heq _)). exact H.
Qed.

Lemma exits_in_nil : forall S, exits_in S t_nil.
Proof.
  intros S. split.
  - intros tr code fs H. unfold t_nil in H. destruct tr; discriminate H.
  - intros tr sig fs H. unfold t_nil in H. destruct tr; discriminate H.
Qed.

Lemma exits_in_emit : forall S evs T,
  evs_exits_in S evs -> exits_in S T -> exits_in S (t_emit evs T).
Proof.
  intros S evs T [HevE HevK] [HE HK]. split.
  - intros tr code fs [Hp | (tr' & Heq & Htr')].
    + exact (HevE code fs (is_prefix_snoc_In _ _ _ Hp)).
    + destruct (snoc_eq_app _ _ _ _ Heq) as [[-> ->] | (l2' & -> & ->)].
      * apply (HevE code fs). apply in_or_app. right. left. reflexivity.
      * exact (HE _ _ _ Htr').
  - intros tr sig fs [Hp | (tr' & Heq & Htr')].
    + exact (HevK sig fs (is_prefix_snoc_In _ _ _ Hp)).
    + destruct (snoc_eq_app _ _ _ _ Heq) as [[-> ->] | (l2' & -> & ->)].
      * apply (HevK sig fs). apply in_or_app. right. left. reflexivity.
      * exact (HK _ _ _ Htr').
Qed.

Lemma evs_exits_in_exit : forall S code fs, In code S -> evs_exits_in S [ExitEv code fs].
Proof.
  intros S code fs Hin. split.
  - intros code' fs' [H | []]. injection H as <- _. exact Hin.
  - intros sig fs' [H | []]. discriminate H.
Qed.

Lemma evs_exits_in_writes : forall S ch bs, evs_exits_in S (map (WriteEv ch) bs).
Proof.
  intros S ch bs. split.
  - intros code fs H. apply in_map_iff in H as (b & Hb & _). discriminate Hb.
  - intros sig fs H. apply in_map_iff in H as (b & Hb & _). discriminate Hb.
Qed.

Lemma evs_exits_in_nil : forall S, evs_exits_in S [].
Proof. intros S. split; [intros ? ? [] | intros ? ? []]. Qed.

Lemma exits_in_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply exits_in_emit; [apply evs_exits_in_exit; exact Hin | apply exits_in_nil].
Qed.

Lemma exits_in_alt2 : forall S A B, exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof.
  intros S A B [HAE HAK] [HBE HBK]. split.
  - intros tr code fs [H | H]; [exact (HAE _ _ _ H) | exact (HBE _ _ _ H)].
  - intros tr sig fs [H | H]; [exact (HAK _ _ _ H) | exact (HBK _ _ _ H)].
Qed.

Lemma exits_in_alt2_inv : forall S A B, exits_in S (t_alt2 A B) -> exits_in S A /\ exits_in S B.
Proof.
  intros S A B [HE HK]. split; split.
  - intros tr code fs H. apply (HE tr code fs). left. exact H.
  - intros tr sig fs H. apply (HK tr sig fs). left. exact H.
  - intros tr code fs H. apply (HE tr code fs). right. exact H.
  - intros tr sig fs H. apply (HK tr sig fs). right. exact H.
Qed.

Lemma exits_in_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, exits_in S (f i)) -> exits_in S (t_alt f).
Proof.
  intros S I f Hf. split.
  - intros tr code fs [i Hi]. exact (proj1 (Hf i) _ _ _ Hi).
  - intros tr sig fs [i Hi]. exact (proj2 (Hf i) _ _ _ Hi).
Qed.

Lemma exits_in_alt_inv : forall S (I : Type) (f : I -> TSet) i,
  exits_in S (t_alt f) -> exits_in S (f i).
Proof.
  intros S I f i [HE HK]. split.
  - intros tr code fs H. apply (HE tr code fs). exists i. exact H.
  - intros tr sig fs H. apply (HK tr sig fs). exists i. exact H.
Qed.

Lemma exits_in_emit_inv : forall S evs T, exits_in S (t_emit evs T) -> exits_in S T.
Proof.
  intros S evs T [HE HK]. split.
  - intros tr code fs H. apply (HE (evs ++ tr) code fs). right. exists (tr ++ [ExitEv code fs]).
    split; [rewrite app_assoc; reflexivity | exact H].
  - intros tr sig fs H. apply (HK (evs ++ tr) sig fs). right. exists (tr ++ [KillEv sig fs]).
    split; [rewrite app_assoc; reflexivity | exact H].
Qed.

(* [comment removed for export] *)
Lemma exits_in_emit_evs : forall S evs T, exits_in S (t_emit evs T) -> evs_exits_in S evs.
Proof.
  intros S evs T [HE HK]. split.
  - intros code fs Hin. apply in_split in Hin as (l1 & l2 & ->).
    apply (HE l1 code fs). left. change (ExitEv code fs :: l2) with ([ExitEv code fs] ++ l2).
    rewrite app_assoc. apply is_prefix_app.
  - intros sig fs Hin. apply in_split in Hin as (l1 & l2 & ->).
    apply (HK l1 sig fs). left. change (KillEv sig fs :: l2) with ([KillEv sig fs] ++ l2).
    rewrite app_assoc. apply is_prefix_app.
Qed.

Lemma exits_in_writes : forall S ch bs T, exits_in S T -> exits_in S (t_emit (map (WriteEv ch) bs) T).
Proof. intros S ch bs T HT. apply exits_in_emit; [apply evs_exits_in_writes | exact HT]. Qed.

(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs', Specs.syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
    as [H | H]; [left; exact H | right].
  intros eff' m' evs' Hspec. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
  exfalso. apply H. exists eff', m', evs'. split; [exact Hspec | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition halted_in (S : list word) (c : config) : Prop :=
  forall code, m_halted (cfg_model c) = Some code -> In code S /\ m_killed (cfg_model c) = None.

Lemma halted_in_of_running : forall S c, m_halted (cfg_model c) = None -> halted_in S c.
Proof. intros S c H code Hc. rewrite H in Hc. discriminate Hc. Qed.

(* [comment removed for export] *)
Lemma halted_in_next : forall S c e c',
  sstep segs c e (SNext c') -> evs_exits_in S e -> halted_in S c'.
Proof.
  intros S c e c' Hss [HeE HeK].
  destruct (sstep_next_halts_by_exit segs c e c' Hss)
    as [Hnone | [(evs0 & code & -> & Hh & Hk) | (evs0 & sig & -> & Hk)]].
  - apply halted_in_of_running. exact Hnone.
  - intros code' Hc'. rewrite Hh in Hc'. injection Hc' as <-. split; [| exact Hk].
    apply (HeE code (m_fs (cfg_model c'))). apply in_or_app. right. left. reflexivity.
  - exfalso. apply (HeK sig (m_fs (cfg_model c'))). apply in_or_app. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_must_exit : forall S c (I : Type) (evs : I -> list event) (nx : I -> config) (i0 : I),
  node_ok segs c I evs nx ->
  (forall i, fo_step segs c (evs i) (nx i) -> must_exit_in_at_cfg forced_only_cfg segs S (nx i)) ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros S c I evs nx i0 [Hcomp Hsound] Hch.
  apply must_exit_in_at_cfg_running.
  - exact (sstep_not_halted segs c (evs i0) (SNext (nx i0)) (Hcomp i0)).
  - destruct c as [ms model].
    eapply (sstep_cfg_progress segs forced_only_cfg ms model (evs i0) (SNext (nx i0))); [| exact (Hcomp i0)].
    intros x8 _. apply refusal_decided_classic.
  - intros e Herr. destruct (Hsound e SError (sstep_cfg_sub segs _ _ _ _ Herr)) as (i & _ & Habs). discriminate Habs.
  - intros e c' Hss. destruct (Hsound e (SNext c') (sstep_cfg_sub segs _ _ _ _ Hss)) as (i & -> & Heq).
    injection Heq as ->. apply Hch. exact Hss.
Qed.

Theorem srealizes_must_exit : forall (S : list word) c T,
  srealizes segs c T -> exits_in S T -> halted_in S c ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros S. fix REC 3. intros c T H.
  destruct H as [c I evs nx T i0 Hnode Hch | c Hh | c I evs nx T i0 Hnode Hch | c T T' H Heq]; intros HS Hhalt.
  - (* [comment removed for export] *)
    apply (node_must_exit S c I evs nx i0 Hnode). intros i Hst.
    pose proof (exits_in_alt_inv S I (fun i => t_emit (evs i) (T i)) i HS) as HSi. cbn beta in HSi.
    apply (REC (nx i) (T i) (Hch i) (exits_in_emit_inv S _ _ HSi)).
    exact (halted_in_next S c (evs i) (nx i) (sstep_cfg_sub segs _ _ _ _ Hst) (exits_in_emit_evs S _ _ HSi)).
  - (* [comment removed for export] *)
    destruct (m_halted (cfg_model c)) as [code |] eqn:Hc; [| exfalso; exact (Hh eq_refl)].
    destruct (Hhalt code Hc) as [Hin Hk].
    exact (must_exit_in_at_cfg_halted forced_only_cfg segs S c code Hc Hin Hk).
  - (* [comment removed for export] *)
    apply (node_must_exit S c I evs nx i0 Hnode). intros i Hst.
    pose proof (exits_in_alt_inv S I (fun i => t_emit (evs i) (T i)) i HS) as HSi. cbn beta in HSi.
    destruct (Hch i) as [Hlive | [_ Hexc]].
    + apply (REC (nx i) (T i) Hlive (exits_in_emit_inv S _ _ HSi)).
      exact (halted_in_next S c (evs i) (nx i) (sstep_cfg_sub segs _ _ _ _ Hst) (exits_in_emit_evs S _ _ HSi)).
    + exfalso. exact (Hexc Hst).
  - (* [comment removed for export] *)
    exact (REC c T H (exits_in_t_eq S T' T (t_eq_sym _ _ Heq) HS) Hhalt).
Qed.

(* [comment removed for export] *)
Corollary srealizes_must_exit_running : forall (S : list word) c T,
  srealizes segs c T -> exits_in S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros S c T H HS Hnone. exact (srealizes_must_exit S c T H HS (halted_in_of_running S c Hnone)).
Qed.

(* [comment removed for export] *)
Corollary srealizes_must_exit_in_scfg : forall (S : list word) pc ph sp brk0 mbase rnd lim inp T,
  srealizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T ->
  exits_in S T ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp.
Proof.
  intros S pc ph sp brk0 mbase rnd lim inp T H HS.
  cbn [must_exit_in_scfg]. eapply srealizes_must_exit_running; [exact H | exact HS |].
  reflexivity.
Qed.

End WithSegs.
