(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits_in (S : list word) (T : TSet) : Prop :=
  (forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S)
  /\ (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])).

Lemma exits_in_t_eq : forall S T T',
  t_eq T T' -> exits_in S T' -> exits_in S T.
Proof.
  intros S T T' Heq [He Hk]. split.
  - intros tr code fs H. apply (He tr code fs). apply Heq. exact H.
  - intros tr sig fs H. apply (Hk tr sig fs). apply Heq. exact H.
Qed.

Lemma exits_in_mono : forall S1 S2 T,
  (forall code, In code S1 -> In code S2) -> exits_in S1 T -> exits_in S2 T.
Proof.
  intros S1 S2 T Hsub [He Hk]. split; [| exact Hk].
  intros tr code fs H. apply Hsub. exact (He tr code fs H).
Qed.

(* [comment removed for export] *)
Lemma exits_in_alt_emit_tail : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exits_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exits_in S (T i).
Proof.
  intros S I evs T i [He Hk]. split.
  - intros tr code fs H. apply (He (evs i ++ tr) code fs).
    exists i. right. exists (tr ++ [ExitEv code fs]). split; [apply app_assoc_reverse | exact H].
  - intros tr sig fs H. apply (Hk (evs i ++ tr) sig fs).
    exists i. right. exists (tr ++ [KillEv sig fs]). split; [apply app_assoc_reverse | exact H].
Qed.

(* [comment removed for export] *)
Lemma alt_emit_block : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  T i [] -> t_alt (fun i => t_emit (evs i) (T i)) (evs i).
Proof.
  intros I evs T i H0. exists i. right. exists []. split; [symmetry; apply app_nil_r | exact H0].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv code _ => In code S
  | KillEv _ _ => False
  | _ => True
  end.

Definition shape_ok (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (ev_ok S) tr.

Lemma shape_ok_exits_in : forall S T, shape_ok S T -> exits_in S T.
Proof.
  intros S T H. split.
  - intros tr code fs HT. apply H in HT. apply Forall_app in HT as [_ HT].
    inversion HT as [| e l He _]; subst. exact He.
  - intros tr sig fs HT. apply H in HT. apply Forall_app in HT as [_ HT].
    inversion HT as [| e l He _]; subst. exact He.
Qed.

Lemma Forall_is_prefix {A} (P : A -> Prop) : forall (l l' : list A),
  is_prefix l' l -> Forall P l -> Forall P l'.
Proof.
  intros l l'; revert l. induction l' as [| a l' IH]; intros l Hp Hl.
  - constructor.
  - destruct l as [| b l]; [cbn in Hp; contradiction |].
    cbn in Hp. destruct Hp as [-> Hp]. inversion Hl; subst.
    constructor; [assumption | eapply IH; eauto].
Qed.

Lemma shape_ok_t_eq : forall S T T', t_eq T T' -> shape_ok S T' -> shape_ok S T.
Proof. intros S T T' Heq H tr HT. apply H. apply Heq. exact HT. Qed.

Lemma shape_ok_nil : forall S, shape_ok S t_nil.
Proof. intros S tr H. unfold t_nil in H. subst tr. constructor. Qed.

Lemma shape_ok_emit : forall S evs T,
  Forall (ev_ok S) evs -> shape_ok S T -> shape_ok S (t_emit evs T).
Proof.
  intros S evs T He HT tr [Hp | (tr' & -> & H')].
  - exact (Forall_is_prefix _ _ _ Hp He).
  - apply Forall_app. split; [exact He | exact (HT tr' H')].
Qed.

Lemma shape_ok_alt : forall S (I : Type) (f : I -> TSet),
  (forall i, shape_ok S (f i)) -> shape_ok S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.

Lemma shape_ok_alt2 : forall S A B,
  shape_ok S A -> shape_ok S B -> shape_ok S (t_alt2 A B).
Proof. intros S A B HA HB tr [H | H]; [exact (HA tr H) | exact (HB tr H)]. Qed.

Lemma shape_ok_exit : forall S code fs, In code S -> shape_ok S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply shape_ok_emit; [| apply shape_ok_nil].
  constructor; [exact Hin | constructor].
Qed.

Lemma ev_ok_writes : forall S ch (buf : list byte), Forall (ev_ok S) (map (WriteEv ch) buf).
Proof. intros S ch buf. apply Forall_forall. intros e He. apply in_map_iff in He as (b & <- & _). exact I. Qed.

Lemma ev_ok_reads : forall S ch (buf : list byte), Forall (ev_ok S) (map (ReadEv ch) buf).
Proof. intros S ch buf. apply Forall_forall. intros e He. apply in_map_iff in He as (b & <- & _). exact I. Qed.

Lemma shape_ok_emit_writes : forall S ch buf T,
  shape_ok S T -> shape_ok S (t_emit (map (WriteEv ch) buf) T).
Proof. intros S ch buf T HT. apply shape_ok_emit; [apply ev_ok_writes | exact HT]. Qed.

Lemma shape_ok_mono : forall S1 S2 T,
  (forall code, In code S1 -> In code S2) -> shape_ok S1 T -> shape_ok S2 T.
Proof.
  intros S1 S2 T Hsub H tr HT. apply H in HT.
  eapply Forall_impl; [| exact HT].
  intros [ch b | ch b | code fs | sig fs]; cbn; auto.
Qed.

(* [comment removed for export] *)

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Theorem realizes_cfg_must_exit_in : forall (S : list word) c T,
  realizes_cfg cfg segs c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros S c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hnone HS.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
      injection Heq2 as ->.
      pose proof (alt_emit_block I evs T i (realizes_cfg_nonempty cfg segs _ _ (Hcont i))) as Hblk.
      destruct (sstep_cfg_next_halts_by_exit segs cfg c (evs i) (nx i) Hss)
        as [Hn | [(evs0 & code & Hev & Hh & Hk) | (evs0 & sig & Hev & Hk)]].
      * apply (IH i Hn). exact (exits_in_alt_emit_tail S I evs T i HS).
      * apply (must_exit_in_at_cfg_halted cfg segs S (nx i) code Hh); [| exact Hk].
        destruct HS as [He _]. apply (He evs0 code (m_fs (cfg_model (nx i)))).
        rewrite <- Hev. exact Hblk.
      * exfalso. destruct HS as [_ HK]. apply (HK evs0 sig (m_fs (cfg_model (nx i)))).
        rewrite <- Hev. exact Hblk.
  - exfalso. exact (Hh Hnone).
  - apply (IH Hnone). exact (exits_in_t_eq S T T' Heq HS).
Qed.

End WithCfg.

(* [comment removed for export] *)

Lemma refusal_decided_all : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
                       syscall_spec i m (Ok eff' m' evs')
                       /\ refusal_b i m (eff_ret eff') = false)) as [Hex | Hno].
  - left. exact Hex.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
    exfalso. apply Hno. exists eff', m', evs'. split; [exact Hspec | exact E].
Qed.

Lemma decided_from_all : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_all. Qed.

Lemma run_decided_all : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided].
  apply decided_from_all.
Qed.

(* [comment removed for export] *)
Lemma must_exit_in_at_cfg_weaken : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 ->
  must_exit_in_at_cfg cfg2 segs S c ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_all cfg1 segs c) H).
Qed.

Theorem realizes_cfg_must_exit_in_le : forall cfg1 cfg2 segs (S : list word) c T,
  cfg_le cfg1 cfg2 ->
  realizes_cfg cfg2 segs c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c T Hle H Hnone HS.
  apply (must_exit_in_at_cfg_weaken cfg1 cfg2 segs S c Hle).
  exact (realizes_cfg_must_exit_in cfg2 segs S c T H Hnone HS).
Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_must_exit_in_fo : forall cfg segs (S : list word) c T,
  realizes_cfg cfg segs c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros cfg segs S c T. apply realizes_cfg_must_exit_in_le. apply forced_only_cfg_least.
Qed.
