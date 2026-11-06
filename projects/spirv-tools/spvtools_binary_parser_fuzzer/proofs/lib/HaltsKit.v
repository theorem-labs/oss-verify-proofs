(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition t_exits_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> forall code fs, In (ExitEv code fs) tr -> In code S.

Definition evs_exits_in (S : list word) (evs : list event) : Prop :=
  forall code fs, In (ExitEv code fs) evs -> In code S.

Lemma evs_exits_in_writes : forall S ch s, evs_exits_in S (map (WriteEv ch) s).
Proof.
  intros S ch s code fs Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & _). discriminate Hx.
Qed.

Lemma evs_exits_in_exit : forall S code fs, In code S -> evs_exits_in S [ExitEv code fs].
Proof. intros S code fs Hin code' fs' [E | []]. injection E as <- _. exact Hin. Qed.

Lemma evs_exits_in_app : forall S a b,
  evs_exits_in S a -> evs_exits_in S b -> evs_exits_in S (a ++ b).
Proof.
  intros S a b Ha Hb code fs Hin. apply in_app_or in Hin. destruct Hin as [H | H];
    [exact (Ha _ _ H) | exact (Hb _ _ H)].
Qed.

Lemma evs_exits_in_prefix : forall S a b, is_prefix a b -> evs_exits_in S b -> evs_exits_in S a.
Proof. intros S a b Hp Hb code fs Hin. exact (Hb code fs (in_is_prefix _ _ _ Hp Hin)). Qed.

Lemma t_exits_in_eq : forall S T T', t_eq T T' -> t_exits_in S T' -> t_exits_in S T.
Proof. intros S T T' Heq H tr Htr. exact (H tr (proj1 (Heq tr) Htr)). Qed.

Lemma t_exits_in_nil : forall S, t_exits_in S t_nil.
Proof. intros S tr Htr code fs Hin. unfold t_nil in Htr. subst tr. destruct Hin. Qed.

Lemma t_exits_in_emit : forall S evs T,
  evs_exits_in S evs -> t_exits_in S T -> t_exits_in S (t_emit evs T).
Proof.
  intros S evs T He HT tr [Hp | (tr' & -> & Htr')] code fs.
  - exact (evs_exits_in_prefix _ _ _ Hp He code fs).
  - exact (evs_exits_in_app _ _ _ He (HT tr' Htr') code fs).
Qed.

Lemma t_exits_in_exit : forall S code fs, In code S -> t_exits_in S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit.
  apply t_exits_in_emit; [apply evs_exits_in_exit; exact Hin | apply t_exits_in_nil].
Qed.

Lemma t_exits_in_alt2 : forall S A B,
  t_exits_in S A -> t_exits_in S B -> t_exits_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma t_nokill_branch : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  t_nokill (t_alt (fun i => t_emit (evs i) (T i))) -> t_nokill (T i).
Proof.
  intros I evs T i H tr Htr sig fs Hin.
  apply (H (evs i ++ tr) ltac:(exists i; right; exists tr; split; [reflexivity | exact Htr]) sig fs).
  apply in_or_app. right. exact Hin.
Qed.

Lemma t_exits_in_branch : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  t_exits_in S (t_alt (fun i => t_emit (evs i) (T i))) -> t_exits_in S (T i).
Proof.
  intros S I evs T i H tr Htr code fs Hin.
  apply (H (evs i ++ tr) ltac:(exists i; right; exists tr; split; [reflexivity | exact Htr]) code fs).
  apply in_or_app. right. exact Hin.
Qed.

Theorem srealizes_must_exit : forall S c T,
  srealizes segs c T ->
  t_nokill T ->
  t_exits_in S T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg CFG segs S c.
Proof.
  intros S c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros HK HE Hnone.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). exact (Hcomp i0).
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heqc). injection Heqc as ->.
      destruct (sstep_cfg_next_halts_by_exit segs CFG c (evs i) (nx i) Hss)
        as [Hn | [(evs0 & code & Eevs & Hh & Hk) | (evs0 & sig & Eevs & Hk)]].
      *
        exact (IH i (t_nokill_branch I evs T i HK) (t_exits_in_branch S I evs T i HE) Hn).
      *
        apply (must_exit_in_at_cfg_halted CFG segs S (nx i) code Hh); [| exact Hk].
        apply (HE (evs i) ltac:(exists i; left; apply is_prefix_refl) code (m_fs (cfg_model (nx i)))).
        rewrite Eevs. apply in_or_app. right. left. reflexivity.
      *
        exfalso.
        apply (HK (evs i) ltac:(exists i; left; apply is_prefix_refl) sig (m_fs (cfg_model (nx i)))).
        rewrite Eevs. apply in_or_app. right. left. reflexivity.
  - exfalso. exact (Hh Hnone).
  - exact (IH (t_nokill_eq _ _ Heq HK) (t_exits_in_eq _ _ _ Heq HE) Hnone).
Qed.

Lemma decided_from_classic : forall cfg c, decided_from cfg segs c.
Proof. intros cfg c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma must_exit_in_at_cfg_le : forall cfg S c,
  cfg_le cfg CFG ->
  must_exit_in_at_cfg CFG segs S c -> must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg CFG segs S c Hle (decided_from_classic cfg c) H).
Qed.

Theorem srealizes_must_exit_le : forall cfg S c T,
  cfg_le cfg CFG ->
  srealizes segs c T -> t_nokill T -> t_exits_in S T ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg S c T Hle H HK HE Hn.
  apply (must_exit_in_at_cfg_le cfg S c Hle). exact (srealizes_must_exit S c T H HK HE Hn).
Qed.

End WithSegs.

Lemma cfg_le_forced_only_CFG : cfg_le forced_only_cfg CFG.
Proof. apply forced_only_cfg_least. Qed.

Lemma init_config_not_halted : forall segs pc ph sp brk0 mbase rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.

Theorem srealizes_halts_scfg_budgets : forall cfg segs pc ph (lim : Z) S,
  cfg_le cfg CFG ->
  (forall sp brk0 mbase rnd inp,
     valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mbase rnd) inp ->
     valid_input inp ->
     exists T,
       srealizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T
       /\ t_nokill T /\ t_exits_in S T) ->
  halts_allowed_T_scfg_budgets cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S Hle H [sp brk0 mbase rnd] inp Hen Hinp _.
  cbn [must_exit_in_scfg].
  destruct (H sp brk0 mbase rnd inp Hen Hinp) as (T & Hs & HK & HE).
  exact (srealizes_must_exit_le segs cfg S _ T Hle Hs HK HE (init_config_not_halted _ _ _ _ _ _ _ _ _)).
Qed.

