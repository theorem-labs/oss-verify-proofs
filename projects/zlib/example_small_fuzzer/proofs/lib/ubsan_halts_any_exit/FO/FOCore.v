(** * FO.FOCore — moving a halting proof onto a spurious-failure configuration

    The forced-only statements (zlib re-issued with memory set to "fails only if forced",
    [Run.mkSpuriousCfg false true true true true true]) quantify over the FILTERED step relation
    [Run.sstep_cfg cfg].  A halting proof made under the unfiltered relation ([MustExit.must_exit_in],
    the may-fail reading) carries over to every configuration, by
    [MustExit.must_exit_in_scfg_of_must_exit_in], once the filter's question is answered at every
    reachable configuration ([MustExit.run_decided]).  That question, [Run.refusal_decided], is
    "either a non-refusal outcome exists or every outcome is a refusal": an excluded middle, which is
    all this file uses to answer it.  [Classical_Prop.classic] is on the permitted-axiom list
    (the project owner, 2026-09-03).

    [halts_core] is the claim the port proves once per binary: every execution, at every valid entry
    and input, halts with an allowed status under [cfg], with no budget premise.  The statement shells
    are read off it:
    - the release shell [HaltsAllowed.halts_allowed_T_scfg_budgets] drops its budget premise
      ([halts_allowed_T_scfg_budgets_of_core]);
    - lps #1716's [Halting.halts_refusal_T_scfg] (PR #1718) follows from the same core by
      [Halting.must_halt_refusal_scfg_of_must_exit_in_scfg], once that file is in the image. *)

From Stdlib Require Import ZArith List Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The filter's question, answered by excluded middle at every input and model. *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
                       syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
    as [Hex | Hno].
  - left. exact Hex.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
    exfalso. apply Hno. exists eff', m', evs'. split; [exact Hspec | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided].
  apply decided_from_classic.
Qed.

(** THE BRIDGE: a halting proof under the unfiltered relation is one under every configuration. *)
Theorem must_exit_in_at_cfg_of_must_exit_in_at_classic : forall cfg segs S c,
  must_exit_in_at segs S c -> must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg segs S c H.
  exact (must_exit_in_at_cfg_of_must_exit_in_at cfg segs S c (decided_from_classic cfg segs c) H).
Qed.

Theorem must_exit_in_scfg_of_must_exit_in_classic : forall cfg S img lim en inp,
  must_exit_in S img lim en inp -> must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp H.
  exact (must_exit_in_scfg_of_must_exit_in cfg S img lim en inp
           (run_decided_classic cfg img lim en inp) H).
Qed.

(** The configured progress fact on its own, for proofs that build [must_exit_in_at_cfg] directly
    (the trees whose node relation is already filtered): a configuration with a step has a filtered
    step. *)
Lemma sstep_cfg_progress_classic : forall segs cfg ms model evs st,
  sstep segs (mkCfg ms model) evs st ->
  exists evs' st', sstep_cfg segs cfg (mkCfg ms model) evs' st'.
Proof.
  intros segs cfg ms model evs st H.
  apply (sstep_cfg_progress segs cfg ms model evs st); [| exact H].
  intros x8 _. apply refusal_decided_classic.
Qed.

(** Whenever the spec admits an outcome, it admits one the filter keeps: a non-refusal if there is one,
    otherwise the given outcome, which is then not spurious. *)
Lemma nonspurious_outcome_exists : forall cfg i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  exists eff2 m2 evs2, syscall_spec i m (Ok eff2 m2 evs2) /\ ~ spurious_refusal_cfg cfg i m eff2.
Proof.
  intros cfg i m eff m' evs Hs.
  destruct (classic (exists eff' m2 evs2,
                       syscall_spec i m (Ok eff' m2 evs2) /\ refusal_b i m (eff_ret eff') = false))
    as [(eff' & m2 & evs2 & Hs2 & Hnr) | Hno].
  - exists eff', m2, evs2. split; [exact Hs2 | apply spurious_refusal_not_refusal; exact Hnr].
  - exists eff, m', evs. split; [exact Hs |]. intros (_ & _ & Hex). exact (Hno Hex).
Qed.

(** A refusal that survives the filter, at a forced-only family, is forced: no non-refusal outcome. *)
Lemma refusal_not_spurious_forced : forall cfg i m eff,
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  ~ spurious_refusal_cfg cfg i m eff ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros cfg i m eff Hoff Hr Hns eff' m' evs' Hs.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
  exfalso. apply Hns. split; [exact Hoff |]. split; [exact Hr |]. exists eff', m', evs'. split; assumption.
Qed.

(* -------------------------------------------------------------------------
   The core claim, and the statement shells read off it
   ------------------------------------------------------------------------- *)

(** Halting under [cfg] at budget [lim], on every valid entry and input, with no budget premise. *)
Definition halts_core (cfg : SpuriousCfg) (lim : Z) (S : list word) (img : Image) : Prop :=
  forall en inp,
    valid_entry img en inp ->
    valid_input inp ->
    must_exit_in_scfg cfg S img lim en inp.

(** From a may-fail halting proof at [lim], for every configuration. *)
Lemma halts_core_of_must_exit_in : forall cfg lim S img,
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in S img lim en inp) ->
  halts_core cfg lim S img.
Proof.
  intros cfg lim S img H en inp Hen Hv.
  exact (must_exit_in_scfg_of_must_exit_in_classic cfg S img lim en inp (H en inp Hen Hv)).
Qed.

(** From the may-fail statement the bundle trees prove ([HaltsAllowed.halts_allowed_T_scfg] at
    [Run.may_fail_cfg], at the shipped budget). *)
Lemma halts_core_of_halts_allowed_may_fail : forall cfg S img,
  halts_allowed_T_scfg may_fail_cfg S img -> halts_core cfg source_alloc_limit S img.
Proof.
  intros cfg S img H. apply halts_core_of_must_exit_in.
  intros en inp Hen Hv.
  exact (proj1 (must_exit_in_scfg_may_fail S img source_alloc_limit en inp) (H en inp Hen Hv)).
Qed.

(** The core is monotone downward in the configuration: a proof at the memory-only forced configuration
    gives one at [Run.forced_only_cfg] and every other configuration below it. *)
Lemma halts_core_mono : forall cfg1 cfg2 lim S img,
  cfg_le cfg1 cfg2 -> halts_core cfg2 lim S img -> halts_core cfg1 lim S img.
Proof.
  intros cfg1 cfg2 lim S img Hle H en inp Hen Hv.
  exact (must_exit_in_scfg_mono cfg1 cfg2 S img lim en inp Hle (run_decided_classic cfg1 img lim en inp)
           (H en inp Hen Hv)).
Qed.

(** The release shell: the budget premise is not used. *)
Lemma halts_allowed_T_scfg_budgets_of_core : forall cfg lim S img,
  halts_core cfg lim S img -> halts_allowed_T_scfg_budgets cfg lim S img.
Proof. intros cfg lim S img H en inp Hen Hv _. exact (H en inp Hen Hv). Qed.

(** The configured shell without a budget, at the shipped budget. *)
Lemma halts_allowed_T_scfg_of_core : forall cfg S img,
  halts_core cfg source_alloc_limit S img -> halts_allowed_T_scfg cfg S img.
Proof. intros cfg S img H en inp Hen Hv. exact (H en inp Hen Hv). Qed.

(** The forced-only configuration of the zlib re-issue: memory only (the project owner, 2026-10-08 and
    2026-10-19). *)
Definition alloc_forced_cfg : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma alloc_forced_cfg_is_alloc_only : alloc_forced_cfg = alloc_only_cfg false.
Proof. reflexivity. Qed.
