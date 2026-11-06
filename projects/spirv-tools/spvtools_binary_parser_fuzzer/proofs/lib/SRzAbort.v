(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition t_nokill (T : TSet) : Prop :=
  forall tr, T tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Definition evs_nokill (evs : list event) : Prop :=
  forall sig fs, ~ In (KillEv sig fs) evs.

Lemma evs_nokill_app : forall a b, evs_nokill a -> evs_nokill b -> evs_nokill (a ++ b).
Proof.
  intros a b Ha Hb sig fs Hin. apply in_app_or in Hin. destruct Hin as [H | H];
    [exact (Ha _ _ H) | exact (Hb _ _ H)].
Qed.

Lemma evs_nokill_prefix : forall a b, is_prefix a b -> evs_nokill b -> evs_nokill a.
Proof.
  intros a b Hp Hb sig fs Hin. exact (Hb sig fs (in_is_prefix _ _ _ Hp Hin)).
Qed.

Lemma evs_nokill_writes : forall ch s, evs_nokill (map (WriteEv ch) s).
Proof.
  intros ch s sig fs Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & _). discriminate.
Qed.

Lemma evs_nokill_exit : forall code fs, evs_nokill [ExitEv code fs].
Proof. intros code fs sig fs' [H | []]. discriminate. Qed.

Lemma t_nokill_nil : t_nokill t_nil.
Proof. intros tr Htr sig fs Hin. unfold t_nil in Htr. subst tr. exact Hin. Qed.

Lemma t_nokill_emit : forall evs T, evs_nokill evs -> t_nokill T -> t_nokill (t_emit evs T).
Proof.
  intros evs T He HT tr [Hp | (tr' & -> & Htr')] sig fs.
  - exact (evs_nokill_prefix _ _ Hp He sig fs).
  - exact (evs_nokill_app _ _ He (HT tr' Htr') sig fs).
Qed.

Lemma t_nokill_exit : forall code fs, t_nokill (t_exit code fs).
Proof. intros code fs. apply t_nokill_emit; [apply evs_nokill_exit | apply t_nokill_nil]. Qed.

Lemma t_nokill_alt2 : forall A B, t_nokill A -> t_nokill B -> t_nokill (t_alt2 A B).
Proof. intros A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma t_nokill_eq : forall T T', t_eq T T' -> t_nokill T' -> t_nokill T.
Proof. intros T T' Heq H tr Htr. exact (H tr (proj1 (Heq tr) Htr)). Qed.

Theorem spin_shape_strong_equiv_ef_abort :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  t_nokill T ->
  error_free_unkilled (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free_unkilled (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hs Ht HK.
  destruct (spin_shape_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim
              target_segs apc aph asp abrk amb arnd alim T inp Hs Ht) as (Hes & Het & Htr).
  split; [| split; [| exact Htr]].
  - split; [exact Hes|]. intros (tr & sig & fs & Htr' & Hin).
    cbn in Htr'. apply (srealizes_obs_iff source_segs _ T Hs tr) in Htr'.
    exact (HK tr Htr' sig fs Hin).
  - split; [exact Het|]. intros (tr & sig & fs & Htr' & Hin).
    cbn in Htr'. apply (srealizes_obs_iff target_segs _ T Ht tr) in Htr'.
    exact (HK tr Htr' sig fs Hin).
Qed.

Theorem spin_shape_universal_ef_abort :
  forall source_segs rpc rph target_segs apc aph,
  (forall en_source en_target inp,
     valid_entry (mkImage source_segs rpc rph) en_source inp ->
     valid_entry (mkImage target_segs apc aph) en_target inp ->
     valid_input_abort inp ->
     exists T,
       srealizes source_segs
         (init_config source_segs rpc rph (en_sp en_source) (en_brk en_source)
            (en_mmap_base en_source) (en_draw en_source) source_alloc_limit inp) T
       /\ srealizes target_segs
         (init_config target_segs apc aph (en_sp en_target) (en_brk en_target)
            (en_mmap_base en_target) (en_draw en_target) target_alloc_limit inp) T
       /\ t_nokill T) ->
  strong_universal_error_free_T_scfg_budgets_abort CFG source_alloc_limit target_alloc_limit
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros source_segs rpc rph target_segs apc aph H en_s en_t inp Hvs Hvt Hinp _.
  destruct (H en_s en_t inp Hvs Hvt Hinp) as (T & Hs & Ht & HK).
  destruct en_s as [ssp sbrk smb srnd]; destruct en_t as [tsp tbrk tmb trnd].
  unfold strong_equiv_error_free_budgets_scfg_abort.
  exact (spin_shape_strong_equiv_ef_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T inp Hs Ht HK).
Qed.
