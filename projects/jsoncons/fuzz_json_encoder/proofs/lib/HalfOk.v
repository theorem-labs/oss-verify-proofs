(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF KillFree VmLimitFrame.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition half_ok (scfg : SpuriousCfg) (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet) : Prop :=
  error_free_unkilled (run_scfg scfg img lim en inp)
  /\ forall tr, bh_traces (run_scfg scfg img lim en inp) tr <-> T tr.

Lemma base_abort_of_halves : forall scfg lim_s lim_t src tgt en_s en_t inp T,
  half_ok scfg src lim_s en_s inp T -> half_ok scfg tgt lim_t en_t inp T ->
  strong_equiv_error_free_budgets_scfg_abort scfg lim_s lim_t src tgt en_s en_t inp.
Proof.
  intros scfg lim_s lim_t src tgt en_s en_t inp T [HsE HsT] [HtE HtT].
  split; [exact HsE | split; [exact HtE |]].
  intro tr. rewrite (HsT tr), (HtT tr). reflexivity.
Qed.

Lemma half_ok_of_srealizes : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  kill_free T ->
  half_ok scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp T.
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs Hsafe HK. split.
  - exact (srealizes_error_free_unkilled scfg segs pc ph sp brk0 mb rnd lim inp T Hs Hsafe HK).
  - intro tr. exact (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs Hsafe).
Qed.

(* [comment removed for export] *)
Theorem base_abort_of_halves_dep : forall scfg lim_s lim_t (src tgt : Image) (T : ProcInput -> TSet),
  (forall en_s inp, valid_entry src en_s inp -> valid_input_abort inp -> ~ run_scfg_budget_refused scfg src lim_s en_s inp -> half_ok scfg src lim_s en_s inp (T inp)) ->
  (forall en_s en_t inp, valid_entry src en_s inp -> valid_entry tgt en_t inp -> valid_input_abort inp -> ~ run_scfg_budget_refused scfg src lim_s en_s inp ->
     half_ok scfg tgt lim_t en_t inp (T inp)) ->
  strong_universal_error_free_T_scfg_budgets_abort scfg lim_s lim_t src tgt.
Proof.
  intros scfg lim_s lim_t src tgt T HS HT en_s en_t inp Hens Hent Hvalid Hwb.
  exact (base_abort_of_halves _ _ _ _ _ _ _ _ _ (HS en_s inp Hens Hvalid Hwb) (HT en_s en_t inp Hens Hent Hvalid Hwb)).
Qed.
