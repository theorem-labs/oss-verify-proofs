(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/cgif/cgif_rgb_fuzzer/proofs/lib/HaltsKitFO.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6 (halts_budgets_of_srealizes), restated for this unit's flagged relation, specification and statement budget. *)
(* The flagged top fact is this unit's
   [Common/SpinAlg.srealizesM true] over the run's segment list, read through [SpinAlg.srealizes_fo]; the exits are
   [Exits.ok_or_refused] of the specification ([Corpus/SpecShape.shape_ok_spec]); the limit is lowered to the
   statement's own budget by [Corpus/LimSimSys.must_exit_in_scfg_relim_closed] and the statement is read through
   [halts_within_budget_is_lps], as [Corpus/Halts.v] [coturn_fuzzstunclient_ubsan_halts] does. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SpinAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Import HaltsFO SpecShape LimSimSys.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma init_config_not_halted : forall segs pc ph sp brk mb rnd lim inp,
  m_halted (cfg_model (init_config segs pc ph sp brk mb rnd lim inp)) = None.
Proof. intros. reflexivity. Qed.

(* A build whose every launch is realized at the flag [true], at a limit [Lbig] at least the statement's budget,
   halts within that budget with an exit the specification allows. *)
Theorem halts_of_srealizesM : forall segs pc ph (Lbig : Z),
  (Budgets.Standard.lim_source <= Lbig)%Z ->
  (forall sp brk mb rnd inp,
      valid_entry (mkImage segs pc ph) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
      srealizesM (run_segments segs inp sp mb) true
        (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd Lbig inp)
        (spec (in_argv inp) (in_fs inp))) ->
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused (mkImage segs pc ph).
Proof.
  intros segs pc ph Lbig HLE H.
  rewrite halts_within_budget_is_lps.
  intros [sp brk mb rnd] inp Hen Hinp Hbud.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg Exits.ok_or_refused
           (mkImage segs pc ph) Lbig Budgets.Standard.lim_source (mkEntry sp brk mb rnd) inp HLE Hbud).
  cbn [must_exit_in_scfg].
  apply (fo_exits_must_exit _ Exits.ok_or_refused _ (spec (in_argv inp) (in_fs inp))).
  - apply srealizes_fo. exact (H sp brk mb rnd inp Hen Hinp).
  - exact (shape_ok_spec (in_argv inp) (in_fs inp)).
  - apply init_config_not_halted.
Qed.

(* The two AddressSanitizer builds, from their flagged launch statements ([Asan/AsanTopGlue.v]), realized at
   [target_alloc_limit]. *)
Lemma source_le_target_san : (Budgets.Standard.lim_source <= target_alloc_limit)%Z.
Proof. apply Z.leb_le. reflexivity. Qed.

Theorem asan_halts_of_spec : OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.asan_spec_stmt_T ->
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused
    (mkImage OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.ASANM.loaded_segments
             OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.ASANM.init_pc
             OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.ASANM.phdrs).
Proof. intros H. exact (halts_of_srealizesM _ _ _ target_alloc_limit source_le_target_san H). Qed.

Theorem both_halts_of_spec : OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.both_spec_stmt_T ->
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused
    (mkImage OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.BOTHM.loaded_segments
             OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.BOTHM.init_pc
             OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanTopGlue.BOTHM.phdrs).
Proof. intros H. exact (halts_of_srealizesM _ _ _ target_alloc_limit source_le_target_san H). Qed.
