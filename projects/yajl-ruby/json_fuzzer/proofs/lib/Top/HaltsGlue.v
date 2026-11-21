(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the walk lifted to the run's start over run_segments by run_init and run_init_ms0, with the premise that the binary carries no vDSO segment, and the local must-exit transfer dropped). *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import HaltsGen RunInitCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* LPS 08b1429: [must_exit_in_scfg] runs the binary over [run_segments ..] from the run's own
   start; a walk over the binary's segments reaches it through [RomStable.run_init] (from
   [init_config]) or [RunInitCfg.run_init_ms0] (from [ms0]).  The binary carries no vDSO
   segment ([vdso_image segs = None]); each top row closes it on its concrete image. *)

(* [comment removed for export] *)
Lemma must_exit_in_scfg_fo_of_realizes_ms0 : forall cfg segs pc ph lim S en inp T,
  vdso_image segs = None ->
  realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) T ->
  exits_in S T ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim en inp.
Proof.
  intros cfg segs pc ph lim S en inp T Hvi HR HS.
  pose proof (run_init_ms0 cfg segs pc ph lim en inp T Hvi HR) as HR'.
  destruct en as [sp brk mb dr]. cbn [en_sp en_brk en_mmap_base en_draw] in HR'.
  cbn [must_exit_in_scfg]. cbv zeta.
  apply (realizes_cfg_must_exit_in_fo cfg _ S _ T HR'); [reflexivity | exact HS].
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_ms0_premise :
  forall cfg segs pc ph lim S (T : ExecEntry -> ProcInput -> TSet),
  vdso_image segs = None ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     source_within_budget_scfg forced_only_cfg lim (mkImage segs pc ph) en inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T en inp)
     /\ exits_in S (T en inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T Hvi H en inp HE HI HB.
  destruct (H en inp HE HI HB) as [HR HS].
  exact (must_exit_in_scfg_fo_of_realizes_ms0 cfg segs pc ph lim S en inp _ Hvi HR HS).
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_ms0 :
  forall cfg segs pc ph lim S (T : ProcInput -> TSet),
  vdso_image segs = None ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T Hvi HR HS.
  apply (halts_allowed_of_realizes_ms0_premise cfg segs pc ph lim S (fun _ inp => T inp) Hvi).
  intros en inp HE HI _. split; [exact (HR en inp HE HI) | exact (HS inp HI)].
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_init :
  forall cfg segs pc ph lim S (T : ProcInput -> TSet),
  vdso_image segs = None ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs
       (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
       (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T Hvi HR HS [sp brk mb dr] inp HE HI _.
  pose proof (run_init cfg segs inp sp mb pc ph brk dr lim (T inp) Hvi
                (HR (mkEntry sp brk mb dr) inp HE HI)) as HR'.
  cbn [must_exit_in_scfg]. cbv zeta.
  apply (realizes_cfg_must_exit_in_fo cfg _ S _ (T inp) HR'); [reflexivity | exact (HS inp HI)].
Qed.
