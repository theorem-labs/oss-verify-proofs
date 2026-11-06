(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg LimTransfer.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import HaltsGen HaltsGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem halts_allowed_of_realizes_init_big :
  forall cfg segs pc ph (lb ls : Z) S (T : ProcInput -> TSet),
  ls <= lb ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs
       (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lb inp)
       (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg ls S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lb ls S T Hle HR HS.
  apply (halts_allowed_budgets_of_big forced_only_cfg S (mkImage segs pc ph) lb ls Hle).
  intros [sp brk mb dr] inp HE HI. cbn [must_exit_in_scfg].
  apply (realizes_cfg_must_exit_in_fo cfg segs S _ (T inp) (HR (mkEntry sp brk mb dr) inp HE HI));
    [reflexivity | exact (HS inp HI)].
Qed.

Theorem halts_allowed_of_realizes_ms0_big :
  forall cfg segs pc ph (lb ls : Z) S (T : ProcInput -> TSet),
  ls <= lb ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lb en inp)) (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg ls S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lb ls S T Hle HR HS.
  apply (halts_allowed_budgets_of_big forced_only_cfg S (mkImage segs pc ph) lb ls Hle).
  intros en inp HE HI.
  exact (must_exit_in_scfg_fo_of_realizes_ms0 cfg segs pc ph lb S en inp (T inp) (HR en inp HE HI) (HS inp HI)).
Qed.
