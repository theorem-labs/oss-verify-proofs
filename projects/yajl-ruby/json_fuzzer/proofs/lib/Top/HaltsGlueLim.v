(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the walk lifted to the run's start over run_segments by run_init, with the premise that the binary carries no vDSO segment). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg LimTransfer.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import HaltsGen HaltsGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* LPS 08b1429: the binary carries no vDSO segment ([vdso_image segs = None]), so a walk over
   its segments is a walk of the run ([RomStable.run_init], [HaltsGlue]). *)
Theorem halts_allowed_of_realizes_init_big :
  forall cfg segs pc ph (lb ls : Z) S (T : ProcInput -> TSet),
  vdso_image segs = None ->
  ls <= lb ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs
       (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lb inp)
       (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg ls S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lb ls S T Hvi Hle HR HS.
  apply (halts_allowed_budgets_of_big forced_only_cfg S (mkImage segs pc ph) lb ls Hle).
  intros [sp brk mb dr] inp HE HI.
  pose proof (run_init cfg segs inp sp mb pc ph brk dr lb (T inp) Hvi
                (HR (mkEntry sp brk mb dr) inp HE HI)) as HR'.
  cbn [must_exit_in_scfg]. cbv zeta.
  apply (realizes_cfg_must_exit_in_fo cfg _ S _ (T inp) HR'); [reflexivity | exact (HS inp HI)].
Qed.

Theorem halts_allowed_of_realizes_ms0_big :
  forall cfg segs pc ph (lb ls : Z) S (T : ProcInput -> TSet),
  vdso_image segs = None ->
  ls <= lb ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lb en inp)) (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg ls S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lb ls S T Hvi Hle HR HS.
  apply (halts_allowed_budgets_of_big forced_only_cfg S (mkImage segs pc ph) lb ls Hle).
  intros en inp HE HI.
  exact (must_exit_in_scfg_fo_of_realizes_ms0 cfg segs pc ph lb S en inp (T inp) Hvi (HR en inp HE HI) (HS inp HI)).
Qed.
