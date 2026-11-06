(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort RealizesHalts.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimTop LimSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem halts_allowed_lowered_of_realizes : forall cfg segs pc ph L L' S Spec,
  (L <= L')%Z ->
  image_realizes_cfg_e cfg segs pc ph L' Spec ->
  spec_exits_in S Spec ->
  no_kill Spec ->
  halts_allowed_T_scfg_budgets forced_only_cfg L S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph L L' S Spec Hle HR HE HK.
  apply (halts_allowed_lower_limit spec_frame_facts_hold forced_only_cfg S (mkImage segs pc ph) L L' Hle).
  intros [sp brk0 mb rnd] inp Hven Hinp.
  apply (must_exit_in_scfg_of_realizes forced_only_cfg cfg segs pc ph sp brk0 mb rnd L' inp S (Spec inp) (forced_only_cfg_least cfg)).
  - apply HR; [exact Hven | exact (valid_input_either_of_valid_input _ Hinp)].
  - exact (HE inp).
  - exact (no_kill_kill_free Spec inp HK).
Qed.
