(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: adds the halting statement asan_halts of the ASan build from the fifth tree's dead-arm check (TW1_dead). *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import AsanTopW.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Main5W1Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import MainGlue Main5Asan DeadArm.
Require OSSVerify.Core.Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem asan_base :
  strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
             OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
             OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
    (mkImage OSSVerify.coturn.FuzzStunClient.images.Asan.M.loaded_segments
             OSSVerify.coturn.FuzzStunClient.images.Asan.M.init_pc
             OSSVerify.coturn.FuzzStunClient.images.Asan.M.phdrs).
Proof. exact (asan_base_W1 TW1 TW1_ok). Qed.

(* The dead-arm check of the fifth tree, computed per r. *)
Lemma TW1_dead : forall rsb, mtree_dead hf26 (TREE5 (rsb := rsb) (TW1 rsb)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Theorem asan_halts :
  OSSVerify.Core.Shapes.halts_within_budget OSSVerify.Core.Shapes.Budgets.Standard.lim_source
    OSSVerify.Core.Shapes.Exits.ok_or_refused
    (mkImage OSSVerify.coturn.FuzzStunClient.images.Asan.M.loaded_segments
             OSSVerify.coturn.FuzzStunClient.images.Asan.M.init_pc
             OSSVerify.coturn.FuzzStunClient.images.Asan.M.phdrs).
Proof. exact (asan_halts_W1 TW1 TW1_ok TW1_dead). Qed.
