(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm8FpSites.
Abbreviation SEGS := Asan.M.loaded_segments.
Lemma site_9a4bc : FPB.inl_step SEGS 0x9a50c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a4c0 : FPB.inl_step SEGS 0x9a510 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a58c : FPB.inl_step SEGS 0x9a5dc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a5f8 : FPB.inl_step SEGS 0x9a648 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a5fc : FPB.inl_step SEGS 0x9a64c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a670 : FPB.inl_step SEGS 0x9a6c0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a7b0 : FPB.inl_step SEGS 0x9a800 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a7b4 : FPB.inl_step SEGS 0x9a804 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a7bc : FPB.inl_step SEGS 0x9a80c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_132980 : FPB.inl_step SEGS 0x1329d0 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_132b10 : FPB.inl_step SEGS 0x132b60 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_138454 : FPB.inl_step SEGS 0x138498 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_138d7c : FPB.inl_step SEGS 0x138dc0 4 [10%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_138dac : FPB.inl_step SEGS 0x138df0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1397e8 : FPB.inl_step SEGS 0x13982c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139800 : FPB.inl_step SEGS 0x139844 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139860 : FPB.inl_step SEGS 0x1398a4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139864 : FPB.inl_step SEGS 0x1398a8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139820 : FPB.inl_step SEGS 0x139864 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139838 : FPB.inl_step SEGS 0x13987c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141860 : FPB.inl_step SEGS 0x1418a4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141864 : FPB.inl_step SEGS 0x1418a8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141868 : FPB.inl_step SEGS 0x1418ac 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141908 : FPB.inl_step SEGS 0x14194c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141980 : FPB.inl_step SEGS 0x1419c4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1407d0 : FPB.inl_step SEGS 0x140814 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1407d8 : FPB.inl_step SEGS 0x14081c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1407dc : FPB.inl_step SEGS 0x140820 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_140588 : FPB.inl_step SEGS 0x1405cc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141048 : FPB.inl_step SEGS 0x14108c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141054 : FPB.inl_step SEGS 0x141098 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14107c : FPB.inl_step SEGS 0x1410c0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14116c : FPB.inl_step SEGS 0x1411b0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141170 : FPB.inl_step SEGS 0x1411b4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141140 : FPB.inl_step SEGS 0x141184 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141180 : FPB.inl_step SEGS 0x1411c4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14066c : FPB.inl_step SEGS 0x1406b0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_140670 : FPB.inl_step SEGS 0x1406b4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_140674 : FPB.inl_step SEGS 0x1406b8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141eb8 : FPB.inl_step SEGS 0x141efc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142044 : FPB.inl_step SEGS 0x142088 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141f50 : FPB.inl_step SEGS 0x141f94 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1422a0 : FPB.inl_step SEGS 0x1422e4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm8FpSites.

