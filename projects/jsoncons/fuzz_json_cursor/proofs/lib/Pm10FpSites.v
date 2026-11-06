(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm10FpSites.
Abbreviation SEGS := Plain.M.loaded_segments.
Lemma site_ada08 : FPB.inl_step SEGS 0xada44 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a92fc : FPB.inl_step SEGS 0xa9338 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9314 : FPB.inl_step SEGS 0xa9350 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9374 : FPB.inl_step SEGS 0xa93b0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9378 : FPB.inl_step SEGS 0xa93b4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9334 : FPB.inl_step SEGS 0xa9370 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a934c : FPB.inl_step SEGS 0xa9388 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_aee24 : FPB.inl_step SEGS 0xaee60 4 [10%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_aee54 : FPB.inl_step SEGS 0xaee90 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b246c : FPB.inl_step SEGS 0xb24a8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2470 : FPB.inl_step SEGS 0xb24ac 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2474 : FPB.inl_step SEGS 0xb24b0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2514 : FPB.inl_step SEGS 0xb2550 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b258c : FPB.inl_step SEGS 0xb25c8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13dc : FPB.inl_step SEGS 0xb1418 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13e4 : FPB.inl_step SEGS 0xb1420 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13e8 : FPB.inl_step SEGS 0xb1424 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1194 : FPB.inl_step SEGS 0xb11d0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c54 : FPB.inl_step SEGS 0xb1c90 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c60 : FPB.inl_step SEGS 0xb1c9c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c88 : FPB.inl_step SEGS 0xb1cc4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d78 : FPB.inl_step SEGS 0xb1db4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d7c : FPB.inl_step SEGS 0xb1db8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d4c : FPB.inl_step SEGS 0xb1d88 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d8c : FPB.inl_step SEGS 0xb1dc8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1278 : FPB.inl_step SEGS 0xb12b4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b127c : FPB.inl_step SEGS 0xb12b8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1280 : FPB.inl_step SEGS 0xb12bc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b296c : FPB.inl_step SEGS 0xb29a8 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2c20 : FPB.inl_step SEGS 0xb2c5c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2dac : FPB.inl_step SEGS 0xb2de8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2cb8 : FPB.inl_step SEGS 0xb2cf4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3008 : FPB.inl_step SEGS 0xb3044 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3204 : FPB.inl_step SEGS 0xb3240 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm10FpSites.

