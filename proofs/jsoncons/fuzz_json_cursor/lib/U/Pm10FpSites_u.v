(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm10FpSites.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Lemma site_ada08 : FPB.inl_step SEGS 0xaf898 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a92fc : FPB.inl_step SEGS 0xab18c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9314 : FPB.inl_step SEGS 0xab1a4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9374 : FPB.inl_step SEGS 0xab204 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9378 : FPB.inl_step SEGS 0xab208 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a9334 : FPB.inl_step SEGS 0xab1c4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_a934c : FPB.inl_step SEGS 0xab1dc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_aee24 : FPB.inl_step SEGS 0xb0cb4 4 [10%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_aee54 : FPB.inl_step SEGS 0xb0ce4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b246c : FPB.inl_step SEGS 0xb42fc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2470 : FPB.inl_step SEGS 0xb4300 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2474 : FPB.inl_step SEGS 0xb4304 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2514 : FPB.inl_step SEGS 0xb43a4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b258c : FPB.inl_step SEGS 0xb441c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13dc : FPB.inl_step SEGS 0xb326c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13e4 : FPB.inl_step SEGS 0xb3274 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b13e8 : FPB.inl_step SEGS 0xb3278 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1194 : FPB.inl_step SEGS 0xb3024 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c54 : FPB.inl_step SEGS 0xb3ae4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c60 : FPB.inl_step SEGS 0xb3af0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1c88 : FPB.inl_step SEGS 0xb3b18 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d78 : FPB.inl_step SEGS 0xb3c08 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d7c : FPB.inl_step SEGS 0xb3c0c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d4c : FPB.inl_step SEGS 0xb3bdc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1d8c : FPB.inl_step SEGS 0xb3c1c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1278 : FPB.inl_step SEGS 0xb3108 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b127c : FPB.inl_step SEGS 0xb310c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b1280 : FPB.inl_step SEGS 0xb3110 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b296c : FPB.inl_step SEGS 0xb47fc 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2c20 : FPB.inl_step SEGS 0xb4ab0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2dac : FPB.inl_step SEGS 0xb4c3c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b2cb8 : FPB.inl_step SEGS 0xb4b48 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3008 : FPB.inl_step SEGS 0xb4e98 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3204 : FPB.inl_step SEGS 0xb5094 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm10FpSites.

