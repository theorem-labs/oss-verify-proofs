(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm4FpSites.
Abbreviation SEGS := Asan.M.loaded_segments.
Lemma site_9b888 : FPB.inl_step SEGS 0x9b8d8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9b88c : FPB.inl_step SEGS 0x9b8dc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9b958 : FPB.inl_step SEGS 0x9b9a8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9b9c4 : FPB.inl_step SEGS 0x9ba14 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9b9c8 : FPB.inl_step SEGS 0x9ba18 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9ba3c : FPB.inl_step SEGS 0x9ba8c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9bb7c : FPB.inl_step SEGS 0x9bbcc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9bb80 : FPB.inl_step SEGS 0x9bbd0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9bb88 : FPB.inl_step SEGS 0x9bbd8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14051c : FPB.inl_step SEGS 0x14056c 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1406ac : FPB.inl_step SEGS 0x1406fc 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_145ff0 : FPB.inl_step SEGS 0x146034 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_146918 : FPB.inl_step SEGS 0x14695c 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_146948 : FPB.inl_step SEGS 0x14698c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_147384 : FPB.inl_step SEGS 0x1473c8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14739c : FPB.inl_step SEGS 0x1473e0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1473fc : FPB.inl_step SEGS 0x147440 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_147400 : FPB.inl_step SEGS 0x147444 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1473bc : FPB.inl_step SEGS 0x147400 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_1473d4 : FPB.inl_step SEGS 0x147418 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14f3fc : FPB.inl_step SEGS 0x14f440 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14f400 : FPB.inl_step SEGS 0x14f444 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14f404 : FPB.inl_step SEGS 0x14f448 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14f4a4 : FPB.inl_step SEGS 0x14f4e8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14f51c : FPB.inl_step SEGS 0x14f560 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e36c : FPB.inl_step SEGS 0x14e3b0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e374 : FPB.inl_step SEGS 0x14e3b8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e378 : FPB.inl_step SEGS 0x14e3bc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e124 : FPB.inl_step SEGS 0x14e168 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ebe4 : FPB.inl_step SEGS 0x14ec28 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ebf0 : FPB.inl_step SEGS 0x14ec34 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ec18 : FPB.inl_step SEGS 0x14ec5c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ed08 : FPB.inl_step SEGS 0x14ed4c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ed0c : FPB.inl_step SEGS 0x14ed50 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ecdc : FPB.inl_step SEGS 0x14ed20 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14ed1c : FPB.inl_step SEGS 0x14ed60 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e208 : FPB.inl_step SEGS 0x14e24c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e20c : FPB.inl_step SEGS 0x14e250 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14e210 : FPB.inl_step SEGS 0x14e254 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14fa54 : FPB.inl_step SEGS 0x14fa98 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14fbe0 : FPB.inl_step SEGS 0x14fc24 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14faec : FPB.inl_step SEGS 0x14fb30 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14fe3c : FPB.inl_step SEGS 0x14fe80 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm4FpSites.
(* [comment removed for export] *)
