(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm6FpSites.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Lemma site_b2624 : FPB.inl_step SEGS 0xb604c 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf18 : FPB.inl_step SEGS 0xb1940 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf30 : FPB.inl_step SEGS 0xb1958 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf90 : FPB.inl_step SEGS 0xb19b8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf94 : FPB.inl_step SEGS 0xb19bc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf50 : FPB.inl_step SEGS 0xb1978 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf68 : FPB.inl_step SEGS 0xb1990 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3a40 : FPB.inl_step SEGS 0xb7468 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3a70 : FPB.inl_step SEGS 0xb7498 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7088 : FPB.inl_step SEGS 0xbaab0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b708c : FPB.inl_step SEGS 0xbaab4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7090 : FPB.inl_step SEGS 0xbaab8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7130 : FPB.inl_step SEGS 0xbab58 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b71a8 : FPB.inl_step SEGS 0xbabd0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5ff8 : FPB.inl_step SEGS 0xb9a20 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6000 : FPB.inl_step SEGS 0xb9a28 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6004 : FPB.inl_step SEGS 0xb9a2c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5db0 : FPB.inl_step SEGS 0xb97d8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6870 : FPB.inl_step SEGS 0xba298 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b687c : FPB.inl_step SEGS 0xba2a4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b68a4 : FPB.inl_step SEGS 0xba2cc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6994 : FPB.inl_step SEGS 0xba3bc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6998 : FPB.inl_step SEGS 0xba3c0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6968 : FPB.inl_step SEGS 0xba390 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b69a8 : FPB.inl_step SEGS 0xba3d0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e94 : FPB.inl_step SEGS 0xb98bc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e98 : FPB.inl_step SEGS 0xb98c0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e9c : FPB.inl_step SEGS 0xb98c4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7588 : FPB.inl_step SEGS 0xbafb0 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b783c : FPB.inl_step SEGS 0xbb264 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b79c8 : FPB.inl_step SEGS 0xbb3f0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b78d4 : FPB.inl_step SEGS 0xbb2fc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7c24 : FPB.inl_step SEGS 0xbb64c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7e20 : FPB.inl_step SEGS 0xbb848 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm6FpSites.
(* [comment removed for export] *)
