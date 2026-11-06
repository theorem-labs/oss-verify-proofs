(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm6FpSites.
Abbreviation SEGS := Plain.M.loaded_segments.
Lemma site_b2624 : FPB.inl_step SEGS 0xb2660 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf18 : FPB.inl_step SEGS 0xadf54 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf30 : FPB.inl_step SEGS 0xadf6c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf90 : FPB.inl_step SEGS 0xadfcc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf94 : FPB.inl_step SEGS 0xadfd0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf50 : FPB.inl_step SEGS 0xadf8c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_adf68 : FPB.inl_step SEGS 0xadfa4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3a40 : FPB.inl_step SEGS 0xb3a7c 4 [10%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b3a70 : FPB.inl_step SEGS 0xb3aac 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7088 : FPB.inl_step SEGS 0xb70c4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b708c : FPB.inl_step SEGS 0xb70c8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7090 : FPB.inl_step SEGS 0xb70cc 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7130 : FPB.inl_step SEGS 0xb716c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b71a8 : FPB.inl_step SEGS 0xb71e4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5ff8 : FPB.inl_step SEGS 0xb6034 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6000 : FPB.inl_step SEGS 0xb603c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6004 : FPB.inl_step SEGS 0xb6040 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5db0 : FPB.inl_step SEGS 0xb5dec 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6870 : FPB.inl_step SEGS 0xb68ac 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b687c : FPB.inl_step SEGS 0xb68b8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b68a4 : FPB.inl_step SEGS 0xb68e0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6994 : FPB.inl_step SEGS 0xb69d0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6998 : FPB.inl_step SEGS 0xb69d4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b6968 : FPB.inl_step SEGS 0xb69a4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b69a8 : FPB.inl_step SEGS 0xb69e4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e94 : FPB.inl_step SEGS 0xb5ed0 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e98 : FPB.inl_step SEGS 0xb5ed4 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b5e9c : FPB.inl_step SEGS 0xb5ed8 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7588 : FPB.inl_step SEGS 0xb75c4 4 [11%nat].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b783c : FPB.inl_step SEGS 0xb7878 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b79c8 : FPB.inl_step SEGS 0xb7a04 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b78d4 : FPB.inl_step SEGS 0xb7910 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7c24 : FPB.inl_step SEGS 0xb7c60 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_b7e20 : FPB.inl_step SEGS 0xb7e5c 4 [].   (* [comment removed for export] *)
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm6FpSites.
(* [comment removed for export] *)
