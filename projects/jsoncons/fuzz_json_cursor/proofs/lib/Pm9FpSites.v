(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv FpBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module Pm9FpSites.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Lemma site_9a884 : FPB.inl_step SEGS 0x9a8cc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a888 : FPB.inl_step SEGS 0x9a8d0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a954 : FPB.inl_step SEGS 0x9a99c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a9c0 : FPB.inl_step SEGS 0x9aa08 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9a9c4 : FPB.inl_step SEGS 0x9aa0c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9aa38 : FPB.inl_step SEGS 0x9aa80 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9ab78 : FPB.inl_step SEGS 0x9abc0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9ab7c : FPB.inl_step SEGS 0x9abc4 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_9ab84 : FPB.inl_step SEGS 0x9abcc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_133ea4 : FPB.inl_step SEGS 0x133eec 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_134034 : FPB.inl_step SEGS 0x13407c 4 [11%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_139a18 : FPB.inl_step SEGS 0x139a54 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13a340 : FPB.inl_step SEGS 0x13a37c 4 [10%nat].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13a370 : FPB.inl_step SEGS 0x13a3ac 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13adac : FPB.inl_step SEGS 0x13ade8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13adc4 : FPB.inl_step SEGS 0x13ae00 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13ae24 : FPB.inl_step SEGS 0x13ae60 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13ae28 : FPB.inl_step SEGS 0x13ae64 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13ade4 : FPB.inl_step SEGS 0x13ae20 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_13adfc : FPB.inl_step SEGS 0x13ae38 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142e24 : FPB.inl_step SEGS 0x142e60 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142e28 : FPB.inl_step SEGS 0x142e64 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142e2c : FPB.inl_step SEGS 0x142e68 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142ecc : FPB.inl_step SEGS 0x142f08 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142f44 : FPB.inl_step SEGS 0x142f80 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141d94 : FPB.inl_step SEGS 0x141dd0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141d9c : FPB.inl_step SEGS 0x141dd8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141da0 : FPB.inl_step SEGS 0x141ddc 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141b4c : FPB.inl_step SEGS 0x141b88 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14260c : FPB.inl_step SEGS 0x142648 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142618 : FPB.inl_step SEGS 0x142654 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142640 : FPB.inl_step SEGS 0x14267c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142730 : FPB.inl_step SEGS 0x14276c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142734 : FPB.inl_step SEGS 0x142770 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142704 : FPB.inl_step SEGS 0x142740 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_142744 : FPB.inl_step SEGS 0x142780 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141c30 : FPB.inl_step SEGS 0x141c6c 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141c34 : FPB.inl_step SEGS 0x141c70 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_141c38 : FPB.inl_step SEGS 0x141c74 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_14347c : FPB.inl_step SEGS 0x1434b8 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_143608 : FPB.inl_step SEGS 0x143644 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_143514 : FPB.inl_step SEGS 0x143550 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
Lemma site_143864 : FPB.inl_step SEGS 0x1438a0 4 [].
Proof. apply FPB.inl_step_chk; [lia | vm_compute; reflexivity]. Qed.
End Pm9FpSites.

