(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import StreamSim.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Abbreviation RSEGS := Plain.M.loaded_segments.
Lemma wseg_1 : wseg_ok RSEGS (Z_to_bv 64 0x20000) 204800 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_0 : wseg_ok RSEGS (0x20000 : word) 204800%nat = true.
Proof.
  assert (EA : (0x20000 : word) = (Z_to_bv 64 0x20000)) by (apply bv_eq; reflexivity).
  assert (EN : (204800%nat)%nat = (204800)%nat) by reflexivity.
  try rewrite EA; try rewrite EN. exact wseg_1.
Qed.
Lemma wseg_2 : wseg_ok RSEGS (Z_to_bv 64 0x20000) 0x32000 = true.
Proof.
  assert (EA : (Z_to_bv 64 0x20000) = (Z_to_bv 64 0x20000)) by (apply bv_eq; reflexivity).
  assert (EN : (0x32000)%nat = (204800)%nat) by reflexivity.
  try rewrite EA; try rewrite EN. exact wseg_1.
Qed.
