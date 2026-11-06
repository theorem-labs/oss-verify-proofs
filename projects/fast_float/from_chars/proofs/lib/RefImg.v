(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Local Instance img_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_60b10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 396048) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 140596)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63c68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408680) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63c70_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 140856)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63c78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408696) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 329092)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63c80_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408704) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 331224)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63c88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63d78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 482048)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63d80_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 613976)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63d88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408968) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 613968)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63d90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 396056)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63d98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408984) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 396048)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65000_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 413696) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65010_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 413712) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95be8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 613352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95bf8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 613368) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95c00_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 613376) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95e48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 613960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95e70_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 614000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_95e88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 614024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_63da0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408992) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 613952)).
Proof. vm_refl_bv. Qed.
