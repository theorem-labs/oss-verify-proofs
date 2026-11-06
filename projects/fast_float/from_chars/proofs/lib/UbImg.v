(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Local Instance img_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Lemma img_628c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 403656) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 141256)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65a20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65a28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 141516)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65a30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 336700)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65a38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 338832)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65a40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416560) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 489664)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 621592)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 621584)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403664)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416592) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403656)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_66db8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 421304) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_66dd0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 421328) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_979a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 620968) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_979b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 620984) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_979c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 620992) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_97c08_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 621576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_97c30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 621616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_97c48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 621640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_65b58_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 621568)).
Proof. vm_refl_bv. Qed.
