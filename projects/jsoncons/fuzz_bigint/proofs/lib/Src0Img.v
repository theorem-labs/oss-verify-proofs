(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_5b1e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 373216) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131060)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_5e4a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386216) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131320)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e4b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386224) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 306104)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e4b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386232) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 308236)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e4c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386504) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 459624)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386512) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 591552)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 591544)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386528) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 373224)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386536) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 373216)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5e5f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386544) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 591528)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_5f870_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 391280) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
Lemma img_5e4a0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 386208) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_5f860_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 391264) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_90450_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 590928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_90460_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 590944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_90468_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 590952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_906b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 591536) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_906d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 591576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_906f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 591600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
