(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
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
Lemma img_afeb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 726248) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 213368)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 749656) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 749664) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 213628)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 749672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 631940)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 749680) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 634272)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 749688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750016) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 827120)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 959048)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 959040)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5ba0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 726256)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5ba8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750048) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 726248)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5bb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 750056) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 959024)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b6ea8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 754912) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b6ed0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 754944) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 958424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 958440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 958448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8c88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 959032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8cb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 959072) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8cc8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 959096) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
