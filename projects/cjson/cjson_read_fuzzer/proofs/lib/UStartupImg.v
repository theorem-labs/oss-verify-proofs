(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PropExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
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
Lemma img_23530_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 77928)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_235b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_235c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144832) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 78188)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_235c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144840) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 88384)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_235d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144848) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 90280)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_235d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144856) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23608_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 215296)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23610_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 347216)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23618_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 347208)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23620_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 144696)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23628_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 144688)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23630_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 144944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 347192)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_24868_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 149608) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_24870_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 149616) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_549e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 346600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_549f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 346616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_54a00_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 346624) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_54c40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 347200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_54c68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 347240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_54c80_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 347264) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
