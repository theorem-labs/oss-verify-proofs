(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StepTac.
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
Lemma img_c0688_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 802992) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 237676)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6640_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827496) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6648_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827504) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 237936)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6650_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827512) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 708520)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6658_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 710852)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6660_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827528) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 905024)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1036952)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1036944)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 803000)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 802992)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c67f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 827936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1036928)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c7af0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 832792) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c7b10_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 832832) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d9528_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1036328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d9538_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1036344) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d9540_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1036352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d98d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1036936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d9900_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1036976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d9918_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1037000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
