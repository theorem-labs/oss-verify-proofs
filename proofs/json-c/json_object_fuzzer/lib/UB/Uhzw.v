(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.

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

Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 7)).
Proof. vm_refl_bv. Qed.

Lemma img_10168_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 398976)).
Proof. vm_refl_bv. Qed.

Lemma img_10178_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_10180_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
Proof. vm_refl_bv. Qed.

Lemma img_10188_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
Proof. vm_refl_bv. Qed.

Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.

Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.

Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.

Lemma img_10228_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66088) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.

Lemma img_10270_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66160) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.

Lemma img_63cd8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 415856) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_63ce0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 415864) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 134020)).
Proof. vm_refl_bv. Qed.

Lemma img_63ce8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 415872) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 329100)).
Proof. vm_refl_bv. Qed.

Lemma img_63cf0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 415880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 331292)).
Proof. vm_refl_bv. Qed.

Lemma img_63cf8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 415888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_63e10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 490288)).
Proof. vm_refl_bv. Qed.

Lemma img_63e18_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416176) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 622216)).
Proof. vm_refl_bv. Qed.

Lemma img_63e20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416184) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 622208)).
Proof. vm_refl_bv. Qed.

Lemma img_63e28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416192) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403080)).
Proof. vm_refl_bv. Qed.

Lemma img_63e30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 403072)).
Proof. vm_refl_bv. Qed.

Lemma img_63e38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 416208) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 622192)).
Proof. vm_refl_bv. Qed.

Lemma img_608a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 403072) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 133760)).
Proof. vm_refl_bv. Qed.

Lemma img_65140_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 421656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.

Lemma img_75d60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 621584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_76118_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 622200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_65150_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 421680) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.

