(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Ubsan.M.loaded_segments.













Lemma img_bba68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 776440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 233800)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a18_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 800936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 234060)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 800944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 681972)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 800952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 684304)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 800960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_c1b90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 878384)).
Proof. vm_refl_bv. Qed.

Lemma img_c1b98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1010312)).
Proof. vm_refl_bv. Qed.

Lemma img_c1ba0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1010304)).
Proof. vm_refl_bv. Qed.

Lemma img_c1ba8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 776448)).
Proof. vm_refl_bv. Qed.

Lemma img_c1bb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801344) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 776440)).
Proof. vm_refl_bv. Qed.

Lemma img_c1bb8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 801352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1010288)).
Proof. vm_refl_bv. Qed.

Lemma img_c2ee0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 806256) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.

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
Lemma img_c1a50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 800928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_c2ef8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 806216) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_f49c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1009688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f49d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1009704) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f49e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1009712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1010296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1010336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1010360) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
