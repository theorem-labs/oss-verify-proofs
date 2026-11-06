(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Plain.M.loaded_segments.

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

Lemma img_10168_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 391416)).
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

Lemma img_63cd8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408872) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_63ce0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 133568)).
Proof. vm_refl_bv. Qed.

Lemma img_63ce8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 321540)).
Proof. vm_refl_bv. Qed.

Lemma img_63cf0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 323732)).
Proof. vm_refl_bv. Qed.

Lemma img_63cf8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 408904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_63e10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409184) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 482720)).
Proof. vm_refl_bv. Qed.

Lemma img_63e18_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409192) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 614648)).
Proof. vm_refl_bv. Qed.

Lemma img_63e20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 614640)).
Proof. vm_refl_bv. Qed.

Lemma img_63e28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409208) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 395520)).
Proof. vm_refl_bv. Qed.

Lemma img_63e30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409216) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 395512)).
Proof. vm_refl_bv. Qed.

Lemma img_63e38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 409224) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 614624)).
Proof. vm_refl_bv. Qed.

Lemma img_608a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 395512) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 133308)).
Proof. vm_refl_bv. Qed.

Lemma img_65140_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 414096) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.

Lemma img_75d60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 614016) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_76118_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 614632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_65150_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 414112) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.

