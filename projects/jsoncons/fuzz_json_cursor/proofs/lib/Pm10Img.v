(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.













Lemma img_bba68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 768680) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 233048)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a18_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793176) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 233308)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793184) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 674368)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793192) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 676700)).
Proof. vm_refl_bv. Qed.

Lemma img_c1a30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_c1b90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793552) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 870624)).
Proof. vm_refl_bv. Qed.

Lemma img_c1b98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793560) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1002552)).
Proof. vm_refl_bv. Qed.

Lemma img_c1ba0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1002544)).
Proof. vm_refl_bv. Qed.

Lemma img_c1ba8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 768688)).
Proof. vm_refl_bv. Qed.

Lemma img_c1bb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 768680)).
Proof. vm_refl_bv. Qed.

Lemma img_c1bb8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793592) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1002528)).
Proof. vm_refl_bv. Qed.

Lemma img_c2ee0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 798496) 1%nat = Some ([Z_to_bv 8 0]).
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
Lemma img_c1a50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 793168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_c2ef8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 798456) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_f49c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1001928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f49d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1001944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f49e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1001952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1002536) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1002576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_f4c68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1002600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
