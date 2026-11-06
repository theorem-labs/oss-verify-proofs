(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
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
Lemma img_afeb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 720640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 212560)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a20_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744048) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744056) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 212820)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744064) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 626332)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744072) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 628664)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5a40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744080) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 821520)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 953448)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5b98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 953440)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5ba0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744432) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 720648)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5ba8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 720640)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b5bb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 744448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 953424)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b6ea8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 749304) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b6ed0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 749344) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 952824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 952840) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c88f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 952848) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8c88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 953432) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8cb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 953472) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c8cc8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 953496) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
