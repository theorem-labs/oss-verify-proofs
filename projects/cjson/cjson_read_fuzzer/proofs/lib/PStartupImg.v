(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PropExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
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
Lemma img_223e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140264) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 73800)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22470_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140400) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22478_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 74060)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22480_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 83964)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22488_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 85860)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_22490_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140432) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140480) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 210880)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140488) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 342800)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140496) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 342792)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140504) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 140272)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140512) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 140264)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_224e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 140520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 342776)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23720_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 145184) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_23730_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 145200) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_538a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342184) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_538b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342200) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_538c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342208) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_53b00_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342784) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_53b28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_53b40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 342848) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
