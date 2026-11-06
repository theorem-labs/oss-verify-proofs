(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StepTac.
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
Lemma img_b4020_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 737392) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 215368)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9c40_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 760976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9c48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 760984) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 215628)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9c50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 760992) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 643080)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9c58_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 645412)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9c60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761008) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9da8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 838384)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9db0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761344) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 970312)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9db8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 970304)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9dc0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761360) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 737400)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9dc8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761368) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 737392)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_b9dd0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 761376) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 970288)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_bb0c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 766232) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_bb0f0_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 766272) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_ccab8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 969688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_ccac8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 969704) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_ccad0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 969712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_cce68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 970296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_cce90_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 970336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_ccea8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 970360) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
