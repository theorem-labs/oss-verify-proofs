(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_5bcd8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 376024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131652)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_5efa0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131912)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5efa8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 308916)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5efb0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 311048)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5efb8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389048) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 462440)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 594368)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 594360)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 376032)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389344) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 376024)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_5f0e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 594344)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_60370_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 394096) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Lemma img_5ef98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 389016) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_60358_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 394072) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_90f50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 593744) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_90f60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 593760) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_90f68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 593768) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_911b0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 594352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_911d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 594392) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_911f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 594416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
