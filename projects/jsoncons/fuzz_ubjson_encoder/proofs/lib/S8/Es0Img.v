(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Lemma img_b24a8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 730352) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 214080)).
Proof. vm_refl_bv. Qed.

Lemma img_b80c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 753936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_b80d0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 753944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 214340)).
Proof. vm_refl_bv. Qed.

Lemma img_b80d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 753952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 636044)).
Proof. vm_refl_bv. Qed.

Lemma img_b80e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 753960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 638376)).
Proof. vm_refl_bv. Qed.

Lemma img_b80e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 753968) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_b8230_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 831344)).
Proof. vm_refl_bv. Qed.

Lemma img_b8238_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 963272)).
Proof. vm_refl_bv. Qed.

Lemma img_b8240_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 963264)).
Proof. vm_refl_bv. Qed.

Lemma img_b8248_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 730360)).
Proof. vm_refl_bv. Qed.

Lemma img_b8250_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 730352)).
Proof. vm_refl_bv. Qed.

Lemma img_b8258_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 754336) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 963248)).
Proof. vm_refl_bv. Qed.

Lemma img_b9550_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 759192) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.

Lemma img_b9570_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 759232) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.

Lemma img_caf38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 962648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_caf48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 962664) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_caf50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 962672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_cb2e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 963256) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_cb310_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 963296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

Lemma img_cb328_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 963320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
