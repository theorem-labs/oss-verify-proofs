(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_90ca8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593064) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90ca9_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593065) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cb8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593080) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cb9_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593081) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cc8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593096) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cc9_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593097) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cd8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593112) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cd9_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593113) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90ce8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593128) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90cf8_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593144) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90d08_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593160) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90d18_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593176) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_90d28_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 593192) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
