(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JcM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JcM4.GaB2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma b2j_cert_ML_94 : cert_stmt ML 94.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_96 : cert_stmt ML 96.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_98 : cert_stmt ML 98.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_11 : cert_stmt MS 11.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_13 : cert_stmt MS 13.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_16 : cert_stmt MS 16.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_18 : cert_stmt MS 18.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_20 : cert_stmt MS 20.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_24 : cert_stmt MS 24.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_26 : cert_stmt MS 26.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_27 : cert_stmt MS 27.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_30 : cert_stmt MS 30.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
