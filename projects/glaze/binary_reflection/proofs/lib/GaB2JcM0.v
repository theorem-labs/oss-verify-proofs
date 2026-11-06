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
Lemma b2j_cert_ML_0 : cert_stmt ML 0.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_1 : cert_stmt ML 1.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_2 : cert_stmt ML 2.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_3 : cert_stmt ML 3.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_4 : cert_stmt ML 4.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_5 : cert_stmt ML 5.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_6 : cert_stmt ML 6.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_8 : cert_stmt ML 8.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_0 : cert_stmt MS 0.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_1 : cert_stmt MS 1.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_2 : cert_stmt MS 2.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_3 : cert_stmt MS 3.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
