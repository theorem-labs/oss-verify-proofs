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
Lemma b2j_cert_MS_4 : cert_stmt MS 4.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_5 : cert_stmt MS 5.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_6 : cert_stmt MS 6.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_7 : cert_stmt MS 7.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_9 : cert_stmt MS 9.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_10 : cert_stmt ML 10.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_22 : cert_stmt ML 22.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_40 : cert_stmt ML 40.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_42 : cert_stmt ML 42.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_48 : cert_stmt ML 48.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_50 : cert_stmt ML 50.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_52 : cert_stmt ML 52.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
