(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JcM1.BgB2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma b2j_cert_ML_22 : cert_stmt ML 22.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_40 : cert_stmt ML 40.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_50 : cert_stmt ML 50.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_74 : cert_stmt ML 74.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_1 : cert_stmt ML 1.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_6 : cert_stmt ML 6.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_52 : cert_stmt ML 52.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_68 : cert_stmt ML 68.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_70 : cert_stmt ML 70.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_102 : cert_stmt ML 102.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_0 : cert_stmt ML 0.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_2 : cert_stmt ML 2.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_3 : cert_stmt ML 3.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_4 : cert_stmt ML 4.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_56 : cert_stmt ML 56.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_58 : cert_stmt ML 58.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_92 : cert_stmt ML 92.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_98 : cert_stmt ML 98.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_5 : cert_stmt ML 5.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_8 : cert_stmt ML 8.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_10 : cert_stmt ML 10.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_42 : cert_stmt ML 42.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_48 : cert_stmt ML 48.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_54 : cert_stmt ML 54.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_78 : cert_stmt ML 78.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_80 : cert_stmt ML 80.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_90 : cert_stmt ML 90.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_96 : cert_stmt ML 96.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_100 : cert_stmt ML 100.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_76 : cert_stmt ML 76.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_88 : cert_stmt ML 88.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_94 : cert_stmt ML 94.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_ML_126 : cert_stmt ML 126.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_11 : cert_stmt MS 11.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_69 : cert_stmt MS 69.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_13 : cert_stmt MS 13.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_3 : cert_stmt MS 3.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_4 : cert_stmt MS 4.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_6 : cert_stmt MS 6.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_27 : cert_stmt MS 27.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_51 : cert_stmt MS 51.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_49 : cert_stmt MS 49.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_63 : cert_stmt MS 63.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_0 : cert_stmt MS 0.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_18 : cert_stmt MS 18.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_57 : cert_stmt MS 57.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_72 : cert_stmt MS 72.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_2 : cert_stmt MS 2.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_7 : cert_stmt MS 7.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_9 : cert_stmt MS 9.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_20 : cert_stmt MS 20.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_24 : cert_stmt MS 24.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_47 : cert_stmt MS 47.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_55 : cert_stmt MS 55.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_125 : cert_stmt MS 125.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_5 : cert_stmt MS 5.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_30 : cert_stmt MS 30.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_38 : cert_stmt MS 38.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_44 : cert_stmt MS 44.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_46 : cert_stmt MS 46.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_66 : cert_stmt MS 66.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_79 : cert_stmt MS 79.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_cert_MS_89 : cert_stmt MS 89.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
