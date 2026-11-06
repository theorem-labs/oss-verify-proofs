(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon GaWDT GaWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GaWD_A7.
Lemma cut : cut_ok 7 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A7.

Module GaWD_A8.
Lemma cut : cut_ok 8 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A8.

Module GaWD_A9.
Lemma cut : cut_ok 9 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A9.

Module GaWD_A10.
Lemma cut : cut_ok 10 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A10.

Module GaWD_A11.
Lemma cut : cut_ok 11 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A11.

Module GaWD_A12.
Lemma cut : cut_ok 12 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A12.

Module GaWD_A13.
Lemma cut : cut_ok 13 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaWD_A13.
