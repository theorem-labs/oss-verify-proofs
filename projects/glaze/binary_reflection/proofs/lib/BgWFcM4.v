(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon BgWFT BgWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module BgWF_A32.
Lemma cut : cut_ok 32 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A32.

Module BgWF_A33.
Lemma cut : cut_ok 33 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A33.

Module BgWF_A34.
Lemma cut : cut_ok 34 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A34.

Module BgWF_A35.
Lemma cut : cut_ok 35 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A35.

Module BgWF_A36.
Lemma cut : cut_ok 36 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A36.

Module BgWF_A37.
Lemma cut : cut_ok 37 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A37.

Module BgWF_A38.
Lemma cut : cut_ok 38 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A38.
