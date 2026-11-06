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

Module BgWF_A24.
Lemma cut : cut_ok 24 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A24.

Module BgWF_A25.
Lemma cut : cut_ok 25 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A25.

Module BgWF_A26.
Lemma cut : cut_ok 26 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A26.

Module BgWF_A27.
Lemma cut : cut_ok 27 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A27.

Module BgWF_A28.
Lemma cut : cut_ok 28 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A28.

Module BgWF_A29.
Lemma cut : cut_ok 29 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A29.

Module BgWF_A30.
Lemma cut : cut_ok 30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A30.

Module BgWF_A31.
Lemma cut : cut_ok 31 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWF_A31.
