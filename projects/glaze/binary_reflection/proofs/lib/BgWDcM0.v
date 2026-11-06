(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon BgWDT BgWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module BgWD_A0.
Lemma cut : cut_ok 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A0.

Module BgWD_A1.
Lemma cut : cut_ok 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A1.

Module BgWD_A2.
Lemma cut : cut_ok 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A2.

Module BgWD_A3.
Lemma cut : cut_ok 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A3.

Module BgWD_A4.
Lemma cut : cut_ok 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A4.

Module BgWD_A5.
Lemma cut : cut_ok 5 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A5.

Module BgWD_A6.
Lemma cut : cut_ok 6 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End BgWD_A6.
