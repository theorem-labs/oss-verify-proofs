(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon GaFA GaFAPlanDef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GaFA_A0.
Lemma cut : cut_ok 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaFA_A0.

Module GaFA_A1.
Lemma cut : cut_ok 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaFA_A1.

Module GaFA_A2.
Lemma cut : cut_ok 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End GaFA_A2.
