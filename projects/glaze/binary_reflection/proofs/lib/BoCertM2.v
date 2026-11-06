(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma cert_2 : cert_okB IT1 T902 HS_901 s1_q5 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_3 : cert_okB IT1 T903 HS_902 s1_q7 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5b : cert_okB IT1 T5bJ HS_916J s1_q17 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5c : cert_okB IT1 T0 HS_917J s1_q18r = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5d : cert_okB IT1 T0 HS_918J s1_q18g = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma cert_4b : cert_okB IT1 T11_13b HS_904 s1_q11b = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
