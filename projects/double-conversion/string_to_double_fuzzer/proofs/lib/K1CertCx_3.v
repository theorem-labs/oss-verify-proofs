(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Tpl K1Dx_5 K1Dx_6 K1Dx_4 K1Dx_3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1r5x_ok : segb KCm BFUELm FUELm ITm TT HS_hr5x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) [(120%nat, (1%nat, HS_hg6x))] 1%nat (k1r5x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s4xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) [(150%nat, (2%nat, HS_hr4x))] 1%nat (k1s4xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s4xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) [(150%nat, (2%nat, HS_hr4x))] 1%nat (k1s4xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f4x_ok : segb KCm BFUELm FUELm ITm TT HS_hr4x (root_class 5 ++ [(QFlen, 524288, 1048575)]) [(181%nat, (2%nat, HS_ht4x))] 2%nat (k1f4x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1r4x_ok : segb KCm BFUELm FUELm ITm TT HS_hr4x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) [(117%nat, (1%nat, HS_hg5x))] 1%nat (k1r4x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s3xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) [(147%nat, (2%nat, HS_hr3x))] 1%nat (k1s3xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s3xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) [(147%nat, (2%nat, HS_hr3x))] 1%nat (k1s3xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f3x_ok : segb KCm BFUELm FUELm ITm TT HS_hr3x (root_class 5 ++ [(QFlen, 262144, 524287)]) [(178%nat, (2%nat, HS_ht3x))] 2%nat (k1f3x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
