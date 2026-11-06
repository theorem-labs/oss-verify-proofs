(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Tpl K1Dx_9 K1Dx_10 K1Dx_8 K1Dx_7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1r9x_ok : segb KCm BFUELm FUELm ITm TT HS_hr9x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) [(132%nat, (1%nat, HS_hg10x))] 1%nat (k1r9x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s8xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) [(162%nat, (2%nat, HS_hr8x))] 1%nat (k1s8xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s8xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) [(162%nat, (2%nat, HS_hr8x))] 1%nat (k1s8xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f8x_ok : segb KCm BFUELm FUELm ITm TT HS_hr8x (root_class 5 ++ [(QFlen, 8388608, 16777215)]) [(193%nat, (2%nat, HS_ht8x))] 2%nat (k1f8x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1r8x_ok : segb KCm BFUELm FUELm ITm TT HS_hr8x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) [(129%nat, (1%nat, HS_hg9x))] 1%nat (k1r8x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s7xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) [(159%nat, (2%nat, HS_hr7x))] 1%nat (k1s7xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s7xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) [(159%nat, (2%nat, HS_hr7x))] 1%nat (k1s7xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f7x_ok : segb KCm BFUELm FUELm ITm TT HS_hr7x (root_class 5 ++ [(QFlen, 4194304, 8388607)]) [(190%nat, (2%nat, HS_ht7x))] 2%nat (k1f7x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
