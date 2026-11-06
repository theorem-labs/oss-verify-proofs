(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth K1BTpl K1BDx_7 K1BDx_8 K1BDx_6 K1BDx_5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1r7x_ok : segb KCm BFUELm FUELm BITm TT HS_hr7x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) [(126%nat, (1%nat, HS_hg8x))] 1%nat (k1r7x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s6xa_ok : segb KCm BFUELm FUELm BITm TT (mcase_lo HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) [(156%nat, (2%nat, HS_hr6x))] 1%nat (k1s6xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s6xb_ok : segb KCm BFUELm FUELm BITm TT (mcase_hi HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) [(156%nat, (2%nat, HS_hr6x))] 1%nat (k1s6xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f6x_ok : segb KCm BFUELm FUELm BITm TT HS_hr6x (root_class 5 ++ [(QFlen, 2097152, 4194303)]) [(187%nat, (2%nat, HS_ht6x))] 2%nat (k1f6x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1r6x_ok : segb KCm BFUELm FUELm BITm TT HS_hr6x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) [(123%nat, (1%nat, HS_hg7x))] 1%nat (k1r6x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s5xa_ok : segb KCm BFUELm FUELm BITm TT (mcase_lo HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) [(153%nat, (2%nat, HS_hr5x))] 1%nat (k1s5xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s5xb_ok : segb KCm BFUELm FUELm BITm TT (mcase_hi HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) [(153%nat, (2%nat, HS_hr5x))] 1%nat (k1s5xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f5x_ok : segb KCm BFUELm FUELm BITm TT HS_hr5x (root_class 5 ++ [(QFlen, 1048576, 2097151)]) [(184%nat, (2%nat, HS_ht5x))] 2%nat (k1f5x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
