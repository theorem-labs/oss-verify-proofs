(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth K1BTpl K1BDx_3 K1BDx_4 K1BDx_2 K1BD0 K1BDx_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1r3x_ok : segb KCm BFUELm FUELm BITm TT HS_hr3x (root_class 5 ++ [(QFlen, 524288, QMAX)]) [(114%nat, (1%nat, HS_hg4x))] 1%nat (k1r3x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s2xa_ok : segb KCm BFUELm FUELm BITm TT (mcase_lo HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) [(144%nat, (2%nat, HS_hr2x))] 1%nat (k1s2xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s2xb_ok : segb KCm BFUELm FUELm BITm TT (mcase_hi HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) [(144%nat, (2%nat, HS_hr2x))] 1%nat (k1s2xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f2x_ok : segb KCm BFUELm FUELm BITm TT HS_hr2x (root_class 5 ++ [(QFlen, 131072, 262143)]) [(175%nat, (2%nat, HS_ht2x))] 2%nat (k1f2x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1r2x_ok : segb KCm BFUELm FUELm BITm TT HS_hr2x (root_class 5 ++ [(QFlen, 262144, QMAX)]) [(111%nat, (1%nat, HS_hg3x))] 1%nat (k1r2x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s1xa_ok : segb KCm BFUELm FUELm BITm TT (mcase_lo HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) [(141%nat, (2%nat, HS_hr1x))] 1%nat (k1s1xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s1xb_ok : segb KCm BFUELm FUELm BITm TT (mcase_hi HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) [(141%nat, (2%nat, HS_hr1x))] 1%nat (k1s1xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f1x_ok : segb KCm BFUELm FUELm BITm TT HS_hr1x (root_class 5 ++ [(QFlen, 65536, 131071)]) [(172%nat, (2%nat, HS_ht1x))] 2%nat (k1f1x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
