(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Tpl K1Dx_10 K1Dx_9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1xx_ok : payb KCm BFUELm FUELm ITm TT HS_hg11x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) 2%nat (xx) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s10xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) [(168%nat, (2%nat, HS_hr10x))] 1%nat (k1s10xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s10xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) [(168%nat, (2%nat, HS_hr10x))] 1%nat (k1s10xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f10x_ok : segb KCm BFUELm FUELm ITm TT HS_hr10x (root_class 5 ++ [(QFlen, 33554432, 67108863)]) [(199%nat, (2%nat, HS_ht10x))] 2%nat (k1f10x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1r10x_ok : segb KCm BFUELm FUELm ITm TT HS_hr10x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) [(135%nat, (2%nat, HS_hg11x))] 2%nat (k1r10x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s9xa_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) [(165%nat, (2%nat, HS_hr9x))] 1%nat (k1s9xa) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1s9xb_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) [(165%nat, (2%nat, HS_hr9x))] 1%nat (k1s9xb) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1f9x_ok : segb KCm BFUELm FUELm ITm TT HS_hr9x (root_class 5 ++ [(QFlen, 16777216, 33554431)]) [(196%nat, (2%nat, HS_ht9x))] 2%nat (k1f9x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
