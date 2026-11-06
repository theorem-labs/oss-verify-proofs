(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Dx_10 K1G3Sx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition C_G3x : class := [(QLook,4,4); (QFlen,1048576,67108863); (QRoom,1040385,67108857)].
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1g3tx_ok : payb KCm BFUELm FUELm ITm TT HS_g3x C_G3x 3%nat ((k1p_hi10x_tail JSraw_xj_g3x_31)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
