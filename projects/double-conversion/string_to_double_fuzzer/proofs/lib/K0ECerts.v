(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab ArgFragsAsan PlanForms K0HS_p5 K0E_empty K0E_short K0E_ovra K0E_ovrb K0TailAll.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)

Definition C_K0E_empty : class := ((root_class 5 ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, QMIN, 0)]).
Lemma K0E_empty_ok : payb KCm BFUELm FUELm ITm TT_r5 HS_p5 C_K0E_empty 2%nat K0E_empty.err_empty = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition C_K0E_short : class := [(QLook,4,4); (QFlen,1,5)].
Lemma K0E_short_ok : payb KCm BFUELm FUELm ITm TT_r5 HS_p5 C_K0E_short 2%nat K0E_short.err_short = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition C_K0E_ovra : class := [(QLook,4,4); (QFlen,6,64); (QRoom,QMIN,(-1))].
Lemma K0E_ovra_ok : payb KCm BFUELm FUELm ITm TT_r5 HS_p5 C_K0E_ovra 2%nat K0E_ovra.err_ovra = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition C_K0E_ovrb : class := [(QLook,4,4); (QFlen,65,65535); (QRoom,QMIN,(-1))].
Lemma K0E_ovrb_ok : payb KCm BFUELm FUELm ITm TT_r5 HS_p5 C_K0E_ovrb 2%nat K0E_ovrb.err_ovrb = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

