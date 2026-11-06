(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth ArgFragsBoth PlanFormsBoth BK0HS_p5 BK0S_sec BK0S_sec_js.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Definition C_K0S_sec : class := [(QLook,4,4); (QFlen,65,65535); (QRoom,64513,65529)].
Lemma K0S_sec_ok : payb KCm BFUELm FUELm BITm TT HS_p5 C_K0S_sec 2%nat (BK0S_sec.sec BK0S_sec_js.JSraw_secj_2 BK0S_sec_js.JSraw_secj_10 BK0S_sec_js.JSraw_secj_8 BK0S_sec_js.JSraw_secj_11) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition T_sec : mtree := MLeaf 2%nat (BK0S_sec.sec BK0S_sec_js.JSraw_secj_2 BK0S_sec_js.JSraw_secj_10 BK0S_sec_js.JSraw_secj_8 BK0S_sec_js.JSraw_secj_11).
Lemma T_sec_ok : mtree_ok KCm BFUELm FUELm BITm TT 0%nat 2%nat HS_p5 C_K0S_sec T_sec = true.
Proof. exact (payb_leaf KCm BFUELm FUELm BITm TT 0%nat 2%nat HS_p5 C_K0S_sec 2%nat (BK0S_sec.sec BK0S_sec_js.JSraw_secj_2 BK0S_sec_js.JSraw_secj_10 BK0S_sec_js.JSraw_secj_8 BK0S_sec_js.JSraw_secj_11) eq_refl K0S_sec_ok). Qed.
Lemma T_sec_lvl : lvl_shape T_sec = LNode 2%nat.
Proof. reflexivity. Qed.
End TTS.
