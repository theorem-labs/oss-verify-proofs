(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms MainHSAsan ArgFragsAsan K0HS_p5 K0HS_jc K0Defs K0TailDefs K0TailAll K0PreP5 K0PreJcA K0PreJcB K0JS_jca_al K0JS_jcb_al.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition K0_C_FILE : class := (root_class 5 ++ [(QFlen, QMIN, 65535)]).
Definition K0_C_A : class := [(QLook,4,4); (QFlen,6,64); (QRoom,1,58)].
Definition K0_C_B : class := [(QLook,4,4); (QFlen,65,65535); (QRoom,1,64512)].
Definition K0_HT_p5 : list (nat * (nat * acs)) := [(42%nat, (2%nat, HS_p5))].
Definition K0_HT_jc : list (nat * (nat * acs)) := [(52%nat, (2%nat, HS_jc))].
Lemma pre_p5f_ok : segb KCm BFUELm FUELm ITm TT_r5 (HSA HS_main 0) K0_C_FILE K0_HT_p5 0 pre_p5f = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma pre_jcaf_ok : segb KCm BFUELm FUELm ITm TT HS_p5 K0_C_A K0_HT_jc 2 (pre_jcaf JSraw_jca_al_2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma pre_jcbf_ok : segb KCm BFUELm FUELm ITm TT HS_p5 K0_C_B K0_HT_jc 2 (pre_jcbf JSraw_jcb_al_2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End TTS.
