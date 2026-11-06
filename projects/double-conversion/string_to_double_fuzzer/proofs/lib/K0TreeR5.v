(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms MainHSAsan K0HS_p5 K0Defs K0TailAll K0CertFront K0BCerts K0SCerts K0TreeTop K1Tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition T_K0c : mtree := T_K0 T_batch T_sec.
Lemma T_K0c_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (HSA HS_main 0) K0_C_FILE T_K0c = true.
Proof. exact (T_K0_ok T_batch T_batch_ok T_batch_lvl T_sec (T_sec_ok TT_r5)). Qed.
Definition T_r5 : mtree := MSplit QFlen 65535 T_K0c T_K1.
Lemma T_r5_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (HSA HS_main 0) (root_class 5) T_r5 = true.

Proof. first [ exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 0%nat (HSA HS_main 0) (root_class 5) QFlen 65535 T_K0c T_K1 T_K0c_ok (T_K1_ok TT_r5))
             | exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 0%nat (HSA HS_main 0) (root_class 5) QFlen 65535 T_K0c T_K1 T_K0c_ok T_K1_ok) ]. Qed.
