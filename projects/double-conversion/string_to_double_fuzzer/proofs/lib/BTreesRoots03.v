(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain StartupHSBoth MainHSBoth MainItabBoth ArgFragsBoth BMainErrPlans BCertRoots03_0 BCertRoots03_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section TTS.
Variable TT : nat -> option (acs * plan * shape).   (* [comment removed for export] *)


Lemma u0_0_0_h0_shape_ok : class_shape_ok C_u0_0_0_h0 s_u0_0_0_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_0_0_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_0_0_h0 (MLeaf 0 (plan_u0_0_0_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_0_0_h0 (plan_u0_0_0_both) s_u0_0_0_h0 (u0_0_0_h0_ok TT) u0_0_0_h0_shape_ok). Qed.
Lemma u0_1_63_h0_shape_ok : class_shape_ok C_u0_1_63_h0 s_u0_1_63_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_1_63_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_1_63_h0 (MLeaf 0 (plan_u0_1_63_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_1_63_h0 (plan_u0_1_63_both) s_u0_1_63_h0 (u0_1_63_h0_ok TT) u0_1_63_h0_shape_ok). Qed.
Lemma u0_64_64_h0_shape_ok : class_shape_ok C_u0_64_64_h0 s_u0_64_64_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_64_64_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_64_64_h0 (MLeaf 0 (plan_u0_64_64_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_64_64_h0 (plan_u0_64_64_both) s_u0_64_64_h0 (u0_64_64_h0_ok TT) u0_64_64_h0_shape_ok). Qed.
Lemma u0_65_66_h0_shape_ok : class_shape_ok C_u0_65_66_h0 s_u0_65_66_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_65_66_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_65_66_h0 (MLeaf 0 (plan_u0_65_66_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_65_66_h0 (plan_u0_65_66_both) s_u0_65_66_h0 (u0_65_66_h0_ok TT) u0_65_66_h0_shape_ok). Qed.
Lemma u0_67_73_h0_shape_ok : class_shape_ok C_u0_67_73_h0 s_u0_67_73_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_67_73_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_67_73_h0 (MLeaf 0 (plan_u0_67_73_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_67_73_h0 (plan_u0_67_73_both) s_u0_67_73_h0 (u0_67_73_h0_ok TT) u0_67_73_h0_shape_ok). Qed.
Lemma u0_74_inf_h0_shape_ok : class_shape_ok C_u0_74_inf_h0 s_u0_74_inf_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u0_74_inf_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u0_74_inf_h0 (MLeaf 0 (plan_u0_74_inf_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u0_74_inf_h0 (plan_u0_74_inf_both) s_u0_74_inf_h0 (u0_74_inf_h0_ok TT) u0_74_inf_h0_shape_ok). Qed.
Lemma u1_0_0_h0_shape_ok : class_shape_ok C_u1_0_0_h0 s_u1_0_0_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_0_0_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_0_0_h0 (MLeaf 0 (plan_u1_0_0_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_0_0_h0 (plan_u1_0_0_both) s_u1_0_0_h0 (u1_0_0_h0_ok TT) u1_0_0_h0_shape_ok). Qed.
Lemma u1_1_63_h0_shape_ok : class_shape_ok C_u1_1_63_h0 s_u1_1_63_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_1_63_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_1_63_h0 (MLeaf 0 (plan_u1_1_63_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_1_63_h0 (plan_u1_1_63_both) s_u1_1_63_h0 (u1_1_63_h0_ok TT) u1_1_63_h0_shape_ok). Qed.
Lemma u1_64_64_h0_shape_ok : class_shape_ok C_u1_64_64_h0 s_u1_64_64_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_64_64_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_64_64_h0 (MLeaf 0 (plan_u1_64_64_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_64_64_h0 (plan_u1_64_64_both) s_u1_64_64_h0 (u1_64_64_h0_ok TT) u1_64_64_h0_shape_ok). Qed.
Lemma u1_65_66_h0_shape_ok : class_shape_ok C_u1_65_66_h0 s_u1_65_66_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_65_66_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_65_66_h0 (MLeaf 0 (plan_u1_65_66_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_65_66_h0 (plan_u1_65_66_both) s_u1_65_66_h0 (u1_65_66_h0_ok TT) u1_65_66_h0_shape_ok). Qed.
Lemma u1_67_73_h0_shape_ok : class_shape_ok C_u1_67_73_h0 s_u1_67_73_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_67_73_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_67_73_h0 (MLeaf 0 (plan_u1_67_73_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_67_73_h0 (plan_u1_67_73_both) s_u1_67_73_h0 (u1_67_73_h0_ok TT) u1_67_73_h0_shape_ok). Qed.
Lemma u1_74_inf_h0_shape_ok : class_shape_ok C_u1_74_inf_h0 s_u1_74_inf_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u1_74_inf_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_u1_74_inf_h0 (MLeaf 0 (plan_u1_74_inf_both)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_74_inf_h0 (plan_u1_74_inf_both) s_u1_74_inf_h0 (u1_74_inf_h0_ok TT) u1_74_inf_h0_shape_ok). Qed.
Lemma toolong_h0_shape_ok : class_shape_ok C_toolong_h0 s_toolong_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma toolong_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_toolong_h0 (MLeaf 0 (main_toolong)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_toolong_h0 (main_toolong) s_toolong_h0 (toolong_h0_ok TT) toolong_h0_shape_ok). Qed.
Lemma noent_0_h0_shape_ok : class_shape_ok C_noent_0_h0 s_noent_0_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noent_0_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_noent_0_h0 (MLeaf 0 (main_noent0)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_0_h0 (main_noent0) s_noent_0_h0 (noent_0_h0_ok TT) noent_0_h0_shape_ok). Qed.
Lemma noent_1_62_h0_shape_ok : class_shape_ok C_noent_1_62_h0 s_noent_1_62_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noent_1_62_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_noent_1_62_h0 (MLeaf 0 (main_noent_1_62)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_1_62_h0 (main_noent_1_62) s_noent_1_62_h0 (noent_1_62_h0_ok TT) noent_1_62_h0_shape_ok). Qed.
Lemma noent_63_63_h0_shape_ok : class_shape_ok C_noent_63_63_h0 s_noent_63_63_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noent_63_63_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_noent_63_63_h0 (MLeaf 0 (main_noent_63_63)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_63_63_h0 (main_noent_63_63) s_noent_63_63_h0 (noent_63_63_h0_ok TT) noent_63_63_h0_shape_ok). Qed.
Lemma noent_64_64_h0_shape_ok : class_shape_ok C_noent_64_64_h0 s_noent_64_64_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noent_64_64_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_noent_64_64_h0 (MLeaf 0 (main_noent_64_64)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_64_64_h0 (main_noent_64_64) s_noent_64_64_h0 (noent_64_64_h0_ok TT) noent_64_64_h0_shape_ok). Qed.
Lemma noent_65_4095_h0_shape_ok : class_shape_ok C_noent_65_4095_h0 s_noent_65_4095_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noent_65_4095_h0_leaf : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) C_noent_65_4095_h0 (MLeaf 0 (main_noent_65_4095)) = true.
Proof. exact (mtree_ok_leaf0 HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_65_4095_h0 (main_noent_65_4095) s_noent_65_4095_h0 (noent_65_4095_h0_ok TT) noent_65_4095_h0_shape_ok). Qed.

(* [comment removed for export] *)
Definition T_h0_r0 : mtree := MSplit QL0 0 (MLeaf 0 plan_u0_0_0_both) (MSplit QL0 63 (MLeaf 0 plan_u0_1_63_both) (MSplit QL0 64 (MLeaf 0 plan_u0_64_64_both) (MSplit QL0 66 (MLeaf 0 plan_u0_65_66_both) (MSplit QL0 73 (MLeaf 0 plan_u0_67_73_both) (MLeaf 0 plan_u0_74_inf_both))))).
Lemma T_h0_r0_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) (root_class 0) T_h0_r0 = true.
Proof. apply mtree_ok_split; [exact u0_0_0_h0_leaf | apply mtree_ok_split; [exact u0_1_63_h0_leaf | apply mtree_ok_split; [exact u0_64_64_h0_leaf | apply mtree_ok_split; [exact u0_65_66_h0_leaf | apply mtree_ok_split; [exact u0_67_73_h0_leaf | exact u0_74_inf_h0_leaf]]]]]. Qed.

(* [comment removed for export] *)
Definition T_h0_r1 : mtree := MSplit QL0 0 (MLeaf 0 plan_u1_0_0_both) (MSplit QL0 63 (MLeaf 0 plan_u1_1_63_both) (MSplit QL0 64 (MLeaf 0 plan_u1_64_64_both) (MSplit QL0 66 (MLeaf 0 plan_u1_65_66_both) (MSplit QL0 73 (MLeaf 0 plan_u1_67_73_both) (MLeaf 0 plan_u1_74_inf_both))))).
Lemma T_h0_r1_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) (root_class 1) T_h0_r1 = true.
Proof. apply mtree_ok_split; [exact u1_0_0_h0_leaf | apply mtree_ok_split; [exact u1_1_63_h0_leaf | apply mtree_ok_split; [exact u1_64_64_h0_leaf | apply mtree_ok_split; [exact u1_65_66_h0_leaf | apply mtree_ok_split; [exact u1_67_73_h0_leaf | exact u1_74_inf_h0_leaf]]]]]. Qed.

(* [comment removed for export] *)
Definition T_h0_r2 : mtree := MLeaf 0 main_toolong.
Lemma T_h0_r2_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) (root_class 2) T_h0_r2 = true.
Proof. exact toolong_h0_leaf. Qed.

(* [comment removed for export] *)
Definition T_h0_r3 : mtree := MSplit QL1 0 (MLeaf 0 main_noent0) (MSplit QL1 62 (MLeaf 0 main_noent_1_62) (MSplit QL1 63 (MLeaf 0 main_noent_63_63) (MSplit QL1 64 (MLeaf 0 main_noent_64_64) (MLeaf 0 main_noent_65_4095)))).
Lemma T_h0_r3_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) (root_class 3) T_h0_r3 = true.
Proof. apply mtree_ok_split; [exact noent_0_h0_leaf | apply mtree_ok_split; [exact noent_1_62_h0_leaf | apply mtree_ok_split; [exact noent_63_63_h0_leaf | apply mtree_ok_split; [exact noent_64_64_h0_leaf | exact noent_65_4095_h0_leaf]]]]. Qed.

End TTS.