(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain StartupHSAsan MainHSAsan MainItab ArgFragsAsan ArgFragsDirAsan Main_dir_r01 Main_dir_r2 K0TailAll CertRoot4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)


Lemma dir_r01_h0_shape_ok : class_pay_ok 0 C_dir_r01_h0 s_dir_r01_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dir_r01_h0_leaf : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (mcase_lo (HSA HS_main 0) e_r 4046) C_dir_r01_h0 (MLeaf 0 (main_dir_r01)) = true.
Proof. exact (mtree_ok_leafP KCm BFUELm FUELm ITm TT_r5 0%nat 0%nat (mcase_lo (HSA HS_main 0) e_r 4046) C_dir_r01_h0 0%nat (main_dir_r01) s_dir_r01_h0 eq_refl dir_r01_h0_ok dir_r01_h0_shape_ok). Qed.
Lemma dir_r2_h0_shape_ok : class_pay_ok 0 C_dir_r2_h0 s_dir_r2_h0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dir_r2_h0_leaf : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (mcase_hi (HSA HS_main 0) e_r 4046) C_dir_r2_h0 (MLeaf 0 (main_dir_r2)) = true.
Proof. exact (mtree_ok_leafP KCm BFUELm FUELm ITm TT_r5 0%nat 0%nat (mcase_hi (HSA HS_main 0) e_r 4046) C_dir_r2_h0 0%nat (main_dir_r2) s_dir_r2_h0 eq_refl dir_r2_h0_ok dir_r2_h0_shape_ok). Qed.

(* [comment removed for export] *)
Definition T_h0_r4 : mtree := MCase e_r 4046 (MLeaf 0 main_dir_r01) (MLeaf 0 main_dir_r2).
Lemma T_h0_r4_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (HSA HS_main 0) (root_class 4) T_h0_r4 = true.
Proof. apply mtree_ok_case; [reflexivity | exact dir_r01_h0_leaf | exact dir_r2_h0_leaf]. Qed.

