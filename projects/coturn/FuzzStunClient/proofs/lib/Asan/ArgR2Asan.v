(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContOAllAsan ContOAll5Asan ArgR234PlansAsan ArgR2AsanDefs ArgR2AsanCerts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma pay_5 : class_pay_ok 0%nat (root_class 2) (subst_holes (rs_of HR_1) s_4) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_6 : mcoverS HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_8 : class_le (root_class 2) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma rn_9 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (C_o_asan) (RLeaf cont_o_all_asan) = true.
Proof. exact (o_leaf_ok). Qed.
Lemma rn_7 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (root_class 2) (RClass (C_o_asan) (RLeaf cont_o_all_asan)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (root_class 2) (C_o_asan) _ le_8 rn_9). Qed.
Lemma rf_10 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_1 (root_class 2) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_1 (root_class 2) 3%nat (RClass (C_o_asan) (RLeaf cont_o_all_asan)) _ (cont_o_all_asan_s) TO_asan eq_refl rn_7 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_1 (root_class 2))). Qed.
Lemma nd_2 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 2) (MPreS 0%nat pfx_o2a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 2) 0%nat pfx_o2a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] _ eq_refl c_3 pay_5 covs_6 rf_10). Qed.
Definition TREE2 : mtree := (MPreS 0%nat pfx_o2a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]).
Lemma TREE2_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 2) TREE2 = true.
Proof. exact nd_2. Qed.
