(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContOAllAsan ContOAll5Asan ArgR234PlansAsan ArgR3AsanDefs ArgR3AsanCerts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma pay_6 : class_pay_ok 0%nat ((root_class 3) ++ [(QL1, QMIN, 0)]) (subst_holes (rs_of HR_1) s_5) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_7 : mcoverS HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_9 : class_le ((root_class 3) ++ [(QL1, QMIN, 0)]) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_16 : class_pay_ok 0%nat (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) (subst_holes (rs_of HR_1) s_15) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_18 : class_le (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_24 : class_pay_ok 0%nat ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) (subst_holes (rs_of HR_1) s_23) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_26 : class_le ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_31 : class_pay_ok 0%nat ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) (subst_holes (rs_of HR_1) s_30) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_33 : class_le ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma rn_10 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (C_o_asan) (RLeaf cont_o_all_asan) = true.
Proof. exact (o_leaf_ok). Qed.
Lemma rn_8 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((root_class 3) ++ [(QL1, QMIN, 0)]) (RClass (C_o_asan) (RLeaf cont_o_all_asan)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((root_class 3) ++ [(QL1, QMIN, 0)]) (C_o_asan) _ le_9 rn_10). Qed.
Lemma rf_11 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_1 ((root_class 3) ++ [(QL1, QMIN, 0)]) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_1 ((root_class 3) ++ [(QL1, QMIN, 0)]) 3%nat (RClass (C_o_asan) (RLeaf cont_o_all_asan)) _ (cont_o_all_asan_s) TO_asan eq_refl rn_8 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_1 ((root_class 3) ++ [(QL1, QMIN, 0)]))). Qed.
Lemma nd_3 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((root_class 3) ++ [(QL1, QMIN, 0)]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((root_class 3) ++ [(QL1, QMIN, 0)]) 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] _ eq_refl c_4 pay_6 covs_7 rf_11). Qed.
Lemma rn_17 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) (RClass (C_o_asan) (RLeaf cont_o_all_asan)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) (C_o_asan) _ le_18 rn_10). Qed.
Lemma rf_19 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_1 (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_1 (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) 3%nat (RClass (C_o_asan) (RLeaf cont_o_all_asan)) _ (cont_o_all_asan_s) TO_asan eq_refl rn_17 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_1 (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]))). Qed.
Lemma nd_13 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]) 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] _ eq_refl c_14 pay_16 covs_7 rf_19). Qed.
Lemma rn_25 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) (RClass (C_o_asan) (RLeaf cont_o_all_asan)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) (C_o_asan) _ le_26 rn_10). Qed.
Lemma rf_27 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) 3%nat (RClass (C_o_asan) (RLeaf cont_o_all_asan)) _ (cont_o_all_asan_s) TO_asan eq_refl rn_25 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]))). Qed.
Lemma nd_21 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]) 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] _ eq_refl c_22 pay_24 covs_7 rf_27). Qed.
Lemma rn_32 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) (RClass (C_o_asan) (RLeaf cont_o_all_asan)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) (C_o_asan) _ le_33 rn_10). Qed.
Lemma rf_34 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) 3%nat (RClass (C_o_asan) (RLeaf cont_o_all_asan)) _ (cont_o_all_asan_s) TO_asan eq_refl rn_32 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_1 ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]))). Qed.
Lemma nd_28 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))] _ eq_refl c_29 pay_31 covs_7 rf_34). Qed.
Lemma nd_20 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))])) = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) nd_21 nd_28). Qed.
Lemma nd_12 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) (MSplit QL1 62 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]))) = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) ((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) QL1 62 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))])) nd_13 nd_20). Qed.
Lemma nd_2 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 3) (MSplit QL1 0 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 62 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))])))) = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 3) QL1 0 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 62 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]))) nd_3 nd_12). Qed.
Definition TREE3 : mtree := (MSplit QL1 0 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 62 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MSplit QL1 63 (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))]) (MPreS 0%nat pfx_o3a3 HR_1 [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asan)))])))).
Lemma TREE3_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 3) TREE3 = true.
Proof. exact nd_2. Qed.
