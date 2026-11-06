(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ContOAll5Both ArgR234PlansBoth ArgR4RepBoth ArgR4BothDefs ArgR4BothCerts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma pay_5 : class_pay_ok 0%nat (root_class 4) (subst_holes (rs_of HR_1) s_4) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_6 : mcoverS HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both))); (26%nat, (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)))] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_8 : class_le (root_class 4) ((root_class 4)) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_12 : shape_eqb s_11 (SNil) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_13 : shape_vars_lt NX0 (SNil) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_15 : class_le (root_class 4) (C_o_both) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma rn_9 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (SNil) REP4b_s ((root_class 4)) (RLeaf argdb1o_tospin1) = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (SNil) REP4b_s ((root_class 4)) argdb1o_tospin1 _ c_10 eq_12 vl_13). Qed.
Lemma rn_7 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (SNil) REP4b_s (root_class 4) (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (SNil) REP4b_s (root_class 4) ((root_class 4)) _ le_8 rn_9). Qed.
Lemma rn_16 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (C_o_both) (RLeaf cont_o_all_both) = true.
Proof. exact (o_leaf_ok_both). Qed.
Lemma rn_14 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (root_class 4) (RClass (C_o_both) (RLeaf cont_o_all_both)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (root_class 4) (C_o_both) _ le_15 rn_16). Qed.
Lemma rf_17 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 4) [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both))); (26%nat, (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 4) 3%nat (RClass (C_o_both) (RLeaf cont_o_all_both)) _ (cont_o_all_both_s) TO_both eq_refl rn_14 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 4) 26%nat (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)) _ (SNil) REP4b_s eq_refl rn_7 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 4)))). Qed.
Lemma nd_2 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 4) (MPreS 0%nat argdb1otr HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both))); (26%nat, (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 4) 0%nat argdb1otr HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both))); (26%nat, (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)))] _ eq_refl c_3 pay_5 covs_6 rf_17). Qed.
Definition TREE4 : mtree := (MPreS 0%nat argdb1otr HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both))); (26%nat, (RClass ((root_class 4)) (RLeaf argdb1o_tospin1)))]).
Lemma TREE4_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 4) TREE4 = true.
Proof. exact nd_2. Qed.
