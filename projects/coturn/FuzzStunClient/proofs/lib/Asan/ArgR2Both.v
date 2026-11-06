(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ContOAll5Both ArgR234PlansBoth ArgR2BothDefs ArgR2BothCerts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma pay_5 : class_pay_ok 0%nat (root_class 2) (subst_holes (rs_of HR_1) s_4) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_6 : mcoverS HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both)))] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_8 : class_le (root_class 2) (C_o_both) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma rn_9 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (C_o_both) (RLeaf cont_o_all_both) = true.
Proof. exact (o_leaf_ok_both). Qed.
Lemma rn_7 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (root_class 2) (RClass (C_o_both) (RLeaf cont_o_all_both)) = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (cont_o_all_both_s) TO_both (root_class 2) (C_o_both) _ le_8 rn_9). Qed.
Lemma rf_10 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 2) [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both)))] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 2) 3%nat (RClass (C_o_both) (RLeaf cont_o_all_both)) _ (cont_o_all_both_s) TO_both eq_refl rn_7 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_1 (root_class 2))). Qed.
Lemma nd_2 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 2) (MPreS 0%nat pfx_o2b3 HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both)))]) = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 2) 0%nat pfx_o2b3 HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both)))] _ eq_refl c_3 pay_5 covs_6 rf_10). Qed.
Definition TREE2 : mtree := (MPreS 0%nat pfx_o2b3 HR_1 [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_both)))]).
Lemma TREE2_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 2) TREE2 = true.
Proof. exact nd_2. Qed.
