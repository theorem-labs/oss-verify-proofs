(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB ItabBoth ArgleafTmplBoth ArgleafContOAllBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma o_cert_both : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of C_o_both)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C_o_both)) HS_none 0%nat 400000%nat 5000%nat None (pay_start TO_both C_o_both) cont_o_all_both = COk cont_o_all_both_s.
Proof. vm_cast_no_check (eq_refl (COk cont_o_all_both_s)). Qed.
Lemma o_f1_both : shape_eqb cont_o_all_both_s cont_o_all_both_s = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_f2_both : shape_vars_lt NX0 cont_o_all_both_s = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_leaf_ok_both : rtree_ok 0%nat 400000%nat 5000%nat IT_both cont_o_all_both_s TO_both C_o_both (RLeaf cont_o_all_both) = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both cont_o_all_both_s TO_both C_o_both cont_o_all_both _ o_cert_both o_f1_both o_f2_both). Qed.
