(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan ArgleafTmplAsan ArgleafContOAllAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma o_cert : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of C_o_asan)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C_o_asan)) HS_none 0%nat 400000%nat 5000%nat None (pay_start TO_asan C_o_asan) cont_o_all_asan = COk cont_o_all_asan_s.
Proof. vm_cast_no_check (eq_refl (COk cont_o_all_asan_s)). Qed.
Lemma o_f1 : shape_eqb cont_o_all_asan_s cont_o_all_asan_s = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_f2 : shape_vars_lt NX0 cont_o_all_asan_s = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o_leaf_ok : rtree_ok 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s TO_asan C_o_asan (RLeaf cont_o_all_asan) = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s TO_asan C_o_asan cont_o_all_asan _ o_cert o_f1 o_f2). Qed.
