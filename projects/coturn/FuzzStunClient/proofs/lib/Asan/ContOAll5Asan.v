(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the TO leaf is checked for each launch rseq layout from the collected template TOTmplRAsan.TO_asan_r, with its plan renumbered by VarShift.psh, in place of the recorded certificate. *)
(* The TO leaf starts from the per-r collected template [TOTmplRAsan.TO_asan_r rsb]; its plan is
   renumbered by [VarShift.psh]. One reflection per r ([o_leaf_ok1], [o_leaf_ok0]), joined in [o_leaf_ok]. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan ArgleafTmplAsan ArgleafContOAllAsan VarShift TOTmplRAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition cont_o_all_asanR : plan := psh cont_o_all_asan.
Lemma o_leaf_ok1 : rtree_ok (rsb := true) 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s (TO_asan_r true) C_o_asan (RLeaf cont_o_all_asanR) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma o_leaf_ok0 : rtree_ok (rsb := false) 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s (TO_asan_r false) C_o_asan (RLeaf cont_o_all_asanR) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma o_leaf_ok {rsb : bool} : rtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s (TO_asan_r rsb) C_o_asan (RLeaf cont_o_all_asanR) = true.
Proof. destruct rsb; [exact o_leaf_ok1 | exact o_leaf_ok0]. Qed.
