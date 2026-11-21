(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the TO leaf is checked for each launch rseq layout from the collected template TOTmplRBoth.TO_both_r, with its plan renumbered by VarShift.psh, in place of the recorded certificate. *)
(* The TO leaf starts from the per-r collected template [TOTmplRBoth.TO_both_r rsb]; its plan is
   renumbered by [VarShift.psh]. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB ItabBoth ArgleafTmplBoth ArgleafContOAllBoth VarShift TOTmplRBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition cont_o_all_bothR : plan := psh cont_o_all_both.
Lemma o_leaf_ok_both {rsb : bool} : rtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both cont_o_all_both_s (TO_both_r rsb) C_o_both (RLeaf cont_o_all_bothR) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
