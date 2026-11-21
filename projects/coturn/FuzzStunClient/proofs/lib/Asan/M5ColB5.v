(* SPDX-License-Identifier: MIT *)
(* One piece of Main5Both's t_48 subtree (see M5ColB.v): the MSplit chain's node at depth 5 (t_32 and the rtree
   leaves below its holes), collected per r by [TreeColB.tcol] from the root's collected hole-10 entry [M5ColB.AR0c rsb],
   under the classes the whole chain gives it. Nothing here is trusted. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB ItabBoth W0BPlans VarShift MainCol TOTmplRBoth TreeColB M5TreeB.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import M5ColB.

Definition M5P5_B1 : mtree := Eval vm_compute in fst (tcol true esh (AR0c true) C48 (mkeep (Nat.eqb 5) 0 M5RelB.t_45)).
Definition M5P5_B0 : mtree := Eval vm_compute in fst (tcol false esh (AR0c false) C48 (mkeep (Nat.eqb 5) 0 M5RelB.t_45)).
Definition M5P5 (rsb : bool) : mtree := if rsb then M5P5_B1 else M5P5_B0.
Lemma pk5 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat (AR0c rsb) ((((((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) (pick 5 (M5P5 rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
