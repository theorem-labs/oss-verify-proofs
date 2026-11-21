(* SPDX-License-Identifier: MIT *)
(* One piece of Main5Asan's t_48 subtree (see M5ColA.v), at launch layout r = 0: the MSplit chain's node at depth 3
   (t_14 and the rtree leaves below its holes), collected by [TreeColA.tcol] from the root's collected hole-10 entry
   [M5ColA.AR0c false], under the classes the whole chain gives it. One file per r, so that the two compile in
   parallel: this node's collection is the longest of the subtree. Nothing here is trusted. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan W0Plans VarShift MainCol TOTmplRAsan TreeColA M5TreeA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import M5ColA.

Definition M5P3_A0 : mtree := Eval vm_compute in fst (tcol false esh (AR0c false) C48 (mkeep (Nat.eqb 3) 0 M5RelA.t_45)).
Lemma pk3_0 : mtree_ok (rsb := false) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c false) ((((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) (pick 3 M5P3_A0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
