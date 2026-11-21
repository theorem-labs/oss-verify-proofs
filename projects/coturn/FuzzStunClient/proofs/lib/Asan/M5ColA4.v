(* SPDX-License-Identifier: MIT *)
(* One piece of Main5Asan's t_48 subtree (see M5ColA.v): the MSplit chain's node at depth 4 (t_25 and the rtree
   leaves below its holes), collected per r by [TreeColA.tcol] from the root's collected hole-10 entry [M5ColA.AR0c rsb],
   under the classes the whole chain gives it. Nothing here is trusted. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan W0Plans VarShift MainCol TOTmplRAsan TreeColA M5TreeA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import M5ColA.

Definition M5P4_A1 : mtree := Eval vm_compute in fst (tcol true esh (AR0c true) C48 (mkeep (Nat.eqb 4) 0 M5RelA.t_45)).
Definition M5P4_A0 : mtree := Eval vm_compute in fst (tcol false esh (AR0c false) C48 (mkeep (Nat.eqb 4) 0 M5RelA.t_45)).
Definition M5P4 (rsb : bool) : mtree := if rsb then M5P4_A1 else M5P4_A0.
Lemma pk4 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) (((((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) (pick 4 (M5P4 rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
