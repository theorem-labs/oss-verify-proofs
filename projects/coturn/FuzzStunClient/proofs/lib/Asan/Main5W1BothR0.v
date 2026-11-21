(* SPDX-License-Identifier: MIT *)
(* Main5W1Both's W1 tree at launch layout r = 0: the released tree W1TreeB.t_160 collected by [TreeColB.tcol] from that layout's
   hand-off template [M5TmplRBoth.HG1_r false] (plans renumbered by [VarShift.pshj], MCase scrutinees by [VarShift.esh], hole
   tables re-collected from [VarShift.ash] of the released templates, a [PCaseNJ] all of whose arms the revised model makes
   dead, checked as [AsanPlanCore.nj_starts_all] allows), computed at each compile and decided by one [mtree_ok] reflection. Nothing about the
   collection is trusted. One file per r so that the two collections compile in parallel. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB ItabBoth VarShift MainCol TOTmplRBoth M5TmplRBoth TreeColB W1TreeB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition TW1_B0 : mtree := Eval vm_compute in fst (tcol false esh (HG1_r false) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) t_160).
Lemma TW1_ok0 : mtree_ok (rsb := false) 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat (HG1_r false) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TW1_B0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
