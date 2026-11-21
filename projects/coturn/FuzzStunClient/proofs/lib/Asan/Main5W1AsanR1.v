(* SPDX-License-Identifier: MIT *)
(* Main5W1Asan's W1 tree at launch layout r = 1: the released tree W1TreeA.t_164 collected by [TreeColA.tcol] from that layout's
   hand-off template [M5TmplRAsan.HG1_r true] (plans renumbered by [VarShift.pshj], MCase scrutinees by [VarShift.esh], hole
   tables re-collected from [VarShift.ash] of the released templates, a [PCaseNJ] all of whose arms the revised model makes
   dead, checked as [AsanPlanCore.nj_starts_all] allows), computed at each compile and decided by one [mtree_ok] reflection. Nothing about the
   collection is trusted. One file per r so that the two collections compile in parallel. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan VarShift MainCol TOTmplRAsan M5TmplRAsan TreeColA W1TreeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition TW1_A1 : mtree := Eval vm_compute in fst (tcol true esh (HG1_r true) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) t_164).
Lemma TW1_ok1 : mtree_ok (rsb := true) 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat (HG1_r true) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TW1_A1 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
