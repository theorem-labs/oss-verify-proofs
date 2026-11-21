(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: one tree per launch rseq layout, with hole 3 started from the collected template TOTmplRBoth.TO_both_r, every plan renumbered by VarShift.psh and each tree decided by one reflection per layout, in place of the recorded certificates. *)
(* One tree per r. Hole 3 holds the per-r collected template [TOTmplRBoth.TO_both_r rsb]; every
   plan is renumbered by [VarShift.psh]; the whole tree is decided by one [mtree_ok] reflection per r. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ArgR234PlansBoth VarShift TOTmplRBoth ContOAll5Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HR_1 (rsb : bool) : list (nat * (shape * acs)) := [(3%nat, (cont_o_all_both_s, TO_both_r rsb))].
Definition TREE2 (rsb : bool) : mtree := (MPreS 0%nat (psh pfx_o2b3) (HR_1 rsb) [(3%nat, (RClass (C_o_both) (RLeaf cont_o_all_bothR)))]).
Lemma TREE2_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) (root_class 2) (TREE2 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
