(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: one tree per launch rseq layout from the collected template TUTmplRBoth.TU_both_r, with the prefix plan renumbered by VarShift.psh and each root node decided by one reflection per layout, in place of the recorded certificates. *)
(* One tree per r; HT hole 0 holds [TUTmplRBoth.TU_both_r rsb]; the prefix plan is renumbered by
   [VarShift.psh]; the root node is decided by one [mtree_ok] reflection per r. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth VarShift TUTmplRBoth ArgleafContUBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HTBoth1 (rsb : bool) : list (nat * (nat * acs)) := [(0%nat, (0%nat, TU_both_r rsb))].
Definition TREEBoth1 (rsb : bool) : mtree := MPre 0 (psh pfx_u3b) (HTBoth1 rsb) [(0%nat, MClass CC_u_both CONTUBoth)].
Lemma TREEBoth1_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) (root_class 1) (TREEBoth1 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
