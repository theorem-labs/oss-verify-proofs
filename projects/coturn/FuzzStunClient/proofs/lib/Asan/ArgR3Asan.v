(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: one tree per launch rseq layout, with hole 3 started from the collected template TOTmplRAsan.TO_asan_r, every plan renumbered by VarShift.psh and each tree decided by one reflection per layout, in place of the recorded certificates. *)
(* One tree per r. Hole 3 holds the per-r collected template [TOTmplRAsan.TO_asan_r rsb]; every
   plan is renumbered by [VarShift.psh]; the whole tree is decided by one [mtree_ok] reflection per r
   ([TREE3_ok1] r = 1, [TREE3_ok0] r = 0), joined in [TREE3_ok]. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContOAllAsan ArgR234PlansAsan VarShift TOTmplRAsan ContOAll5Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HR_1 (rsb : bool) : list (nat * (shape * acs)) := [(3%nat, (cont_o_all_asan_s, TO_asan_r rsb))].
Definition node3 (rsb : bool) : mtree := MPreS 0%nat (psh pfx_o3a3) (HR_1 rsb) [(3%nat, (RClass (C_o_asan) (RLeaf cont_o_all_asanR)))].
Definition TREE3 (rsb : bool) : mtree := (MSplit QL1 0 (node3 rsb) (MSplit QL1 62 (node3 rsb) (MSplit QL1 63 (node3 rsb) (node3 rsb)))).
Lemma TREE3_ok1 : mtree_ok (rsb := true) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA true (HS_mainA (rseq_z true)) 0%nat) (root_class 3) (TREE3 true) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TREE3_ok0 : mtree_ok (rsb := false) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA false (HS_mainA (rseq_z false)) 0%nat) (root_class 3) (TREE3 false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TREE3_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 3) (TREE3 rsb) = true.
Proof. destruct rsb; [exact TREE3_ok1 | exact TREE3_ok0]. Qed.
