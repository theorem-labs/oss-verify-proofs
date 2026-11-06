(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContUBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition HTBoth1 : list (nat * (nat * acs)) := [(0%nat, (0%nat, TU_both))].
Definition TREEBoth1 : mtree := MPre 0 pfx_u3b HTBoth1 [(0%nat, MClass CC_u_both CONTUBoth)].
Lemma both_r1_pfx : pre_check HS_mainB 0%nat 400000%nat 5000%nat IT_both 0%nat (root_class 1) HTBoth1 pfx_u3b = COk (SHole 0).
Proof. vm_cast_no_check (eq_refl (COk (SHole 0))). Qed.
Lemma both_r1_seg : class_seg_ok (lv_of HTBoth1) 0 (root_class 1) (SHole 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_r1_cle : class_le (root_class 1) CC_u_both = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TREEBoth1_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 1) TREEBoth1 = true.
Proof.
  unfold TREEBoth1.
  apply (mtree_ok_pre0 HS_mainB 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (root_class 1) 0%nat pfx_u3b (HTBoth1) [(0%nat, MClass CC_u_both CONTUBoth)] (SHole 0) eq_refl both_r1_pfx both_r1_seg eq_refl).
  apply (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 0%nat (HTBoth1) (root_class 1) 0%nat _ [] 0%nat TU_both eq_refl); [| apply mforest_ok_nil].
  exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat TU_both (root_class 1) CC_u_both CONTUBoth both_r1_cle CONTUBoth_ok).
Qed.
