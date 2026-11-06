(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape
  MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth
  ArgleafRootBoth0 ArgleafRootBoth1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require ArgR2Both ArgR3Both ArgR4Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Tree.
  Variable TREE5 : mtree.
  Hypothesis TREE5_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 5) TREE5 = true.

  Definition TREE_both (h i : nat) : mtree :=
    match i with
    | 0%nat => TREEBoth0 | 1%nat => TREEBoth1 | 2%nat => ArgR2Both.TREE2 | 3%nat => ArgR3Both.TREE3 | 4%nat => ArgR4Both.TREE4
    | _ => TREE5
    end.

  Theorem TREES_both : forall h ch i, HS_mainB h = Some ch -> (i < 6)%nat ->
    mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB h) (root_class i) (TREE_both h i) = true.
  Proof.
    intros h ch i Hh Hi. destruct h as [|h]; [|cbn in Hh; discriminate Hh].
    destruct i as [|[|[|[|[|[|i]]]]]]; cbn [TREE_both].
    - exact TREEBoth0_ok.
    - exact TREEBoth1_ok.
    - exact ArgR2Both.TREE2_ok.
    - exact ArgR3Both.TREE3_ok.
    - exact ArgR4Both.TREE4_ok.
    - exact TREE5_ok.
    - exfalso. lia.
  Qed.
End Tree.
