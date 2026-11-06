(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape
  MainGlueDefs MainGlue StartupHSMainAsan ItabAsan
  ArgleafRootAsan0 ArgleafRootAsan1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require ArgR2Asan ArgR3Asan ArgR4Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Tree.
  Variable TREE5 : mtree.
  Hypothesis TREE5_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 5) TREE5 = true.

  Definition TREE_asan (h i : nat) : mtree :=
    match i with
    | 0%nat => TREEAsan0 | 1%nat => TREEAsan1 | 2%nat => ArgR2Asan.TREE2 | 3%nat => ArgR3Asan.TREE3 | 4%nat => ArgR4Asan.TREE4
    | _ => TREE5
    end.

  Theorem TREES_asan : forall h ch i, HS_mainA h = Some ch -> (i < 6)%nat ->
    mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA h) (root_class i) (TREE_asan h i) = true.
  Proof.
    intros h ch i Hh Hi. destruct h as [|h]; [|cbn in Hh; discriminate Hh].
    destruct i as [|[|[|[|[|[|i]]]]]]; cbn [TREE_asan].
    - exact TREEAsan0_ok.
    - exact TREEAsan1_ok.
    - exact ArgR2Asan.TREE2_ok.
    - exact ArgR3Asan.TREE3_ok.
    - exact ArgR4Asan.TREE4_ok.
    - exact TREE5_ok.
    - exfalso. lia.
  Qed.
End Tree.
