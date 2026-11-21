(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the trees are made for each launch rseq layout (rsb), and TREES_both_dead gives the dead-arm check of the six trees. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape
  MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth
  ArgleafRootBoth0 ArgleafRootBoth1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require ArgR2Both ArgR3Both ArgR4Both.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import DeadArm DeadTrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Tree.
  Context {rsb : bool}.   (* the launch's kb_rseq; the table is ASAN_at/BOTH_at (rseq_z rsb) *)
  Variable TREE5 : mtree.
  Hypothesis TREE5_ok : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) (root_class 5) TREE5 = true.

  Definition TREE_both (h i : nat) : mtree :=
    match i with
    | 0%nat => TREEBoth0 rsb | 1%nat => TREEBoth1 rsb | 2%nat => ArgR2Both.TREE2 rsb | 3%nat => ArgR3Both.TREE3 rsb | 4%nat => ArgR4Both.TREE4 rsb
    | _ => TREE5
    end.

  Theorem TREES_both : forall h ch i, (HS_mainB (rseq_z rsb)) h = Some ch -> (i < 6)%nat ->
    mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA rsb (HS_mainB (rseq_z rsb)) h) (root_class i) (TREE_both h i) = true.
  Proof.
    intros h ch i Hh Hi. destruct h as [|h]; [|cbn in Hh; discriminate Hh].
    destruct i as [|[|[|[|[|[|i]]]]]]; cbn [TREE_both].
    - exact (TREEBoth0_ok (rsb := rsb)).
    - exact (TREEBoth1_ok (rsb := rsb)).
    - exact (ArgR2Both.TREE2_ok (rsb := rsb)).
    - exact (ArgR3Both.TREE3_ok (rsb := rsb)).
    - exact (ArgR4Both.TREE4_ok (rsb := rsb)).
    - exact TREE5_ok.
    - exfalso. lia.
  Qed.

  (* The dead-arm check of the six trees ([MainGlueB.mtree_dead hf26]); the fifth tree's
     is its caller's. *)
  Theorem TREES_both_dead : mtree_dead hf26 TREE5 = true ->
    forall h ch i, (HS_mainB (rseq_z rsb)) h = Some ch -> (i < 6)%nat -> mtree_dead hf26 (TREE_both h i) = true.
  Proof.
    intros H5 h ch i Hh Hi.
    destruct i as [|[|[|[|[|[|i]]]]]]; cbn [TREE_both].
    - destruct rsb; vm_compute; reflexivity.
    - destruct rsb; vm_compute; reflexivity.
    - exact (TREE2_both_dead rsb).
    - exact (TREE3_both_dead rsb).
    - exact (TREE4_both_dead rsb).
    - exact H5.
    - exfalso. lia.
  Qed.
End Tree.
