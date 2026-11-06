(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg SpinAlg ShapeEFS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_of_realizes_s_budgets :
  forall (ls lt : Z) (segs1 : list Segment) (pc1 : N) (ph1 : PhdrInfo)
         (segs2 : list Segment) (pc2 : N) (ph2 : PhdrInfo) (S : ProcInput -> TSet),
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs1 pc1 ph1) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     realizes segs1 (init_config segs1 pc1 ph1 sp brk mb rnd ls inp) (S inp)) ->
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs2 pc2 ph2) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     srealizes segs2 (init_config segs2 pc2 ph2 sp brk mb rnd lt inp) (S inp)) ->
  strong_universal_error_free_T_budgets ls lt (mkImage segs1 pc1 ph1) (mkImage segs2 pc2 ph2).
Proof.
  intros ls lt segs1 pc1 ph1 segs2 pc2 ph2 S H1 H2 [sp brk mb rnd] [sp' brk' mb' rnd'] inp He1 He2 Hv _.
  unfold strong_equiv_error_free_budgets.
  exact (shape_strong_equiv_efs segs1 pc1 ph1 sp brk mb rnd ls
           segs2 pc2 ph2 sp' brk' mb' rnd' lt (S inp) inp
           (H1 sp brk mb rnd inp He1 Hv) (H2 sp' brk' mb' rnd' inp He2 Hv)).
Qed.
