(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg ShapeEF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem base_of_realizes :
  forall (segs1 : list Segment) (pc1 : N) (ph1 : PhdrInfo)
         (segs2 : list Segment) (pc2 : N) (ph2 : PhdrInfo) (S : ProcInput -> TSet),
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs1 pc1 ph1) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     realizes segs1 (init_config segs1 pc1 ph1 sp brk mb rnd source_alloc_limit inp) (S inp)) ->
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs2 pc2 ph2) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     realizes segs2 (init_config segs2 pc2 ph2 sp brk mb rnd target_alloc_limit inp) (S inp)) ->
  strong_universal_error_free_T (mkImage segs1 pc1 ph1) (mkImage segs2 pc2 ph2).
Proof.
  intros segs1 pc1 ph1 segs2 pc2 ph2 S H1 H2 [sp brk mb rnd] [sp' brk' mb' rnd'] inp He1 He2 Hv.
  unfold strong_equiv_error_free.
  exact (shape_strong_equiv_ef segs1 pc1 ph1 sp brk mb rnd source_alloc_limit
           segs2 pc2 ph2 sp' brk' mb' rnd' target_alloc_limit (S inp) inp
           (H1 sp brk mb rnd inp He1 Hv) (H2 sp' brk' mb' rnd' inp He2 Hv)).
Qed.

(* [comment removed for export] *)
Theorem base_of_realizes_eq :
  forall (segs1 : list Segment) (pc1 : N) (ph1 : PhdrInfo)
         (segs2 : list Segment) (pc2 : N) (ph2 : PhdrInfo) (S1 S2 : ProcInput -> TSet),
  (forall inp, valid_input inp -> t_eq (S1 inp) (S2 inp)) ->
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs1 pc1 ph1) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     realizes segs1 (init_config segs1 pc1 ph1 sp brk mb rnd source_alloc_limit inp) (S1 inp)) ->
  (forall sp brk mb rnd inp,
     valid_entry (mkImage segs2 pc2 ph2) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
     realizes segs2 (init_config segs2 pc2 ph2 sp brk mb rnd target_alloc_limit inp) (S2 inp)) ->
  strong_universal_error_free_T (mkImage segs1 pc1 ph1) (mkImage segs2 pc2 ph2).
Proof.
  intros segs1 pc1 ph1 segs2 pc2 ph2 S1 S2 Heq H1 H2 [sp brk mb rnd] [sp' brk' mb' rnd'] inp He1 He2 Hv.
  unfold strong_equiv_error_free.
  exact (shape_strong_equiv_ef_eq segs1 pc1 ph1 sp brk mb rnd source_alloc_limit
           segs2 pc2 ph2 sp' brk' mb' rnd' target_alloc_limit (S1 inp) (S2 inp) inp
           (H1 sp brk mb rnd inp He1 Hv) (H2 sp' brk' mb' rnd' inp He2 Hv) (Heq inp Hv)).
Qed.
