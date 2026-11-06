(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5KnA L5DefsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBGAP.
Definition GAP_LO : Z := 0x23a80.
Definition GAP_HI : Z := 0x23be0.
Definition GAPB_LO : Z := 0x23300.
Definition GAPB_HI : Z := 0x233e0.
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x69c000.
Definition rt_img_gap (HI : asan_iface) : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    ((forall x, HeapIfaceA.S GAP_LO <= x < HeapIfaceA.S GAP_HI -> byte_at M x 0) /\ shadow_allowed A GAP_LO (GAP_HI - GAP_LO))
    /\ (forall x, HeapIfaceA.S GAPB_LO <= x < HeapIfaceA.S GAPB_HI -> byte_at M x 0)
    /\ shadow_allowed A IMG_LO (IMG_HI - IMG_LO).

Lemma gap_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147469136 44.
Proof.
  intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as ((Z0 & SA) & _).
  assert (INS : forall j, 0 <= j < 44 -> in_shadow_of GAP_LO (GAP_HI - GAP_LO) (2147469136 + j)).
  { intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI.
    change (0x23a80 / 8 + 2147450880) with 2147469136. change ((0x23a80 + (0x23be0 - 0x23a80) - 1) / 8 + 2147450880) with 2147469179. lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ 44 (L5A.avis_of_shadow_allowed Aw model GAP_LO (GAP_HI - GAP_LO) 2147469136 44 SA INS))).
  intros j Hj. pose proof (Z0 (2147469136 + j)) as B. unfold byte_at in B. apply B.
  unfold HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI. change (0x23a80 / 8 + 2147450880) with 2147469136. change (0x23be0 / 8 + 2147450880) with 2147469180. lia.
Qed.

Lemma img_shallowed HI (GAP : rt_img_gap HI) LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> shadow_allowed Aw 0x10000 (0x69c000 - 0x10000).
Proof. intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (_ & _ & SA). exact SA. Qed.
Lemma img_sh_avis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model a n x g :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> 0x10000 <= a -> a + n <= 0x69c000 -> 0 < n ->
  (forall j, 0 <= j < g -> in_shadow_of a n (x + j)) -> L5A.avis (ahid Aw model) x g.
Proof.
  intros HH H1 H2 Hn INS.
  apply (L5A.avis_of_shadow_allowed Aw model 0x10000 (0x69c000 - 0x10000) x g (img_shallowed HI GAP _ _ _ _ _ _ _ HH)).
  intros j Hj. pose proof (INS j Hj) as X. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in *.
  pose proof (Z.div_le_mono 0x10000 a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (a + n - 1) (0x10000 + (0x69c000 - 0x10000) - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma gapB_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147468896 28.
Proof.
  intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (_ & Z0 & _).
  assert (INS : forall j, 0 <= j < 28 -> in_shadow_of GAPB_LO (GAPB_HI - GAPB_LO) (2147468896 + j)).
  { intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAPB_LO, GAPB_HI.
    change (0x23300 / 8 + 2147450880) with 2147468896. change ((0x23300 + (0x233e0 - 0x23300) - 1) / 8 + 2147450880) with 2147468923. lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ 28 (img_sh_avis HI GAP _ _ _ _ _ _ _ GAPB_LO (GAPB_HI - GAPB_LO) 2147468896 28 HH
            ltac:(unfold GAPB_LO; lia) ltac:(unfold GAPB_LO, GAPB_HI; lia) ltac:(unfold GAPB_LO, GAPB_HI; lia) INS))).
  intros j Hj. pose proof (Z0 (2147468896 + j)) as B. unfold byte_at in B. apply B.
  unfold HeapIfaceA.S, HeapIfaceA.SB, GAPB_LO, GAPB_HI. change (0x23300 / 8 + 2147450880) with 2147468896. change (0x233e0 / 8 + 2147450880) with 2147468924. lia.
Qed.
End PMBGAP.
