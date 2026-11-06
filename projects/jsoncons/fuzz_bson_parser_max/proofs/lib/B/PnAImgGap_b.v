(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5KnA. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMAGAP.
Definition GAP_LO : Z := 0x23780.
Definition GAP_HI : Z := 0x23880.
Definition rt_img_gap (HI : asan_iface) : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall x, HeapIfaceA.S GAP_LO <= x < HeapIfaceA.S GAP_HI -> byte_at M x 0) /\ shadow_allowed A GAP_LO (GAP_HI - GAP_LO).

(* [comment removed for export] *)
Lemma gap_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147469040 32.
Proof.
  intros Inv.
  pose proof (GAP LB FF LK cr Aw M (vml_of model) Inv) as [Zeroes Allowed].
  assert (SLo : HeapIfaceA.S GAP_LO = 2147469040) by reflexivity.
  assert (SHi : HeapIfaceA.S GAP_HI = 2147469072) by reflexivity.
  assert (SLast : HeapIfaceA.S (GAP_LO + (GAP_HI - GAP_LO) - 1) = 2147469071) by reflexivity.
  assert (Vis : L5A.avis (ahid Aw model) 2147469040 32).
  { apply (L5A.avis_of_shadow_allowed Aw model GAP_LO (GAP_HI - GAP_LO) 2147469040 32 Allowed).
    intros k Kin. unfold in_shadow_of. rewrite SLo, SLast. lia. }
  apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M 2147469040 32 Vis)).
  intros k Kin. apply Zeroes. rewrite SLo, SHi. lia.
Qed.
End PMAGAP.
