(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5KnA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
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
  intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (Z0 & SA).
  assert (INS : forall j, 0 <= j < 32 -> in_shadow_of GAP_LO (GAP_HI - GAP_LO) (2147469040 + j)).
  { intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI.
    change (0x23780 / 8 + 2147450880) with 2147469040. change ((0x23780 + (0x23880 - 0x23780) - 1) / 8 + 2147450880) with 2147469071. lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ 32 (L5A.avis_of_shadow_allowed Aw model GAP_LO (GAP_HI - GAP_LO) 2147469040 32 SA INS))).
  intros j Hj. pose proof (Z0 (2147469040 + j)) as B. unfold byte_at in B. apply B.
  unfold HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI. change (0x23780 / 8 + 2147450880) with 2147469040. change (0x23880 / 8 + 2147450880) with 2147469072. lia.
Qed.
End PMAGAP.
