(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct HeapIface HeapIfaceA L5Defs L5KnA L5DefsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAGAP.
Definition GAP_LO : Z := 0x231e0.
Definition GAP_HI : Z := 0x23340.
Definition rt_img_gap (HI : asan_iface) : Prop :=
forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
(forall x, HeapIfaceA.S GAP_LO <= x < HeapIfaceA.S GAP_HI -> byte_at M x 0) /\ shadow_allowed A GAP_LO (GAP_HI - GAP_LO).
Lemma gap_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147468860 44.
Proof.
intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (Z0 & SA).
assert (INS : forall j, 0 <= j < 44 -> in_shadow_of GAP_LO (GAP_HI - GAP_LO) (2147468860 + j)).
{ intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI.
change (0x231e0 / 8 + 2147450880) with 2147468860. change ((0x231e0 + (0x23340 - 0x231e0) - 1) / 8 + 2147450880) with 2147468903. lia. }
apply (proj2 (L5A.zeros_at_vis _ M _ 44 (L5A.avis_of_shadow_allowed Aw model GAP_LO (GAP_HI - GAP_LO) 2147468860 44 SA INS))).
intros j Hj. pose proof (Z0 (2147468860 + j)) as B. unfold byte_at in B. apply B.
unfold HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI. change (0x231e0 / 8 + 2147450880) with 2147468860. change (0x23340 / 8 + 2147450880) with 2147468904. lia.
Qed.
End PMAGAP.
