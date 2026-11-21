(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_TF2 LB_Tables LB_Inv LB_Kernel LB_Embed LB_Tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition bigb (n : Z) : Z := if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) else 0.

Definition NREQ : Z := 2^29 - 2^16.

Definition ROOM (BL : list blk) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LR BL (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63 BL + 1 <= P 63).

Definition CORE_POSTQ (n : Z) (BL : list blk) (P : Z -> Z) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  match snd r with
  | None => SINV x0 (fst r) BL /\ AQ (fst r) BL P
  | Some (g, idx) => forall bg off, hosts (fst r) bg g ->
      SINV x0 (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL)
      /\ AQ (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL) P
  end.

Definition malloc_core_fq_stmt : Prop :=
  forall st L BL LS P n B,
    INVL x0 st L BL LS -> TF0 st -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> n <= NREQ -> ROOM BL P n ->
    PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
    fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).
