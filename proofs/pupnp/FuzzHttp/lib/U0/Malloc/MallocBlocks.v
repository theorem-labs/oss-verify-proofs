(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog KRemapDef MRemapOp.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocRep MallocTree.
Import ListNotations.
Open Scope Z_scope.

Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_slot (b : block) : cptr := fst (fst (fst b)).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.

Definition brk_link (st : mstate) (pbrk : Z) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => pbrk = conc st (rid, off)
  | _ => True
  end.

Definition mresize (st : mstate) (c : cptr) (off n n' : Z) : mstate :=
  match (s_slots st) !! c with
  | Some (m, i) =>
      let stride := get_stride (get_meta_rec st m) in
      let p := aadd c (UNIT * off) in
      let e := aadd c (stride - IB) in
      let b3 := i + 32 * Z.min (snd e - snd p - n) 5 in
      havoc p n' (set_size p e n' b3 (set_tick (N.succ (s_tick st)) st))
  | None => st
  end.

Definition mresize_ok (st : mstate) (c : cptr) (off n' : Z) : Prop :=
  exists m i, (s_slots st) !! c = Some (m, i)
    /\ UNIT * off + n' <= get_stride (get_meta_rec st m) - IB

    /\ ((m_sizeclass (get_meta_rec st m) < 48 -> m_sizeclass (get_meta_rec st m) <= size_to_class n' + 1)
        /\ (m_sizeclass (get_meta_rec st m) = 63 -> get_stride (get_meta_rec st m) <= n' + UNIT * off + IB + 4095))
    /\ get_stride (get_meta_rec st m) - IB - UNIT * off - n' < 2 ^ 32.

Inductive AREACH_from (resv : list (Z * Z)) : mstate -> list block -> Prop :=

| areach_init : forall ceil, ceil <= alloc_ceiling_max -> AREACH_from resv (minit 0 resv ceil) []
| areach_malloc_some : forall st LB n (o o' : mem) ans st' (pf : aptr) cst (c : cptr),
    AREACH_from resv st LB -> 0 <= n ->
    follow (mrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    AREACH_from resv st' (((c, fresh_off cst c n), conc st' pf, n) :: LB)
| areach_malloc_none : forall st LB n (o o' : mem) ans st',
    AREACH_from resv st LB -> 0 <= n ->
    follow (mrun o (malloc st n)) ans = Some (o', (st', None)) ->
    AREACH_from resv st' LB
| areach_free : forall st LB (b : block) (pf : aptr) (o o' : mem) ans st',
    AREACH_from resv st LB -> In b LB ->
    fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
    follow (mrun o (free st (Some pf))) ans = Some (o', st') ->
    AREACH_from resv st' (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB)

| areach_resize : forall st LB (b : block) (off n' : Z),
    AREACH_from resv st LB -> In b LB ->
    0 <= off -> blk_addr b = conc st (blk_slot b) + UNIT * off -> 0 <= n' ->
    mresize_ok st (blk_slot b) off n' ->
    AREACH_from resv (mresize st (blk_slot b) off (blk_size b) n')
                ((blk_id b, blk_addr b, n') :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB)

| areach_mremap : forall st LB (b : block) (off n' dst : Z) (g : aptr) (rg : region),
    AREACH_from resv st LB -> In b LB ->
    0 <= off -> blk_addr b = conc st (blk_slot b) + UNIT * off -> 0 <= n' ->
    (s_slots st) !! (blk_slot b) = Some (g, 0) -> m_sizeclass (get_meta_rec st g) = 63 ->
    (s_regions st) !! (fst (blk_slot b)) = Some rg ->
    cremap_ok (strip st) (blk_slot b) dst (mremap_needed off n') ->
    AREACH_from resv (mremap_full st (blk_slot b) off (blk_size b) n' dst)
                ((blk_id b, dst + 16 + UNIT * off, n') :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
Arguments areach_init {resv}.
Arguments areach_malloc_some {resv}.
Arguments areach_malloc_none {resv}.
Arguments areach_free {resv}.
Arguments areach_resize {resv}.
Arguments areach_mremap {resv}.