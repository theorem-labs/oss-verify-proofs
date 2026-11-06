(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Prog MAlign.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_slot (b : block) : cptr := fst (fst (fst b)).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.

(* [comment removed for export] *)
Definition brk_link (st : mstate) (pbrk : Z) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => pbrk = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
Inductive AREACH_from (resv : list (Z * Z)) : mstate -> list block -> Prop :=
| areach_init : AREACH_from resv (minit 0 resv) []
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
(* [comment removed for export] *)
| areach_realign : forall st LB (b : block) (g : aptr) (idx off adj n : Z),
    AREACH_from resv st LB -> In b LB ->
    s_slots st !! (blk_slot b) = Some (g, idx) ->
    (idx = 0 \/ get_stride (get_meta_rec st g) * (idx + 1) < 2 ^ 20) -> get_stride (get_meta_rec st g) - UNIT * off - n < 2 ^ 32 ->
    0 <= off -> blk_addr b = conc st (blk_slot b) + UNIT * off ->
    0 <= adj -> adj mod UNIT = 0 -> 0 <= n -> adj + n <= blk_size b -> off + adj / UNIT <= 258 ->
    AREACH_from resv (fst (realign_at st g idx n off adj))
      ((blk_id b, blk_addr b + adj, n) :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
End WithCeiling0.
Arguments areach_init {resv}.
Arguments areach_malloc_some {resv}.
Arguments areach_malloc_none {resv}.
Arguments areach_free {resv}.
Arguments areach_realign {resv}.
