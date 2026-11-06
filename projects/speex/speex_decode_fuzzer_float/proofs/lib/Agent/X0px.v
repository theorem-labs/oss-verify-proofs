(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0qn.
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

Definition resize_state (st : mstate) (c : cptr) (off n' : Z) : mstate :=
match (s_slots st) !! c with
| None => st
| Some (g, idx) =>
let st0 := set_tick (N.succ (s_tick st)) st in
let p := aadd c (UNIT * off) in
let e := aadd c (get_stride (get_meta_rec st g) - IB) in
let res := snd e - snd p - n' in

let st1 := if negb (res =? 0) then wr8 (aadd e (- res)) 0 st0 else st0 in
let st2 := if 5 <=? res then wr32 (aadd e (-4)) res (wr8 (aadd e (-5)) 0 st1) else st1 in
havoc p n' (wr8 (aadd p (-3)) (Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5) st2)
end.

Definition lb_resize (b : block) (n' : Z) (LB : list block) : list block :=
(blk_id b, blk_addr b, n') :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB.

Inductive AREACH_from {RCEIL : RunCeiling} (resv : list (Z * Z)) : mstate -> list block -> Prop :=
| areach_init : AREACH_from resv (minit 0 alloc_ceiling resv) []

| areach_malloc_some : forall st LB n (o o' : mem) ans st' (pf : aptr) cst (c : cptr) (bo : Z),
AREACH_from resv st LB -> 0 <= n ->
follow (mrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
AREACH_from resv st' (((c, bo), conc st' pf, n) :: LB)
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
0 <= off -> blk_addr b = conc st (blk_slot b) + UNIT * off ->
0 <= n' ->
(forall g idx, (s_slots st) !! (blk_slot b) = Some (g, idx) ->
UNIT * off + n' <= get_stride (get_meta_rec st g) - IB
/\ get_stride (get_meta_rec st g) - IB - UNIT * off - n' < 2^32) ->
AREACH_from resv (resize_state st (blk_slot b) off n') (lb_resize b n' LB).
Arguments areach_init {RCEIL resv}.
Arguments areach_malloc_some {RCEIL resv}.
Arguments areach_malloc_none {RCEIL resv}.
Arguments areach_free {RCEIL resv}.
Arguments areach_resize {RCEIL resv}.

Notation AREACH := (AREACH_from agent_reserved).

