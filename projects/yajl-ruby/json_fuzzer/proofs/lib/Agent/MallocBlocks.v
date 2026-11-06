(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl RawAlloc Realloc ReallocProto ReallocKeep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocOracle MallocVocab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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
| areach_init : AREACH_from resv (minit rc_secret resv) []   (* [comment removed for export] *)
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
| areach_tick : forall st LB t,
    AREACH_from resv st LB -> (s_tick st <= t)%N ->
    AREACH_from resv (set_tick t st) LB
| areach_realloc_keep : forall st LB (b : block) (pf : aptr) n st',
    AREACH_from resv st LB -> In b LB -> 0 <= n ->
    fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
    realloc_keep st pf n st' ->
    AREACH_from resv st' ((blk_id b, conc st' pf, n) :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
End RC__1.
(* [comment removed for export] *)
Arguments areach_init {RC__} {resv}.
Arguments areach_malloc_some {RC__} {resv}.
Arguments areach_malloc_none {RC__} {resv}.
Arguments areach_free {RC__} {resv}.
Arguments areach_tick {RC__} {resv}.
Arguments areach_realloc_keep {RC__} {resv}.
Section RC__1b.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)

End RC__1b.
