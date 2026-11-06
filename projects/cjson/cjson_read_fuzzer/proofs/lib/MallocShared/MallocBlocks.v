(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv MI_Inv.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition AINV (resv : list (Z * Z)) (st : mstate) (LB : list block) : Prop :=
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = 0
    /\ Forall2 (fun (b : block) (k : blk) =>
                  blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k) LB BL.
Definition AEXT (resv : list (Z * Z)) (st : mstate) (LB : list block) (st' : mstate) (LB' : list block) : Prop :=
  AINV resv st LB -> AINV resv st' LB'.

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
| areach_ext : forall st LB st' LB',
    AREACH_from resv st LB -> AEXT resv st LB st' LB' -> AREACH_from resv st' LB'.
Arguments areach_init {resv}.
Arguments areach_malloc_some {resv}.
Arguments areach_malloc_none {resv}.
Arguments areach_ext {resv}.
Arguments areach_free {resv}.

End CeilWrap.
(* [comment removed for export] *)
Arguments areach_init {ACEIL resv}.
Arguments areach_malloc_some {ACEIL resv}.
Arguments areach_malloc_none {ACEIL resv}.
Arguments areach_ext {ACEIL resv}.
Arguments areach_free {ACEIL resv}.
