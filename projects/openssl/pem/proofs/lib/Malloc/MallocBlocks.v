(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocRep MallocTree.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
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
(* [comment removed for export] *)
Definition reframe_ok (st : mstate) (c : cptr) (off0 n0 off' n' : Z) (st' : mstate) : Prop :=
  s_regions st' = s_regions st /\ s_secret st' = s_secret st
  /\ forall L BL LS, MI_Inv.INVL MI_Inv.x0 st L BL LS -> In ((c, off0), n0) BL ->
       MI_Inv.INVL MI_Inv.x0 st' L (((c, off'), n') :: MI_Inv.bl_remove c BL) LS.

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
| areach_reframe : forall st LB (b : block) (off' n' : Z) st',
    AREACH_from resv st LB -> In b LB ->
    reframe_ok st (blk_slot b) ((blk_addr b - conc st (blk_slot b)) / UNIT) (blk_size b) off' n' st' ->
    AREACH_from resv st' ((blk_id b, conc st (blk_slot b) + UNIT * off', n')
                          :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
End WithCeiling0.
Arguments areach_init {resv}.
Arguments areach_malloc_some {resv}.
Arguments areach_malloc_none {resv}.
Arguments areach_free {resv}.
Arguments areach_reframe {resv}.
