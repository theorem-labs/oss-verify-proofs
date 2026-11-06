(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~jb4bptr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks3HCW~~~~~~ne5block03fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~t44cptr03sndt46mstate37Corelib4Init5Logichi74Truehe1Nt48brkstate04pairhi72eqt45c_brkt44conct43ctx" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition block : ltac2:(zQ "00T") := ltac2:(zQ "30!h8!j7!n7@2$0@2$0$2$1$1").
Definition blk_id : ltac2:(zQ "20!s7!n7>1b$0$1") := ltac2:(zQ "50!j7!sf!n7!h8!s7\1b$4@3$1$2$0@3$1@2$3$2$0$0^1").
Definition blk_slot : ltac2:(zQ "20!s7!hh2>1b$0$1") := ltac2:(zQ "60!j7!sf!n7!h8!s7!hh2\1b$4@3$1$5$0@3$1$2$0@3$1@2$3$2$0$0^1").
Definition blk_addr : ltac2:(zQ "20!j7!s7>1b$1$0") := ltac2:(zQ "60!j7!n7!sf!h8!hh9!s7\1b$5@3$4$1$0@3$2@2$3$1$0$0^1").
Definition blk_size : ltac2:(zQ "20!j7!s7>1b$1$0") := ltac2:(zQ "50!j7!h8!hh9!s7!n7\1b$3@3$2@2$1$4$0$0^1").

(* [comment removed for export] *)
Definition brk_link : ltac2:(zQ "20!j7!hhe>2st$1>4pbrk$0P") := ltac2:(zQ "a0!j7!hjb!hk3!hk7!hl2!hl8!hle!hm6!hmd!hhe\2st$9\4pbrk$0M3\1x$3P@1$6@1$8^2$1$1\3rid$2\3off$0@3$5$0^3@2$7^4@4$4$2$0^2^1").

(* [comment removed for export] *)
Inductive AREACH_from (resv : list (Z * Z)) : mstate -> list block -> Prop :=
| areach_init : AREACH_from resv (minit hsecret resv) []   (* [comment removed for export] *)
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
    AREACH_from resv st' (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).

End HCW.
(* [comment removed for export] *)
Arguments areach_init {HSEC} {resv}.
Arguments areach_malloc_some {HSEC} {resv}.
Arguments areach_malloc_none {HSEC} {resv}.
Arguments areach_free {HSEC} {resv}.


Notation AREACH := (AREACH_from agent_reserved).
