(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueAlloc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition cxN (S uspb src len dst dn small n tt l16 l4 : Z) : bctx :=
  BCX S uspb src len dst dn (uspb + 140) uspb small n tt l16 l4.
Definition cx10 (S uspb src len dst dn small : Z) : bctx := cxN S uspb src len dst dn small 0 0 0 0.

(* [comment removed for export] *)
Definition hwf10 (h : dsh) (uspb small : Z) : Prop :=
  sh_strm h = uspb /\ sh_state h = 10 /\ sh_bsBuff h = 0 /\ sh_bsLive h = 0 /\ bv_unsigned (sh_small h) = small /\
  sh_cbn h = 0 /\ sh_verb h = 0 /\
  length (sh_p1 h) = 3%nat /\ length (sh_p2 h) = 3%nat /\ length (sh_p3 h) = 3%nat /\
  0 <= sh_solen h < 2 ^ 32 /\ 0 <= sh_rNToGo h < 2 ^ 32 /\ 0 <= sh_rTPos h < 2 ^ 32 /\ 0 <= sh_n h < 2 ^ 32 /\
  0 <= sh_origPtr h < 2 ^ 32.

(* [comment removed for export] *)
Definition pres10 (LB : list ablock) (S uspb : Z) (m m' : word -> option byte) : Prop :=
  forall a : Z, 0 <= a < 2 ^ 64 ->
    (uspb - 112 <= a \/ (0x32000 <= a < 0x66000 /\ ~ S0_private a /\ ~ (0x4413c <= a < 0x44140)) \/ in_block LB a) ->
    ~ (S <= a < S + 64144) -> ~ (uspb <= a < uspb + 20) ->
    m' (wa a) = m (wa a) /\ (wview s0segs m (wa a) <> None -> wview s0segs m' (wa a) <> None).

Section Dec10.
  Context (AI : AllocIface s0segs S0_layout).
  Let L := S0_layout.

  (* [comment removed for export] *)
End Dec10.

End ACeilS1.
