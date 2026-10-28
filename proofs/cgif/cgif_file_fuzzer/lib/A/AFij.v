(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFi3 AFik AFil AFim AFin.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x52bcc regs0 ch.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 64512.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Lemma prim_fp : from_primary n = true.
Proof.
clear - Nrange. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
destruct (Z.leb_spec n 48); [change (Z.shiftl 16 0) with 16; lia|].
destruct (Z.leb_spec n 96); [change (Z.shiftl 16 1) with 32; lia|].
destruct (Z.leb_spec n 448); [change (Z.shiftl 16 2) with 64; lia|].
destruct (Z.leb_spec n 3968); [change (Z.shiftl 16 3) with 128; lia|].
destruct (Z.leb_spec n 16128); [change (Z.shiftl 16 4) with 256; lia|].
destruct (Z.leb_spec n 32256); [change (Z.shiftl 16 5) with 512; lia|].
destruct (Z.leb_spec n 64512); [change (Z.shiftl 16 6) with 1024; lia|]. lia.
Qed.
Section c.
Variables (l : list Z) (off : Z).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S (chunk_class n)) = l ++ [off].
Theorem malloc_hit :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- exact (malloc_hitg B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(lia) Htr Hlive l off Hinited Hcache).
- exact (malloc_hitk B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(lia) Htr Hlive l off Hinited Hcache).
Qed.
End c.
Theorem malloc_miss : pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
intros Hmiss. destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- exact (malloc_missg B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(lia) Htr Hlive Hmiss).
- exact (malloc_missk B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(lia) Htr Hlive Hmiss).
Qed.
Theorem malloc_prim :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El; [exact (malloc_miss El)|].
assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
destruct LX as (l & off & LX). rewrite LX in El.
pose proof (proj1 (proj1 PRE)) as HARm. pose proof (primary_geometry n ltac:(lia) prim_fp) as (Hcl & _).
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) (chunk_class n) ltac:(lia))) as WC.
destruct (st_cache_inited S) eqn:CI; [exact (malloc_hit l off CI El)|].
exfalso. rewrite WC in El. cbn in El. destruct l; discriminate El.
Qed.
End b.
End a.
