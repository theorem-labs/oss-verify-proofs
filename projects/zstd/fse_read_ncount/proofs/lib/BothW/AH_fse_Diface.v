(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AHarness_iface AH_fse_kit
AF_fse_iface AF_fse_rd_iface AH_fse_Eiface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Section CANSEC1. Context {rc : runConstT}.
Section D2.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.
Definition pD2_post (L : alayout) (RNG : footprint) (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32)
(st : astate) (LB : list ablock) (SPA lo F P B : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y28 y29 y30 y31 : word)
(m' : amem),
ms' = MS (mkR y1 (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 (Z_to_bv 64 P) y24 y25 (Z_to_bv 64 (SHF F)) (Z_to_bv 64 B) y28 y29 y30 y31)
FR (Z_to_bv 64 0x81240) fc None m' (seg_rom bsegs)
/\ mem_inv bsegs m' /\ stk bsegs m' lo SPA
/\ magree bsegs (fun a => aclient_addr CI LB SPA a /\ ~ (F + 1184 <= a < F + 1696)
/\ ~ (F + 1760 <= a < F + 1764) /\ ~ (F + 1776 <= a < F + 1780)) m m'
/\ AHEAP AI L RNG st LB m'.
Definition pD2_stmt : Prop :=
fse_read_stmtA AI rng_fs -> fse_iserror_stmtA ->
forall (L : alayout) (RNG : footprint) (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x25 x28 x29 x30 x31 : word)
(m : amem) (st : astate) (LB : list ablock) (SPA lo F P B : Z) (pB : aptr) (pl : list Z)
(tl msv dsz bsz rem : Z) (nc data junk : list Z) (j0 j16 jrt jtl : list byte),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
Forall (fun c => 0 <= c < 256) pl -> zlen pl < 2^26 ->
Forall (fun c => 0 <= c < 256) junk -> zlen junk = bsz - dsz ->
AHEAP AI L RNG st LB m ->
(forall F' k, ~ In (mkABlock (ABFake 0) F' k) LB) ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
In (FB5 F) LB -> In (HB pB B bsz) LB ->
bv_unsigned sp mod 16 = 0 -> SPA = (bv_unsigned sp - 224) - (bv_unsigned sp - 224) mod 32 ->
stk bsegs m lo SPA -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK -> bv_unsigned sp + 16 <= al_top L ->
tp = Z_to_bv 64 ATP ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
rw_cells bsegs m SPA (FRA_E F tl msv dsz j0 j16) ->
u8arr bsegs m (F + 608) (u16s (map (Z_to_bv 64) nc)) ->
rw_cells bsegs m (F + 1184) [CB 512 jrt] ->
rw_cells bsegs m (F + 1760) [C4 (Z_to_bv 64 255)] ->
rw_cells bsegs m (F + 1776) [CB 4 jtl] ->
u8arr bsegs m B (map (Z_to_bv 8) (data ++ junk)) ->
rw_cells bsegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
mem_inv bsegs m ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG -> rng RNG F 2048 -> rng RNG (shad F) 256 ->
evtF bsegs RNG (pD2_post L RNG gp tp sp FR fc st LB SPA lo F P B m)
(MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 2147450880) x20 x21 (Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 (F + 608))
x25 (Z_to_bv 64 (SHF F)) (Z_to_bv 64 B) x28 x29 x30 x31)
FR (Z_to_bv 64 0x8114c) fc None m (seg_rom bsegs)).
End D2.
End CANSEC1.
