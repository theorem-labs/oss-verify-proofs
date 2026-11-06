(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AHarness_iface AFake5_iface AH_fse_kit.
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
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition FRA_E (F tl msv dsz : Z) (j0 j16 : list byte) : list cell :=
[CB 24 j0; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (F + 1760));
C8 (Z_to_bv 64 dsz); C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 j16;
C8 (Z_to_bv 64 F)].
Definition pE1_stmt : Prop :=
forall (RNG : footprint) (gp tp s0 s2 s3 s4 s5 s6 s8 s9 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : amem) (SPA F P tl msv dsz : Z) (j0 j16 : list byte),
0 <= SPA -> SPA + 120 <= 2^64 -> KHIGH <= SPA ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
rw_cells bsegs m SPA (FRA_E F tl msv dsz j0 j16) ->
rw_cells bsegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
mem_inv bsegs m -> fse_rt m ->
rng RNG SPA 120 -> rng RNG (shad F) 256 -> rng_aimg RNG ->
evtF bsegs RNG
(fun ms' => exists m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ms' = MS (mkR (Z_to_bv 64 0x81268) (Z_to_bv 64 SPA) gp tp y5 y6 y7 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 P) y11 y12 y13 y14 y15 y16 y17
s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 (Z_to_bv 64 (SHF F)) s11 y28 y29 y30 y31)
FR (Z_to_bv 64 0x8272c) fc None m' (seg_rom bsegs)
/\ munch [(SHF F, SHF F + 256)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' SPA (FRA_E F tl msv dsz j0 j16)
/\ rw_cells bsegs m' (SHF F) (FSH Z64 Z64 F8S BF8 BF8))
(MS (mkR (Z_to_bv 64 0x81248) (Z_to_bv 64 SPA) gp tp x5 x6 x7 s0 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 (Z_to_bv 64 (SHF F)) s11 x28 x29 x30 x31)
FR (Z_to_bv 64 0x81248) fc None m (seg_rom bsegs)).
Section E2.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition pE2_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32) (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom bsegs)
/\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP AI L RNG st LB m'.
Definition pE2_stmt : Prop :=
forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word)
(m : amem) (st : astate) (LB : list ablock) (SPA lo F P tl msv dsz : Z) (j0 j1 j2 : word) (k0 j16 : list byte),
AHEAP AI L RNG st (FB5 F :: LB) m ->
(forall b, In b LB -> exists p A n, b = HB p A n) ->
bv_unsigned sp mod 16 = 0 -> SPA = (bv_unsigned sp - 224) - (bv_unsigned sp - 224) mod 32 ->
stk bsegs m lo SPA -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK -> bv_unsigned sp + 16 <= al_top L ->
tp = Z_to_bv 64 ATP ->
rw_cells bsegs m SPA (FRA_E F tl msv dsz k0 j16) ->
stk bsegs m (SPA + 120) (bv_unsigned sp + -104) ->
rw_cells bsegs m (bv_unsigned sp + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
rw_cells bsegs m F [C8 j0; C8 j1; C8 j2] ->
rw_cells bsegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells bsegs m (SHF F) (FSH Z64 Z64 F8S BF8 BF8) ->
mem_inv bsegs m ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG -> rng RNG F 2048 -> rng RNG (shad F) 256 ->
stack_free_5_stmt AI fflag rng_fs ->
evtF bsegs RNG (pE2_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
(MS (mkR (Z_to_bv 64 0x81268) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 P) x24 x25 (Z_to_bv 64 (SHF F)) x27 x28 x29 x30 x31)
FR (Z_to_bv 64 0x81268) fc None m (seg_rom bsegs)).
End E2.
End CANSEC1.
