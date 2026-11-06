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
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AHarness_iface AFake5_iface AH_fse_kit.
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
Definition FRA_E (F tl B : Z) (j16 : list byte) : list cell :=
[C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 B); CB 16 j16; C8 (Z_to_bv 64 F)].
Definition pE1_stmt : Prop :=
forall (RNG : footprint) (gp tp s0 s2 s3 s4 s5 s6 s7 s9 s10 : word) (FR : bvmap 5 word) (fc : bv 32)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : amem) (SPA F P tl B : Z) (j16 : list byte),
0 <= SPA -> SPA + 88 <= 2^64 -> KHIGH <= SPA ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
rw_cells asegs m SPA (FRA_E F tl B j16) ->
rw_cells asegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
mem_inv asegs m -> fse_rt m ->
rng RNG SPA 88 -> rng RNG (shad F) 256 -> rng_aimg RNG ->
evtF asegs RNG
(fun ms' => exists m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ms' = MS (mkR (Z_to_bv 64 0x812fc) (Z_to_bv 64 SPA) gp tp y5 y6 y7 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 P) y11 y12 y13 y14 y15 y16 y17
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 P) s9 s10 (Z_to_bv 64 (SHF F)) y28 y29 y30 y31)
FR (Z_to_bv 64 0x825e4) fc None m' (seg_rom asegs)
/\ munch [(SHF F, SHF F + 256)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' SPA (FRA_E F tl B j16)
/\ rw_cells asegs m' (SHF F) (FSH Z64 Z64 F8S BF8 BF8))
(MS (mkR (Z_to_bv 64 0x812dc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 s0 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 P) s9 s10 (Z_to_bv 64 (SHF F)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x812dc) fc None m (seg_rom asegs)).
Section E2.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition pE2_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32) (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP AI L RNG st LB m'.
Definition pE2_stmt : Prop :=
forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word)
(m : amem) (st : astate) (LB : list ablock) (SPA lo F P tl B : Z) (j0 j1 j2 : word) (j16 : list byte),
AHEAP AI L RNG st (FB5 F :: LB) m ->
(forall b, In b LB -> exists p A n, b = HB p A n) ->
bv_unsigned sp mod 16 = 0 -> SPA = (bv_unsigned sp - 192) - (bv_unsigned sp - 192) mod 32 ->
stk asegs m lo SPA -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK -> bv_unsigned sp + 16 <= al_top L ->
tp = Z_to_bv 64 ATP ->
rw_cells asegs m SPA (FRA_E F tl B j16) ->
stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
rw_cells asegs m (bv_unsigned sp + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
rw_cells asegs m F [C8 j0; C8 j1; C8 j2] ->
rw_cells asegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells asegs m (SHF F) (FSH Z64 Z64 F8S BF8 BF8) ->
mem_inv asegs m ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG -> rng RNG F 2048 -> rng RNG (shad F) 256 ->
stack_free_5_stmt AI fflag rng_fs ->
evtF asegs RNG (pE2_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
(MS (mkR (Z_to_bv 64 0x812fc) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 F) x19 x20 x21 x22 x23 (Z_to_bv 64 P) x25 x26 (Z_to_bv 64 (SHF F)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x812fc) fc None m (seg_rom asegs)).
End E2.
End CANSEC1.
