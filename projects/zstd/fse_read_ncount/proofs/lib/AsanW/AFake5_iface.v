(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface F_memset F_asetshadow.
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
Definition ASM5_ENTRY : Z := 0x3d994.
Definition ASF5_ENTRY : Z := 0x3dba0.
Definition SM5_STACK : Z := 4096.
Definition SF5_STACK : Z := 64.
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Definition sm5_post (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP AI L RNG st (FB5 F :: LB) m'
/\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP
/\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))]
/\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) 32)
/\ rng RNG F 2048 /\ rng RNG (shad F) 256.
Definition stack_malloc_5_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
AHEAP AI L RNG st LB m ->
(forall F n, ~ In (mkABlock (ABFake 5) F n) LB) ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM5_STACK ->
bv_unsigned sp <= al_top L ->
tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
evtF asegs RNG (sm5_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASM5_ENTRY) fc None m (seg_rom asegs)).
Definition sf5_post (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(st : astate) (LB : list ablock) (lo F : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP AI L RNG st LB m'
/\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5)) 32).
Definition stack_free_5_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z) (sh : list byte),
AHEAP AI L RNG st (FB5 F :: LB) m ->
rw_cells asegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells asegs m (shad F) [CB 256 sh] ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SF5_STACK ->
bv_unsigned sp <= al_top L ->
a0 = Z_to_bv 64 F ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG -> rng RNG F 2048 -> rng RNG (shad F) 256 ->
evtF asegs RNG (sf5_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo F m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASF5_ENTRY) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.
