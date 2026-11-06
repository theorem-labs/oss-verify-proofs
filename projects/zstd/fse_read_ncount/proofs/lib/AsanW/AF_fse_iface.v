(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Image ZBridge Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells.
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
Notation zlen l := (Z.of_nat (length l)).
Definition AFSE_WBOUND : Z := 0x8165c.
Definition AFSE_WRITE : Z := 0x81680.
Definition AFSE_ISERROR : Z := 0x81ba0.
Definition APROD_U32R : Z := 0x825e8.
Definition APROD_I32R : Z := 0x82728.
Section CANSEC1. Context {rc : runConstT}.
Definition fse_iserror_postA (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (c : Z) (m : amem) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (2^64 - 119 <=? c))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).
Definition fse_iserror_stmtA : Prop :=
forall (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
evtF asegs RNG (fse_iserror_postA ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFSE_ISERROR) fc None m (seg_rom asegs)).
Definition fse_wbound_postA (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (msv tl : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists a1',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (write_bound msv tl)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).
Definition fse_wbound_stmtA : Prop :=
forall (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (msv tl : Z),
0 <= msv < 2^16 -> 0 <= tl < 2^16 ->
a0 = Z_to_bv 64 msv -> a1 = Z_to_bv 64 tl ->
evtF asegs RNG (fse_wbound_postA ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msv tl m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFSE_WBOUND) fc None m (seg_rom asegs)).
Definition prod_atA (m : amem) (P D size : Z) : Prop :=
rw_cells asegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_atA (m : amem) (D : Z) (pl : list Z) : Prop :=
bytes_at asegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.
Definition prod_u32r_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo SPV
/\ prod_atA m' P D (snd (uint32Range pl size mn mx)).
Definition prod_u32r_stmtA : Prop :=
forall (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
prod_atA m P D size -> payload_atA m D pl -> 0 <= size <= zlen pl ->
0 < P -> P mod 8 = 0 -> 0 < D ->
stk asegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
mem_inv asegs m ->
0 <= mn <= mx -> mx - mn < 2^24 -> mx < 2^31 ->
ablk P (P + 16) -> (0 < zlen pl -> ablk D (D + zlen pl)) -> D mod 8 = 0 -> KHIGH <= lo ->
rt_got m -> rt_shbase m ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
rng_aimg RNG -> rng RNG lo (SPV - lo) ->
rng RNG P 16 -> rng RNG (shad P) 2 -> rng RNG D (zlen pl) -> rng RNG (shad D) (nshad (zlen pl)) ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
evtF asegs RNG (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APROD_U32R) fc None m (seg_rom asegs)).
Definition prod_i32r_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (int32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(P + 8, P + 16); (SPV - 32, SPV)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo SPV
/\ prod_atA m' P D (snd (int32Range pl size mn mx)).
Definition prod_i32r_stmtA : Prop :=
forall (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
prod_atA m P D size -> payload_atA m D pl -> 0 <= size <= zlen pl ->
0 < P -> P mod 8 = 0 -> 0 < D ->
stk asegs m lo SPV -> lo <= SPV - 32 -> 0 <= SPV < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
mem_inv asegs m ->
- 2^31 <= mn <= mx -> mx - mn < 2^24 -> mx < 2^31 ->
ablk P (P + 16) -> (0 < zlen pl -> ablk D (D + zlen pl)) -> D mod 8 = 0 -> KHIGH <= lo ->
rt_got m -> rt_shbase m ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
rng_aimg RNG -> rng RNG lo (SPV - lo) ->
rng RNG P 16 -> rng RNG (shad P) 2 -> rng RNG D (zlen pl) -> rng RNG (shad D) (nshad (zlen pl)) ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
evtF asegs RNG (prod_i32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APROD_I32R) fc None m (seg_rom asegs)).
Definition FSE_WRITE_STACK_A : Z := 96.
Definition fse_write_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV BUF : Z) (buf0 buf' : list Z) (n lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(BUF, BUF + zlen buf0); (SPV - FSE_WRITE_STACK_A, SPV)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo SPV
/\ u8arr asegs m' BUF (map (Z_to_bv 8) buf').
Definition fse_write_stmtA : Prop :=
forall (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BUF NC : Z)
(buf0 buf' nc : list Z) (msv tl n lo : Z),
u8arr asegs m BUF (map (Z_to_bv 8) buf0) -> Forall (fun c => 0 <= c < 256) buf0 ->
bytes_at asegs m NC (u16s (map (Z_to_bv 64) nc)) -> Forall (fun c => - 32768 <= c < 32768) nc ->
write_ncount buf0 nc msv tl = Ok (buf', n) ->
0 <= msv <= 255 -> 0 <= tl < 2^32 -> zlen buf0 <= 65536 ->
0 < BUF -> 0 < NC -> NC mod 2 = 0 ->
stk asegs m lo SPV -> lo <= SPV - FSE_WRITE_STACK_A -> 0 <= SPV < 2^64 ->
(BUF + zlen buf0 <= SPV - FSE_WRITE_STACK_A \/ SPV <= BUF) -> (NC + 2 * zlen nc <= SPV - FSE_WRITE_STACK_A \/ SPV <= NC) ->
(NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC) ->
mem_inv asegs m ->
ablk BUF (BUF + zlen buf0) -> ablk NC (NC + 2 * zlen nc) -> BUF mod 8 = 0 -> NC mod 8 = 0 -> KHIGH <= lo ->
rt_got m -> rt_shbase m ->
unpoisoned m BUF (BUF + zlen buf0) -> unpoisoned m NC (NC + 2 * zlen nc) ->
rng_aimg RNG -> rng RNG lo (SPV - lo) ->
rng RNG BUF (zlen buf0) -> rng RNG (shad BUF) (nshad (zlen buf0)) ->
rng RNG NC (2 * zlen nc) -> rng RNG (shad NC) (nshad (2 * zlen nc)) ->
a0 = Z_to_bv 64 BUF -> a1 = Z_to_bv 64 (zlen buf0) -> a2 = Z_to_bv 64 NC -> a3 = Z_to_bv 64 msv -> a4 = Z_to_bv 64 tl ->
evtF asegs RNG (fse_write_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BUF buf0 buf' n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFSE_WRITE) fc None m (seg_rom asegs)).
End CANSEC1.
