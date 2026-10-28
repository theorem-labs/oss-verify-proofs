(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).
Definition PFSE_WBOUND : Z := 0x13900.
Definition PFSE_WRITE : Z := 0x13924.
Definition PFSE_ISERROR : Z := 0x13d50.
Definition PFSE_READ : Z := 0x14528.
Definition PPROD_U32R : Z := 0x14580.
Definition PPROD_I32R : Z := 0x1464c.
Definition fse_iserror_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (c : Z) (m : fmem) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (2^64 - 119 <=? c))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).
Definition fse_iserror_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (c : Z),
0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
evt usegs (fse_iserror_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_ISERROR) fc None m (seg_rom usegs)).
Definition fse_wbound_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (msv tl : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists a1',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (write_bound msv tl)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).
Definition fse_wbound_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (msv tl : Z),
0 <= msv < 2^16 -> 0 <= tl < 2^16 ->
a0 = Z_to_bv 64 msv -> a1 = Z_to_bv 64 tl ->
evt usegs (fse_wbound_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msv tl m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_WBOUND) fc None m (seg_rom usegs)).
Definition prod_at (m : fmem) (P D size : Z) : Prop :=
rw_cells usegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_at (m : fmem) (D : Z) (pl : list Z) : Prop :=
bytes_at usegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.
Definition prod_u32r_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo SPV
/\ prod_at m' P D (snd (uint32Range pl size mn mx)).
Definition prod_u32r_stmt : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
0 < P -> P mod 8 = 0 -> 0 < D ->
stk usegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
mem_inv usegs m ->
0 <= mn <= mx -> mx - mn < 2^24 -> mx < 2^31 ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
evt usegs (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PPROD_U32R) fc None m (seg_rom usegs)).
Definition prod_i32r_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (int32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(P + 8, P + 16); (SPV - 32, SPV)] m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo SPV
/\ prod_at m' P D (snd (int32Range pl size mn mx)).
Definition prod_i32r_stmt : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
0 < P -> P mod 8 = 0 -> 0 < D ->
stk usegs m lo SPV -> lo <= SPV - 32 -> 0 <= SPV < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
mem_inv usegs m ->
- 2^31 <= mn <= mx -> mx - mn < 2^24 -> mx < 2^31 ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
evt usegs (prod_i32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PPROD_I32R) fc None m (seg_rom usegs)).
Definition FSE_READ_STACK : Z := 256.
Definition fse_read_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV NC MSVP TLP : Z) (rt0 rt : list Z) (msv tl n lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - FSE_READ_STACK, SPV)] m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo SPV
/\ u8arr usegs m' NC (u16s (map (Z_to_bv 64) rt))
/\ rw_cells usegs m' MSVP [C4 (Z_to_bv 64 msv)]
/\ rw_cells usegs m' TLP [C4 (Z_to_bv 64 tl)].
Definition fse_read_stmt : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV NC MSVP TLP BUF : Z)
(rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word),
u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
rw_cells usegs m TLP [C4 tl0] ->
bytes_at usegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) ->
0 <= msv0 <= 255 -> zlen buf <= 65536 ->
0 < NC -> NC mod 2 = 0 -> 0 < MSVP -> MSVP mod 4 = 0 -> 0 < TLP -> TLP mod 4 = 0 -> 0 < BUF ->
BUF + zlen buf + 8 <= 2^64 ->
stk usegs m lo SPV -> lo <= SPV - FSE_READ_STACK -> 0 <= SPV < 2^64 ->
(NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) ->
(TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
(NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
(NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
(MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
(MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
mem_inv usegs m ->
a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
evt usegs (fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_READ) fc None m (seg_rom usegs)).
Definition FSE_WRITE_STACK : Z := 128.
Definition fse_write_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV BUF : Z) (buf0 buf' : list Z) (n lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(BUF, BUF + zlen buf0); (SPV - FSE_WRITE_STACK, SPV)] m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo SPV
/\ u8arr usegs m' BUF (map (Z_to_bv 8) buf').
Definition fse_write_stmt : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV BUF NC : Z)
(buf0 buf' nc : list Z) (msv tl n lo : Z),
u8arr usegs m BUF (map (Z_to_bv 8) buf0) -> Forall (fun c => 0 <= c < 256) buf0 ->
bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)) -> Forall (fun c => - 32768 <= c < 32768) nc ->
write_ncount buf0 nc msv tl = Ok (buf', n) ->
0 <= msv <= 255 -> 0 <= tl < 2^32 -> zlen buf0 <= 65536 ->
0 < BUF -> 0 < NC -> NC mod 2 = 0 ->
BUF + zlen buf0 < 2^64 -> NC + 2 * zlen nc < 2^64 ->
stk usegs m lo SPV -> lo <= SPV - FSE_WRITE_STACK -> 0 <= SPV < 2^64 ->
(BUF + zlen buf0 <= SPV - FSE_WRITE_STACK \/ SPV <= BUF) -> (NC + 2 * zlen nc <= SPV - FSE_WRITE_STACK \/ SPV <= NC) ->
(NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC) ->
mem_inv usegs m ->
a0 = Z_to_bv 64 BUF -> a1 = Z_to_bv 64 (zlen buf0) -> a2 = Z_to_bv 64 NC -> a3 = Z_to_bv 64 msv -> a4 = Z_to_bv 64 tl ->
evt usegs (fse_write_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BUF buf0 buf' n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_WRITE) fc None m (seg_rom usegs)).
