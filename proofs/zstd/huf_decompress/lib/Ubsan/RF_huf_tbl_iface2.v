(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FSE_DECOMP_STACK : Z := 448.     (* [comment removed for export] *)

Definition fse_decomp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DST dcap W wks maxLog : Z) (src : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - FSE_DECOMP_STACK, bv_unsigned sp); (DST, DST + dcap); (W, W + wks)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ 0 <= r < 2^64
    /\ match fse_decompress_wksp (repeat 0 256) dcap src maxLog wks with
       | Ok l => r = zlen l /\ exists jrest, u8arr usegs m' DST (map (Z_to_bv 8) l ++ jrest) /\ zlen jrest = dcap - zlen l
       | Err e => r = 2^64 - e /\ 0 < e < 120
       | Ub | NoFuel => False
       end.

Definition fse_decomp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DST dcap S W wks maxLog : Z) (src : list Z) (jd jw : list byte) (lo : Z),
  (* [comment removed for export] *)
  u8arr usegs m DST jd -> zlen jd = dcap ->
  bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  u8arr usegs m W jw -> zlen jw = wks ->
  0 <= dcap <= 255 -> zlen src <= 65536 -> 0 <= maxLog <= 12 -> wks < 2^32 ->
  (* [comment removed for export] *)
  4 <= DST -> 8 <= S -> 0 < W -> W mod 4 = 0 ->
  DST + dcap <= lo -> S + zlen src <= lo -> W + wks <= lo ->
  (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FSE_DECOMP_STACK -> bv_unsigned sp mod 16 = 0 ->
  bv_unsigned sp <= 2^47 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 maxLog ->
  a5 = Z_to_bv 64 W -> a6 = Z_to_bv 64 wks ->
  evt usegs (fse_decomp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap W wks maxLog src lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_DECOMP) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HUF_RSTATS_STACK : Z := 512.     (* [comment removed for export] *)

Definition huf_rstats_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (HW RK NSP TLP W : Z) (src : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - HUF_RSTATS_STACK, bv_unsigned sp); (HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4);
              (TLP, TLP + 4); (W, W + 876)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ 0 <= r < 2^64
    /\ match read_stats src with
       | Ok h => r = hs_ret h
                 /\ (exists jrest, u8arr usegs m' HW (map (Z_to_bv 8) (hs_weights h) ++ jrest)
                                   /\ zlen jrest = 256 - hs_nbSymbols h)
                 /\ u32arr usegs m' RK (map (Z_to_bv 64) (hs_rank h))
                 /\ rw_cells usegs m' NSP [C4 (Z_to_bv 64 (hs_nbSymbols h))]
                 /\ rw_cells usegs m' TLP [C4 (Z_to_bv 64 (hs_tableLog h))]
       | Err e => r = 2^64 - e /\ 0 < e < 120
       | Ub | NoFuel => False
       end.

Definition huf_rstats_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (HW RK NSP TLP S W : Z) (src : list Z) (jh jr jw : list byte)
         (nsv tlv : word) (lo : Z),
  (* [comment removed for export] *)
  u8arr usegs m HW jh -> zlen jh = 256 ->
  u8arr usegs m RK jr -> zlen jr = 52 ->
  rw_cells usegs m NSP [C4 nsv] -> rw_cells usegs m TLP [C4 tlv] ->
  bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  u8arr usegs m W jw -> zlen jw = 876 ->
  rw_cells usegs m (bv_unsigned sp) [C8 (Z_to_bv 64 876)] ->
  (* [comment removed for export] *)
  4 <= HW -> 0 < RK -> 7 <= S -> 0 < W -> W mod 4 = 0 -> RK mod 4 = 0 -> NSP mod 4 = 0 -> TLP mod 4 = 0 ->
  HW + 256 <= lo -> RK + 52 <= lo -> S + zlen src <= lo -> W + 876 <= lo ->
  (HW + 256 <= RK \/ RK + 52 <= HW) -> (HW + 256 <= S \/ S + zlen src <= HW) -> (HW + 256 <= W \/ W + 876 <= HW) ->
  (RK + 52 <= S \/ S + zlen src <= RK) -> (RK + 52 <= W \/ W + 876 <= RK) -> (S + zlen src <= W \/ W + 876 <= S) ->
  bv_unsigned sp + 8 <= NSP -> NSP + 4 <= TLP ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HUF_RSTATS_STACK -> bv_unsigned sp mod 16 = 0 ->
  bv_unsigned sp <= 2^47 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 HW -> a1 = Z_to_bv 64 256 -> a2 = Z_to_bv 64 RK -> a3 = Z_to_bv 64 NSP -> a4 = Z_to_bv 64 TLP ->
  a5 = Z_to_bv 64 S -> a6 = Z_to_bv 64 (zlen src) -> a7 = Z_to_bv 64 W ->
  evt usegs (huf_rstats_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW RK NSP TLP W src lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_READ_STATS) fc None m (seg_rom usegs)).
