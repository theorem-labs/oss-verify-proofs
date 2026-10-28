(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PFSE_INIT_DSTATE : Z := 0x20ac0.   (* [comment removed for export] *)
Definition PFSE_BUILD_DT : Z := 0x1f14c.      (* [comment removed for export] *)
Definition PFSE_DECOMP : Z := 0x1f638.        (* [comment removed for export] *)
Definition PFSE_READNC_B : Z := 0x1e7b8.      (* [comment removed for export] *)
Definition PHUF_READ_STATS : Z := 0x1eda0.    (* [comment removed for export] *)
Definition BIT_MASK_TAB : Z := 0x10578.       (* [comment removed for export] *)
Definition ZEROFILLED_F : Z := 0x105f8.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bitdz_cells (S : Z) (d : bitD) (jp : list byte) : list cell :=
  [C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp;
   C8 (Z_to_bv 64 (if bd_zero d then ZEROFILLED_F else S + bd_ptr d)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].

(* [comment removed for export] *)
Definition bitd_ok (bs : list Z) (d : bitD) : Prop :=
  0 <= bd_cont d < 2^64 /\ 0 <= bd_bits d < 2^30 /\ 0 <= bd_ptr d /\ bd_ptr d + 8 <= Z.max 8 (zlen bs)
  /\ (zlen bs < 8 -> bd_ptr d = 0) /\ (bd_zero d = true -> 64 < bd_bits d).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_init_dstate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (DS BD DT S : Z) (v : Z) (d2 : bitD) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (jp : list byte) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DS, DS + 16); (BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' DS [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells usegs m' BD (bitdz_cells S d2 jp).

Definition fse_init_dstate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DS BD DT S tl : Z) (bs : list Z) (d : bitD) (jds jp : list byte)
         (fmw : word) (v : Z) (d1 : bitD) (st : dstatus) (d2 : bitD) (lo : Z),
  (* [comment removed for export] *)
  rw_cells usegs m DS [CB 16 jds] -> rw_cells usegs m BD (bitdz_cells S d jp) ->
  rw_cells usegs m DT [C2 (Z_to_bv 64 tl); C2 fmw] ->
  bytes_at usegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  (* [comment removed for export] *)
  0 <= tl <= 12 -> bitd_ok bs d ->
  read_bits d tl = Ok (v, d1) -> reload_dstream bs d1 = Ok (st, d2) ->
  (* [comment removed for export] *)
  0 < DS -> DS mod 8 = 0 -> 0 < BD -> BD mod 8 = 0 -> 0 < DT -> DT mod 2 = 0 -> DT + 4 < 2^64 -> 8 <= S -> S + Z.max 8 (zlen bs) + 8 <= 2^64 ->
  (DS + 16 <= BD \/ BD + 40 <= DS) -> (DS + 16 <= DT \/ DT + 4 <= DS) -> (BD + 40 <= DT \/ DT + 4 <= BD) ->
  (DS + 16 <= S \/ S + zlen bs <= DS) -> (BD + 40 <= S \/ S + zlen bs <= BD) ->
  stk usegs m lo (bv_unsigned sp) -> (DS + 16 <= lo \/ bv_unsigned sp <= DS) -> (BD + 40 <= lo \/ bv_unsigned sp <= BD) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DS -> a1 = Z_to_bv 64 BD -> a2 = Z_to_bv 64 DT ->
  evt usegs (fse_init_dstate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DS BD DT S v d2 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_INIT_DSTATE) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FSE_BUILD_STACK : Z := 128.

Definition fse_cell_bytes (c : dcell) : list byte :=
  le2 (Z_to_bv 64 (dc_newState c)) ++ [Z_to_bv 8 (dc_symbol c); Z_to_bv 8 (dc_nbBits c)].
Definition fse_dt_bytes (d : dtable) : list byte :=
  le2 (Z_to_bv 64 (dt_tableLog d)) ++ le2 (Z_to_bv 64 (dt_fastMode d)) ++ concat (map fse_cell_bytes (dt_cells d)).

Definition fse_build_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DT WK msv tl : Z) (d : dtable) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - FSE_BUILD_STACK, bv_unsigned sp); (DT, DT + FSE_DTABLE_SIZE tl);
              (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' DT (fse_dt_bytes d).

Definition fse_build_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DT NC WK wks msv tl : Z) (nc : list Z) (jdt jw : list byte)
         (d : dtable) (lo : Z),
  (* [comment removed for export] *)
  build_dtable nc msv tl wks = Ok d -> 0 <= msv -> 0 <= wks < 2^64 ->
  (* [comment removed for export] *)
  u8arr usegs m DT jdt -> zlen jdt = FSE_DTABLE_SIZE tl ->
  u8arr usegs m WK jw -> zlen jw = FSE_BUILD_DTABLE_WKSP_SIZE tl msv ->
  bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)) -> Forall (fun c => - 32768 <= c < 32768) nc ->
  (* [comment removed for export] *)
  0 < DT -> DT mod 4 = 0 -> 0 < WK -> WK mod 2 = 0 -> 0 < NC -> NC mod 2 = 0 ->
  (DT + FSE_DTABLE_SIZE tl <= WK \/ WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= DT) ->
  (DT + FSE_DTABLE_SIZE tl <= NC \/ NC + 2 * zlen nc <= DT) ->
  (WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= NC \/ NC + 2 * zlen nc <= WK) ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FSE_BUILD_STACK ->
  (DT + FSE_DTABLE_SIZE tl <= lo \/ bv_unsigned sp <= DT) ->
  (WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= lo \/ bv_unsigned sp <= WK) ->
  (NC + 2 * zlen nc <= lo \/ bv_unsigned sp <= NC) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DT -> a1 = Z_to_bv 64 NC -> a2 = Z_to_bv 64 msv -> a3 = Z_to_bv 64 tl -> a4 = Z_to_bv 64 WK ->
  a5 = Z_to_bv 64 wks ->
  evt usegs (fse_build_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT WK msv tl d lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_BUILD_DT) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FSE_READ_STACK : Z := 256.

Definition fse_readh_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV NC MSVP TLP : Z) (rt0 : list Z) (msv0 : Z) (buf : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : fmem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - FSE_READ_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ 0 <= r < 2^64
    /\ match read_ncount rt0 msv0 buf with
       | Ok (rt, msv, tl, n) => r = n /\ u8arr usegs m' NC (u16s (map (Z_to_bv 64) rt))
                                /\ rw_cells usegs m' MSVP [C4 (Z_to_bv 64 msv)] /\ rw_cells usegs m' TLP [C4 (Z_to_bv 64 tl)]
       | Err e => r = 2^64 - e /\ 0 < e < 120
       | Ub | NoFuel => False
       end.

Definition fse_readh_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV NC MSVP TLP BUF : Z)
         (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word),
  (* [comment removed for export] *)
  u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
  rw_cells usegs m TLP [C4 tl0] ->
  bytes_at usegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen buf <= 65536 ->
  0 < NC -> NC mod 2 = 0 -> 0 < MSVP -> MSVP mod 4 = 0 -> 0 < TLP -> TLP mod 4 = 0 -> 0 < BUF ->   (* [comment removed for export] *)
  BUF + zlen buf + 8 <= 2^64 ->    (* [comment removed for export] *)
  (* [comment removed for export] *)
  stk usegs m lo SPV -> lo <= SPV - FSE_READ_STACK -> 0 <= SPV < 2^64 ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) ->
  (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  evt usegs (fse_readh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 msv0 buf lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_READNC_B) fc None m (seg_rom usegs)).
