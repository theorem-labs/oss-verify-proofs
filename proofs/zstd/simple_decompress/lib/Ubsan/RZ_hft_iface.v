(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_RSTATS : Z := 0x2a2b4.       (* [comment removed for export] *)
Definition PFSE_BDT : Z := 0x2a660.          (* [comment removed for export] *)
Definition PFSE_DEC : Z := 0x2ab4c.          (* [comment removed for export] *)
Definition PFSE_BITINIT : Z := 0x2bd40.      (* [comment removed for export] *)
Definition PFSE_INITDS : Z := 0x2bfd4.       (* [comment removed for export] *)
Definition FSE_ZEROFILLED : Z := 0x112d0.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_dtable (m : fmem) (DT tl fast : Z) (tb : list Z) : Prop :=
  rw_cells usegs m DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)] /\
  u8arr usegs m (DT + 4) (map (Z_to_bv 8) tb) /\ zlen tb = 4 * 2^tl /\
  0 <= fast <= 1 /\ Forall (fun v => 0 <= v < 256) tb /\
  forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u.

Definition FSE_BDT_STACK : Z := 128.

(* [comment removed for export] *)
Definition fse_bdt_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DT W wlen tl lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 128, SPV)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' W (W + wlen) /\ 0 <= r < 2^64
    /\ ((r = 0 /\ exists fast tb, fse_dtable m' DT tl fast tb)
        \/ (zd_is_error r = true /\ stk usegs m' DT (DT + 4 + 4 * 2^tl))).

(* [comment removed for export] *)
Definition fse_bdt_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DT NC W wlen maxSV tl lo : Z) (norm : list Z),
  mem_inv usegs m ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - 128 -> SPV < 2^47 ->
  DT mod 4 = 0 -> W mod 2 = 0 -> NC mod 2 = 0 ->
  stk usegs m DT (DT + 4 + 4 * 2^tl) -> 4096 <= DT -> DT + 4 + 4 * 2^tl < 2^47 ->
  stk usegs m W (W + wlen) -> 4096 <= W -> 0 <= wlen < 2^32 -> W + wlen < 2^47 ->
  bytes_at usegs m NC (u16s (map (Z_to_bv 64) norm)) -> 4096 <= NC -> NC + 2 * zlen norm < 2^47 ->
  5 <= tl <= 9 -> 0 <= maxSV <= 255 -> maxSV + 1 <= zlen norm ->
  (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
  wsum (firstn (Z.to_nat (maxSV + 1)) norm) = 2^tl ->
  (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT) -> (W + wlen <= lo \/ SPV <= W) -> (NC + 2 * zlen norm <= lo \/ SPV <= NC) ->
  (DT + 4 + 4 * 2^tl <= W \/ W + wlen <= DT) -> (DT + 4 + 4 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT) ->
  (W + wlen <= NC \/ NC + 2 * zlen norm <= W) ->
  evt usegs (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 tl)
               (Z_to_bv 64 W) (Z_to_bv 64 wlen) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_BDT) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fbit_ok (SRC n bc ptr : Z) : Prop :=
  0 <= bc <= 4096 /\ (bc <= 64 -> ptr = SRC \/ (8 <= n /\ SRC <= ptr <= SRC + n - 8)).

Definition fse_initds_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ST BD SRC n DT tl bc : Z) (pad : list byte) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st cont' bc' ptr',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(ST, ST + 16); (BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' ST [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (DT + 4))] /\ 0 <= st < 2^tl
    /\ rw_cells usegs m' BD (bitd_cells cont' (Z_to_bv 64 bc') pad ptr' SRC) /\ fbit_ok SRC n bc' ptr' /\ bc' <= bc + tl.

Definition fse_initds_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (ST BD SRC n DT tl fast bc ptr : Z) (cont : word) (pad src junk : list byte),
  mem_inv usegs m ->
  rw_cells usegs m ST [CB 16 junk] ->
  rw_cells usegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRC) -> fbit_ok SRC n bc ptr -> bc <= 2048 ->
  bytes_at usegs m SRC src -> zlen src = n ->
  bytes_at usegs m DT (le2 (Z_to_bv 64 tl)) -> 0 <= tl <= 12 ->
  4096 <= ST -> ST + 16 < 2^47 -> 4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 4 < 2^47 ->
  ST mod 8 = 0 -> BD mod 8 = 0 -> DT mod 2 = 0 ->
  (ST + 16 <= BD \/ BD + 40 <= ST) ->
  (ST + 16 <= SRC \/ SRC + n <= ST) -> (BD + 40 <= SRC \/ SRC + n <= BD) ->
  (ST + 16 <= DT \/ DT + 2 <= ST) -> (BD + 40 <= DT \/ DT + 2 <= BD) ->
  evt usegs (fse_initds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ST BD SRC n DT tl bc pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 BD) (Z_to_bv 64 DT) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_INITDS) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FSE_DEC_STACK : Z := 448.

Definition fse_dec_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DST cap WK wksz lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' DST (DST + cap) /\ stk usegs m' WK (WK + wksz)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= cap).

Definition fse_dec_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST cap SRC n ml WK wksz lo : Z) (src : list byte),
  mem_inv usegs m ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - 448 -> SPV < 2^47 -> SPV mod 16 = 0 ->
  stk usegs m DST (DST + cap) -> 4096 <= DST -> 0 <= cap <= 65536 -> DST + cap < 2^47 ->
  bytes_at usegs m SRC src -> zlen src = n -> 4096 <= SRC -> n <= 65536 -> SRC + n < 2^47 ->
  stk usegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  0 <= ml <= 9 ->
  (DST + cap <= lo \/ SPV <= DST) -> (WK + wksz <= lo \/ SPV <= WK) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (DST + cap <= WK \/ WK + wksz <= DST) -> (DST + cap <= SRC \/ SRC + n <= DST) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  evt usegs (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 cap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 ml) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_DEC) fc None m (seg_rom usegs)).

