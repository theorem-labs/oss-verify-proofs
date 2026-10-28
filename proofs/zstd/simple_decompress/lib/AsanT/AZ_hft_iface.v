(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_huf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation zlen l := (Z.of_nat (length l)).
Notation FSE_BDT_STACK_A := 192 (only parsing).   (* [comment removed for export] *)
Notation FSE_DEC_STACK_A := 4992 (only parsing).   (* [comment removed for export] *)
Notation FSE_DEC_DEPTH := 3 (only parsing).

Section CANSEC1. Context {rc : runConstT}.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APHUF_RSTATS : Z := 0xab294.   (* [comment removed for export] *)
Definition APFSE_BDT : Z := 0xab764.   (* [comment removed for export] *)
Definition APFSE_DEC : Z := 0xabea0.   (* [comment removed for export] *)
Definition APFSE_BITINIT : Z := 0xadd08.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_dtable (m : amem) (DT tl fast : Z) (tb : list Z) : Prop :=
  rw_cells bsegs m DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)] /\
  u8arr bsegs m (DT + 4) (map (Z_to_bv 8) tb) /\ zlen tb = 4 * 2^tl /\
  0 <= fast <= 1 /\ Forall (fun v => 0 <= v < 256) tb /\
  forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u.


(* [comment removed for export] *)
Definition fse_bdt_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DT W wlen tl lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - FSE_BDT_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV /\ stk bsegs m' W (W + wlen) /\ 0 <= r < 2^64
    /\ ((r = 0 /\ exists fast tb, fse_dtable m' DT tl fast tb)
        \/ (zd_is_error r = true /\ stk bsegs m' DT (DT + 4 + 4 * 2^tl))).

(* [comment removed for export] *)
Definition fse_bdt_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DT NC W wlen maxSV tl lo : Z) (norm : list Z),
  (* [comment removed for export] *)
  areg RNG m DT (4 + 4 * 2^tl) -> areg RNG m W wlen -> aro RNG m NC (2 * zlen norm) ->
  art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FSE_BDT_STACK_A -> SPV < 2^47 ->
  DT mod 4 = 0 -> W mod 2 = 0 -> NC mod 2 = 0 ->      (* [comment removed for export] *)
  stk bsegs m DT (DT + 4 + 4 * 2^tl) -> 4096 <= DT -> DT + 4 + 4 * 2^tl < 2^47 ->
  stk bsegs m W (W + wlen) -> 4096 <= W -> 0 <= wlen < 2^32 -> W + wlen < 2^47 ->
  bytes_at bsegs m NC (u16s (map (Z_to_bv 64) norm)) -> 4096 <= NC -> NC + 2 * zlen norm < 2^47 ->
  5 <= tl <= 9 -> 0 <= maxSV <= 255 -> maxSV + 1 <= zlen norm ->
  (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
  wsum (firstn (Z.to_nat (maxSV + 1)) norm) = 2^tl ->
  (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT) -> (W + wlen <= lo \/ SPV <= W) -> (NC + 2 * zlen norm <= lo \/ SPV <= NC) ->
  (DT + 4 + 4 * 2^tl <= W \/ W + wlen <= DT) -> (DT + 4 + 4 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT) ->
  (W + wlen <= NC \/ NC + 2 * zlen norm <= W) ->
  evtF bsegs RNG (fse_bdt_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 tl)
               (Z_to_bv 64 W) (Z_to_bv 64 wlen) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APFSE_BDT) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fbit_ok (SRC n bc ptr : Z) : Prop :=
  0 <= bc <= 4096 /\ (bc <= 64 -> ptr = SRC \/ (8 <= n /\ SRC <= ptr <= SRC + n - 8)).





(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition fse_dec_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DST cap WK wksz lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DST, DST + cap); (WK, WK + wksz); (SPV - FSE_DEC_STACK_A, SPV)] ++ fake_area L) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(DST, DST + cap); (WK, WK + wksz)] LB m m' /\ AHEAP AI L RNG st LB m' /\ stk bsegs m' DST (DST + cap) /\ stk bsegs m' WK (WK + wksz)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= cap).

Definition fse_dec_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DST cap SRC n ml WK wksz lo : Z) (src : list byte),
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV FSE_DEC_DEPTH -> azstk RNG m lo SPV -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m ->
  areg RNG m DST cap -> ainblk LB DST cap -> aregU RNG m SRC n -> ahull RNG m SRC n -> ainimg LB SRC n ->   (* [comment removed for export] *)
  WK mod 4 = 0 -> areg RNG m WK wksz -> ahull RNG m WK wksz -> ainblk LB WK wksz ->
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FSE_DEC_STACK_A -> SPV < 2^47 ->
  stk bsegs m DST (DST + cap) -> 4096 <= DST -> 0 <= cap <= 65536 -> DST + cap < 2^47 ->
  bytes_at bsegs m SRC src -> zlen src = n -> 4096 <= SRC -> n <= 65536 -> SRC + n < 2^47 ->
  stk bsegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 ->
  0 <= ml <= 9 ->
  (DST + cap <= lo \/ SPV <= DST) -> (WK + wksz <= lo \/ SPV <= WK) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (DST + cap <= WK \/ WK + wksz <= DST) -> (DST + cap <= SRC \/ SRC + n <= DST) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  evtF bsegs RNG (fse_dec_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 cap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 ml) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APFSE_DEC) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
