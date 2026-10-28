(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufStats.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation HUF_RSTATS_STACK_A := 5056 (only parsing).   (* [comment removed for export] *)
Notation HUF_RSTATS_DEPTH := 3 (only parsing).

Section CANSEC1. Context {rc : runConstT}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition huf_rstats_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV HW RS NBP TLP n WK wksz lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz); (SPV - HUF_RSTATS_STACK_A, SPV)] ++ fake_area L) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz)] LB m m' /\ AHEAP AI L RNG st LB m' /\ stk bsegs m' WK (WK + wksz) /\ 0 <= r < 2^64
    /\ ((zd_is_error r = false /\ 1 <= r <= n /\ exists hw rank tl nbs,
           u8arr bsegs m' HW (map (Z_to_bv 8) hw) /\ zlen hw = 256 /\ Forall (fun v => 0 <= v < 256) hw /\
           u32arr bsegs m' RS (map (Z_to_bv 64) rank) /\
           rw_cells bsegs m' NBP [C4 (Z_to_bv 64 nbs)] /\ rw_cells bsegs m' TLP [C4 (Z_to_bv 64 tl)] /\
           huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl /\ 2 <= nbs <= 256)
        \/ (zd_is_error r = true /\ stk bsegs m' HW (HW + 256) /\ stk bsegs m' RS (RS + 52) /\ stk bsegs m' NBP (NBP + 4) /\ stk bsegs m' TLP (TLP + 4))).

Definition huf_rstats_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV HW RS NBP TLP SRC n WK wksz lo B bsz : Z) (src : list byte),
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV HUF_RSTATS_DEPTH -> azstk RNG m lo SPV -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m ->
  areg RNG m B bsz -> ahull RNG m B bsz -> ainblk LB B bsz -> aro RNG m NBP 4 -> ainblk LB NBP 4 -> aro RNG m TLP 4 -> ainblk LB TLP 4 ->
  areg RNG m SRC n -> (0 < n -> ainimg LB SRC n) -> (0 < n -> ahull RNG m SRC n) ->
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - HUF_RSTATS_STACK_A ->
  bytes_at bsegs m SPV (le8 (Z_to_bv 64 wksz)) ->
  stk bsegs m HW (HW + 256) -> stk bsegs m RS (RS + 52) -> stk bsegs m NBP (NBP + 4) -> stk bsegs m TLP (TLP + 4) ->
  bytes_at bsegs m SRC src -> zlen src = n -> 4096 <= SRC -> n < 2^32 -> SRC + n < 2^47 ->
  stk bsegs m WK (WK + wksz) -> 0 <= wksz < 2^32 -> WK mod 4 = 0 ->      (* [comment removed for export] *)
  RS mod 4 = 0 ->                                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  4096 <= B -> B + bsz < 2^47 -> B <= RS -> RS + 52 <= HW -> RS + 52 <= WK -> HW + 256 <= B + bsz -> WK + wksz <= B + bsz ->
  (WK + wksz <= HW \/ HW + 256 <= WK) ->
  (* [comment removed for export] *)
  4096 <= NBP -> NBP + 4 < 2^47 -> NBP mod 4 = 0 -> (NBP + 4 <= lo \/ SPV <= NBP) ->
  4096 <= TLP -> TLP + 4 < 2^47 -> TLP mod 4 = 0 -> (TLP + 4 <= lo \/ SPV <= TLP) -> (NBP + 4 <= TLP \/ TLP + 4 <= NBP) ->
  (* [comment removed for export] *)
  (B + bsz <= lo \/ SPV + 8 <= B) -> (B + bsz <= NBP \/ NBP + 4 <= B) -> (B + bsz <= TLP \/ TLP + 4 <= B) -> (B + bsz <= SRC \/ SRC + n <= B) ->
  (0 < n -> NBP + 4 <= SRC \/ SRC + n <= NBP) -> (0 < n -> TLP + 4 <= SRC \/ SRC + n <= TLP) -> (SRC + n <= lo \/ SPV <= SRC) ->
  evtF bsegs RNG (huf_rstats_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV HW RS NBP TLP n WK wksz lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HW) (Z_to_bv 64 256) (Z_to_bv 64 RS) (Z_to_bv 64 NBP)
               (Z_to_bv 64 TLP) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APHUF_RSTATS) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
