(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdTbl ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_tbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation SEQHDR_STACK_A := 5248 (only parsing).   (* [comment removed for export] *)
Notation SEQHDR_DEPTH := 3 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

Definition APZD_SEQHDR : Z := 0x8889c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition seqhdr_tab (m : amem) (DCTX : Z) (k : seq_kind) (own dflt : Z) (d : seq_table) (pv : word) : Prop :=
  exists T t, pv = Z_to_bv 64 T /\ tbl_ptr DCTX own dflt d T t /\ seq_tbl_at bsegs m k T t.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition zd_seqhdr_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX NBP srcSize : Z) (llt mlt oft huf : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r llt' mlt' oft' nbw,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4); (SPV - SEQHDR_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ dctx_ptrs bsegs m' DCTX llt' mlt' oft' huf
    /\ stk bsegs m' (DCTX + 32) (DCTX + 10296) /\ stk bsegs m' (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells bsegs m' NBP [C4 nbw]
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true
        \/ (r <= srcSize /\ exists nbSeq, nbw = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
            ((nbSeq = 0 /\ llt' = llt /\ mlt' = mlt /\ oft' = oft /\ munch [(NBP, NBP + 4); (SPV - SEQHDR_STACK_A, SPV)] m m')
             \/ (nbSeq <> 0 /\
                 seqhdr_tab m' DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable llt' /\
                 seqhdr_tab m' DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable oft' /\
                 seqhdr_tab m' DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable mlt')))).

Definition zd_seqhdr_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo DCTX NBP SRC : Z) (src : list Z)
         (llt mlt oft huf pcs dsz bt stg le fe nb0 : word) (ws : list word),
  (* [comment removed for export] *)
  dctx_ptrs bsegs m DCTX llt mlt oft huf ->
  stk bsegs m (DCTX + 32) (DCTX + 10296) -> stk bsegs m (DCTX + 27324) (DCTX + 29884) ->
  dctx_h3 bsegs m DCTX pcs dsz bt stg le fe -> dctx_h5 bsegs m DCTX ws ->
  atbl_seq m DCTX llt mlt oft fe ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 ->
  (* [comment removed for export] *)
  rw_cells bsegs m NBP [C4 nb0] -> 4096 <= NBP -> NBP + 4 < 2^47 ->
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> Z.of_nat (length src) <= 1048576 ->
  4096 <= SRC -> SRC + Z.of_nat (length src) < 2^47 ->
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - SEQHDR_STACK_A -> SPV < 2^47 ->
  off_stack lo SPV DCTX 95992 -> off_stack lo SPV NBP 4 -> off_stack lo SPV SRC (Z.of_nat (length src)) ->
  apart DCTX 95992 NBP 4 -> apart DCTX 95992 SRC (Z.of_nat (length src)) -> apart NBP 4 SRC (Z.of_nat (length src)) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV SEQHDR_DEPTH -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m ->
  DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ainblk LB DCTX 95992 -> areg RNG m NBP 4 -> ainblk LB NBP 4 ->
  areg RNG m SRC (Z.of_nat (length src)) -> (0 < Z.of_nat (length src) -> ainimg LB SRC (Z.of_nat (length src))) -> (0 < Z.of_nat (length src) -> ahull RNG m SRC (Z.of_nat (length src))) ->
  NBP mod 4 = 0 ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 NBP -> a2 = Z_to_bv 64 SRC -> a3 = Z_to_bv 64 (Z.of_nat (length src)) ->
  evtF bsegs RNG (zd_seqhdr_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (Z.of_nat (length src)) llt mlt oft huf lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_SEQHDR) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
