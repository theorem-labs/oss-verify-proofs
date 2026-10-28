(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation DBLOCK_STACK_A := 6384 (only parsing).   (* [comment removed for export] *)
Notation DBLOCK_DEPTH := 6 (only parsing).

Section CANSEC1. Context {rc : runConstT}.


(* [comment removed for export] *)
Definition h5_block_owned (i : nat) : bool :=
  (Nat.eqb i H5_litPtr || Nat.eqb i H5_litSize || Nat.eqb i H5_rleSize || Nat.eqb i H5_ddictIsCold
   || Nat.eqb i H5_litBuffer || Nat.eqb i H5_litBufferEnd || Nat.eqb i H5_litBufferLocation)%bool.

Definition tbl_pred : Type := amem -> Z -> word -> word -> word -> word -> word -> word -> Prop.

(* [comment removed for export] *)
Record tbl_laws (TBL : tbl_pred) : Prop := {
  (* [comment removed for export] *)
  tbl_init : forall m DCTX,
    bytes_at bsegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
    bytes_at bsegs m (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)) ->
    TBL m DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
        (Z_to_bv 64 0) (Z_to_bv 64 0);
  (* [comment removed for export] *)
  tbl_frame : forall m m' W DCTX llt mlt oft huf le fe,
    TBL m DCTX llt mlt oft huf le fe -> munch W m m' -> mem_inv bsegs m -> mem_inv bsegs m' ->
    (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) ->
    TBL m' DCTX llt mlt oft huf le fe
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Variable TBL : tbl_pred.
Definition zd_dblock_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX DST CAP B0 B1 : Z) (pcs dsz bt stg : word) (ws : list word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r llt' mlt' oft' huf' le' fe' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940);
              (SPV - DBLOCK_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ stk bsegs m' B0 B1
    /\ dctx_ptrs bsegs m' DCTX llt' mlt' oft' huf'
    /\ dctx_h3 bsegs m' DCTX pcs dsz bt stg le' fe'
    /\ dctx_h5 bsegs m' DCTX ws' /\ (forall i, h5_block_owned i = false -> wnth ws' i = wnth ws i)
    /\ dctx_owned bsegs m' DCTX
    /\ (zd_is_error r = false -> TBL m' DCTX llt' mlt' oft' huf' le' fe')
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= CAP).

Definition zd_dblock_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (SPV lo DCTX DST CAP B0 B1 PFX SRC : Z) (src : list Z) (ip cbs : Z) (h : frame_header)
         (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  dctx_ptrs bsegs m DCTX llt mlt oft huf ->
  dctx_h1 bsegs m DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd ->
  rw_cells bsegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_bsmax h <= 131072 -> 0 <= fh_window h < 2^64 ->
  dctx_h3 bsegs m DCTX pcs dsz bt stg le fe ->
  dctx_h5 bsegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
  dctx_owned bsegs m DCTX ->
  TBL m DCTX llt mlt oft huf le fe ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= ip -> 0 <= cbs < 2^21 -> ip + cbs <= zlen src ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  (* [comment removed for export] *)
  stk bsegs m B0 B1 -> B0 <= DST -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (* [comment removed for export] *)
  ((PFX = 0 /\ CAP = 0) \/ B0 <= PFX <= DST) ->
  (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= B0) -> (DST <> 0 -> B0 < B1) ->   (* [comment removed for export] *)
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - DBLOCK_STACK_A -> SPV < 2^47 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (B1 <= lo \/ SPV <= B0) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (B1 <= DCTX \/ DCTX + 95992 <= B0) -> (B1 <= SRC \/ SRC + zlen src <= B0) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV DBLOCK_DEPTH -> tp = Z_to_bv 64 ATP ->
  azstk RNG m lo SPV ->
  aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) -> (0 < zlen src -> ahull RNG m SRC (zlen src)) -> DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ahull RNG m DCTX 95992 -> ainblk LB DCTX 95992 ->
  (B0 < B1 -> areg RNG m B0 (B1 - B0) /\ ahull RNG m B0 (B1 - B0) /\ ainblk LB B0 (B1 - B0)) ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 (SRC + ip) -> a4 = Z_to_bv 64 cbs ->
  a5 = Z_to_bv 64 0 ->
  evtF bsegs RNG (zd_dblock_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 pcs dsz bt stg ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DBLOCK) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
