(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_blk_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation ALLOCLIT_STACK_A := 16 (only parsing).   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

Definition APZD_ALLOCLIT : Z := 0x94f38.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lit_base_addr (DCTX DST : Z) (b : lit_base) : Z :=
  match b with LB_dst => DST | LB_extra => DCTX + DCTX_litExtraBuffer | LB_src => 0 end.

(* [comment removed for export] *)
Definition h5_placed (ws : list word) (DCTX DST : Z) (p : lit_place) : list word :=
  wupd (wupd (wupd ws H5_litBuffer (Z_to_bv 64 (lit_base_addr DCTX DST (lp_base p) + lp_buf p)))
             H5_litBufferEnd (Z_to_bv 64 (lit_base_addr DCTX DST (lp_base p) + lp_end p)))
       H5_litBufferLocation (Z_to_bv 64 (lp_loc p)).

Definition zd_alloclit_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX DST : Z) (ws : list word) (p : lit_place) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DCTX + DCTX_litBuffer, DCTX + DCTX_litBuffer + 20); (SPV - ALLOCLIT_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ dctx_h5 bsegs m' DCTX (h5_placed ws DCTX DST p).

Definition zd_alloclit_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DCTX DST CAP litSize ews : Z) (imm : bool) (h : frame_header) (ws : list word) (lo : Z),
  rw_cells bsegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_bsmax h <= 131072 ->
  dctx_h5 bsegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> 0 <= DST -> 0 <= CAP -> DST + CAP < 2^47 ->
  (DST = 0 -> CAP = 0) ->      (* [comment removed for export] *)
  0 <= litSize <= ews -> ews = Z.min (fh_bsmax h) CAP -> 0 <= SPV < 2^64 ->
  stk bsegs m lo SPV -> lo <= SPV - ALLOCLIT_STACK_A -> SPV < 2^47 ->
  (* [comment removed for export] *)
  off_stack lo SPV DCTX 95992 ->      (* [comment removed for export] *)
  DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 litSize -> a4 = Z_to_bv 64 0 ->
  a5 = Z_to_bv 64 ews -> a6 = Z_to_bv 64 (if imm then 1 else 0) ->
  evtF bsegs RNG (zd_alloclit_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST ws (alloc_lit_buffer (fh_bsmax h) CAP litSize ews imm) lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_ALLOCLIT) fc None m (seg_rom bsegs)).
End CANSEC1.
