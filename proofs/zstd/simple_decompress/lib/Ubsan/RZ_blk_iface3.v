(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdTbl ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_tbl.
Import ListNotations.
Open Scope Z_scope.

Definition PZD_SEQHDR : Z := 0x172fc.          (* [comment removed for export] *)
Notation SEQHDR_STACK := 544 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition seqhdr_tab (m : fmem) (DCTX : Z) (k : seq_kind) (own dflt : Z) (d : seq_table) (pv : word) : Prop :=
  exists T t, pv = Z_to_bv 64 T /\ tbl_ptr DCTX own dflt d T t /\ seq_tbl_at usegs m k T t.

Definition zd_seqhdr_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX NBP srcSize : Z) (llt mlt oft huf : word) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r llt' mlt' oft' nbw,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4); (SPV - SEQHDR_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ dctx_ptrs usegs m' DCTX llt' mlt' oft' huf
    /\ stk usegs m' (DCTX + 32) (DCTX + 10296) /\ stk usegs m' (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells usegs m' NBP [C4 nbw]
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true
        \/ (r <= srcSize /\ exists nbSeq, nbw = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
            ((nbSeq = 0 /\ llt' = llt /\ mlt' = mlt /\ oft' = oft /\ munch [(NBP, NBP + 4); (SPV - SEQHDR_STACK, SPV)] m m')
             \/ (nbSeq <> 0 /\
                 seqhdr_tab m' DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable llt' /\
                 seqhdr_tab m' DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable oft' /\
                 seqhdr_tab m' DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable mlt')))).

Definition zd_seqhdr_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DCTX NBP SRC : Z) (src : list Z)
         (llt mlt oft huf pcs dsz bt stg le fe nb0 : word) (ws : list word),
  (* [comment removed for export] *)
  dctx_ptrs usegs m DCTX llt mlt oft huf ->
  stk usegs m (DCTX + 32) (DCTX + 10296) -> stk usegs m (DCTX + 27324) (DCTX + 29884) ->
  dctx_h3 usegs m DCTX pcs dsz bt stg le fe -> dctx_h5 usegs m DCTX ws ->
  ptbl_seq m DCTX llt mlt oft fe ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 ->
  (* [comment removed for export] *)
  rw_cells usegs m NBP [C4 nb0] -> 4096 <= NBP -> NBP + 4 < 2^47 ->
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> Z.of_nat (length src) <= 1048576 ->
  4096 <= SRC -> SRC + Z.of_nat (length src) < 2^47 ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - SEQHDR_STACK -> SPV < 2^47 ->
  off_stack lo SPV DCTX 95992 -> off_stack lo SPV NBP 4 -> off_stack lo SPV SRC (Z.of_nat (length src)) ->
  apart DCTX 95992 NBP 4 -> apart DCTX 95992 SRC (Z.of_nat (length src)) -> apart NBP 4 SRC (Z.of_nat (length src)) ->
  DCTX mod 8 = 0 -> NBP mod 4 = 0 -> SPV mod 16 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 NBP -> a2 = Z_to_bv 64 SRC -> a3 = Z_to_bv 64 (Z.of_nat (length src)) ->
  evt usegs (zd_seqhdr_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (Z.of_nat (length src)) llt mlt oft huf lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_SEQHDR) fc None m (seg_rom usegs)).
