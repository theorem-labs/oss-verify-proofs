(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PZD_SEQ_LONG : Z := 0x17a94.        (* [comment removed for export] *)
Definition PZD_SEQ_SPLIT : Z := 0x1ac08.       (* [comment removed for export] *)
Definition PZD_SEQ_DEFAULT : Z := 0x1ca68.     (* [comment removed for export] *)
Definition PZD_EXECEND : Z := 0x1dfe4.         (* [comment removed for export] *)
Definition PZD_SAFECOPY : Z := 0x1e154.        (* [comment removed for export] *)
Definition PZD_EXECEND_SPLIT : Z := 0x1e5d0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Notation SEQ_STACK := 544 (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition seq_dctx (m : fmem) (DCTX LLT MLT OFT : Z) (huf r0 r1 r2 pde : word) (PFX VST : Z) (dend expd : word)
                    (pcs dsz bt stg le fe : word) (ws : list word) : Prop :=
  dctx_ptrs usegs m DCTX (Z_to_bv 64 LLT) (Z_to_bv 64 MLT) (Z_to_bv 64 OFT) huf /\
  rw_cells usegs m (DCTX + DCTX_entropy_rep) [C4 r0; C4 r1; C4 r2] /\
  dctx_h1 usegs m DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 VST) dend expd /\
  dctx_h3 usegs m DCTX pcs dsz bt stg le fe /\
  dctx_h5 usegs m DCTX ws.

(* [comment removed for export] *)
Definition seq_lit (ws : list word) (LITP LITSZ LITB LOC : Z) : Prop :=
  wnth ws H5_litPtr = Z_to_bv 64 LITP /\ wnth ws H5_litSize = Z_to_bv 64 LITSZ /\
  wnth ws H5_litBuffer = Z_to_bv 64 LITB /\ wnth ws H5_litBufferLocation = Z_to_bv 64 LOC.

(* [comment removed for export] *)
Definition seq_table_at (m : fmem) (k : seq_kind) (T : Z) (t : seq_table) : Prop :=
  bytes_at usegs m T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok k t.

(* [comment removed for export] *)
Definition off_stack (lo SPV X n : Z) : Prop := X + n <= lo \/ SPV <= X.
(* [comment removed for export] *)
Definition apart (X n Y k : Z) : Prop := X + n <= Y \/ Y + k <= X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_seq_default_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX DST CAP B0 B1 nbSeq : Z) (pcs dsz bt stg le fe : word) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r r0' r1' r2',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
              (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (SPV - SEQ_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ stk usegs m' B0 B1
    /\ rw_cells usegs m' (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']
    /\ dctx_h3 usegs m' DCTX pcs dsz bt stg le (if nbSeq =? 0 then fe else Z_to_bv 64 1)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= CAP).

Definition zd_seq_default_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC : Z)
         (sq : list Z) (tLL tOF tML : seq_table) (huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws -> seq_lit ws LITP LITSZ LITB LOC ->
  4096 <= DCTX -> DCTX + DCTX_SIZEOF < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) -> all_bytes sq -> 4096 <= SEQ -> SEQ + zlen sq < 2^47 ->
  0 <= nbSeq <= 98047 ->
  (* [comment removed for export] *)
  (nbSeq <> 0 -> seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
                 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47) ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> B0 <= DST -> (nbSeq <> 0 -> B0 <= PFX <= DST) -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (DST = 0 -> CAP = 0 /\ nbSeq = 0) -> (DST <> 0 -> 4096 <= B0) ->
  (* [comment removed for export] *)
  (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst) ->
  0 <= LITSZ < 2^32 -> 4096 <= LITP -> LITP + LITSZ + WILDCOPY_OVERLENGTH < 2^47 ->
  rdbl usegs m LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH) ->
  (LOC = ZSTD_in_dst -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH <= B1) ->
  (LOC = ZSTD_not_in_dst -> apart LITP (LITSZ + WILDCOPY_OVERLENGTH) B0 (B1 - B0)) ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - SEQ_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV DCTX DCTX_SIZEOF -> off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SEQ (zlen sq) ->
  off_stack lo SPV LITP (LITSZ + WILDCOPY_OVERLENGTH) ->
  (nbSeq <> 0 -> off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9))) ->
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF -> apart B0 (B1 - B0) SEQ (zlen sq) ->
  (nbSeq <> 0 -> apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9))) ->
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) ->
  apart LITP (LITSZ + WILDCOPY_OVERLENGTH) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep) ->
  (nbSeq <> 0 -> apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)) ->
  SPV mod 16 = 0 -> (nbSeq <> 0 -> LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SEQ -> a4 = Z_to_bv 64 (zlen sq) ->
  a5 = Z_to_bv 64 nbSeq ->
  evt usegs (zd_seq_default_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_SEQ_DEFAULT) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation SEQ_SPLIT_STACK := 592 (only parsing).
Notation SEQ_LONG_STACK := 896 (only parsing).

Definition seq_lit2 (ws : list word) (LITP LBE LITB LOC : Z) : Prop :=
  wnth ws H5_litPtr = Z_to_bv 64 LITP /\ wnth ws H5_litBufferEnd = Z_to_bv 64 LBE /\
  wnth ws H5_litBuffer = Z_to_bv 64 LITB /\ wnth ws H5_litBufferLocation = Z_to_bv 64 LOC.

(* [comment removed for export] *)
Definition seq_lit_placed (m : fmem) (DCTX DST CAP B0 B1 LITP LBE LITB LOC : Z) : Prop :=
  (LOC = ZSTD_not_in_dst /\ apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) B0 (B1 - B0)) \/
  (LOC = ZSTD_in_dst /\ DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= B1) \/
  (LOC = ZSTD_split /\ DST <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= DST + CAP /\
   rdbl usegs m (DCTX + DCTX_litExtraBuffer) (DCTX + DCTX_litExtraBuffer + DCTX_litExtraBuffer_sz)).

Definition zd_seq_split_post (STACK : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX DST CAP B0 B1 nbSeq : Z) (pcs dsz bt stg le fe : word) (ws : list word) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r r0' r1' r2' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
              (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
              (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4); (SPV - STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ stk usegs m' B0 B1
    /\ rw_cells usegs m' (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']
    /\ dctx_h3 usegs m' DCTX pcs dsz bt stg le (if nbSeq =? 0 then fe else Z_to_bv 64 1)
    /\ dctx_h5 usegs m' DCTX ws' /\ (forall i, i <> H5_litBufferLocation -> wnth ws' i = wnth ws i)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= CAP).

(* [comment removed for export] *)
Definition zd_seq_split_stmt_at (ENTRY STACK : Z) (LOCOK : Z -> Prop) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC : Z)
         (sq : list Z) (tLL tOF tML : seq_table) (huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws -> seq_lit2 ws LITP LBE LITB LOC ->
  4096 <= DCTX -> DCTX + DCTX_SIZEOF < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) -> all_bytes sq -> 4096 <= SEQ -> SEQ + zlen sq < 2^47 ->
  0 <= nbSeq <= 98047 ->
  (* [comment removed for export] *)
  (nbSeq <> 0 -> seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
                 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47) ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> 4096 <= B0 -> B0 <= DST -> (nbSeq <> 0 -> B0 <= PFX <= DST) -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (* [comment removed for export] *)
  LOCOK LOC -> 4096 <= LITP -> LITP <= LBE -> LBE + WILDCOPY_OVERLENGTH < 2^47 ->
  rdbl usegs m LITP (LBE + WILDCOPY_OVERLENGTH) ->
  seq_lit_placed m DCTX DST CAP B0 B1 LITP LBE LITB LOC ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV DCTX DCTX_SIZEOF -> off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SEQ (zlen sq) ->
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) ->
  (nbSeq <> 0 -> off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9))) ->
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF -> apart B0 (B1 - B0) SEQ (zlen sq) ->
  (nbSeq <> 0 -> apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9))) ->
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) ->
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)) ->
  (nbSeq <> 0 -> apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)) ->
  SPV mod 16 = 0 -> (nbSeq <> 0 -> LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SEQ -> a4 = Z_to_bv 64 (zlen sq) ->
  a5 = Z_to_bv 64 nbSeq ->
  evt usegs (zd_seq_split_post STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition zd_seq_long_stmt_at (ENTRY STACK : Z) (LOCOK : Z -> Prop) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC : Z)
         (sq : list Z) (tLL tOF tML : seq_table) (huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws -> seq_lit2 ws LITP LBE LITB LOC ->
  4096 <= DCTX -> DCTX + DCTX_SIZEOF < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) -> all_bytes sq -> 4096 <= SEQ -> SEQ + zlen sq < 2^47 ->
  0 <= nbSeq <= 98047 ->
  (* [comment removed for export] *)
  (nbSeq <> 0 -> seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
                 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47) ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> B0 <= DST -> (nbSeq <> 0 -> B0 <= PFX <= DST) -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (DST = 0 -> CAP = 0 /\ nbSeq = 0) -> (DST <> 0 -> 4096 <= B0) ->
  (* [comment removed for export] *)
  LOCOK LOC -> 4096 <= LITP -> LITP <= LBE -> LBE + WILDCOPY_OVERLENGTH < 2^47 ->
  rdbl usegs m LITP (LBE + WILDCOPY_OVERLENGTH) ->
  seq_lit_placed m DCTX DST CAP B0 B1 LITP LBE LITB LOC ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV DCTX DCTX_SIZEOF -> off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SEQ (zlen sq) ->
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) ->
  (nbSeq <> 0 -> off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9))) ->
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF -> apart B0 (B1 - B0) SEQ (zlen sq) ->
  (nbSeq <> 0 -> apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9))) ->
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) ->
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)) ->
  (nbSeq <> 0 -> apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)) ->
  SPV mod 16 = 0 -> (nbSeq <> 0 -> LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SEQ -> a4 = Z_to_bv 64 (zlen sq) ->
  a5 = Z_to_bv 64 nbSeq ->
  evt usegs (zd_seq_split_post STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition zd_seq_split_stmt : Prop := zd_seq_split_stmt_at PZD_SEQ_SPLIT SEQ_SPLIT_STACK (fun LOC => LOC = ZSTD_split).
Definition zd_seq_long_stmt : Prop :=
  zd_seq_long_stmt_at PZD_SEQ_LONG SEQ_LONG_STACK (fun LOC => LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation SAFECOPY_STACK := 80 (only parsing).

Definition zd_safecopy_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV OP LEN OENDW B0 B1 R0 R1 lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(OP, Z.max (OP + LEN) (OENDW + 32)); (SPV - SAFECOPY_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' B0 B1 /\ rdbl usegs m' R0 R1.

Definition zd_safecopy_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo OP OENDW IP LEN OV B0 B1 R0 R1 : Z),
  stk usegs m B0 B1 -> 4096 <= B0 -> B1 < 2^47 ->
  B0 <= OP -> 0 <= LEN -> OP + LEN <= B1 -> 0 <= OENDW -> OENDW + 32 <= B1 ->
  rdbl usegs m R0 R1 -> 4096 <= R0 -> R1 < 2^47 -> R0 <= IP ->
  ((OV = 1 /\ R0 = B0 /\ R1 = B1 /\ IP <= OP)
   \/ (OV = 0 /\ IP + LEN + 32 <= R1 /\ (apart R0 (R1 - R0) B0 (B1 - B0) \/ (B0 <= R0 /\ R1 <= B1)))) ->
  stk usegs m lo SPV -> lo <= SPV - SAFECOPY_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV R0 (R1 - R0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 OP -> a1 = Z_to_bv 64 OENDW -> a2 = Z_to_bv 64 IP -> a3 = Z_to_bv 64 LEN -> a4 = Z_to_bv 64 OV ->
  evt usegs (zd_safecopy_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN OENDW B0 B1 R0 R1 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_SAFECOPY) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Notation EXECEND_STACK := 192 (only parsing).

Definition zd_execend_post (STACK : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r lp',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(OP, OEND); (LPP, LPP + 8); (SPV - STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' B0 B1
    /\ rw_cells usegs m' SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)]
    /\ rw_cells usegs m' LPP [C8 (Z_to_bv 64 lp')]
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true \/ (r = LL + ML /\ OP + r <= OEND /\ lp' = LP + LL /\ LP + LL <= LLIM)).

Definition zd_execend_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z),
  stk usegs m B0 B1 -> 4096 <= B0 -> B1 < 2^47 -> B0 <= PFX <= OP -> OP <= OEND <= B1 ->
  rw_cells usegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
  rw_cells usegs m LPP [C8 (Z_to_bv 64 LP)] ->
  0 <= LL < 2^32 -> 0 <= ML < 2^32 -> 0 <= OFS < 2^64 ->
  4096 <= LP <= LLIM -> LLIM + WILDCOPY_OVERLENGTH < 2^47 -> rdbl usegs m LP (LLIM + WILDCOPY_OVERLENGTH) ->
  (apart LP (LLIM + WILDCOPY_OVERLENGTH - LP) B0 (B1 - B0) \/ (B0 <= LP /\ LLIM + WILDCOPY_OVERLENGTH <= B1)) ->
  4096 <= SQP -> SQP + 24 < 2^47 -> 4096 <= LPP -> LPP + 8 < 2^47 ->
  apart SQP 24 B0 (B1 - B0) -> apart LPP 8 B0 (B1 - B0) -> apart SQP 24 LPP 8 ->
  apart LP (LLIM + WILDCOPY_OVERLENGTH - LP) LPP 8 ->
  stk usegs m lo SPV -> lo <= SPV - EXECEND_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SQP 24 -> off_stack lo SPV LPP 8 ->
  off_stack lo SPV LP (LLIM + WILDCOPY_OVERLENGTH - LP) ->
  SQP mod 8 = 0 -> LPP mod 8 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 OP -> a1 = Z_to_bv 64 OEND -> a2 = Z_to_bv 64 SQP -> a3 = Z_to_bv 64 LPP -> a4 = Z_to_bv 64 LLIM ->
  a5 = Z_to_bv 64 PFX -> a6 = Z_to_bv 64 PFX -> a7 = Z_to_bv 64 DEND ->
  evt usegs (zd_execend_post EXECEND_STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_EXECEND) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Notation EXECEND_SPLIT_STACK := 208 (only parsing).

Definition zd_execend_split_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z),
  stk usegs m B0 B1 -> 4096 <= B0 -> B1 < 2^47 -> B0 <= PFX <= OP -> OP <= OEND <= B1 -> 0 <= OENDW -> OENDW + 32 <= OEND ->
  rw_cells usegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
  rw_cells usegs m LPP [C8 (Z_to_bv 64 LP)] ->
  0 <= LL < 2^32 -> 0 <= ML < 2^32 -> 0 <= OFS < 2^64 ->
  4096 <= LP <= LLIM -> LLIM < 2^47 -> rdbl usegs m LP LLIM ->
  (apart LP (LLIM - LP) B0 (B1 - B0) \/ (B0 <= LP /\ LLIM <= B1)) ->
  4096 <= SQP -> SQP + 24 < 2^47 -> 4096 <= LPP -> LPP + 8 < 2^47 ->
  apart SQP 24 B0 (B1 - B0) -> apart LPP 8 B0 (B1 - B0) -> apart SQP 24 LPP 8 -> apart LP (LLIM - LP) LPP 8 ->
  stk usegs m lo SPV -> lo <= SPV - EXECEND_SPLIT_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SQP 24 -> off_stack lo SPV LPP 8 -> off_stack lo SPV LP (LLIM - LP) ->
  SQP mod 8 = 0 -> LPP mod 8 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 OP -> a1 = Z_to_bv 64 OEND -> a2 = Z_to_bv 64 OENDW -> a3 = Z_to_bv 64 SQP -> a4 = Z_to_bv 64 LPP ->
  a5 = Z_to_bv 64 LLIM -> a6 = Z_to_bv 64 PFX -> a7 = Z_to_bv 64 PFX -> t3 = Z_to_bv 64 DEND ->
  evt usegs (zd_execend_post EXECEND_SPLIT_STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_EXECEND_SPLIT) fc None m (seg_rom usegs)).
