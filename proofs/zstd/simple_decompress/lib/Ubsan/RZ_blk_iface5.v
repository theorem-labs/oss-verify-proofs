(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_huf_iface RZ_block_iface RZ_hufinv.
Import ListNotations.
Open Scope Z_scope.

Definition PZD_DECLIT : Z := 0x16714.          (* [comment removed for export] *)
Notation DECLIT_STACK := 1184 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition declit_placed (DCTX DST CAP LSRC slen : Z) (ws' : list word) : Prop :=
  exists LITP LITSZ LITB LBE LOC,
    wnth ws' H5_litPtr = Z_to_bv 64 LITP /\ wnth ws' H5_litSize = Z_to_bv 64 LITSZ /\ wnth ws' H5_litBuffer = Z_to_bv 64 LITB /\
    wnth ws' H5_litBufferEnd = Z_to_bv 64 LBE /\ wnth ws' H5_litBufferLocation = Z_to_bv 64 LOC /\
    0 <= LITSZ <= 131072 /\ LITP <= LBE /\
    ((LOC = ZSTD_not_in_dst /\ LBE = LITP + LITSZ /\
        ((LITP = DCTX + DCTX_litExtraBuffer /\ LITSZ <= ZSTD_LITBUFFEREXTRASIZE)
         \/ (LSRC <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= LSRC + slen)))
     \/ (LOC = ZSTD_in_dst /\ LBE = LITP + LITSZ /\ LITB = LITP /\ DST <= LITB /\ LBE + WILDCOPY_OVERLENGTH <= DST + CAP)
     \/ (LOC = ZSTD_split /\ ZSTD_LITBUFFEREXTRASIZE < LITSZ /\ LITB = LITP /\ DST <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= DST + CAP)).

Definition zd_declit_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX DST CAP B0 B1 LSRC slen : Z) (llt mlt oft : word) (pcs dsz bt stg fe : word) (ws : list word) (lo : Z) (m : fmem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r huf' le' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
              (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV - DECLIT_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ stk usegs m' B0 B1
    /\ dctx_ptrs usegs m' DCTX llt mlt oft huf'
    /\ stk usegs m' (DCTX + 10296) (DCTX + 26684) /\ stk usegs m' (DCTX + 27324) (DCTX + 29884)
    /\ dctx_h3 usegs m' DCTX pcs dsz bt stg le' fe
    /\ dctx_h5 usegs m' DCTX ws' /\ (forall i, h5_block_owned i = false -> wnth ws' i = wnth ws i)
    /\ stk usegs m' (DCTX + 30372) (DCTX + 95940)
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true
        \/ (1 <= r <= slen /\ HUFINVw m' DCTX huf' le' /\ declit_placed DCTX DST CAP LSRC slen ws')).

Definition zd_declit_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 LSRC : Z) (src : list Z) (h : frame_header)
         (llt mlt oft huf pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  dctx_ptrs usegs m DCTX llt mlt oft huf ->
  stk usegs m (DCTX + 10296) (DCTX + 26684) -> HUFINVw m DCTX huf le ->
  stk usegs m (DCTX + 27324) (DCTX + 29884) ->
  rw_cells usegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_bsmax h <= 131072 ->
  dctx_h3 usegs m DCTX pcs dsz bt stg le fe ->
  dctx_h5 usegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
  stk usegs m (DCTX + 30372) (DCTX + 95940) ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m LSRC (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> Z.of_nat (length src) <= 131072 ->
  4096 <= LSRC -> LSRC + Z.of_nat (length src) < 2^47 ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> B0 <= DST -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= B0) ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - DECLIT_STACK -> SPV < 2^47 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (B1 <= lo \/ SPV <= B0) -> (LSRC + Z.of_nat (length src) <= lo \/ SPV <= LSRC) ->
  (B1 <= DCTX \/ DCTX + 95992 <= B0) -> (B1 <= LSRC \/ LSRC + Z.of_nat (length src) <= B0) ->
  (LSRC + Z.of_nat (length src) <= DCTX \/ DCTX + 95992 <= LSRC) ->
  SPV mod 16 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 LSRC -> a2 = Z_to_bv 64 (Z.of_nat (length src)) -> a3 = Z_to_bv 64 DST -> a4 = Z_to_bv 64 CAP ->
  a5 = Z_to_bv 64 0 ->
  evt usegs (zd_declit_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 LSRC (Z.of_nat (length src))
                            llt mlt oft pcs dsz bt stg fe ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DECLIT) fc None m (seg_rom usegs)).
