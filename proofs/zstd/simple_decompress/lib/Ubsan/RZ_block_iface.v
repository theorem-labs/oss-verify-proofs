(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface.
Import ListNotations.
Open Scope Z_scope.

Notation DBLOCK_STACK := 2048 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h5_block_owned (i : nat) : bool :=
  (Nat.eqb i H5_litPtr || Nat.eqb i H5_litSize || Nat.eqb i H5_rleSize || Nat.eqb i H5_ddictIsCold
   || Nat.eqb i H5_litBuffer || Nat.eqb i H5_litBufferEnd || Nat.eqb i H5_litBufferLocation)%bool.

Definition tbl_pred : Type := fmem -> Z -> word -> word -> word -> word -> word -> word -> Prop.

(* [comment removed for export] *)
Record tbl_laws (TBL : tbl_pred) : Prop := {
  (* [comment removed for export] *)
  tbl_init : forall m DCTX,
    bytes_at usegs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
    bytes_at usegs m (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)) ->
    TBL m DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
        (Z_to_bv 64 0) (Z_to_bv 64 0);
  (* [comment removed for export] *)
  tbl_frame : forall m m' W DCTX llt mlt oft huf le fe,
    TBL m DCTX llt mlt oft huf le fe -> munch W m m' -> mem_inv usegs m -> mem_inv usegs m' ->
    (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) ->
    TBL m' DCTX llt mlt oft huf le fe
}.

Section DBLOCK.
Variable TBL : tbl_pred.

Definition zd_dblock_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX DST CAP B0 B1 : Z) (pcs dsz bt stg : word) (ws : list word) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r llt' mlt' oft' huf' le' fe' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940);
              (SPV - DBLOCK_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ stk usegs m' B0 B1
    /\ dctx_ptrs usegs m' DCTX llt' mlt' oft' huf'
    /\ dctx_h3 usegs m' DCTX pcs dsz bt stg le' fe'
    /\ dctx_h5 usegs m' DCTX ws' /\ (forall i, h5_block_owned i = false -> wnth ws' i = wnth ws i)
    /\ dctx_owned usegs m' DCTX
    /\ (zd_is_error r = false -> TBL m' DCTX llt' mlt' oft' huf' le' fe')
    /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= CAP).

Definition zd_dblock_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 PFX SRC : Z) (src : list Z) (ip cbs : Z) (h : frame_header)
         (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  dctx_ptrs usegs m DCTX llt mlt oft huf ->
  dctx_h1 usegs m DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd ->
  rw_cells usegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_bsmax h <= 131072 -> 0 <= fh_window h < 2^64 ->
  dctx_h3 usegs m DCTX pcs dsz bt stg le fe ->
  dctx_h5 usegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
  dctx_owned usegs m DCTX ->
  TBL m DCTX llt mlt oft huf le fe ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= ip -> 0 <= cbs < 2^21 -> ip + cbs <= zlen src ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> B0 <= DST -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (* [comment removed for export] *)
  ((PFX = 0 /\ CAP = 0) \/ B0 <= PFX <= DST) ->
  (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= B0) ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - DBLOCK_STACK -> SPV < 2^47 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (B1 <= lo \/ SPV <= B0) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (B1 <= DCTX \/ DCTX + 95992 <= B0) -> (B1 <= SRC \/ SRC + zlen src <= B0) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  SPV mod 16 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 (SRC + ip) -> a4 = Z_to_bv 64 cbs ->
  a5 = Z_to_bv 64 0 ->
  evt usegs (zd_dblock_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 pcs dsz bt stg ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DBLOCK) fc None m (seg_rom usegs)).
End DBLOCK.
