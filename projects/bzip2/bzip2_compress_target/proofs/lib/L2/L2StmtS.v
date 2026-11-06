(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read R_unwind_chain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCState BzCLemmasFs CmpMem CmpCut AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCStream BzCDriver CmpSess CmpSessB A0_b2c_wrV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section StmtIE.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition INIT_COST : Z := mcost ESTATE_SIZE + mcost ARR1_SIZE + mcost ARR2_SIZE + mcost (4 * FTAB_WORDS).

(* [comment removed for export] *)
Definition bzCompressInit_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (STRM : Z) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 : word) (lo : Z),
  let usp := bv_unsigned sp in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> a1 = Z_to_bv 64 BLOCKSIZE100K -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 WORKFACTOR ->
  tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rw_cells a0segs m STRM (A0_b2c_wrV.STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) -> strm_okA RT Σ m STRM ->
  uw_chain USTACK_TOP m usp (bv_unsigned s0) [0x81a58; 0x817b4] ->          (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> INIT_COST <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 144 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x81cb4) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT) (E r1 r2 r3 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (J : list byte)
                                        (ar1 ar2 ft inU uns mtf sel selM len code rfreq lenp : zarr) (bsB bsL nIn oP nM : Z),
          let cx := CC E r1 r2 r3 (STRM - BZF_STRM) 0 J [] in
          let e0 := est_init ar1 ar2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ cctx_ok cx /\ cctx_sep cx /\ cctx_img (aci_c A0C) cx
          /\ emem cx a0segs (eg_init (Z_to_bv 64 0)) e0 m' /\ CmpCut.amem cx a0segs e0 m'
          /\ zbok ar1 /\ zbok ar2 /\ bh_w32 ft
          /\ rw_cells a0segs m' STRM (A0_b2c_wrV.STRMC w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) w20 w24 w32 (Z_to_bv 64 0) (Z_to_bv 64 0) w44 (Z_to_bv 64 E)
                                         (Z_to_bv 64 A0_b2c_wrV.DBZA) (Z_to_bv 64 A0_b2c_wrV.DBZF) (Z_to_bv 64 0))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(STRM, STRM + 80)] m m') c
       /\ rt_live RT Σ' = (r3, 4 * FTAB_WORDS) :: (r2, ARR2_SIZE) :: (r1, ARR1_SIZE) :: (E, ESTATE_SIZE) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - INIT_COST).

(* [comment removed for export] *)
Definition bzCompressEnd_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (cx : cctx) (ob on dbza : Z) (g : eg) (e : est) (z : BzCDriver.zstrm) (nin : Z) (p1 p2 : word) (lo : Z),
  let usp := bv_unsigned sp in
  let STRM := c_bz cx + BZF_STRM in
  let W := [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS); (STRM + 48, STRM + 56)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rw_cells a0segs m (c_E cx) (EHEAD1 cx g e) ->
  rw_cells a0segs m STRM (CmpSessB.STRMB cx ob on dbza A0_b2c_wrV.DBZF z nin p1 p2) -> strm_okA RT Σ m STRM ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 64 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x83c8c) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ rw_cells a0segs m' STRM (A0_b2c_wrV.STRMS ob on dbza A0_b2c_wrV.DBZF z nin p1 p2 0)
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = live_remove (c_E cx) (live_remove (c_FT cx) (live_remove (c_A2 cx) (live_remove (c_A1 cx) (rt_live RT Σ))))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).
End StmtIE.
