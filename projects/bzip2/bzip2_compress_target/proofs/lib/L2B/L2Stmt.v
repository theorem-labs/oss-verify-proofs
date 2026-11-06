(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState BzCSortF BzCBlock BzCHuff BzArrD CmpMem CmpCut CmpCutMS CmpHmKit AsanKit AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCStream BzCLemmas1 CmpCutSM BzCDriver CmpSess CmpSessB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).



Section Stmt.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition hbMakeCodeLengths_contract : Prop :=
  forall (Σ : rts RT) PMc (X : hmenv) (m : mem) (pl nl : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  let usp := bv_unsigned (he_sp X) in
  fdfs_only PMc -> mat_stable PMc -> hmenv_ok X -> he_tp X = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  u8arr b0segs m (he_El X) (ovb (he_len X) (he_Jl X) (he_NL X)) -> u32arr b0segs m (he_Ef X) (ovw (he_freq X) (he_Jf X) (he_NF X)) ->
  In (pl, nl) (rt_live RT Σ) -> pl <= he_El X -> he_El X + he_NL X + 7 <= pl + nl -> pl <= he_Ef X -> he_Ef X + 4 * he_NF X + 7 <= pl + nl ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m (he_lo X) usp -> rt_sp0 RT Σ - STACK_WIN <= he_lo X -> he_lo X + RT_STACK + 304 <= usp ->
  usp + 16 <= USTACK_TOP ->
  hm_facts (he_len X) (he_freq X) (he_lb X) (he_fb X) (he_A X) ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR (he_ra X) (he_sp X) (he_gp X) (he_tp X) t0 t1 t2 (he_s0 X) (he_s1 X) (Z_to_bv 64 (he_El X + he_lb X))
                                       (Z_to_bv 64 (he_Ef X + 4 * he_fb X)) (Z_to_bv 64 (he_A X)) (Z_to_bv 64 17) a4 a5 a6 a7
                                       (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6)
                                  (he_F X) (Z_to_bv 64 0xa7e6c) (he_fc X) None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR (he_ra X) (he_sp X) (he_gp X) (he_tp X) t0 t1 t2 (he_s0 X) (he_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                       (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6)
                  F' (ret_pc (he_ra X)) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' (he_lo X) usp
          /\ u8arr b0segs m' (he_El X) (ovb (hs_len (hm_rounds 40 (he_A X) 17 (he_lb X) (hp_rs (he_len X) (he_freq X) (he_lb X) (he_fb X) (he_A X) 0))) (he_Jl X) (he_NL X))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(he_El X + he_lb X, he_El X + he_lb X + he_A X)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1).

(* [comment removed for export] *)
Definition fallbackSort_contract (FSFACTS : zarr -> zarr -> zarr -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (cx : cctx) (e : est) (nblock lo : Z),
  let usp := bv_unsigned sp in
  let W := [(c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (c_A1 cx) -> a1 = Z_to_bv 64 (c_A2 cx) -> a2 = Z_to_bv 64 (c_FT cx) -> a3 = Z_to_bv 64 nblock -> a4 = Z_to_bv 64 0 ->
  tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  u8arr b0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr b0segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) ->
  u32arr b0segs m (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) ->
  In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) -> In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 1408 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx ->
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> (forall i, 0 <= zget (e_ftab e) i < 4294967296) ->
  1 <= nblock <= NBLOCKMAX + 19 -> FSFACTS (e_arr1 e) (e_arr2 e) (e_ftab e) nblock ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa4c28) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ (let r := fallbackSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew nblock in
              u8arr b0segs m' (c_A1 cx) (zb8 (fr_fm r) ARR1_SIZE) /\ u8arr b0segs m' (c_A2 cx) (zb8 (fr_ec r) ARR2_SIZE)
              /\ u32arr b0segs m' (c_FT cx) (zw32 (fr_bh r) FTAB_WORDS))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1).

(* [comment removed for export] *)
Definition blockSort_contract (BSFACTS : est -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z),
  let usp := bv_unsigned sp in
  let W := [(c_E cx + 48, c_E cx + 52); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (c_E cx) -> tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rw_cells b0segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells b0segs m (c_E cx + 640) (EHEAD2 cx g e) -> CmpCut.amem cx b0segs e m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 1408 + 656 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx -> est_ok e -> 1 <= e_nblock e <= NBLOCKMAX + 9 -> BSFACTS e ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa0988) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : word -> option byte) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          (* [comment removed for export] *)
          /\ (let e' := fst (fst (fst (blockSort e znew))) in
              let g' := EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g) in
              rw_cells b0segs m' (c_E cx) (EHEAD1 cx g' e') /\ rw_cells b0segs m' (c_E cx + 640) (EHEAD2 cx g' e') /\ CmpCut.amem cx b0segs e' m')
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 2 <= rt_credit RT Σ' <= rt_credit RT Σ - 1).

(* [comment removed for export] *)
Definition sendMTFValues_contract (SMAF : est -> Prop) (SMBF : est -> zarr -> zarr -> zarr -> zarr -> zarr -> Prop) (SDF : est -> Z -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z),
  let usp := bv_unsigned sp in
  let eD := CmpCutSM.est_D e znew znew znew znew znew znew znew in
  let W := [(c_E cx, c_E cx + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (c_E cx) -> tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) ->
  emem cx b0segs g e m -> CmpCut.amem cx b0segs e m ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> 25 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 1712 + 304 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx ->
  zb8 (CmpCut.zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE = zb8 (e_arr2 e) ARR2_SIZE -> BzCLemmas1.bw_ok (e_bw e) -> 0 <= e_nblock e ->
  e_nblock e + BzCStream.bw_numZ (e_bw eD) <= ARR2_SIZE ->
  SMAF e -> SMBF e znew znew znew znew znew ->
  SDF (CmpCutSM.est_C e znew znew znew znew znew znew) (CmpCutSM.smA_ng e) (CmpCutSM.smB_nsel e znew znew znew znew znew) ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x8bc40) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : word -> option byte) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ emem cx b0segs g eD m'
          /\ u8arr b0segs m' (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE)
          /\ u8arr b0segs m' (c_A2 cx) (zb8 (CmpCut.zbl (e_arr2 e) (e_nblock e) (e_bw eD)) ARR2_SIZE)
          /\ u32arr b0segs m' (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS)
          /\ BzCLemmas1.bw_ok (e_bw eD)
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (1 + 4 * CmpCutSM.smA_ng e)).

(* [comment removed for export] *)
Definition compressBlock_contract (CBFACTS : est -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (is_last : bool) (lo : Z),
  let usp := bv_unsigned sp in
  let W := [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 (if is_last then 1 else 0) -> tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  emem cx b0segs g e m -> CmpCut.amem cx b0segs e m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) + 2 < FRAMES_MAX)%nat -> 28 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 304 + 2064 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx -> cb_pre g e -> CBFACTS e ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x89970) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : word -> option byte) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ (let e' := fst (BzCBlock.compressBlock e is_last znew) in
              emem cx b0segs (eg_after_cb cx g e) e' m' /\ CmpCut.amem cx b0segs e' m')
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 28 <= rt_credit RT Σ' <= rt_credit RT Σ - 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strm_okA (Σ : rts RT) (m : word -> option byte) (STRM : Z) : Prop :=
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= STRM /\ STRM + 80 <= f + fs_size k - 8) /\ STRM mod 8 = 0 /\
  bytes_at bsegs m (shad STRM) (repeat z8 10).
(* [comment removed for export] *)
Definition pay_liveA (Σ : rts RT) (ob on nin : Z) (pl : list byte) : Prop :=
  pl <> [] -> exists p n, In (p, n) (rt_live RT Σ) /\ p <= nin /\ nin + Z.of_nat (length pl) <= p + n /\ (p, n) <> (ob, on).
Definition HC_CREDIT (z : BzCDriver.zstrm) : Z := 28 * Z.of_nat (BzCDriver.hc_fuel z).

(* [comment removed for export] *)
Definition handle_compress_contract (HCXB : cctx -> Z -> eg -> est -> BzCDriver.zstrm -> Prop) (CBFACTS : est -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : BzCDriver.zstrm)
         (nin : Z) (pl OB : list byte) (p1 p2 : word) (lo : Z),
  let usp := bv_unsigned sp in
  let STRM := c_bz cx + BZF_STRM in
  let W := [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
            (ob, ob + on); (STRM, STRM + 80)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  emem cx b0segs g e m -> CmpCut.amem cx b0segs e m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m ->
  rw_cells b0segs m STRM (CmpSessB.STRMB cx ob on dbza dbzfr z nin p1 p2) -> strm_okA Σ m STRM ->
  u8arr b0segs m ob OB -> Z.of_nat (length OB) = on -> CmpSessB.out_okB (aci_c B0C) cx ob on -> In (ob, on) (rt_live RT Σ) ->
  u8ro b0segs m nin pl -> BzCDriver.z_in z = map bv_unsigned pl -> CmpSessB.pay_condB cx ob on nin pl -> pay_liveA Σ ob on nin pl ->
  BzCDriver.z_outr z = [] -> BzCDriver.z_avail_out z = on ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) + 3 < FRAMES_MAX)%nat -> HC_CREDIT z <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 288 + 304 + 2064 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx -> CmpSessB.hc_lawsB HCXB CBFACTS -> HCXB cx on g e z ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x82470) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : word -> option byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (g' : eg),
          let '(e', z', pr) := BzCDriver.handle_compress znew e z in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if pr then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ emem cx b0segs g' e' m' /\ CmpCut.amem cx b0segs e' m' /\ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m'
          /\ rw_cells b0segs m' STRM (CmpSessB.STRMB cx ob on dbza dbzfr z' (nin + (BzCDriver.z_avail_in z - BzCDriver.z_avail_in z')) p1 p2)
          /\ u8arr b0segs m' ob (CmpSess.outb (BzCDriver.z_outr z') OB)
          /\ BzCDriver.z_in z' = skipn (Z.to_nat (BzCDriver.z_avail_in z - BzCDriver.z_avail_in z')) (BzCDriver.z_in z)
          /\ HCXB cx on g' e' z'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - HC_CREDIT z <= rt_credit RT Σ' <= rt_credit RT Σ).

(* [comment removed for export] *)
Definition bzCompress_contract (HCXB : cctx -> Z -> eg -> est -> BzCDriver.zstrm -> Prop) (CBFACTS : est -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : BzCDriver.zstrm)
         (nin : Z) (pl OB : list byte) (p1 p2 : word) (lo : Z),
  let usp := bv_unsigned sp in
  let STRM := c_bz cx + BZF_STRM in
  let W := [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
            (ob, ob + on); (STRM, STRM + 80)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> a1 = Z_to_bv 64 BzCDriver.BZ_FINISH -> tp = Z_to_bv 64 0x6094d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  e_mode e = BZ_M_RUNNING -> e_state e = BZ_S_INPUT ->
  BzCDriver.z_avail_in z = Z.of_nat (length pl) -> BzCDriver.z_outr z = [] -> BzCDriver.z_avail_out z = on ->
  emem cx b0segs g e m -> CmpCut.amem cx b0segs e m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m ->
  rw_cells b0segs m STRM (CmpSessB.STRMB cx ob on dbza dbzfr z nin p1 p2) -> strm_okA Σ m STRM ->
  u8arr b0segs m ob OB -> Z.of_nat (length OB) = on -> CmpSessB.out_okB (aci_c B0C) cx ob on -> In (ob, on) (rt_live RT Σ) ->
  u8ro b0segs m nin pl -> BzCDriver.z_in z = map bv_unsigned pl -> CmpSessB.pay_condB cx ob on nin pl -> pay_liveA Σ ob on nin pl ->
  In (c_E cx, ESTATE_SIZE) (rt_live RT Σ) -> In (c_A1 cx, ARR1_SIZE) (rt_live RT Σ) -> In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ) ->
  In (c_FT cx, 4 * FTAB_WORDS) (rt_live RT Σ) ->
  (length (rt_frames RT Σ) + 3 < FRAMES_MAX)%nat -> HC_CREDIT z <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 80 + 288 + 304 + 2064 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c B0C) cx -> CmpSessB.hc_lawsB HCXB CBFACTS ->
  HCXB cx on (CmpSess.eg_set_aie g) (CmpSess.e_finish e z) z ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x81ff0) fc None m (seg_rom b0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : word -> option byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (g' : eg),
          let '(ret, e', z') := BzCDriver.bzCompress znew e z BzCDriver.BZ_FINISH in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom b0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo usp
          /\ emem cx b0segs g' e' m' /\ CmpCut.amem cx b0segs e' m' /\ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m'
          /\ rw_cells b0segs m' STRM (CmpSessB.STRMB cx ob on dbza dbzfr z' (nin + (BzCDriver.z_avail_in z - BzCDriver.z_avail_in z')) p1 p2)
          /\ u8arr b0segs m' ob (CmpSess.outb (BzCDriver.z_outr z') OB)
          /\ (0 <= BzCDriver.z_avail_out z' <= on /\ Z.of_nat (length (BzCDriver.z_outr z')) = on - BzCDriver.z_avail_out z')
          /\ est_ok e'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - HC_CREDIT z <= rt_credit RT Σ' <= rt_credit RT Σ).

End Stmt.
