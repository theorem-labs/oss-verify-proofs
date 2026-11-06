(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_bi_fuzz : Z := 0x96514.                (* [comment removed for export] *)
Definition e_pixBilateral : Z := 0xce2f4.           (* [comment removed for export] *)
Definition e_pixBilateralGray : Z := 0xceaa0.       (* [comment removed for export] *)
Definition e_bilateralCreate : Z := 0xcee64.        (* [comment removed for export] *)
Definition e_bilateralApply : Z := 0xd0374.         (* [comment removed for export] *)
Definition e_bilateralDestroy : Z := 0xd0c0c.       (* [comment removed for export] *)
Definition e_pixBilateralExact : Z := 0xd0e80.      (* [comment removed for export] *)
Definition e_pixBilateralGrayExact : Z := 0xd1368.  (* [comment removed for export] *)
Definition e_pixBlockBilateralExact : Z := 0xd1ee0. (* [comment removed for export] *)
Definition e_makeGaussianKernel : Z := 0xce088.     (* [comment removed for export] *)
Definition e_makeRangeKernel : Z := 0xd2330.        (* [comment removed for export] *)
Definition e_kernelInvert : Z := 0xcdc20.
Definition e_kernelGetParameters : Z := 0xccebc.
Definition e_kernelSetOrigin : Z := 0xcd3d0.
Definition e_expf : Z := 0xf9790.                   (* [comment removed for export] *)
Definition e_pixAddMirroredBorder : Z := 0xa0114.   (* [comment removed for export] *)
Definition e_pixAddBorderGeneral : Z := 0x9fbdc.    (* [comment removed for export] *)
Definition e_pixRasterop : Z := 0xb3514.            (* [comment removed for export] *)
Definition e_rasteropLow : Z := 0xb45bc.            (* [comment removed for export] *)
Definition e_rasteropUniLow : Z := 0xb39f0.         (* [comment removed for export] *)
Definition e_pixGetExtremeValue : Z := 0xa4f4c.     (* [comment removed for export] *)
Definition e_pixaAddPix : Z := 0x974c4.             (* [comment removed for export] *)
Definition e_pixaGetPix : Z := 0x97994.
Definition e_pixaGetCount : Z := 0x97c40.
Definition e_pixaVerifyDepth : Z := 0x983bc.        (* [comment removed for export] *)
Definition e_pixaGetPixDimensions : Z := 0x97ff4.   (* [comment removed for export] *)
Definition e_pixaGetLinePtrs : Z := 0x98840.        (* [comment removed for export] *)
Definition e_pixGetLinePtrs : Z := 0x9d248.
Definition e_pixCreateTemplate : Z := 0x9a248.
Definition e_pixCopyResolution : Z := 0x9a9c4.
Definition e_pixGetRGBComponent : Z := 0x9e6fc.     (* [comment removed for export] *)
Definition e_pixSetRGBComponent : Z := 0x9ec78.     (* [comment removed for export] *)
Definition e_pixCreateRGBImage : Z := 0xa0bdc.      (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RA_BI_COPY1 : Z := 0x9667c.      Definition RA_BI_BILAT : Z := 0x966a0.
Definition RA_BI_DESTROY1 : Z := 0x966ac.   Definition RA_BI_DESTROY2 : Z := 0x966b4.
Definition RA_BI_COPY2 : Z := 0x966c4.      Definition RA_BI_BLOCK : Z := 0x966dc.
Definition RA_BI_DESTROY3 : Z := 0x966e8.   Definition RA_BI_DESTROY4 : Z := 0x966f0.  Definition RA_BI_DESTROY5 : Z := 0x966f8.

(* [comment removed for export] *)
Definition PIX_SRC : Z := 12.   Definition PIX_CLR : Z := 0.
Definition L_SELECT_MIN : Z := 4.   Definition L_SELECT_MAX : Z := 5.
Definition L_INSERT : Z := 0.   Definition L_CLONE : Z := 2.

(* [comment removed for export] *)
Definition fs32 (bits : Z) : word := nan_box (Z_to_bv 32 bits).
Definition F_5_0 : Z := 0x40a00000.   Definition F_10_0 : Z := 0x41200000.   Definition F_1_0 : Z := 0x3f800000.
Definition r_fa0 : reg := Z_to_bv 5 10.   Definition r_fa1 : reg := Z_to_bv 5 11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BI_FUZZ_LIVE : Z := 128.
Definition BI_FUZZ_SECB : Z := 15 * 2^26 + 2^22.
Definition BI_FUZZ_COST : Z := 2^34.
(* [comment removed for export] *)
Definition BC_SECB : Z := 12 * 2^26 + 2^21.            (* [comment removed for export] *)
Definition BC_COST : Z := 22 * RASTER_COST + 2^26.      (* [comment removed for export] *)
Definition PBG_SECB : Z := BC_SECB + 2^26.              (* [comment removed for export] *)
Definition PBG_COST : Z := BC_COST + RASTER_COST + 2^10.
Definition PB_SECB : Z := PBG_SECB + 2^26.              (* [comment removed for export] *)
Definition PB_COST : Z := 3 * PBG_COST + 8 * RASTER_COST.
Definition PBE_SECB : Z := 4 * 2^26.                    (* [comment removed for export] *)
Definition PBE_COST : Z := 12 * RASTER_COST + 2^20.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_new_live (pix : Z) (v : pixv) (live : list (Z * Z)) : list (Z * Z) := (p_data v, rsize v) :: (pix, 64) :: live.
(* [comment removed for export] *)
Definition pix8 (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) : Prop :=
  pix_obj live m pix v (mkCmapv 0 0 0 0) /\ p_d v = 8 /\ p_cmap v = 0 /\ p_data v <> 0.
(* [comment removed for export] *)
Definition pix8rc (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (rc : Z) : Prop :=
  pix_obj_rc live m pix v (mkCmapv 0 0 0 0) rc /\ p_d v = 8 /\ p_cmap v = 0 /\ p_data v <> 0.

(* [comment removed for export] *)
Record pixe : Type := mkPixe { pe_pix : Z; pe_v : pixv }.
Definition pixa_cellsn (n nalloc parr ba : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 parr); C8 (Z_to_bv 64 ba)].
Definition pe_chunks (e : pixe) : list Z := [pe_pix e; p_data (pe_v e)].
Definition pixa_objn (live : list (Z * Z)) (m : mem) (pa nalloc parr ba barr : Z) (ps : list pixe) : Prop :=
  (exists pad, rw_cells asegs m pa (pixa_cellsn (Z.of_nat (length ps)) nalloc parr ba pad)) /\ chunk live pa 32
  /\ chunk live parr (8 * nalloc) /\ u64arr asegs m parr (map (fun e => Z_to_bv 64 (pe_pix e)) ps)
  /\ boxa_empty live m ba nalloc barr /\ 1 <= nalloc <= 20 /\ Z.of_nat (length ps) <= nalloc
  /\ Forall (fun e => pix8 live m (pe_pix e) (pe_v e)) ps
  /\ List.NoDup ([pa; parr; ba; barr] ++ flat_map pe_chunks ps).
(* [comment removed for export] *)
Definition pixa_live (pa parr ba barr n : Z) (live : list (Z * Z)) : list (Z * Z) :=
  (barr, n * 8) :: (ba, 24) :: (parr, n * 8) :: (pa, 32) :: live.
(* [comment removed for export] *)
Definition pe_destroy (live : list (Z * Z)) (e : pixe) : list (Z * Z) := live_remove (pe_pix e) (live_remove (p_data (pe_v e)) live).
Definition pixa_unlive (pa parr ba barr : Z) (ps : list pixe) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove pa (live_remove ba (live_remove barr (live_remove parr (fold_left pe_destroy ps live)))).

(* [comment removed for export] *)
Definition row_ptrs (v : pixv) : list word := map (fun i => Z_to_bv 64 (p_data v + 4 * p_wpl v * Z.of_nat i)) (seq 0 (Z.to_nat (p_h v))).
Definition lines_obj (live : list (Z * Z)) (m : mem) (lp : Z) (v : pixv) : Prop :=
  chunk live lp (8 * p_h v) /\ u64arr asegs m lp (row_ptrs v).
(* [comment removed for export] *)
Definition ls_obj (live : list (Z * Z)) (m : mem) (ls : Z) (lps : list Z) (ps : list pixe) : Prop :=
  chunk live ls (8 * Z.of_nat (length ps)) /\ u64arr asegs m ls (map (Z_to_bv 64) lps) /\ length lps = length ps
  /\ Forall2 (fun lp e => lines_obj live m lp (pe_v e)) lps ps /\ List.NoDup (ls :: lps).
(* [comment removed for export] *)
Definition ls_live (ls : Z) (lps : list Z) (ps : list pixe) (live : list (Z * Z)) : list (Z * Z) :=
  rev (map (fun '(lp, e) => (lp, 8 * p_h (pe_v e))) (combine lps ps)) ++ (ls, 8 * Z.of_nat (length ps)) :: live.

(* [comment removed for export] *)
Record bilv : Type := mkBilv { b_pixs : Z; b_pixsc : Z; b_spatial : Z; b_range : Z; b_minval : Z; b_maxval : Z; b_ncomps : Z;
                               b_nc : Z; b_kindex : Z; b_kfract : Z; b_pixac : Z; b_lineset : Z;
                               (* [comment removed for export] *) b_parr : Z; b_ba : Z; b_barr : Z }.
Definition bil_cells (b : bilv) (sstd rstd : word) (pad1 pad2 : list byte) : list cell :=
  [C8 (Z_to_bv 64 (b_pixs b)); C8 (Z_to_bv 64 (b_pixsc b)); C4 (Z_to_bv 64 1); C4 sstd; C4 rstd; CB 4 pad1;
   C8 (Z_to_bv 64 (b_spatial b)); C8 (Z_to_bv 64 (b_range b)); C4 (Z_to_bv 64 (b_minval b)); C4 (Z_to_bv 64 (b_maxval b));
   C4 (Z_to_bv 64 (b_ncomps b)); CB 4 pad2; C8 (Z_to_bv 64 (b_nc b)); C8 (Z_to_bv 64 (b_kindex b)); C8 (Z_to_bv 64 (b_kfract b));
   C8 (Z_to_bv 64 (b_pixac b)); C8 (Z_to_bv 64 (b_lineset b))].
(* [comment removed for export] *)
Definition kidx_ok (ncomps : Z) (ks : list word) : Prop :=
  length ks = 256%nat /\ Forall (fun w => 0 <= bv_unsigned w <= ncomps - 2) ks.
(* [comment removed for export] *)
Definition bil_obj (live : list (Z * Z)) (m : mem) (bil : Z) (b : bilv) (vs vsc : pixv) (ps : list pixe) (lps : list Z) : Prop :=
  (exists sstd rstd pad1 pad2, rw_cells asegs m bil (bil_cells b sstd rstd pad1 pad2)) /\ chunk live bil 104 /\ b_ncomps b = 10
  /\ pix_obj_rc live m (b_pixs b) vs (mkCmapv 0 0 0 0) 2 /\ p_d vs = 8 /\ p_cmap vs = 0 /\ p_data vs <> 0
  /\ pix8 live m (b_pixsc b) vsc /\ p_w vsc = p_w vs + 22 /\ p_h vsc = p_h vs + 22
  /\ chunk live (b_spatial b) 44 /\ chunk live (b_range b) 1024 /\ chunk live (b_nc b) 40 /\ chunk live (b_kfract b) 1024
  /\ chunk live (b_kindex b) 1024 /\ (exists ks, u32arr asegs m (b_kindex b) ks /\ kidx_ok 10 ks)
  /\ pixa_objn live m (b_pixac b) 10 (b_parr b) (b_ba b) (b_barr b) ps /\ length ps = 10%nat
  /\ Forall (fun e => p_w (pe_v e) = p_w vs /\ p_h (pe_v e) = p_h vs) ps
  /\ ls_obj live m (b_lineset b) lps ps
  /\ List.NoDup ([bil; b_pixs b; b_pixsc b; p_data vs; p_data vsc; b_spatial b; b_range b; b_nc b; b_kindex b; b_kfract b;
                  b_pixac b; b_parr b; b_ba b; b_barr b; b_lineset b] ++ flat_map pe_chunks ps ++ lps).
(* [comment removed for export] *)
Definition bil_live (bil : Z) (b : bilv) (vsc : pixv) (ps : list pixe) (lps : list Z) (live : list (Z * Z)) : list (Z * Z) :=
  ls_live (b_lineset b) lps ps
    (rev (flat_map (fun e => [(pe_pix e, 64); (p_data (pe_v e), rsize (pe_v e))]) ps)
     ++ pixa_live (b_pixac b) (b_parr b) (b_ba b) (b_barr b) 10
          ((b_range b, 1024) :: (b_spatial b, 44) :: (b_kfract b, 1024) :: (b_kindex b, 1024) :: (b_nc b, 40) :: (bil, 104)
           :: pix_new_live (b_pixsc b) vsc live)).

Section BiIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expf_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_expf m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition kout (Σ : rts RT) (m : mem) (p : Z) : Prop := p = 0 \/ (optrF RT Σ m p 4 /\ exists x, rw_cells asegs m p [C4 x]).
Definition kout_post (m' : mem) (p v : Z) : Prop := p = 0 \/ rw_cells asegs m' p [C4 (Z_to_bv 64 v)].
Definition kout_fp (ps : list Z) : list (Z * Z) := map (fun p => (p, p + 4)) (List.filter (fun p => negb (p =? 0)) ps).
Definition kernelGetParameters_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kel sy sx cy cx data psy psx pcy pcx : Z) (rows : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kel -> a1 = Z_to_bv 64 psy -> a2 = Z_to_bv 64 psx -> a3 = Z_to_bv 64 pcy -> a4 = Z_to_bv 64 pcx ->
  kel_obj (rt_live RT Σ) m kel sy sx cy cx data rows -> 0 <= cy < 2^31 -> 0 <= cx < 2^31 ->
  optrF RT Σ m psy 4 -> (exists x, rw_cells asegs m psy [C4 x]) -> optrF RT Σ m psx 4 -> (exists x, rw_cells asegs m psx [C4 x]) ->
  psy <> psx ->
  ((pcy = 0 /\ pcx = 0)
   \/ (optrF RT Σ m pcy 4 /\ (exists x, rw_cells asegs m pcy [C4 x]) /\ optrF RT Σ m pcx 4 /\ (exists x, rw_cells asegs m pcx [C4 x])
       /\ List.NoDup [psy; psx; pcy; pcx])) ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelGetParameters m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp ((psy, psy + 4) :: (psx, psx + 4) :: (if pcy =? 0 then [] else [(pcy, pcy + 4); (pcx, pcx + 4)])) m m'
          /\ rw_cells asegs m' psy [C4 (Z_to_bv 64 sy)] /\ rw_cells asegs m' psx [C4 (Z_to_bv 64 sx)]
          /\ (pcy <> 0 -> rw_cells asegs m' pcy [C4 (Z_to_bv 64 cy)] /\ rw_cells asegs m' pcx [C4 (Z_to_bv 64 cx)])) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition kernelSetOrigin_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kel sy sx cy cx cy' cx' data : Z) (rows : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kel -> s32 a1 cy' -> s32 a2 cx' -> kel_obj (rt_live RT Σ) m kel sy sx cy cx data rows ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelSetOrigin m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(kel + 8, kel + 16)] m m'
          /\ kel_obj (rt_live RT Σ') m' kel sy sx cy' cx' data rows) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition kernelInvert_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kels sy sx cy cx datas : Z) (rowss : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kels -> kel_obj (rt_live RT Σ) m kels sy sx cy cx datas rowss ->
  1 <= sy <= 20000 -> 1 <= sx <= 20000 -> sy * sx <= 2^26 -> 0 <= cy < sy -> 0 <= cx < sx ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 (sy + 2) (km_cost sy sx) ->
  sec_bytes (rt_live RT Σ) + 8 * sy + 4 * (sx * sy) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelInvert m)))
    (fun c => exists (Σ' : rts RT) (keld data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 keld) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' keld sy sx (sy - 1 - cy) (sx - 1 - cx) data rows
          /\ kel_obj (rt_live RT Σ') m' kels sy sx cy cx datas rowss) c
       /\ rt_live RT Σ' = km_live keld data sy sx rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost sy sx <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition makeGaussianKernel_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (hh hw : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 hh -> a1 = Z_to_bv 64 hw -> 0 <= hh <= 1000 -> 0 <= hw <= 1000 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 (2 * hh + 3) (km_cost (2 * hh + 1) (2 * hw + 1)) ->
  sec_bytes (rt_live RT Σ) + 8 * (2 * hh + 1) + 4 * ((2 * hw + 1) * (2 * hh + 1)) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeGaussianKernel m)))
    (fun c => exists (Σ' : rts RT) (kel data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' kel (2 * hh + 1) (2 * hw + 1) hh hw data rows) c
       /\ rt_live RT Σ' = km_live kel data (2 * hh + 1) (2 * hw + 1) rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - km_cost (2 * hh + 1) (2 * hw + 1) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition makeRangeKernel_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  reg_get F r_fa0 = fs32 F_1_0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 3 (km_cost 1 256) ->
  sec_bytes (rt_live RT Σ) + 8 * 1 + 4 * (256 * 1) <= SEC_BYTES ->   (* [comment removed for export] *)
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeRangeKernel m)))
    (fun c => exists (Σ' : rts RT) (kel data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' kel 1 256 0 0 data rows) c
       /\ rt_live RT Σ' = km_live kel data 1 256 rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost 1 256 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixBilateralGrayExact_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix8 (rt_live RT Σ) m pix v -> kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 8 50 (3 * RASTER_COST + 2^20) ->
  sec_bytes (rt_live RT Σ) + 2 * 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralGrayExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix8 (rt_live RT Σ') m' pix v /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (3 * RASTER_COST + 2^20) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixBilateralExact_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 9 60 (PBE_COST - 2^19) ->
  sec_bytes (rt_live RT Σ) + PBE_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (PBE_COST - 2^19) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixBlockBilateralExact_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> reg_get F r_fa0 = fs32 F_10_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 10 (BI_FUZZ_LIVE - 16) PBE_COST ->
  sec_bytes (rt_live RT Σ) + PBE_SECB + 2^20 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBlockBilateralExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - PBE_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rect_in (v : pixv) (x y w h : Z) : Prop := 0 <= x -> 0 <= y -> 0 < w -> 0 < h -> x + w <= p_w v /\ y + h <= p_h v.
Definition rect_ok (v : pixv) (x y w h : Z) : Prop := 0 <= x /\ 0 <= y /\ 0 < w /\ 0 < h /\ x + w <= p_w v /\ y + h <= p_h v.
(* [comment removed for export] *)
Definition pixRasterop_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (dx dy dw dh op sx sy rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> s32 a1 dx -> s32 a2 dy -> s32 a3 dw -> s32 a4 dh -> a5 = Z_to_bv 64 op -> a6 = Z_to_bv 64 ps -> s32 a7 sx ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] -> 0 <= sy < 2^31 ->
  (pd = 0 \/ (pix8 (rt_live RT Σ) m pd vd /\ rect_ok vd dx dy dw dh)) ->
  ((op = PIX_CLR /\ ps = 0)
   \/ (op = PIX_SRC /\ pix8rc (rt_live RT Σ) m ps vs rcs /\ 1 <= rcs <= 2 /\ rect_ok vs sx sy dw dh /\ (ps = pd -> vs = vd /\ rcs = 1))) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 8 0 8 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp (if pd =? 0 then [] else [(p_data vd, p_data vd + rsize vd)]) m m'
          /\ (pd <> 0 -> pix8 (rt_live RT Σ') m' pd vd) /\ (op = PIX_SRC -> pix8rc (rt_live RT Σ') m' ps vs rcs)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 8 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixAddBorderGeneral0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (l r t b rc : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 r -> a3 = Z_to_bv 64 t -> a4 = Z_to_bv 64 b -> a5 = Z_to_bv 64 0 ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 -> p_data v <> 0 ->
  1 <= l <= 21 -> 1 <= r <= 21 -> 1 <= t <= 21 -> 1 <= b <= 21 ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 9 2 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v + l + r /\ p_h vd = p_h v + t + b)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixAddMirroredBorder_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (l r t b rc : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 r -> a3 = Z_to_bv 64 t -> a4 = Z_to_bv 64 b ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 -> p_data v <> 0 ->
  1 <= l <= 21 -> 1 <= r <= 21 -> 1 <= t <= 21 -> 1 <= b <= 21 -> l <= p_w v -> r <= p_w v -> t <= p_h v -> b <= p_h v ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 10 2 (RASTER_COST + 1024) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddMirroredBorder m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v + l + r /\ p_h vd = p_h v + t + b)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 1024) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixGetRGBComponent_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (comp : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 comp -> 0 <= comp <= 2 ->
  pix_obj (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) -> p_d v = 32 -> p_cmap v = 0 -> p_data v <> 0 ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 4 2 (RASTER_COST + 16) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetRGBComponent m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0)
          /\ pixd <> 0 /\ pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v) c
       /\ rt_live RT Σ' = pix_new_live pixd vd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 16) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixSetRGBComponent_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (comp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> a1 = Z_to_bv 64 ps -> a2 = Z_to_bv 64 comp -> 0 <= comp <= 2 ->
  pix_obj (rt_live RT Σ) m pd vd (mkCmapv 0 0 0 0) -> p_d vd = 32 -> p_cmap vd = 0 -> p_data vd <> 0 ->
  pix8 (rt_live RT Σ) m ps vs -> p_w vs = p_w vd -> p_h vs = p_h vd -> pd <> ps ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 3 0 3 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetRGBComponent m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m'
          /\ pix_obj (rt_live RT Σ') m' pd vd (mkCmapv 0 0 0 0) /\ pix8 (rt_live RT Σ') m' ps vs) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 3 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition optpix8 (live : list (Z * Z)) (m : mem) (p : Z) (v : pixv) : Prop := p = 0 \/ pix8 live m p v.
Definition pixCreateRGBImage_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pr pg pb : Z) (vr vg vb : pixv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pr -> a1 = Z_to_bv 64 pg -> a2 = Z_to_bv 64 pb ->
  optpix8 (rt_live RT Σ) m pr vr -> optpix8 (rt_live RT Σ) m pg vg -> optpix8 (rt_live RT Σ) m pb vb ->
  p_w vg = p_w vr -> p_w vb = p_w vr -> p_h vg = p_h vr -> p_h vb = p_h vr ->
  (pr <> 0 -> pg <> 0 -> pb <> 0 -> List.NoDup [pr; pg; pb]) ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 5 2 (RASTER_COST + 32) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateRGBImage m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ optpix8 (rt_live RT Σ') m' pr vr /\ optpix8 (rt_live RT Σ') m' pg vg /\ optpix8 (rt_live RT Σ') m' pb vb
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_d vd = 32 /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w vr /\ p_h vd = p_h vr)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 32) <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PIXA_CALLOC1 : Z := 0x970d8.
Definition pixaCreate_n_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 20 ->
  (* [comment removed for export] *)
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 4 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaCreate m)))
    (fun c => exists (Σ' : rts RT) (pa parr ba barr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pa) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixa_objn (rt_live RT Σ') m' pa n parr ba barr []) c
       /\ rt_live RT Σ' = pixa_live pa parr ba barr n (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixaAddPix_ins_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr pix : Z) (v : pixv) (ps : list pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 pix -> a2 = Z_to_bv 64 L_INSERT ->
  pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps -> Z.of_nat (length ps) < nalloc ->
  pix8 (rt_live RT Σ) m pix v -> ~ In pix ([pa; parr; ba; barr] ++ flat_map pe_chunks ps)
  -> ~ In (p_data v) ([pa; parr; ba; barr] ++ flat_map pe_chunks ps) ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaAddPix m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(pa, pa + 4); (parr + 8 * Z.of_nat (length ps), parr + 8 * Z.of_nat (length ps) + 8)] m m'
          /\ pixa_objn (rt_live RT Σ') m' pa nalloc parr ba barr (ps ++ [mkPixe pix v])) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixaGetCount_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr : Z) (ps : list pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaGetCount m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length ps))) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixaGetPix_clone_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr i : Z) (ps : list pixe) (e : pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 L_CLONE ->
  pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps -> 0 <= i -> nth_error ps (Z.to_nat i) = Some e ->
  lenv RT Σ m sp lo (LSTK 2) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaGetPix m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (pe_pix e)) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pe_pix e + 20, pe_pix e + 24)] m m'
          /\ rw_cells asegs m' (pe_pix e) (pix_cells_rc (pe_v e) 2)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixaGetPixDimensions_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr i pd : Z) (ps : list pixe) (e : pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 pd ->
  pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps -> 0 <= i -> nth_error ps (Z.to_nat i) = Some e ->
  optrF RT Σ m pd 4 -> (exists x, rw_cells asegs m pd [C4 x]) ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaGetPixDimensions m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pd, pd + 4)] m m'
          /\ pixa_objn (rt_live RT Σ') m' pa nalloc parr ba barr ps
          /\ rw_cells asegs m' pd [C4 (Z_to_bv 64 (p_d (pe_v e)))]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixaVerifyDepth_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr psame : Z) (ps : list pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 psame -> a2 = Z_to_bv 64 0 ->
  pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps -> ps <> [] ->
  bv_unsigned sp <= psame -> psame + 4 <= USTACK_TOP -> psame mod 4 = 0 -> (exists x, rw_cells asegs m psame [C4 x]) ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 3 0 (3 * Z.of_nat (length ps) + 4) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaVerifyDepth m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(psame, psame + 4)] m m'
          /\ pixa_objn (rt_live RT Σ') m' pa nalloc parr ba barr ps
          /\ rw_cells asegs m' psame [C4 (Z_to_bv 64 1)]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (3 * Z.of_nat (length ps) + 4) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixGetLinePtrs_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix rc : Z) (v : pixv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 0 ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_data v <> 0 ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 1 (mcost (8 * p_h v)) ->
  sec_bytes (rt_live RT Σ) + 8 * p_h v <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetLinePtrs m)))
    (fun c => exists (Σ' : rts RT) (lp : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 lp) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ lines_obj (rt_live RT Σ') m' lp v /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc) c
       /\ rt_live RT Σ' = (lp, 8 * p_h v) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - mcost (8 * p_h v) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition PGLP_CALLOC : Z := 0x989d0.
Definition pixaGetLinePtrs_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pa nalloc parr ba barr : Z) (ps : list pixe) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 0 ->
  pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps -> ps <> [] ->
  uctx m sp s0 ras -> In (PGLP_CALLOC :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 4 (Z.of_nat (length ps) + 1) (5 * Z.of_nat (length ps) * mcost 160000 + 64) ->
  sec_bytes (rt_live RT Σ) + 160000 * Z.of_nat (length ps) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaGetLinePtrs m)))
    (fun c => exists (Σ' : rts RT) (ls : Z) (lps : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ls) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixa_objn (rt_live RT Σ') m' pa nalloc parr ba barr ps /\ ls_obj (rt_live RT Σ') m' ls lps ps) c
       /\ rt_live RT Σ' = ls_live ls lps ps (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (5 * Z.of_nat (length ps) * mcost 160000 + 64) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixaDestroy_n_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pa nalloc parr ba barr : Z) (ps : list pixe),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (pixa_unlive pa parr ba barr ps (rt_live RT Σ)) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 pa)] -> pixa_objn (rt_live RT Σ) m pa nalloc parr ba barr ps ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 1 0 (Z.of_nat (length ps) + 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = pixa_unlive pa parr ba barr ps (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (Z.of_nat (length ps) + 1) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateTemplate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix rc : Z) (v : pixv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 ->
  p_data v <> 0 ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 (RASTER_COST + 64) ->   (* [comment removed for export] *)
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplate m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) rc
          /\ pixd <> 0 /\ pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v) c
       /\ rt_live RT Σ' = pix_new_live pixd vd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixv_res (v : pixv) (xr yr : Z) : pixv :=
  mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) xr yr (p_inf v) (p_spec v) (p_cmap v) (p_data v).
Definition pixCopyResolution_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (cvd cvs : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> a1 = Z_to_bv 64 ps -> pix_obj (rt_live RT Σ) m pd vd cvd ->
  pix_obj_rc (rt_live RT Σ) m ps vs cvs rc -> 1 <= rc <= 2 -> pd <> ps ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyResolution m)))
    (fun c => exists (Σ' : rts RT) (rv : word) (xr yr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pd + 24, pd + 32)] m m'
          /\ pix_obj (rt_live RT Σ') m' pd (pixv_res vd xr yr) cvd) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition BD_FREE_RAS : list Z := [0xd0cb0; 0xd0ccc; 0xd0ce8; 0xd0d04; 0xd0d20; 0xd0da4; 0xd0de0; 0xd0de8].
Definition bil_unlive (bil : Z) (b : bilv) (vsc : pixv) (ps : list pixe) (lps : list Z) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove bil (live_remove (b_lineset b) (fold_left (fun l lp => live_remove lp l) lps
    (live_remove (b_kfract b) (live_remove (b_kindex b) (live_remove (b_nc b) (live_remove (b_range b) (live_remove (b_spatial b)
      (pixa_unlive (b_pixac b) (b_parr b) (b_ba b) (b_barr b) ps (live_destroy (b_pixsc b) vsc (mkCmapv 0 0 0 0) live))))))))).
Definition bilateralDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp bil : Z) (b : bilv) (vs vsc : pixv) (ps : list pixe) (lps : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> pp = bv_unsigned sp -> rw_cells asegs m pp [C8 (Z_to_bv 64 bil)] ->
  bil_obj (rt_live RT Σ) m bil b vs vsc ps lps ->
  Forall (fun f => In [f; bv_unsigned ra] CLIENT_TRACES) BD_FREE_RAS ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 0 16 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8); (b_pixs b + 20, b_pixs b + 24)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)] /\ pix_obj (rt_live RT Σ') m' (b_pixs b) vs (mkCmapv 0 0 0 0)) c
       /\ rt_live RT Σ' = bil_unlive bil b vsc ps lps (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 16 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixGetExtremeValue_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix rc ty pg : Z) (v : pixv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 ty -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 -> a5 = Z_to_bv 64 0 ->
  a6 = Z_to_bv 64 pg -> (ty = L_SELECT_MIN \/ ty = L_SELECT_MAX) ->
  pix_obj_rc (rt_live RT Σ) m pix v (mkCmapv 0 0 0 0) rc -> 1 <= rc <= 2 -> p_d v = 8 -> p_cmap v = 0 -> p_data v <> 0 ->
  optrF RT Σ m pg 4 -> rw_cells asegs m pg [C4 x] ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 2 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetExtremeValue m)))
    (fun c => exists (Σ' : rts RT) (val : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pg, pg + 4)] m m'
          /\ rw_cells asegs m' pg [C4 (Z_to_bv 64 val)] /\ 0 <= val <= 255) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition BC_CALLOC_RAS : list Z := [0xcf0d8; 0xcf228; 0xcf300; 0xcf394; 0xcf41c; 0xcf4f0].
Definition RA_BC_PIXACREATE : Z := 0xcf5a8.
Definition RA_BC_LINEPTRS : Z := 0xd006c.
Definition bilateralCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix8 (rt_live RT Σ) m pix v -> 22 <= p_w v -> 22 <= p_h v ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) BC_CALLOC_RAS ->
  In (PIXA_CALLOC1 :: RA_BC_PIXACREATE :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  In (PGLP_CALLOC :: RA_BC_LINEPTRS :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 9 48 BC_COST ->
  sec_bytes (rt_live RT Σ) + BC_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralCreate m)))
    (fun c => exists (Σ' : rts RT) (bil : Z) (b : bilv) (vsc : pixv) (ps : list pixe) (lps : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 bil) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ (bil = 0 -> pix8 (rt_live RT Σ') m' pix v)
          /\ (bil <> 0 -> b_pixs b = pix /\ bil_obj (rt_live RT Σ') m' bil b v vsc ps lps)) c
       /\ rt_live RT Σ' = (if bil =? 0 then rt_live RT Σ else bil_live bil b vsc ps lps (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition bilateralApply_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (bil : Z) (b : bilv) (vs vsc : pixv) (ps : list pixe) (lps : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 bil -> bil_obj (rt_live RT Σ) m bil b vs vsc ps lps ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 (RASTER_COST + 128) ->   (* [comment removed for export] *)
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bilateralApply m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ bil_obj (rt_live RT Σ') m' bil b vs vsc ps lps
          /\ pixd <> 0 /\ pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w vs /\ p_h vd = p_h vs) c
       /\ rt_live RT Σ' = pix_new_live pixd vd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 128) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition RA_PBG_DESTROY : Z := 0xced3c.
Definition pixBilateralGray_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix8 (rt_live RT Σ) m pix v -> 22 <= p_w v -> 22 <= p_h v ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 10 52 PBG_COST ->
  sec_bytes (rt_live RT Σ) + PBG_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralGray m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ pix8 (rt_live RT Σ') m' pix v
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - PBG_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixBilateral_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
  reg_get F r_fa0 = fs32 F_5_0 -> reg_get F r_fa1 = fs32 F_10_0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  uctx m sp s0 ras ->
  lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 11 (BI_FUZZ_LIVE - 16) PB_COST ->
  sec_bytes (rt_live RT Σ) + PB_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateral m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (pixd <> 0 -> pix_obj (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_data vd <> 0
                           /\ p_w vd = p_w v /\ p_h vd = p_h v /\ p_d vd = p_d v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - PB_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition bi_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + BI_FUZZ_LIVE <= LIVE_MAX -> BI_FUZZ_COST <= rt_credit RT Σ ->
  sec_bytes (rt_live RT Σ) + BI_FUZZ_SECB <= SEC_BYTES ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_bi_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - BI_FUZZ_COST <= rt_credit RT Σ').

End BiIface.
