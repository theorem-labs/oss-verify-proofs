(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_cf_fuzz : Z := 0x8d5b8.            (* [comment removed for export] *)
Definition e_l_dnaaCreate : Z := 0x8dd78.
Definition e_l_dnaaDestroy : Z := 0x8dedc.
Definition e_numaaCreate : Z := 0x8e240.
Definition e_numaaDestroy : Z := 0x8e3a4.
Definition e_pixaCreate : Z := 0x8e708.
Definition e_pixaDestroy : Z := 0x8e8fc.
Definition e_boxCreate : Z := 0x8eb38.
Definition e_boxaCreate : Z := 0x8ee20.
Definition e_boxaDestroy : Z := 0x8efb8.
Definition e_boxaAddBox : Z := 0x8f30c.
Definition e_pixClone : Z := 0x911c0.
Definition e_colorfillCreate : Z := 0x93b6c.
Definition e_colorfillDestroy : Z := 0x940f4.

(* [comment removed for export] *)
Definition RA_CF_CREATE : Z := 0x8d700.         (* [comment removed for export] *)
Definition RA_CF_DESTROY : Z := 0x8d70c.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CF_TRACES : list (list Z) :=
  [ [0x8eba4]; [0x8ee4c]; [0x8eed0]; [0x8e288]; [0x8e29c]; [0x8ddc0]; [0x8ddd4]; [0x8e7b8];
    [0x8ee4c; RA_CF_CREATE; RA_TOP]; [0x8e74c; RA_CF_CREATE; RA_TOP]; [0x93e80; RA_CF_CREATE; RA_TOP];
    [0x8f138]; [0x8f23c]; [0x8f244]; [0x8ea8c]; [0x8ea9c]; [0x8e5d0]; [0x8e5d8]; [0x8e108]; [0x8e110]; [0x9418c] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_cells_rc (v : pixv) (rc : Z) : list cell :=
  [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 (p_d v)); C4 (Z_to_bv 64 (p_spp v)); C4 (Z_to_bv 64 (p_wpl v));
   C4 (Z_to_bv 64 rc); C4 (Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (p_cmap v)); C8 (Z_to_bv 64 (p_data v))].
Lemma pix_cells_rc_1 : forall v, pix_cells_rc v 1 = pix_cells v.
Proof. reflexivity. Qed.
Definition pix_obj_rc (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z) : Prop :=
  rw_cells asegs m pix (pix_cells_rc v rc) /\ chunk live pix 64 /\ pix_hdr_ok v
  /\ (p_data v = 0 \/ (chunk live (p_data v) (rsize v) /\ p_data v <> pix))
  /\ (p_cmap v = 0 \/ (cmap_obj live m (p_cmap v) cv /\ p_cmap v <> pix /\ c_arr cv <> pix
                        /\ p_cmap v <> p_data v /\ c_arr cv <> p_data v)).
Lemma pix_obj_rc_1 : forall live m pix v cv, pix_obj_rc live m pix v cv 1 <-> pix_obj live m pix v cv.
Proof. intros. unfold pix_obj_rc, pix_obj. rewrite pix_cells_rc_1. tauto. Qed.

(* [comment removed for export] *)
Definition box_cells (x y w h : Z) : list cell :=
  [C4 (Z_to_bv 64 x); C4 (Z_to_bv 64 y); C4 (Z_to_bv 64 w); C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 1)].
Definition box_obj (live : list (Z * Z)) (m : mem) (b x y w h : Z) : Prop :=
  rw_cells asegs m b (box_cells x y w h) /\ chunk live b 20.

(* [comment removed for export] *)
Definition boxa_cells (n nalloc arr : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 arr)].
(* [comment removed for export] *)
Definition boxa_empty (live : list (Z * Z)) (m : mem) (ba nalloc arr : Z) : Prop :=
  (exists pad, rw_cells asegs m ba (boxa_cells 0 nalloc arr pad)) /\ chunk live ba 24 /\ chunk live arr (8 * nalloc)
  /\ 1 <= nalloc <= 20 /\ arr <> ba.
(* [comment removed for export] *)
Definition boxa_new (live : list (Z * Z)) (m : mem) (ba nalloc arr : Z) : Prop :=
  boxa_empty live m ba nalloc arr
  /\ rw_cells asegs m arr [CB (Z.to_nat (nalloc * 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (nalloc * 8)))].
(* [comment removed for export] *)
Definition boxa_one (live : list (Z * Z)) (m : mem) (ba arr b x y w h : Z) : Prop :=
  (exists pad, rw_cells asegs m ba (boxa_cells 1 1 arr pad)) /\ chunk live ba 24 /\ chunk live arr 8
  /\ rw_cells asegs m arr [C8 (Z_to_bv 64 b)] /\ box_obj live m b x y w h /\ arr <> ba /\ b <> ba /\ b <> arr.

(* [comment removed for export] *)
Definition parr16_cells (nalloc arr : Z) : list cell := [C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 arr)].
Definition parr16_obj (live : list (Z * Z)) (m : mem) (o nalloc arr : Z) : Prop :=
  rw_cells asegs m o (parr16_cells nalloc arr) /\ chunk live o 16 /\ chunk live arr (8 * nalloc) /\ 1 <= nalloc <= 50 /\ arr <> o.

(* [comment removed for export] *)
Definition pixa_cells (nalloc parr ba : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 parr); C8 (Z_to_bv 64 ba)].
Definition pixa_obj (live : list (Z * Z)) (m : mem) (pa nalloc parr ba barr : Z) : Prop :=
  (exists pad, rw_cells asegs m pa (pixa_cells nalloc parr ba pad)) /\ chunk live pa 32 /\ chunk live parr (8 * nalloc)
  /\ boxa_empty live m ba nalloc barr /\ 1 <= nalloc <= 20
  /\ List.NoDup [pa; parr; ba; barr].

(* [comment removed for export] *)
Record cfv : Type := mkCfv { cf_pix : Z; cf_tw : Z; cf_th : Z; cf_boxas : Z; cf_barr : Z; cf_box : Z;
                             cf_naa : Z; cf_naarr : Z; cf_dnaa : Z; cf_dnarr : Z;
                             cf_pixa : Z; cf_parr : Z; cf_pba : Z; cf_pbarr : Z }.
Definition cf_cells (c : cfv) (pad : list byte) : list cell :=
  [C8 (Z_to_bv 64 (cf_pix c)); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (cf_tw c)); C4 (Z_to_bv 64 (cf_th c));
   C4 (Z_to_bv 64 0); CB 4 pad; C8 (Z_to_bv 64 (cf_boxas c)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (cf_naa c)); C8 (Z_to_bv 64 (cf_dnaa c)); C8 (Z_to_bv 64 (cf_pixa c))].
(* [comment removed for export] *)
Definition cf_chunks (c : cfv) : list (Z * Z) :=
  [(cf_boxas c, 24); (cf_barr c, 8); (cf_box c, 20); (* [comment removed for export] *)
   (cf_naa c, 16); (cf_naarr c, 8); (cf_dnaa c, 16); (cf_dnarr c, 8);
   (cf_pixa c, 32); (cf_parr c, 160); (cf_pba c, 24); (cf_pbarr c, 160)].
(* [comment removed for export] *)
Definition cf_live (cf : Z) (c : cfv) (live : list (Z * Z)) : list (Z * Z) :=
  (cf_pbarr c, 160) :: (cf_pba c, 24) :: (cf_parr c, 160) :: (cf_pixa c, 32) :: (cf_dnarr c, 8) :: (cf_dnaa c, 16)
  :: (cf_naarr c, 8) :: (cf_naa c, 16) :: (cf, 88) :: (cf_box c, 20) :: (cf_barr c, 8) :: (cf_boxas c, 24) :: live.

Definition cf_obj (live : list (Z * Z)) (m : mem) (cf : Z) (c : cfv) : Prop :=
  (exists pad, rw_cells asegs m cf (cf_cells c pad)) /\ chunk live cf 88
  /\ boxa_one live m (cf_boxas c) (cf_barr c) (cf_box c) 0 0 (cf_tw c) (cf_th c)
  /\ parr16_obj live m (cf_naa c) 1 (cf_naarr c) /\ parr16_obj live m (cf_dnaa c) 1 (cf_dnarr c)
  /\ pixa_obj live m (cf_pixa c) 20 (cf_parr c) (cf_pba c) (cf_pbarr c)
  /\ List.NoDup (map fst (cf_live cf c [])).
Section CfIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixClone_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 1 <= rc < 2^31 - 1 ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixClone m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pix (pix_cells_rc v (rc + 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixDestroy_rc_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 2 <= rc < 2^31 -> (pp + 8 <= pix \/ pix + 64 <= pp) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' pix (pix_cells_rc v (rc - 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition boxCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 y -> a2 = Z_to_bv 64 w -> a3 = Z_to_bv 64 h ->
  0 <= x < 2^31 -> 0 <= y < 2^31 -> 0 <= w < 2^31 -> 0 <= h < 2^31 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxCreate m)))
    (fun c => exists (Σ' : rts RT) (b : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 b) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ box_obj (rt_live RT Σ') m' b x y w h) c
       /\ rt_live RT Σ' = (b, 20) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 20 ->
  uctx m sp s0 ras -> In (0x8ee4c :: ras) CLIENT_TRACES ->
  (ras = [] -> bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaCreate m)))
    (fun c => exists (Σ' : rts RT) (ba arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ba) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ boxa_new (rt_live RT Σ') m' ba n arr) c
       /\ rt_live RT Σ' = (arr, n * 8) :: (ba, 24) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaAddBox_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ba arr b x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 ba -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 0 ->
  boxa_new (rt_live RT Σ) m ba 1 arr -> box_obj (rt_live RT Σ) m b x y w h -> b <> ba -> b <> arr ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaAddBox m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(ba, ba + 4); (arr, arr + 8)] m m'
          /\ boxa_one (rt_live RT Σ') m' ba arr b x y w h) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition parr16Create_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 50 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (o arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 o) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ parr16_obj (rt_live RT Σ') m' o n arr) c
       /\ rt_live RT Σ' = (arr, n * 8) :: (o, 16) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).
Definition numaaCreate_cps : Prop := parr16Create_cps e_numaaCreate.
Definition l_dnaaCreate_cps : Prop := parr16Create_cps e_l_dnaaCreate.

(* [comment removed for export] *)
Definition pixaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 ->
  uctx m sp s0 ras -> In (0x8e74c :: ras) CLIENT_TRACES ->
  (ras = [] -> bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 4 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaCreate m)))
    (fun c => exists (Σ' : rts RT) (pa parr ba barr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pa) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ pixa_obj (rt_live RT Σ') m' pa 20 parr ba barr) c
       /\ rt_live RT Σ' = (barr, 160) :: (ba, 24) :: (parr, 160) :: (pa, 32) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaDestroy_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp ba arr b x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove ba (live_remove arr (live_remove b (rt_live RT Σ)))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 ba)] -> boxa_one (rt_live RT Σ) m ba arr b x y w h ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove ba (live_remove arr (live_remove b (rt_live RT Σ)))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaDestroy_empty_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp ba nalloc arr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove ba (live_remove arr (rt_live RT Σ))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 ba)] -> boxa_empty (rt_live RT Σ) m ba nalloc arr ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove ba (live_remove arr (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition parr16Destroy_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp o nalloc arr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove o (live_remove arr (rt_live RT Σ))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 o)] -> parr16_obj (rt_live RT Σ) m o nalloc arr ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove o (live_remove arr (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).
Definition numaaDestroy_cps : Prop := parr16Destroy_cps e_numaaDestroy.
Definition l_dnaaDestroy_cps : Prop := parr16Destroy_cps e_l_dnaaDestroy.

(* [comment removed for export] *)
Definition pixaDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pa nalloc parr ba barr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp ->
  optrL RT (live_remove pa (live_remove ba (live_remove barr (live_remove parr (rt_live RT Σ))))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 pa)] -> pixa_obj (rt_live RT Σ) m pa nalloc parr ba barr ->
  lenv RT Σ m sp lo (LSTK 2) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove pa (live_remove ba (live_remove barr (live_remove parr (rt_live RT Σ))))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixaDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 2) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition l_colorfillCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 1 -> pix_obj (rt_live RT Σ) m pix v cv ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) [0x8ee4c; 0x8e74c; 0x93e80] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 2 12 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_colorfillCreate m)))
    (fun c => exists (Σ' : rts RT) (cf : Z) (cv' : cfv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cf) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ (cf = 0 -> rw_cells asegs m' pix (pix_cells_rc v 1))
          /\ (cf <> 0 -> cf_obj (rt_live RT Σ') m' cf cv' /\ cf_pix cv' = pix /\ rw_cells asegs m' pix (pix_cells_rc v 2))) c
       /\ rt_live RT Σ' = (if cf =? 0 then rt_live RT Σ else cf_live cf cv' (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cf_live_destroy (cf : Z) (c : cfv) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove cf
   (live_remove (cf_pixa c) (live_remove (cf_pba c) (live_remove (cf_pbarr c) (live_remove (cf_parr c)
     (live_remove (cf_dnaa c) (live_remove (cf_dnarr c)
       (live_remove (cf_naa c) (live_remove (cf_naarr c)
         (live_remove (cf_boxas c) (live_remove (cf_barr c) (live_remove (cf_box c) live))))))))))).
Definition l_colorfillDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp cf pix : Z) (c : cfv) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrF RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 cf)] ->
  (cf = 0 \/ (cf_obj (rt_live RT Σ) m cf c /\ cf_pix c = pix /\ pix_obj_rc (rt_live RT Σ) m pix v cv 2
              /\ ~ In pix (map fst (cf_live cf c [])))) ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 1 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_colorfillDestroy m)))
    (fun c' => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ (cf = 0 -> keeps RT Σ Σ' sp [] m m')
          /\ (cf <> 0 -> keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]
                         /\ rw_cells asegs m' pix (pix_cells_rc v 1))) c'
       /\ rt_live RT Σ' = (if cf =? 0 then rt_live RT Σ else cf_live_destroy cf c (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition CF_FUZZ_LIVE : Z := 24.
Definition cf_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + CF_FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_cf_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').

End CfIface.
