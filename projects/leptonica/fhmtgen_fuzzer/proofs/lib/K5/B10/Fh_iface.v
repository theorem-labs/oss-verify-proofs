(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface I_strcmp_spec I_strcmp_lift Lept_kit D_iface D_defs D_libiface
  Lept_iface Gm_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stringNew : Z := 0x915f4.
Definition e_pixAddBorder : Z := 0x96c74.
Definition e_pixRemoveBorder : Z := 0x9725c.
Definition e_selaCreate : Z := 0xae6e8.
Definition e_selaDestroy : Z := 0xae7d8.
Definition e_selDestroy : Z := 0xae95c.
Definition e_selCreate : Z := 0xaebb4.   (* [comment removed for export] *)
Definition e_selCreateBrick : Z := 0xaf414.
Definition e_selSetElement : Z := 0xaf6f8.
Definition e_selaAddSel : Z := 0xaf98c.
Definition e_selaGetCount : Z := 0xafef4.
Definition e_selaGetSel : Z := 0xaffa8.
Definition e_selGetName : Z := 0xb0110.
Definition e_selaAddHitMiss : Z := 0xb01c0.
Definition e_pixHMTDwa_1 : Z := 0xb08cc.
Definition e_pixFHMTGen_1 : Z := 0xb0c14.
Definition e_fhmtgen_low_1 : Z := 0xb1228.
Definition e_strcmp_tramp : Z := 0x515a0.

(* [comment removed for export] *)
Definition HM_NAME_LIT (i : Z) : Z := 0x26fe0 + 0x20 * i.
Definition SEL_NAMES_AT : Z := LIB_SEL_AT.                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hm_name (i : nat) : list byte := firstn 8 (skipn (80 * i) (cells_bytes LIB_SEL_CELLS)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BORDER1_COST : Z := RASTER_COST + 32.                 (* [comment removed for export] *)
Definition FHMTGEN_COST : Z := TEMPLATE_COST + 8.                (* [comment removed for export] *)
Definition HMT_COST : Z := 2 * BORDER1_COST + FHMTGEN_COST + 16. (* [comment removed for export] *)
Definition FH_FUZZ_NEED : Z := (RASTER_COST + 64) + TEMPLATE_COST + 10 * (HMT_COST + 2) + 16.
Lemma fh_fuzz_need_ok : FH_FUZZ_NEED <= FUZZ_COST.
Proof. unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST. lia. Qed.

Section FhIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record fh_gaps : Prop := mkFhGaps {
  fh_strcmp : strcmp_icontract RT                                                         (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition new_pix1 (Σ Σ' : rts RT) (m' : mem) (r w h : Z) (v : pixv) (cv : cmapv) : Prop :=
  r = 0 \/ (pix_obj (rt_live RT Σ') m' r v cv /\ p_w v = w /\ p_h v = h /\ p_d v = 1 /\ p_data v <> 0).
Definition new_pix1_live (Σ Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv) : Prop :=
  (r = 0 -> rt_live RT Σ' = rt_live RT Σ)
  /\ (r <> 0 -> live_destroy r v cv (rt_live RT Σ') = rt_live RT Σ)
  /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4.

(* [comment removed for export] *)
Definition pixRasterop_clr1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd : Z) (vd : pixv) (cvd : cmapv) (dx dy dw dh : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 dx -> a2 = Z_to_bv 64 dy -> a3 = Z_to_bv 64 dw -> a4 = Z_to_bv 64 dh -> a5 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> p_d vd = 1 -> p_data vd <> 0 -> rect_in dx dy dw dh (p_w vd) (p_h vd) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRasterop_src1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (dx dy dw dh sx sy : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 dx -> a2 = Z_to_bv 64 dy -> a3 = Z_to_bv 64 dw -> a4 = Z_to_bv 64 dh -> a5 = Z_to_bv 64 12 ->
  a6 = Z_to_bv 64 pixs -> a7 = Z_to_bv 64 sx -> rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> p_d vd = 1 -> p_data vd <> 0 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 -> pixd <> pixs -> p_data vd <> p_data vs ->
  rect_in dx dy dw dh (p_w vd) (p_h vd) -> rect_in sx sy dw dh (p_w vs) (p_h vs) -> dx mod 32 = 0 -> sx mod 32 = 0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition addborder1_args (entry : Z) (a1 a2 a3 a4 a5 : word) : Prop :=
  (entry = e_pixAddBorderGeneral /\ a1 = Z_to_bv 64 32 /\ a2 = Z_to_bv 64 32 /\ a3 = Z_to_bv 64 32 /\ a4 = Z_to_bv 64 32 /\ a5 = Z_to_bv 64 0)
  \/ (entry = e_pixAddBorder /\ a1 = Z_to_bv 64 32 /\ a2 = Z_to_bv 64 0).
Definition pixAddBorder1_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> addborder1_args entry a1 a2 a3 a4 a5 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 ->
  (p_cmap vs <> 0 -> uctx m sp s0 ras /\ In (RA_CMAPCOPY_CALLOC1 :: 0x96f08 :: bv_unsigned ra :: ras) CLIENT_TRACES) ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER1_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix1 Σ Σ' m' r (p_w vs + 64) (p_h vs + 64) v cv) c
       /\ new_pix1_live Σ Σ' r v cv
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER1_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition rmborder1_args (entry : Z) (a1 a2 a3 a4 : word) : Prop :=
  (entry = e_pixRemoveBorderGeneral /\ a1 = Z_to_bv 64 32 /\ a2 = Z_to_bv 64 32 /\ a3 = Z_to_bv 64 32 /\ a4 = Z_to_bv 64 32)
  \/ (entry = e_pixRemoveBorder /\ a1 = Z_to_bv 64 32).
Definition pixRemoveBorder1_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> rmborder1_args entry a1 a2 a3 a4 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 -> 64 < p_w vs -> 64 < p_h vs ->
  (p_cmap vs <> 0 -> uctx m sp s0 ras /\ In (RA_CMAPCOPY_CALLOC1 :: 0x974f0 :: bv_unsigned ra :: ras) CLIENT_TRACES) ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER1_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix1 Σ Σ' m' r (p_w vs - 64) (p_h vs - 64) v cv) c
       /\ new_pix1_live Σ Σ' r v cv
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER1_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fhmtgen_low_1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (rd rs w h wpl index : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 (rd + 4 * (32 * wpl + 1)) -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 h -> a3 = Z_to_bv 64 wpl ->
  a4 = Z_to_bv 64 (rs + 4 * (32 * wpl + 1)) -> a5 = Z_to_bv 64 wpl -> a6 = Z_to_bv 64 index -> 0 <= index < 10 ->
  0 < w -> 0 < h -> w + 64 <= 20000 -> h + 64 <= 20000 -> wpl = (w + 64 + 31) / 32 ->
  chunk (rt_live RT Σ) rd (4 * (wpl * (h + 64))) -> chunk (rt_live RT Σ) rs (4 * (wpl * (h + 64))) -> rd <> rs ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fhmtgen_low_1 m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(rd, rd + 4 * (wpl * (h + 64)))] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition hm_name_arg (Σ : rts RT) (m : mem) (name : Z) (i : nat) : Prop :=
  (i < 10)%nat /\ In (name, 8) (rt_live RT Σ) /\ bytes_at asegs m name (hm_name i).

(* [comment removed for export] *)
Definition pixFHMTGen_1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs name : Z) (vs : pixv) (cvs : cmapv) (i : nat),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 name ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 -> 64 < p_w vs -> 64 < p_h vs -> hm_name_arg Σ m name i ->
  LIB_SEL m -> lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 FHMTGEN_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixFHMTGen_1 m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ p_d vd = 1 /\ p_data vd <> 0) c
       /\ live_destroy pixd vd cvd (rt_live RT Σ') = rt_live RT Σ
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - FHMTGEN_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition fh_null_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (entry = e_pixFHMTGen_1 -> a0 = Z_to_bv 64 0 /\ a1 = Z_to_bv 64 0) -> (entry = e_pixRemoveBorder -> a0 = Z_to_bv 64 0) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 2 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixHMTDwa_1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs name : Z) (vs : pixv) (cvs : cmapv) (i : nat) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 name ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 -> hm_name_arg Σ m name i ->
  uctx m sp s0 ras -> bv_unsigned ra = 0x9110c -> ras = [RA_TOP] ->
  LIB_SEL m -> lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 5 12 HMT_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixHMTDwa_1 m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix1 Σ Σ' m' r (p_w vs) (p_h vs) v cv) c
       /\ new_pix1_live Σ Σ' r v cv
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - HMT_COST <= rt_credit RT Σ').

End FhIface.
