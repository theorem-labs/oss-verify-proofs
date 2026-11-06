(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Pm_iface4 () := "C69OSSVerify5KrLib2K53A23:Lept_iface:pix_hdr_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53A23:Lept_iface3p_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5p_wplC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib2K53A239Pm_iface4;hdr_args_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hdr_args_ok (w h d : Z) : Prop :=
  In d [1; 2; 4; 8; 16; 24; 32] /\ 0 < w <= 20000 /\ 0 < h <= 20000 /\ 0 < 4 * ((w * d + 31) / 32 * h) <= 0x4000000.
Lemma hdr_args_of_pix : forall v, pix_hdr_ok v -> hdr_args_ok (p_w v) (p_h v) (p_d v).
Proof.
ltac2:(KReplay.run1 (kr_t_Pm_iface4 ()) [] "h01Hh13HRSh22HDh32HHh42HWh54HWPLh61vh71zp;1p;3p;2p;6p;4g0000j1NTg0011j14Tg001kj17Tg002Ij12Tg002nj1:Tg003Sj1MTg0043j3CTg004Jj13Tg005Dj11Tg006>j16Tg007:j2?Tg007Vj3@Tg008Wj6KTg0093j2>Tg009PR0j2=Tg009kj4BTg00:Fj3JTg00:fj2ETg00;Bj2DTg00;_j2GTg00<<j3ITf0R1#2#2p=Hg00<VR2f1R3;J1p=;%21#2#2#2p=<g00=4R4f2R5'E1?31'=p=0f4R6f3R7/>5/D3/G15I2p=91>31,>5p=51E41p=A1=31,=5p=8%41,>3p=L1D53/G1p=Fg00=R%N1P0%43R4g00>OR8#7%28R9#7%29R9#7R:%29R;#7%2;R;#7%:8R8#2#H#7%2;R;#7R<%M2';';';';';';';R=5C2%33R>%:9#:#:#2#H#:#2#<#7R970>%13R??0?9%63R@P>P4%:8#:#:#7R8P<D9A5:@?R@#A%2;#<#<#<#<#<#7R;,?@3838%35%15%453@P1%47=C2=%36R7?079%16R5?059%66R@P7%46P8P<D9A5:@5R@#A1?@;3838P0f5R@#3R5?059%1@R6?069%6@R7P5%4@P8P<D9A5:76R7?07;38f6R7#3%17%473@P1f7#3R6?069f8R6#1R@?0@9%66R5%36%46P8P<D9A5:5@R5?05;38P0f9R5#1R@?0@9%65R6%35%45P8P<D9A5:6@R6#A1?6;38f:R6#3%16%463@P1f;#1R@?0@9f<R@#6R5%3@%4@P8P<D9%1@95:5R5#A1?5;38P0f=R0#6R5%30%40P8P<D9%1095:5R5?05;f>R5#3%15%453@P1f?R0#6%30%40P8P<D9f@R0#6%1055:R0?00;P2fAR0#6fBR@#1R?95:1R4?04;X72P1%30/L0?F8<R4P3EK%1095:4R4?04;%4@R4=C2=%3@R@?0@9R=A0??9R91>@4?F8<=5:?R??0?;R?'=R;'=P5P=P;P6P9P?P7P1CBCBCBb1W1W5P3P1O2n2001000000121000000W0W3P3P1O2n2001000000121000000W0W4P3P1O2n2001000000121000000W0W2P3P1O2n2001000000121000000W0W6o"). Qed.

Section PmIface4.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixCreateHeader_nn_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateNoInit_nn_cps (entry msite : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  uctx m sp s0 ras -> In (msite :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreateTemplateNoInit_nn_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 3 4 (RASTER_COST + 32) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 32) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCopy_nn_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv -> p_data v <> 0 ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

End PmIface4.
