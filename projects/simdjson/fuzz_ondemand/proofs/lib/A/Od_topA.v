(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_loopA Od_hkit0A Od_deldtorA Od_beginA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (oa_F E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 96)) (Z_to_bv 64 (oa_F E + 192))
           (Z_to_bv 64 (o_COPY E)) xs8 (Z_to_bv 64 (o_BUF E)) xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 OD_ITER) xfc None m (seg_rom asegs)).

Definition od_begin_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    (HLASTP E -> od_head_k E Q od_init) ->
    evt asegs Q (ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Section Top.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.

Record od_outer (Σ : rts RT) (E : oaenv) (A cap size IA OC : Z) (els : list (Z * Z)) (L0 : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (m0 : mem) (mL : mem) : Prop := mkOdOuter {
  out_hi : exists j352 j400, rw_cells asegs mL (oa_S1 E + 352) [CB 48 j352; CB 8 j400];
  out_pad : stk asegs mL (oa_S1 E + 408) (oa_USP E - 104);
  out_saved : rw_cells asegs mL (oa_USP E - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
  out_hdr : exists h0, rw_cells asegs mL (oa_F E) [CB 8 h0];
  out_vec : vrepA mL (oa_F E + 32) A cap size els;
  out_cap : 1 <= cap /\ 1 <= size;
  out_wrs : wr_at asegs mL (oa_F E / 8 + 2147450880) 64;
  out_shv : rw_cells asegs mL (oa_F E / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 0) 3));
  out_shp : rw_cells asegs mL (oa_F E / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 0) 7));
  out_shd : rw_cells asegs mL (oa_F E / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 0) 8));
  out_dl : exists pre8 mid rest, length pre8 = 8%nat /\ length mid = 32%nat /\ length rest = 24%nat
             /\ cells_bytes (dl_cells (o_vptr E) pre8 (Z_to_bv 64 (o_IDX E)) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest) = cells_bytes (dpi_cells E);
  out_live : rt_live RT Σ = (IA, 1024) :: (OC, 8192) :: (o_IDX E, 4 * Z.of_nat (o_icap E)) :: (o_IMPL E, 96) :: (o_SB E, o_CAP E)
                            :: (o_COPY E, o_BUF E - o_COPY E + o_len E + 64) :: vblockA A cap size ++ L0;
  out_lpos : forall p n, In (p, n) L0 -> 0 < n;
  out_lib : LIB mL;
  out_pres : rt_pres_fp L0 [] (oa_USP E) LIB_FP m0 mL
}.

Lemma od_outer_rebase : forall Σ Σ' E m A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mL,
  od_outer Σ E A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mL -> rt_live RT Σ' = rt_live RT Σ ->
  od_outer Σ' (oa_rebase E m) A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mL.
Proof using.
  intros until mL. intros [? ? ? ? ? ? ? ? ? ? ? LV ? ? ?] EL. constructor; try assumption. rewrite EL. exact LV.
Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition od_fin_k (K : config -> Prop) (Σ0 : rts RT) (usp lo : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (cb : Z) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
    ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo usp ->
    rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m' -> LIB m' ->
    rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ' ->
    aevt Σ' K (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x6488f0) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom asegs)).

Definition od_exitp_stmt : Prop :=
  forall (Σ0 Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL m0 : mem) (A cap size IA OC : Z) (els L0 : list (Z * Z))
         (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (cb : Z)
         st vs6 v224 v248 v304 v312 v328 v344
         xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_geo E -> od_rt RT Σ E mL ->
    od_outer Σ E A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mL ->
    L0 = rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ ->
    frm0 xfc -> ODINVg E vs6 v224 v248 v304 v312 v328 v344 st m1 ->
    od_fin_k K Σ0 (oa_USP E) (o_lo E) cra (o_gp E) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
    aevt Σ K (ODXST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_setup_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x6488f0 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->

  (forall (Σ1 : rts RT) (E : oaenv) (A cap size IA OC : Z) (els : list (Z * Z))
          xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
     od_geo E -> od_rt RT Σ1 E m1 -> OD_PRE E m1 -> o_m0 E = m1 ->
     od_outer Σ1 E A cap size IA OC els (rt_live RT Σ) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 ->
     oa_USP E = bv_unsigned sp -> o_lo E = lo -> o_gp E = gp ->
     rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
     rt_credit RT Σ - FUZZ_COST + OD_DBL_CREDIT * (o_n E + 2) <= rt_credit RT Σ1 ->
     frm0 xfc ->
     aevt Σ1 K (ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1)) ->

  od_fin_k K Σ (bv_unsigned sp) lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST) ->
  aevt Σ K (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m).

End WithPM.

Hypothesis HEAD : forall E, od_oka E -> HLASTP E -> od_head_stmt E.
Hypothesis HEXIT : forall E, od_oka E -> od_head_exit_stmt E.
Hypothesis PLUS : forall E, od_oka E -> HLASTP E -> od_plus_stmt E.
Hypothesis BEGIN : forall E, od_oka E -> od_begin_stmt E.
Hypothesis DBL : forall PMc, fdfs_only PMc -> mat_stable PMc -> arm_dbl_cps RT PMc.
Hypothesis SETUP : forall PMc, od_setup_stmt PMc.
Hypothesis EXITP : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_exitp_stmt PMc.

Theorem fuzz_one_odA : fuzz_one_cps RT LIB.
Proof using AF HEAD HEXIT PLUS BEGIN DBL SETUP EXITP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  match goal with |- cps asegs _ ?K0 => set (K := K0) end.

  assert (KFIN : od_fin_k PMc K Σ usp lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST)).
  { unfold od_fin_k. intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' PR' LIB' LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'. subst tp.
      split; [rewrite ESP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| exact LIB'].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (SETUP PMc Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
           FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM); [| exact KFIN].

  intros Σ1 E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
    G R PRE EM0 OUT EUSP ELO EGP SP1 CR1 FRM1.
  pose proof (od_oka_of_rt RT AF Σ1 E m1 G R) as OK.
  pose proof (od_n_range E (og_s1 _ G)) as NR.
  assert (KFIN1 : od_fin_k PMc K Σ (oa_USP E) (o_lo E) ra (o_gp E) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST))
    by (rewrite EUSP, ELO, EGP; exact KFIN).

  assert (KX : forall c, rt_credit RT Σ - FUZZ_COST <= c -> od_exit_kc RT PMc Σ1 K E m1 c).
  { intros c Hc. unfold od_exit_kc.
    intros Σ' m0' st vs6 v224 v248 v304 v312 v328 v344 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 yF yfc m2
      R' LV' FRS' SP' CR' FRM' INV'.
    exact (EXITP PMc FDO MST Σ Σ' K (oa_rebase E m0') m1 m A cap size IA OC els (rt_live RT Σ) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (rt_credit RT Σ - FUZZ_COST) st vs6 v224 v248 v304 v312 v328 v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yF yfc m2
             (od_geo_rebase E m0' G) R' (od_outer_rebase Σ1 Σ' E m0' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OUT LV') eq_refl
             ltac:(rewrite SP'; exact SP1) ltac:(lia) FRM' INV' KFIN1). }
  apply (aevt_evt RT AF PMc MST).
  apply (BEGIN E OK (fun ms => aevt RT PMc Σ1 K ms) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc m1 PRE FRM1 EM0).
  -
    apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
    apply KX. lia.
  -
    intros HL. unfold od_head_k. intros st v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 PRE2 FRM2 INV2.
    apply evt_done.
    destruct PRE2 as [NX|DEAD].
    + apply (od_loopA RT AF PMc MST HEAD HEXIT PLUS (DBL PMc FDO MST) (Z.to_nat (o_n E + 1)) Σ1 K E m1 od_init st v344
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m2 G R HL);
        [ destruct NX as ((A1 & A2) & _); unfold o_left, od_init in *; cbn [o_pos] in A1; rewrite Z2Nat.id by lia; lia
        | rewrite Z2Nat.id by lia; unfold OD_DBL_CREDIT in *; lia | left; exact NX | exact FRM2 | exact INV2 | ].
      apply KX. rewrite Z2Nat.id by lia. unfold OD_DBL_CREDIT in *. lia.
    + apply (aevt_evt RT AF PMc MST).
      apply (HEXIT E OK (fun ms => aevt RT PMc Σ1 K ms) st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m2);
        [destruct DEAD as (_ & DD & _); lia| exact FRM2| exact INV2|].
      apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
      apply KX. lia.
Qed.

End Top.
