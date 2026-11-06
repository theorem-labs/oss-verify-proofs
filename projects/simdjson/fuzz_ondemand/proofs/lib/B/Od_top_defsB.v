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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_hkit0A Od_deldtorA Od_beginB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 (Z_to_bv 64 (oa_F E + 104)) (Z_to_bv 64 (o_BUF E)) xs6 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 228)) xs9
           (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 OD_ITER) xfc None m (seg_rom bsegs)).

Definition od_begin_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    (HLASTP E -> od_head_k E Q od_init) ->
    evt bsegs Q (ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1).

Section Top.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.

Record od_outer (Σ : rts RT) (E : oaenv) (A cap size IA OC : Z) (els : list (Z * Z)) (L0 : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (m0 : mem) (mL : mem) : Prop := mkOdOuter {
  out_lo0 : wr_at bsegs mL (oa_S1 E) 8;
  out_hi : exists j384 j432, rw_cells bsegs mL (oa_S1 E + 384) [CB 48 j384; CB 8 j432];
  out_pad : stk bsegs mL (oa_S1 E + 440) (oa_USP E - 104);
  out_saved : rw_cells bsegs mL (oa_USP E - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
  out_hdr : exists h0, rw_cells bsegs mL (oa_F E) [CB 8 h0];
  out_vec : vrepA mL (oa_F E + 32) A cap size els;
  out_cap : 1 <= cap /\ 1 <= size;
  out_wrs : wr_at bsegs mL (oa_F E / 8 + 2147450880) 64;
  out_shv : rw_cells bsegs mL (oa_F E / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 0) 3));
  out_shp : rw_cells bsegs mL (oa_F E / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 0) 7));
  out_shd : rw_cells bsegs mL (oa_F E / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 0) 8));
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
  intros until mL. intros [? ? ? ? ? ? ? ? ? ? ? ? LV ? ? ?] EL. constructor; try assumption. rewrite EL. exact LV.
Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition od_fin_k (K : config -> Prop) (Σ0 : rts RT) (usp lo : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (cb : Z) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
    ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo usp ->
    rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m' -> LIB m' ->
    rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ' ->
    aevt Σ' K (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x656e70) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Definition od_exitp_stmt : Prop :=
  forall (Σ0 Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL m0 : mem) (A cap size IA OC : Z) (els L0 : list (Z * Z))
         (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (cb : Z)
         st vs v88 v144 v152 v240 v312 v336 v352
         xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_geo E -> od_rt RT Σ E mL ->
    od_outer Σ E A cap size IA OC els L0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 mL ->
    L0 = rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb <= rt_credit RT Σ ->
    frm0 xfc -> ODINVg E vs v88 v144 v152 v240 v312 v336 v352 st m1 ->
    od_fin_k K Σ0 (oa_USP E) (o_lo E) cra (o_gp E) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
    aevt Σ K (ODXST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_setup_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x656e70 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->

  (forall (Σ1 : rts RT) (E : oaenv) (A cap size IA OC : Z) (els : list (Z * Z))
          xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1,
     od_geo E -> od_rt RT Σ1 E m1 -> OD_PRE E m1 -> o_m0 E = m1 ->
     od_outer Σ1 E A cap size IA OC els (rt_live RT Σ) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 ->
     oa_USP E = bv_unsigned sp -> o_lo E = lo -> o_gp E = gp ->
     rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
     rt_credit RT Σ - FUZZ_COST + OD_DBL_CREDIT * (o_n E + 2) <= rt_credit RT Σ1 ->
     frm0 xfc ->
     aevt Σ1 K (ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1)) ->

  od_fin_k K Σ (bv_unsigned sp) lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST) ->
  aevt Σ K (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m).

End WithPM.

End Top.
