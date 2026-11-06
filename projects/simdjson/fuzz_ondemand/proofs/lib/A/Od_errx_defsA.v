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
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_hkit0A Od_deldtorA Od_beginA Od_topA Od_setup_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition od_parserX (IMPL SB : Z) (jp jq : list byte) : list cell := [CB 8 jp; C8 (wz IMPL); CB 32 jq; C8 (wz SB)].

Section ErrxDefs.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition od_errx_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 Σx : rts RT) (m0 mx : mem) (usp S1 F lo A cap size : Z) (els : list (Z * Z))
         (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
         (COPY NCOPY SB CAP IMPL IDX NIDX OC IA act err cb : Z) (LC : list (Z * Z))
         (j0 j192 j224 j248 jp jq pre8 mid rest : list byte)
         (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) xF xfc,
    od_cut0 RT LIB Σ0 Σx m0 mx usp S1 F lo A cap size els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    ((LC = [(COPY, NCOPY)] /\ 0 < COPY /\ 0 < NCOPY) \/ (LC = [] /\ COPY = 0)) ->
    rt_live RT Σx = (IA, 1024) :: (OC, 8192) :: (IDX, NIDX) :: (IMPL, 96) :: (SB, CAP) :: LC ++ vblockA A cap size ++ rt_live RT Σ0 ->
    0 < NIDX -> 0 < CAP -> IMPL mod 8 = 0 ->
    rw_cells asegs mx S1 (od_lowB F act j0 j192 j224 j248) ->
    rw_cells asegs mx (F + 96) (od_parserX IMPL SB jp jq) ->
    rw_cells asegs mx (F / 8 + 2147450880) (od_shadow 0 0) ->
    rw_cells asegs mx IMPL (dl_cells (wz OD_DPI_VPTR) pre8 (wz IDX) mid (wz OC) (wz IA) rest) ->
    0 < err < 2^31 -> cb <= rt_credit RT Σx -> frm0 xfc ->
    od_fin_k RT LIB PMc K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
    aevt Σx K (MS (mkR xra (wz S1) gp (wz 0x6488f0) xt0 xt1 xt2 (wz usp) (wz S1)
                       (wz err) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (wz F) (wz 2147450880) (wz (F + 32)) (wz (F + 96)) (wz (F + 192)) (wz COPY) xs8 xs9 xs10 xs11
                       xt3 xt4 xt5 xt6)
                  xF (wz OD_ERRX) xfc None mx (seg_rom asegs)).

End ErrxDefs.
