(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_hkit0A Od_beginB Od_top_defsB Od_setup_defsB Od_setup_defs2B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section HandDefs.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition od_handover_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 ΣC : rts RT) (m0 mC : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size COPY BUF SB IMPL IDX OC IA : Z) (out : list Z)
         (els : list (Z * Z)) (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 : word) xF xfc,
    od_cutC RT LIB Σ0 ΣC m0 mC usp S1 F lo dz A cap size COPY BUF SB IMPL IDX OC IA 0 out els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    frm0 xfc ->
    od_iter_k RT LIB PMc K Σ0 m0 usp lo gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    aevt ΣC K (MS (mkR xra (wz S1) gp (wz 0x656e70) xt0 xt1 xt2 (wz usp) (wz S1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 (wz (F + 104)) (wz BUF) xs6 (wz 2147450880) (wz (F + 228)) xs9 (wz (F + 32)) (wz (F + 192)) xt3 xt4 xt5 xt6)
                  xF (wz OD_ITER) xfc None mC (seg_rom bsegs)).

End HandDefs.
