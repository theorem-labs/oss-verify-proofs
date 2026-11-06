(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1480 of its 1576 lines of code are new or changed and 830 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/take_seg_kit.v; 233 of its 358 lines of code are new or changed and 1451 lines of the source are left out. *)
(* take_seg_join: the end of a turn of take's loop, transport/src/diginet_session.c:377 (tkw_join): the next turn,
   the tail loop, or the return. Part of the walk of lib/A/Prog/take_cgW.v; the shared section header and helpers
   are lib/A/Prog/take_seg_kit.v. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YK1b YG0s YA0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts AsanKAProof TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg DgnTransportCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGRwA TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import take_seg_model take_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TFE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportFevt.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module FCs := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import take_seg_kit take_seg_exit.
Module TKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_kit.
Module TKX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_exit.
Set Default Proof Using "All".

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation ajx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation ajd := (@ajournal rc tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HTC : trans_take_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B G.
Hypothesis HGN : gx_noerrno B G.
Hypothesis AIM : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis ABC : forall fx' : YK11.FPState,
  @transport_diginet_body_check_cg fx' rc B MT (transport_sigma TS_diginet_body_check).

(* TransportGCg.v dk_kept_step_g at any world of the walk (the step keeps the current world W2). *)
Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (St : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (bp blp hdp allow len hd taken : Z) (body : list byte) (Bw Bw' : list byte).

Hypothesis HJ : ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 TAKE_S.
Hypothesis H11 : YK11.getr regs 11 = w64 bp.
Hypothesis H12 : YK11.getr regs 12 = w64 blp.
Hypothesis H13 : YK11.getr regs 13 = w64 allow.
Hypothesis H14 : YK11.getr regs 14 = w64 hdp.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - TAKE_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HALW : - 2 ^ 31 <= allow < 2 ^ 31.
Hypothesis HBP0 : 0 < bp.
Hypothesis HFAKE : decode_in_fake lyc Sc bp TAKE_BODY.
Hypothesis HTWB : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) bp TAKE_BODY.
Hypothesis HRDB : decode_rd_ok W memc bp TAKE_BODY.
Hypothesis HOWB : decode_off_win regs TAKE_STK bp TAKE_BODY.
Hypothesis HNGB : forall x, bp <= x < bp + TAKE_BODY -> ~ inG G x.
Hypothesis HBL8 : blp mod 8 = 0.
Hypothesis HTWL : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) blp 8.
Hypothesis HRDL : decode_rd_ok W memc blp 8.
Hypothesis HOWL : decode_off_win regs TAKE_STK blp 8.
Hypothesis HNGL : forall x, blp <= x < blp + 8 -> ~ inG G x.
Hypothesis HHD4 : hdp mod 4 = 0.
Hypothesis HTWH : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) hdp 4.
Hypothesis HRDH : decode_rd_ok W memc hdp 4.
Hypothesis HOWH : decode_off_win regs TAKE_STK hdp 4.
Hypothesis HNGH : forall x, hdp <= x < hdp + 4 -> ~ inG G x.
Hypothesis SEP1 : bp + TAKE_BODY <= blp \/ blp + 8 <= bp.
Hypothesis SEP2 : bp + TAKE_BODY <= hdp \/ hdp + 4 <= bp.
Hypothesis SEP3 : blp + 8 <= hdp \/ hdp + 4 <= blp.
Hypothesis HW : tw_at TMAP_A (aview segs (w_H W) memc) Bw.
Hypothesis HGF : TW.g_fail_next Bw <= 1.
Hypothesis HQL : forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN.
Hypothesis HMC : 1 <= TW.S_cfg_max_cmds Bw.
Hypothesis HMB : 1 <= TW.S_cfg_max_body Bw.
Hypothesis HCNT : count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID.
Hypothesis HNEV : st_nev St + k + TAKE_EV <= EV_MAX.

(* The model's run, as take_seg_model.v tkm_take_m reads it off take_m. *)
Variables (BF : list byte) (keptF : Z).
Hypothesis HLP : TS0.take_loop_m Bw allow 0 0 0 0 0 [] (Z.to_nat (TW.S_queued Bw)) =
  Some (BF, (body, len, hd, taken, keptF)).
Hypothesis HBW' : Bw' = TW.set_S_queued BF keptF.
Hypothesis HFF : tkm_wf BF /\ TW.S_queued BF = TW.S_queued Bw /\ TW.g_fail_next BF = TW.g_fail_next Bw /\
  0 <= taken /\ 0 <= keptF /\ taken + keptF = TW.S_queued Bw /\ 0 <= TW.S_queued Bw <= TW.S_queue_N /\
  0 <= len <= TS0.DIGINET_MAX_BODY_LEN /\ Z.of_nat (length body) = len /\ 0 <= hd < 256 /\
  TW.g_fail_next Bw' = TW.g_fail_next Bw.

Local Abbreviation sp := (spZ regs).
Local Abbreviation SP' := (spZ regs - TK_FRAME).
Local Abbreviation OUTS := [(blp, 8); (hdp, 4)].
Local Abbreviation EW := (take_wr Bw bp blp hdp).
Local Abbreviation GP := (YK11.getr regs (Z_to_bv 5 3)).
Local Abbreviation TP := (YK11.getr regs (Z_to_bv 5 4)).
Local Abbreviation Q := (@transport_take_post fx rc B MT STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc k regs bp blp
  hdp Bw Bw' body len hd taken).

(* The saved s11 .. s0 and ra the prologue stores at sp + 120 .. sp + 216. *)
(* the kit's lemmas at this file's copy of the section's variables *)
Local Notation tk_sv := (@TKK.tk_sv fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_inv := (@TKK.tkw_inv fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_mw := (@TKK.tkw_mw fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_mh := (@TKK.tkw_mh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_next := (@TKK.tkw_next fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_mj := (@TKK.tkw_mj fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_mt := (@TKK.tkw_mt fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_jd := (@TKK.tkw_jd fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_jf := (@TKK.tkw_jf fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_lay := (@TKK.tkw_lay fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_AR0 := (@TKK.tkw_AR0 fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_spf := (@TKK.tkw_spf fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cellf := (@TKK.tkw_cellf fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_inG_gs := (@TKK.tkw_inG_gs fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_G_low := (@TKK.tkw_G_low fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_G_vis := (@TKK.tkw_G_vis fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_outs := (@TKK.tkw_outs fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_EW := (@TKK.tkw_EW fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_rel_awr := (@TKK.tkw_rel_awr fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_twr_cur := (@TKK.tkw_twr_cur fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_win_pres := (@TKK.tkw_win_pres fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_aview_H := (@TKK.tkw_aview_H fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_gover_apresent := (@TKK.tkw_gover_apresent fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_gover_in := (@TKK.tkw_gover_in fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cells_keep := (@TKK.tkw_cells_keep fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_K_step := (@TKK.tkw_K_step fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_fsh := (@TKK.tkw_fsh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_body_sh := (@TKK.tkw_body_sh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cell_ra := (@TKK.tkw_cell_ra fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_rd_cur := (@TKK.tkw_rd_cur fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cell_bc := (@TKK.tkw_cell_bc fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_body_bc := (@TKK.tkw_body_bc fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_frame_bc := (@TKK.tkw_frame_bc fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_K_bc := (@TKK.tkw_K_bc fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_jrun := (@TKK.tkw_jrun fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_run := (@TKK.tkw_run fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_rd_view := (@TKK.tkw_rd_view fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_sh_eq := (@TKK.tkw_sh_eq fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_ovr := (@TKK.tkw_ovr fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_world_raw := (@TKK.tkw_world_raw fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_gs_sh := (@TKK.tkw_gs_sh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_fld := (@TKK.tkw_fld fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_fldv := (@TKK.tkw_fldv fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_shv := (@TKK.tkw_shv fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_rdt := (@TKK.tkw_rdt fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_rdj := (@TKK.tkw_rdj fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_stkf := (@TKK.tkw_stkf fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_hd_sh := (@TKK.tkw_hd_sh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_bl_sh := (@TKK.tkw_bl_sh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cell_rng := (@TKK.tkw_cell_rng fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cell_ge := (@TKK.tkw_cell_ge fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_munch_view := (@TKK.tkw_munch_view fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_pres_grow := (@TKK.tkw_pres_grow fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_swrap32 := (@TKK.tkw_swrap32 fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_pres_ret := (@TKK.tkw_pres_ret fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_twin_G := (@TKK.tkw_twin_G fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_fr_size := (@TKK.tkw_fr_size fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_q_sh := (@TKK.tkw_q_sh fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_inv_step := (@TKK.tkw_inv_step fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_inv_mu := (@TKK.tkw_inv_mu fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_o16 := (@TKK.tkw_o16 fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_sh_lt := (@TKK.tkw_sh_lt fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_bytes_of := (@TKK.tkw_bytes_of fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cb_of := (@TKK.tkw_cb_of fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_keep_cells := (@TKK.tkw_keep_cells fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_bcr := (@TKK.tkw_bcr fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cpyq := (@TKK.tkw_cpyq fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_splice_len := (@TKK.tkw_splice_len fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_splice_nth := (@TKK.tkw_splice_nth fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_splice_firstn := (@TKK.tkw_splice_firstn fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_splice_firstn_le := (@TKK.tkw_splice_firstn_le fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_cpyb := (@TKK.tkw_cpyb fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_bc := (@TKK.tkw_bc fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_someq := (@TKK.tkw_someq fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_somet := (@TKK.tkw_somet fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_inv_run0 := (@TKK.tkw_inv_run0 fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_head_P := (@TKK.tkw_head_P fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_join_P := (@TKK.tkw_join_P fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_exit := (@TKX.tkw_exit fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_tail := (@TKX.tkw_tail fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).

Lemma tkw_join : forall n, (forall n', n = Datatypes.S n' -> tkw_head_P n') -> tkw_join_P n.
Proof.
  intros n HEAD Wc md m B1 hd1 X j38 i taken1 kept1 len1 body1 ra t2 s0 a0 a1 a2 a3 s2 s10 s11 t3 t4 t5 t6 ms
    EQV INV MJ.
  destruct MJ as ((WF1 & QE & CE & BE & GE) & QL & Hi & Ht & Hk & HTK & HT0 & HL & HBL & HD & HFU & HFX & HNX).
  pose proof INV as (ly2 & Sx & J & HF & HP & HMO & K & HTW & LW & FR & HDC & BLC & LX & GX).
  pose proof HFF as (WFF & QFF & GFF & T0 & K0 & TK & QR & LR & BL & HDR & GF').
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold TW.S_queue_N in QR. unfold TS0.DIGINET_MAX_BODY_LEN in LR.
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  destruct (tkw_stkf _ _ _ _ _ J) as (STKa & STKb & RFR & SP0 & SP63 & SPLO & SPCE).
  destruct (tkw_rdj ly2 Sx Wc m md B1 HAR2 HTW) as [RDJ RGJ].
  pose proof (tkm_field_ranges B1 i) as (QLr & QDr & MCr & MBr & QUr).
  unfold TKK.tkw_next in HNX. unfold tk_at_J in EQV.
  destruct ((taken1 =? TW.S_cfg_max_cmds B1) || (len1 =? TW.S_cfg_max_body B1)) eqn:BRK.
  - (* a counter is full: the break of :377 *)
    assert (HT1 : 1 <= taken1).
    { apply orb_true_iff in BRK. destruct BRK as [Hb|Hb]; apply Z.eqb_eq in Hb.
      - rewrite CE in Hb. lia.
      - destruct (Z.eq_dec taken1 0) as [Ez|Ez]; [|lia]. rewrite (HT0 Ez) in Hb. rewrite BE in Hb. lia. }
    destruct (TS0.take_tail_m B1 kept1 (i + 1) (Z.to_nat (TW.S_queued B1 - (i + 1)))) as [[B2 kept2]|] eqn:ET;
      [|discriminate HNX].
    cbv iota in HNX. destruct (tkw_someq B2 body1 len1 hd1 taken1 kept2 HNX) as (EB & Eb & El & Eh & Et & Ek).
    replace (Z.to_nat (TW.S_queued B1 - (i + 1))) with n in ET by lia.
    eapply (tkw_run Wc _ _ m ms md _ Q EQV).
    { eapply (tk_run_join_break (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (s9v := s2).
      - exact RDJ.
      - exact RGJ.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - apply orb_true_iff in BRK. destruct BRK as [Hb|Hb]; apply Z.eqb_eq in Hb; [left | right]; exact Hb. }
    intros ms1 ms2 md' HP1 HE1 HG1 HS1.
    destruct HP1 as (z0 & z1 & ->).
    pose proof (tkw_inv_run0 Wc m md md' B1 hd1 X (tk_spill bp blp hdp allow j38) INV HS1) as INV'.
    destruct n as [|nt].
    + (* no turn left: the exit *)
      cbn [TS0.take_tail_m] in ET.
      assert (EB1 : B1 = B2)
        by exact (f_equal (fun o => match o with Some (W2, _) => W2 | None => [] end) ET).
      assert (EK1 : kept1 = kept2)
        by exact (f_equal (fun o => match o with Some (_, kq) => kq | None => 0 end) ET).
      eapply (tkw_run Wc _ _ m ms2 md' _ Q HE1).
      { eapply (tk_run_break_exit (LCK.RNG_W (world segs) (@w_H segs) Wc)).
        - exact FR.
        - reflexivity.
        - exact RFR.
        - exact STKa.
        - lia.
        - lia.
        - exact (proj1 (proj2 (proj2 RDJ))).
        - exact (proj2 (proj2 (proj2 (proj2 (proj2 RDJ))))).
        - exact (proj1 (proj2 (proj2 RGJ))).
        - exact (proj2 (proj2 (proj2 (proj2 (proj2 RGJ))))).
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia. }
      intros ms3 ms4 md2 HP3 HE3 HG3 HS3.
      destruct HP3 as (y0 & y1 & y22 & y23 & ->).
      eapply (tkw_exit Wc md2 m X (tk_spill bp blp hdp allow j38)).
      * rewrite EK1, Ek, Et, El in HE3. exact HE3.
      * pose proof (tkw_inv_run0 Wc m md' md2 B1 hd1 X (tk_spill bp blp hdp allow j38) INV' HS3) as IV.
        rewrite EB1, EB, Eh in IV. exact IV.
      * reflexivity.
      * rewrite El, Eb in HFX. exact HFX.
    + (* a turn is left: the tail *)
      eapply (tkw_run Wc _ _ m ms2 md' _ Q HE1).
      { eapply (tk_run_break_tail (LCK.RNG_W (world segs) (@w_H segs) Wc)).
        - exact FR.
        - reflexivity.
        - exact RFR.
        - exact STKa.
        - lia.
        - lia.
        - exact (proj1 (proj2 (proj2 RDJ))).
        - exact (proj2 (proj2 (proj2 (proj2 (proj2 RDJ))))).
        - exact (proj1 (proj2 (proj2 RGJ))).
        - exact (proj2 (proj2 (proj2 (proj2 (proj2 RGJ))))).
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia. }
      intros ms3 ms4 md2 HP3 HE3 HG3 HS3.
      destruct HP3 as (y0 & y1 & y20 & ->).
      eapply (tkw_tail nt Wc md2 m B1 X j38 (i + 1) kept1).
      * rewrite Et, El in HE3. exact HE3.
      * pose proof (tkw_inv_run0 Wc m md' md2 B1 hd1 X (tk_spill bp blp hdp allow j38) INV' HS3) as IV.
        rewrite Eh in IV. exact IV.
      * split; [exact WF1|]. split; [exact QE|]. split; [exact GE|]. split; [lia|]. split; [lia|].
        split; [rewrite El, Eb in HFX; exact HFX|].
        rewrite EB, Ek in ET. exact ET.
  - (* neither counter is full *)
    apply orb_false_iff in BRK. destruct BRK as [BRa BRb].
    apply Z.eqb_neq in BRa. apply Z.eqb_neq in BRb.
    destruct n as [|n'].
    + (* no turn left: the exit *)
      cbn [TS0.take_loop_m] in HNX.
      destruct (tkw_someq B1 body1 len1 hd1 taken1 kept1 HNX) as (EB & Eb & El & Eh & Et & Ek).
      eapply (tkw_run Wc _ _ m ms md _ Q EQV).
      { eapply (tk_run_join_exit (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (s9v := s2).
        - exact RDJ.
        - exact RGJ.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - exact BRa.
        - exact BRb.
        - lia. }
      intros ms1 ms2 md' HP1 HE1 HG1 HS1.
      destruct HP1 as (y0 & y1 & y2 & y7 & y22 & y23 & y24 & ->).
      eapply (tkw_exit Wc md' m X (tk_spill bp blp hdp allow j38)).
      * rewrite Et, El, Ek in HE1. exact HE1.
      * pose proof (tkw_inv_run0 Wc m md md' B1 hd1 X (tk_spill bp blp hdp allow j38) INV HS1) as IV.
        rewrite EB, Eh in IV. exact IV.
      * reflexivity.
      * rewrite El, Eb in HFX. exact HFX.
    + (* the next turn *)
      eapply (tkw_run Wc _ _ m ms md _ Q EQV).
      { eapply (tk_run_join_next (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (s9v := s2).
        - exact RDJ.
        - exact RGJ.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - exact BRa.
        - exact BRb.
        - lia. }
      intros ms1 ms2 md' HP1 HE1 HG1 HS1.
      destruct HP1 as (y0 & y1 & y2 & y7 & ->).
      eapply (HEAD n' eq_refl Wc md' m B1 hd1 X j38 (i + 1) taken1 kept1 len1 body1).
      * exact HE1.
      * exact (tkw_inv_run0 Wc m md md' B1 hd1 X (tk_spill bp blp hdp allow j38) INV HS1).
      * split; [split; [exact WF1|]; split; [exact QE|]; split; [exact CE|]; split; [exact BE | exact GE]|].
        split; [intros jj Hjj; apply QL; lia|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HT0|].
        split; [lia|]. split; [exact HBL|]. split; [lia|]. split; [lia|].
        split; [exact HFX | exact HNX].
Qed.

(* The refusal (:373-375) at turn i: the world after it is tkm_keep B1 kept1 i. *)
End Call.
End Walk.

