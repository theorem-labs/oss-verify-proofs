(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1480 of its 1576 lines of code are new or changed and 830 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/take_seg_kit.v; 277 of its 404 lines of code are new or changed and 1449 lines of the source are left out. *)
(* take_seg_exit: the return of take (tkw_exit: the state at TK_X with the final model world gives the statement's
   post) and the tail loop of transport/src/diginet_session.c:378-380 (tkw_tail, by induction on its fuel). Part of
   the walk of lib/A/Prog/take_cgW.v; the shared section header and helpers are lib/A/Prog/take_seg_kit.v. *)
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

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import take_seg_kit.
Module TKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_kit.
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

Lemma tkw_exit : forall (Wc : world segs) (md : Model) (m : word -> option byte) (X : list byte) (ws : list word)
    (ra0 t2 a0 a1 a2 a3 a4 t0 t1 s0 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (ms : machine_state),
  ms_eqv (MS (mkR ra0 (Z_to_bv 64 SP') GP TP t0 t1 t2 s0 (Z_to_bv 64 TK_QD) a0 a1 a2 a3 a4 (Z_to_bv 64 taken)
               (Z_to_bv 64 len) (Z_to_bv 64 TK_K) s2 s3 s4 (Z_to_bv 64 keptF) s6 s7 s8
               (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
             (@YK11.fp_regs fx) (Z_to_bv 64 TK_X) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  tkw_inv Wc m md BF hd X ws -> nth 5 ws (Z_to_bv 64 0) = Z_to_bv 64 blp -> firstn (Z.to_nat len) X = body ->
  SRr segs Wc (mkCfg ms md) Q.
Proof.
  intros Wc md m X ws ra0 t2 a0 a1 a2 a3 a4 t0 t1 s0 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 ms EQV INV NTH HXB.
  destruct INV as (ly2 & S2 & J & HF & HP & HMO & K & HTW & LW & FR & HDC & (jb & BLC) & LX & GX).
  pose proof HFF as (WFF & QFF & GFF & T0 & K0 & TK & QR & LR & BL & HDR & GF').
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  unfold amem_range in BM, LM, HM. unfold TW.S_queue_N in QR. unfold TS0.DIGINET_MAX_BODY_LEN in LR.
  pose proof (tkw_cell_ge blp 8 HTWL HNGL HRDL ltac:(lia)) as L4096.
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  destruct (tkw_stkf _ _ _ _ _ J) as (STK1 & STK2 & RFR & SP0 & SP63 & SPLO & SPCE).
  destruct (tkw_gs_sh ly2 S2 Wc m md TK_QD HAR2 ltac:(unfold TK_QD, TK_S, TA_g_s; lia)
              ltac:(unfold TK_QD, TK_S, TA_g_s, TW.SZ_g_s; lia)) as [SQD RSQD].
  destruct (tkw_bl_sh ly2 S2 Wc m md J HP K) as [SBL RSBL].
  destruct (tkw_fld Wc m BF 18144 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as (_ & RQD & BQD).
  change (TA_g_s + 18144) with TK_QD in RQD, BQD.
  assert (QDC : rw_cells rsegs m TK_QD [C4 (Z_to_bv 64 (TW.u_at BF (TW.OFF_g_s + 18144) 4))]).
  { split.
    - split; [cbn; repeat split; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r, TWL.le4_put. exact BQD.
    - split; [unfold TK_QD, TK_S, TA_g_s; lia|]. split; [unfold TK_QD, TK_S, TA_g_s; cbn [cells_size csize]; lia|].
      intros i Hi. cbn [cells_size csize] in Hi.
      exact (gx_rw_writable segs G (TK_QD + i) G_HARNESS_rw
               ltac:(apply tkw_inG_gs; unfold TK_QD, TK_S in *; lia) m). }
  pose proof (tkw_cell_rng blp 8 ly2 S2 Wc m md HTWL HNGL HRDL J HP) as RBL.
  assert (GRET : ret_pc (YK11.getr regs (Z_to_bv 5 1)) = YK11.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (SEPQ : TK_QD + 4 <= SP' \/ SP' + TK_FRAME <= TK_QD) by (left; unfold TK_QD, TK_S, TA_g_s; lia).
  assert (SEPB : blp + 8 <= SP' \/ SP' + TK_FRAME <= blp) by lia.
  assert (SEPBQ : blp + 8 <= TK_QD \/ TK_QD + 4 <= blp).
  { destruct (Z_le_gt_dec (blp + 8) TK_QD) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec (TK_QD + 4) blp) as [Hr|Hr]; [right; exact Hr|]. exfalso.
    apply (HNGL (Z.max blp TK_QD) ltac:(lia)). apply tkw_inG_gs. unfold TK_QD, TK_S in *. lia. }
  assert (SEPSQ : tk_sh blp + 1 <= TK_QD \/ TK_QD + 4 <= tk_sh blp).
  { right. unfold tk_sh, TK_K, FCs.ASAN_K, TK_QD, TK_S, TA_g_s. pose proof (Z.div_pos blp 8 ltac:(lia) ltac:(lia)).
    lia. }
  unfold TKK.tk_sv in FR.
  eapply (tkw_run Wc _ _ m ms md _ Q EQV).
  - eapply (tk_run_exit (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (lo := sp - TAKE_STK) (kbl := 0);
      [ exact FR | exact LW | exact NTH | exact RFR | exact STK1 | lia | lia | exact SQD | exact SBL
      | exact RSQD | exact RSBL | exact RQD | exact RBL | exact QDC | exists jb; exact BLC
      | exact SEPQ | exact SEPB | exact SEPBQ | exact SEPSQ | reflexivity | exact HBL8 | lia | lia
      | lia | lia | lia ].
  - intros ms1 ms2 md' HP1 HE1 HG1 HS1.
    destruct HP1 as (m1 & spx & r1 & r2 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 &
                     -> & Hspx & MU & WM & ST & RQ1 & RB1).
    cbn [ms_mem] in HG1.
    destruct (TFE.decode_eqv_mkst _ _ _ _ HE1) as (R2 & -> & HX2).
    assert (MUo : forall a, 0 <= a < 2 ^ 64 -> ~ (TK_QD <= a < TK_QD + 4) -> ~ (blp <= a < blp + 8) ->
                  m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha Hq Hb. apply MU. rewrite unsigned_lit by lia. cbn [outside]. tauto. }
    apply SRr_ret. unfold transport_take_post, transport_cg_post_out.
    exists ly2, S2, R2, m1, md', 0.
    split; [rewrite GRET; reflexivity|].
    split; [unfold TAKE_EV; lia|].
    split.
    { rewrite Z.add_0_r.
      apply (tkw_jrun ly2 S2 Wc m md m1 md' (fun a => (TK_QD <= a < TK_QD + 4) \/ (blp <= a < blp + 8)) J HP).
      - intros x Hx. apply MU. cbn [outside]. tauto.
      - exact HG1.
      - exact HS1.
      - intros a [Ha | Ha]; [right; right; apply tkw_inG_gs; unfold TK_QD, TK_S in Ha; lia|].
        right; left; apply tkw_outs; left; exact Ha. }
    split; [exact (tkw_pres_ret R2 spx _ _ x5 x6 x7 _ r1 r2 x13 x14 x15 x16 x17 x28 x29 x30 x31 HX2 ltac:(lia)
                     eq_refl eq_refl)|].
    split; [exact HF|].
    split; [exact HP|].
    split.
    { apply (tkw_K_step Wc m m1 K).
      - intros a Ha Hw He. apply tkw_aview_raw. apply MUo; [exact Ha | |].
        + intros Hq. apply He. right; left. unfold twa_fld, TW.A_S_queued, TW.OFF_g_s, TK_QD, TK_S in *. lia.
        + intros Hb. apply He. right; right; right; left. exact Hb.
      - intros a Hp. exact (tkw_pres_grow _ m m1 a HG1 Hp). }
    split; [exact HMO|].
    split; [rewrite (TFE.decode_getr_xeqv _ _ HX2); rewrite tkw_swrap32 by lia; reflexivity|].
    split.
    { rewrite HBW'. unfold TW.set_S_queued, TW.A_S_queued.
      apply (tw_write TMAP_A (aview segs (w_H Wc) m) (aview segs (w_H Wc) m1) BF TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4
               keptF TMAP_A_ok HTW TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      - intros j Hj. change (TA_g_s + 18144) with TK_QD.
        destruct RQ1 as ((_ & BQ1) & _). cbn [cells_bytes cbytes] in BQ1. rewrite app_nil_r, TWL.le4_put in BQ1.
        destruct BQ1 as (_ & _ & BQ1). specialize (BQ1 j ltac:(rewrite TWL.length_put; lia)).
        rewrite decode_aview_mrd by (apply tkw_G_vis; apply tkw_inG_gs; unfold TK_QD, TK_S in *; lia).
        rewrite BQ1. rewrite (nth_error_nth' (TW.put 4 keptF) (Z_to_bv 8 0)) by (rewrite TWL.length_put; lia).
        cbn [option_map]. f_equal. apply tw_le_byte_put. lia.
      - intros x Hx Hn. apply tkw_aview_raw. pose proof (TMAP_A_hull x Hx) as Hh.
        unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
        apply MUo; [lia | change (TA_g_s + 18144) with TK_QD in Hn; lia |].
        intros Hb. exact (HNGL x Hb (tkw_twin_G x Hx)). }
    split; [rewrite GF'; exact HGF|].
    split.
    { exists X. split; [exact LX|]. split.
      - apply (tkw_garr8_ext (w_H Wc) (w_H Wc) m m1 bp (TW.zs X)); [|exact GX].
        intros j Hj. unfold TW.zs in Hj. rewrite length_map in Hj. apply tkw_aview_raw. apply MUo; [lia | |].
        + intros Hq. apply (HNGB (bp + Z.of_nat j) ltac:(unfold TAKE_BODY; lia)). apply tkw_inG_gs.
          unfold TK_QD, TK_S in Hq. lia.
        + unfold TAKE_BODY in SEP1. lia.
      - rewrite HXB. symmetry. apply firstn_all2. lia. }
    split.
    { destruct RB1 as ((_ & BB1) & _). cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r, TWL.le8_put in BB1.
      apply (TFE.decode_bytes_garr8 (w_H Wc) m1 blp (TW.put 8 len)); [|exact BB1].
      intros j Hj. rewrite TWL.length_put in Hj.
      exact (proj1 (proj1 (proj2 (tkw_twr_cur blp 8 ly2 S2 Wc m md (blp + Z.of_nat j) HTWL HNGL ltac:(lia) J HP)))). }
    { destruct HDC as ((_ & BH1) & _). cbn [cells_bytes cbytes] in BH1. rewrite app_nil_r, TWL.le4_put in BH1.
      apply (TFE.decode_bytes_garr8 (w_H Wc) m1 hdp (TW.put 4 hd)).
      - intros j Hj. rewrite TWL.length_put in Hj.
        exact (proj1 (proj1 (proj2 (tkw_twr_cur hdp 4 ly2 S2 Wc m md (hdp + Z.of_nat j) HTWH HNGH ltac:(lia) J HP)))).
      - apply (TFE.decode_bytes_at_eq m m1 hdp _ BH1). intros i Hi. rewrite TWL.length_put in Hi.
        apply MUo; [lia | | lia].
        intros Hq. apply (HNGH (hdp + Z.of_nat i) ltac:(lia)). apply tkw_inG_gs. unfold TK_QD, TK_S in Hq. lia. }
Qed.

(* The tail loop (:378-380) at turn j with S nt turns left. *)
Lemma tkw_tail : forall (nt : nat) (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte)
    (X : list byte) (j38 : word) (j kept1 : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 : word) (ms : machine_state),
  ms_eqv (tk_at_TL ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 GP TP (@YK11.fp_regs fx)
            (@YK11.fp_csr fx) m SP' j taken kept1 len) ms ->
  tkw_inv Wc m md B1 hd X (tk_spill bp blp hdp allow j38) -> tkw_mt (Datatypes.S nt) B1 j kept1 X ->
  SRr segs Wc (mkCfg ms md) Q.
Proof.
  intros nt. pattern nt. apply (well_founded_ind PeanoNat.Nat.lt_wf_0). clear nt. intros nt IH.
  intros Wc md m B1 X j38 j kept1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 ms EQV INV HMT.
  pose proof HFF as (WFF & QFF & GFF & T0 & K0 & HTK & QR & LR & BL & HDR & GF').
  unfold TW.S_queue_N in QR. unfold TS0.DIGINET_MAX_BODY_LEN in LR.
  destruct HMT as (WF1 & QB1 & GB1 & HK1 & HJN & HXB & HTL).
  assert (Hj : 0 <= j < 512) by lia.
  (* the model: one move, s->queue[kept1] = s->queue[j] *)
  assert (L32 : length (TW.sub B1 (TW.A_S_queue_bytes j) 32) = 32%nat).
  { apply TWL.length_sub; [unfold TW.A_S_queue_bytes, TW.OFF_g_s; lia|].
    pose proof WF1 as W1. unfold tkm_wf in W1. rewrite W1.
    unfold TW.W_LEN, TW.A_S_queue_bytes, TW.OFF_g_s. lia. }
  pose proof (tkm_upd_q_wf B1 _ kept1 WF1 ltac:(unfold TW.S_queue_N; lia) L32) as WF2.
  destruct (tkm_upd_q_fields B1 _ kept1 WF1 ltac:(unfold TW.S_queue_N; lia) L32) as (QB2 & GB2 & _ & _).
  rewrite (tkm_tail_S B1 kept1 j nt ltac:(unfold TW.S_queue_N; lia) ltac:(unfold TW.S_queue_N; lia)) in HTL.
  (* +0x36c .. +0x380: the arguments of the copy, the call *)
  unfold tk_at_TL in EQV.
  eapply (tkw_run Wc _ _ m ms md _ Q EQV).
  { eapply (tk_run_tail_cpy (LCK.RNG_W (world segs) (@w_H segs) Wc)); lia. }
  cbv beta. intros ms1 ms2 md1 -> HE1 _ HS1.
  destruct (TFE.decode_eqv_mkst _ _ _ _ HE1) as (R1 & -> & HX1).
  (* memcpy (&s->queue[kept1], &s->queue[j], 32), returning at TK_R4 *)
  apply (tkw_cpyq Wc md1 m B1 hd X (tk_spill bp blp hdp allow j38) R1 kept1 j TK_R4 Q
           (tkw_inv_run0 Wc m md md1 B1 hd X _ INV HS1)).
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). reflexivity.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). reflexivity.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). reflexivity.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). reflexivity.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). exact HGP.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). exact HTP.
  - rewrite (TFE.decode_getr_xeqv _ _ HX1). reflexivity.
  - unfold TK_R4, TK_AT. rewrite (proj1 tk_addrs). lia.
  - unfold TK_R4, TK_AT. rewrite (proj1 tk_addrs). reflexivity.
  - lia.
  - lia.
  - lia.
  - intros regs2 mem2 md2 INV2 HP2.
    pose proof INV2 as (ly3 & S3 & J3 & _ & _ & _ & _ & HTW3 & _ & FR3 & _ & _ & _ & _).
    destruct (tkw_jf _ _ _ _ _ J3) as (HAR3 & _ & _ & _ & _).
    destruct (tkw_stkf _ _ _ _ _ J3) as (STK3 & _ & RFR3 & SP0 & SP63 & _ & _).
    (* what the return reads: s->queued and its shadow byte *)
    destruct (tkw_gs_sh ly3 S3 Wc mem2 md2 TK_QD HAR3 ltac:(unfold TK_QD, TK_S, TA_g_s; lia)
                ltac:(unfold TK_QD, TK_S, TA_g_s, TW.SZ_g_s; lia)) as [SQD RSQD].
    destruct (tkw_fld Wc mem2 _ 18144 4 HTW3 ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as (RQD & GQD & _).
    change (TA_g_s + 18144) with TK_QD in RQD, GQD.
    assert (QU : TW.u_at (TW.upd B1 (TW.A_S_queue_bytes kept1) (TW.sub B1 (TW.A_S_queue_bytes j) 32))
                   (TW.OFF_g_s + 18144) 4 = TW.S_queued Bw) by exact (eq_trans QB2 QB1).
    rewrite QU in RQD.
    (* the callee kept sp, gp, tp, s0 .. s11 *)
    assert (EG : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 SP' /\ YK11.getr regs2 (Z_to_bv 5 3) = GP /\
      YK11.getr regs2 (Z_to_bv 5 4) = TP /\ YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 j /\
      YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 TK_QD /\ YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 taken /\
      YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (TK_Q0 + 32 * j) /\ YK11.getr regs2 (Z_to_bv 5 20) = s4 /\
      YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 kept1 /\ YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 len /\
      YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 TK_Q0 /\ YK11.getr regs2 (Z_to_bv 5 24) = s8 /\
      YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 (tk_sh TK_QD) /\ YK11.getr regs2 (Z_to_bv 5 26) = s10 /\
      YK11.getr regs2 (Z_to_bv 5 27) = s11).
    { repeat match goal with |- _ /\ _ => split end;
        lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?r) = _ =>
          rewrite (HP2 r ltac:(unfold acallee_saved; lia)), (TFE.decode_getr_xeqv _ _ HX1); reflexivity end. }
    destruct EG as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    pose proof (@LeafCgGlue.ms_of_regs_eqv fx TK_R4 regs2 mem2) as EQ2.
    unfold LCK.ms_of_regs in EQ2.
    rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27 in EQ2.
    destruct nt as [|nt'].
    + (* no turn left: +0x384 .. +0x3c8, the exit *)
      cbn [TS0.take_tail_m] in HTL. destruct (tkw_somet _ _ HTL) as [EBF EKF].
      eapply (tkw_run Wc _ _ mem2 _ md2 _ Q EQ2).
      { eapply (tk_run_tail_done (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (queued := TW.S_queued Bw);
          [ exact FR3 | reflexivity | exact RFR3 | exact STK3 | exact SP0 | exact SP63 | exact SQD | exact RQD
          | exact RSQD | exact GQD | lia | lia | lia | lia | lia | lia ]. }
      cbv beta. intros ms1 ms3 md3 (z0 & z1 & z19 & z22 & z23 & ->) HE3 _ HS3.
      pose proof (tkw_inv_run0 Wc mem2 md2 md3 _ hd X _ INV2 HS3) as INV3.
      rewrite EBF in INV3. rewrite EKF in HE3.
      eapply tkw_exit; [exact HE3 | exact INV3 | reflexivity | exact HXB].
    + (* a turn left: +0x384 .. +0x39c, back to the tail loop head at j + 1 *)
      eapply (tkw_run Wc _ _ mem2 _ md2 _ Q EQ2).
      { eapply (tk_run_tail_next (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (queued := TW.S_queued Bw);
          [ exact SQD | exact RQD | exact RSQD | exact GQD | lia | lia | lia | lia | lia | lia ]. }
      cbv beta. intros ms1 ms3 md3 (z0 & z1 & ->) HE3 _ HS3.
      pose proof (tkw_inv_run0 Wc mem2 md2 md3 _ hd X _ INV2 HS3) as INV3.
      eapply (IH nt' (PeanoNat.Nat.lt_succ_diag_r nt')); [exact HE3 | exact INV3 |].
      unfold TKK.tkw_mt. split; [exact WF2|]. split; [exact (eq_trans QB2 QB1)|].
      split; [exact (eq_trans GB2 GB1)|]. split; [lia|]. split; [lia|]. split; [exact HXB | exact HTL].
Qed.

(* The end of a turn (:377): the next turn, the tail, or the exit. *)
End Call.
End Walk.

