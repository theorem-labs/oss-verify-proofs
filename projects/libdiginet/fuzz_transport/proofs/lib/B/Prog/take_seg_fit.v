(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1482 of its 1577 lines of code are new or changed and 831 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/take_seg_kit.v; 314 of its 443 lines of code are new or changed and 1448 lines of the source are left out. *)
(* take_seg_fit: the turn that fits the counters and the pacing (:365-366) in the image-B walk of take
   (lib/B/Prog/take_cgW.v, kit lib/B/Prog/take_seg_kit.v, runs lib/B/Prog/take_seg_run.v): from the loop head TK_L
   (+0x12c), the run to the copy of :365 (the kit's tkw_cpyb), the run to the call of diginet_body_check (the kit's
   tkw_bc), then its return (take_seg_bcret.v tkw_bcret). Image A's twin is lib/A/Prog/take_seg_fit.v. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue AsanKAProof TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg DgnTransportBCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import take_seg_model take_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TFE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportFevt.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module FCs := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import take_seg_kit take_seg_nf take_seg_bcret.
Module TKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.take_seg_kit.
Module TKN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.take_seg_nf.
Module TKB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.take_seg_bcret.
Set Default Proof Using "All".

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation ajd := (@ajournal rc tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HTC : trans_take_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B G.
Hypothesis HGN : gx_noerrno B G.
Hypothesis AIM : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis ABC : forall fx' : YK11.FPState,
  @transport_diginet_body_check_cg fx' rc B MT (transportb_sigma TB_diginet_body_check).

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
Hypothesis HW : tw_at TMAP_B (aview segs (w_H W) memc) Bw.
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
Local Notation tkw_nf := (@TKN.tkw_nf fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_bcret := (@TKB.tkw_bcret fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).

Lemma tkw_fit : forall n, tkw_join_P n ->
  forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z) (X : list byte)
    (j00 : word) (i taken1 kept1 len1 : Z) (body1 : list byte)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (ms : machine_state),
  ms_eqv (tk_at_L ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 GP TP (@YK11.fp_regs fx) (@YK11.fp_csr fx) m
            SP' i kept1) ms ->
  tkw_inv Wc m md B1 hd1 X (tk_spill bp blp hdp allow len1 taken1 j00) ->
  tkw_mh (Datatypes.S n) B1 i taken1 kept1 len1 hd1 body1 X ->
  TW.S_cfg_max_cmds B1 > taken1 ->
  TW.S_cfg_max_body B1 >= len1 + TW.S_queue_len B1 i ->
  (allow <> 0 \/ TW.S_queue_display B1 i = 0) ->
  SRr segs Wc (mkCfg ms md) Q.
Proof.
  intros n JOIN Wc md m B1 hd1 X j00 i taken1 kept1 len1 body1 ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 ms
    EQV INV MH FITa FITb HPACE.
  pose proof MH as ((WF1 & QE & CE & BE & GE) & QL & Hi0 & Ht & Hk & HTK & HT0 & HL & HBL & HD & HFU & HFX & HNX).
  pose proof INV as (ly2 & Sx & J & HF & HP & HMO & K & HTW & LW & FR & HDC & BLC & LX & GX).
  pose proof HFF as (WFF & QFF & GFF & T0 & K0 & TK & QR & LR & BL & HDR & GF').
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  unfold TW.S_queue_N in QR. unfold TS0.DIGINET_MAX_BODY_LEN in LR. unfold amem_range in BM, LM, HM.
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  destruct (tkw_stkf _ _ _ _ _ J) as (STKa & STKb & RFR & SP0 & SP63 & SPLO & SPCE).
  assert (Hi : 0 <= i < 512) by lia.
  pose proof tk_addrs as (TKE & _).
  destruct (tkw_rdt ly2 Sx Wc m md B1 i HAR2 HTW Hi) as [RDT RGT].
  pose proof (tkm_field_ranges B1 i) as (QLr & QDr & MCr & MBr & QUr).
  assert (QL24 : TW.S_queue_len B1 i <= 24) by (apply QL; lia).
  assert (BD : tk_bounds i taken1 kept1 len1 (TW.S_queue_len B1 i) (TW.S_queue_display B1 i)
                 (TW.S_cfg_max_cmds B1) (TW.S_cfg_max_body B1)) by (repeat split; lia).
  rewrite (tkm_loop_S B1 allow i taken1 kept1 len1 hd1 body1 n ltac:(unfold TW.S_queue_N; lia)) in HNX.
  cbv zeta in HNX.
  unfold tk_at_L in EQV.
  assert (F0 : (taken1 <? TW.S_cfg_max_cmds B1) &&
               (len1 + TW.S_queue_len B1 i <=? TW.S_cfg_max_body B1) &&
               (negb (allow =? 0) || (TW.S_queue_display B1 i =? 0)) = true).
  { apply Bool.andb_true_iff. split; [apply Bool.andb_true_iff; split|].
    - apply Z.ltb_lt. lia.
    - apply Z.leb_le. lia.
    - apply Bool.orb_true_iff. destruct HPACE as [Ha|Hd];
        [left; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Ha | right; apply Z.eqb_eq; exact Hd]. }
  rewrite F0 in HNX. rewrite Bool.andb_true_l in HNX.
  assert (HLC : len1 + TW.S_queue_len B1 i <= 1484).
  { destruct (Z_le_gt_dec (len1 + TW.S_queue_len B1 i) 1484) as [Hc|Hc]; [exact Hc|]. exfalso.
    replace (TS0.DIGINET_MAX_BODY_LEN <? len1 + TW.S_queue_len B1 i) with true in HNX
      by (symmetry; apply Z.ltb_lt; unfold TS0.DIGINET_MAX_BODY_LEN; lia).
    cbv iota in HNX. discriminate HNX. }
  replace (TS0.DIGINET_MAX_BODY_LEN <? len1 + TW.S_queue_len B1 i) with false in HNX
    by (symmetry; apply Z.ltb_ge; unfold TS0.DIGINET_MAX_BODY_LEN; lia).
  cbv iota in HNX. rewrite Bool.andb_true_l in HNX.
  (* run: the loop head to the copy of :365 (no store: len and taken stay in the frame) *)
  eapply (tkw_run Wc _ _ m ms md _ Q EQV).
  { eapply (tk_run_fit (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (sv := tk_sv);
      [ exact RDT | exact RGT | exact BD | exact FR | reflexivity | exact RFR | exact SP0 | exact SP63
      | lia | lia | lia | lia | lia | exact HPACE ]. }
  intros ms1 ms2 md1 -> HE1 HG1 HS1.
  pose proof (tkw_inv_run0 Wc m md md1 B1 hd1 X _ INV HS1) as INV1.
  (* the copy of :365 *)
  rewrite (decode_ms_shape _ _ _ _ HE1).
  apply (tkw_cpyb Wc md1 m B1 hd1 X (tk_spill bp blp hdp allow len1 taken1 j00) (ms_regs ms2)
           i len1 (TW.S_queue_len B1 i) TK_R1 Q INV1);
    [ rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; reflexivity
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; reflexivity
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; reflexivity
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; reflexivity
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; exact HGP
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; exact HTP
    | rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity; reflexivity
    | unfold TK_R1, TK_AT; rewrite TKE; lia | unfold TK_R1, TK_AT; rewrite TKE; reflexivity
    | lia | lia | lia | lia |].
  intros regs2 mem2 md2 INV2 HPR2.
  set (XS := firstn (Z.to_nat len1) X ++
             TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i)) ++
             skipn (Z.to_nat len1 + Z.to_nat (TW.S_queue_len B1 i)) X) in INV2.
  assert (LS : length (TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i)))
               = Z.to_nat (TW.S_queue_len B1 i)).
  { apply TWL.length_sub; [unfold TW.A_S_queue_bytes; lia|].
    rewrite (tw_len _ _ _ HTW). unfold TW.W_LEN, TW.A_S_queue_bytes. lia. }
  assert (EXS : firstn (Z.to_nat (len1 + TW.S_queue_len B1 i)) XS =
                body1 ++ TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i))).
  { unfold XS. replace (Z.to_nat (len1 + TW.S_queue_len B1 i))
      with (Z.to_nat len1 + Z.to_nat (TW.S_queue_len B1 i))%nat by lia.
    rewrite (tkw_splice_firstn X _ (Z.to_nat len1) (Z.to_nat (TW.S_queue_len B1 i)) LX ltac:(lia) LS).
    rewrite HFX. reflexivity. }
  assert (EXS0 : firstn (Z.to_nat len1) XS = body1).
  { unfold XS.
    rewrite (tkw_splice_firstn_le X _ (Z.to_nat len1) (Z.to_nat (TW.S_queue_len B1 i)) (Z.to_nat len1)
               ltac:(lia) ltac:(lia) LX). exact HFX. }
  pose proof INV2 as (ly3 & S3 & J3 & HF3 & HP3 & HMO3 & K3 & HTW3 & LW3 & FR3 & HDC3 & BLC3 & LX3 & GX3).
  destruct (tkw_jf _ _ _ _ _ J3) as (HAR3 & _ & _ & _ & _).
  destruct (tkw_rdt ly3 S3 Wc mem2 md2 B1 i HAR3 HTW3 Hi) as [RDT3 RGT3].
  destruct RDT3 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  destruct RGT3 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  (* the call of diginet_body_check: the kept registers as values, so no lookup is left to unify *)
  assert (EG2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 SP').
  { rewrite (HPR2 2 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG3 : YK11.getr regs2 (Z_to_bv 5 3) = GP).
  { rewrite (HPR2 3 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG4 : YK11.getr regs2 (Z_to_bv 5 4) = TP).
  { rewrite (HPR2 4 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG8 : YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 TK_NQ0).
  { rewrite (HPR2 8 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG9 : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))).
  { rewrite (HPR2 9 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG18 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 bp).
  { rewrite (HPR2 18 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG19 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (32 * i)).
  { rewrite (HPR2 19 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG20 : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 (TK_S + 32 * i)).
  { rewrite (HPR2 20 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG21 : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 kept1).
  { rewrite (HPR2 21 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG22 : YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 (- i)).
  { rewrite (HPR2 22 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG23 : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 TK_MAXC).
  { rewrite (HPR2 23 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG24 : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 len1).
  { rewrite (HPR2 24 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG25 : YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 (TK_Q0 + 32 * i)).
  { rewrite (HPR2 25 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG26 : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 (TK_Q0 + 32 * i + 24)).
  { rewrite (HPR2 26 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  assert (EG27 : YK11.getr regs2 (Z_to_bv 5 27) = Z_to_bv 64 i).
  { rewrite (HPR2 27 ltac:(unfold acallee_saved; lia)),
      (decode_ms_reg _ _ _ _ _ _ _ _ _ HE1) by reflexivity. reflexivity. }
  change (SRr segs Wc (@cfg_at fx segs TK_R1 regs2 mem2 md2) Q).
  eapply (TFE.decode_run Wc regs2 mem2 md2 TK_R1 _ Q).
  { unfold LCK.ms_of_regs. rewrite EG2, EG3, EG4, EG8, EG9, EG18, EG19, EG20, EG21, EG22, EG23, EG24, EG25, EG26, EG27.
    eapply (tk_run_bc_call (LCK.RNG_W (world segs) (@w_H segs) Wc)) with (kept := kept1) (len := len1) (bp := bp)
      (i := i);
      [exact D7 | exact N7 | lia | lia | lia | lia | lia]. }
  intros ms3 ms4 md3 -> HE3 HG3 HS3.
  unfold tk_at_R in HE3.
  rewrite (decode_ms_shape _ _ _ _ HE3).
  pose proof (tkw_inv_run0 Wc mem2 md2 md3 B1 hd1 XS (tk_spill bp blp hdp allow len1 taken1 j00) INV2 HS3) as INV3.
  apply (tkw_bc Wc md3 mem2 B1 hd1 XS (tk_spill bp blp hdp allow len1 taken1 j00) (ms_regs ms4)
           (len1 + TW.S_queue_len B1 i) TK_R2 Q INV3).
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. exact HGP.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. exact HTP.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity.
  - unfold TK_R2, TK_AT. rewrite TKE. lia.
  - unfold TK_R2, TK_AT. rewrite TKE. reflexivity.
  - lia.
  - intros W2 regs4 mem4 md4 INV4 HPR4 HR10.
    rewrite EXS in HR10.
    assert (FG2 : YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 SP').
    { rewrite (HPR4 2 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG3 : YK11.getr regs4 (Z_to_bv 5 3) = GP).
    { rewrite (HPR4 3 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG4 : YK11.getr regs4 (Z_to_bv 5 4) = TP).
    { rewrite (HPR4 4 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG8 : YK11.getr regs4 (Z_to_bv 5 8) = Z_to_bv 64 TK_NQ0).
    { rewrite (HPR4 8 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG9 : YK11.getr regs4 (Z_to_bv 5 9) = Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))).
    { rewrite (HPR4 9 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG18 : YK11.getr regs4 (Z_to_bv 5 18) = Z_to_bv 64 bp).
    { rewrite (HPR4 18 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG19 : YK11.getr regs4 (Z_to_bv 5 19) = Z_to_bv 64 (32 * i)).
    { rewrite (HPR4 19 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG20 : YK11.getr regs4 (Z_to_bv 5 20) = Z_to_bv 64 (TK_S + 32 * i)).
    { rewrite (HPR4 20 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG21 : YK11.getr regs4 (Z_to_bv 5 21) = Z_to_bv 64 kept1).
    { rewrite (HPR4 21 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG22 : YK11.getr regs4 (Z_to_bv 5 22) = Z_to_bv 64 (- i)).
    { rewrite (HPR4 22 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG23 : YK11.getr regs4 (Z_to_bv 5 23) = Z_to_bv 64 TK_MAXC).
    { rewrite (HPR4 23 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG24 : YK11.getr regs4 (Z_to_bv 5 24) = Z_to_bv 64 len1).
    { rewrite (HPR4 24 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG25 : YK11.getr regs4 (Z_to_bv 5 25) = Z_to_bv 64 (TK_Q0 + 32 * i)).
    { rewrite (HPR4 25 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG26 : YK11.getr regs4 (Z_to_bv 5 26) = Z_to_bv 64 (TK_Q0 + 32 * i + 24)).
    { rewrite (HPR4 26 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    assert (FG27 : YK11.getr regs4 (Z_to_bv 5 27) = Z_to_bv 64 i).
    { rewrite (HPR4 27 ltac:(unfold acallee_saved; lia)),
        (decode_ms_reg _ _ _ _ _ _ _ _ _ HE3) by reflexivity. reflexivity. }
    change (SRr segs W2 (@cfg_at fx segs TK_R2 regs4 mem4 md4) Q).
    eapply (tkw_bcret n JOIN W2 mem4 md4 _ B1 hd1 XS j00 i taken1 kept1 len1 body1).
    + pose proof (LeafCgGlue.ms_of_regs_eqv TK_R2 regs4 mem4) as EQ.
      unfold LCK.ms_of_regs in EQ.
      assert (GA0 : YK11.getr regs4 (Z_to_bv 5 10) =
        Z_to_bv 64 (DgnLib.body_check
          (body1 ++ TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i))))) by exact HR10.
      rewrite FG2, FG3, FG4, FG8, FG9, FG18, FG19, FG20, FG21, FG22, FG23, FG24, FG25, FG26, FG27, GA0 in EQ.
      exact EQ.
    + exact INV4.
    + split; [exact WF1|]. split; [exact QE|]. split; [exact CE|]. split; [exact BE | exact GE].
    + exact QL.
    + exact Hi.
    + lia.
    + lia.
    + exact HTK.
    + exact HT0.
    + lia.
    + exact HBL.
    + lia.
    + lia.
    + lia.
    + exact EXS0.
    + exact EXS.
    + intros HB. replace (DgnLib.body_check (body1 ++ TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i)))
        =? DgnLib.DIGINET_OK) with true in HNX
        by (symmetry; apply Z.eqb_eq; unfold DgnLib.DIGINET_OK; exact HB).
      cbv iota in HNX. unfold TKK.tkw_next. exact HNX.
    + intros HB. replace (DgnLib.body_check (body1 ++ TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat (TW.S_queue_len B1 i)))
        =? DgnLib.DIGINET_OK) with false in HNX
        by (symmetry; apply Z.eqb_neq; unfold DgnLib.DIGINET_OK; exact HB).
      cbv iota in HNX. unfold TKK.tkw_next. exact HNX.
Qed.

End Call.
End Walk.
