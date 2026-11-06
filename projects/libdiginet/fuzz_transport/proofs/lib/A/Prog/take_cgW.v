(* take_cgW: Theorem transport_take_cg_holds, the statement transport_take_cg_holds_stmt of lib/A/Prog/take_cg.v: the
   G-form caller-journal walk of take (transport/src/diginet_session.c:353-386) on fuzz_transport.asan at 0x8a508 =
   transport_sigma TS_take (1228 bytes, frame 224).

   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) from the entry to the
   return; take takes no side-stack frame, so there is no inner journal. Between its four calls it runs the footprint
   runs of lib/A/Prog/take_seg_run.v (each carried into SRr by TransportFevt.v decode_run, the journal re-established
   across it by ajournal_gx_exec); the three calls of __asan_memcpy go through TransportGCg.v gx_intrin_at and the
   call of diginet_body_check through TransportGCg.v gx_call_cg. The model's facts (lib/A/Prog/take_seg_model.v)
   bound every index: taken + kept = i and S_queued Bw <= 512.

   The cuts follow the plain walk (lib/Prog/T/take.v), one file each so that every file compiles in minutes:
   take_seg_kit.v (the invariant, the helpers, the three call wrappers), take_seg_exit.v (the return, the tail loop),
   take_seg_join.v (the end of a turn), take_seg_nf.v (the refusal), take_seg_bcret.v (after diginet_body_check),
   take_seg_fit.v (a turn that fits), take_seg_head.v (one turn, and the loop by induction). This file runs the
   prologue to the loop head, or straight to the return when s->queued = 0, and closes the statement. *)
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

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import take_seg_kit take_seg_exit take_seg_head.
Module TKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_kit.
Module TKX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_exit.
Module TKH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_seg_head.
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
Local Notation tkw_turn := (@TKH.tkw_turn fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).
Local Notation tkw_head := (@TKH.tkw_head fx rc B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV BF keptF HLP HBW' HFF) (only parsing).

(* tkw_inv at equal model worlds and display flags; stated over fresh names so that the rewrite never abstracts
   a section variable. *)
Lemma tkw_inv_eq : forall (Wc : world segs) m md (B2 B3 : list byte) (hd2 hd3 : Z) (X : list byte) (ws : list word),
  tkw_inv Wc m md B2 hd2 X ws -> B2 = B3 -> hd2 = hd3 -> tkw_inv Wc m md B3 hd3 X ws.
Proof. intros Wc m md B2 B3 hd2 hd3 X ws H E1 E2. rewrite <- E1, <- E2. exact H. Qed.

(* The walk from the entry. *)
Lemma tkw_holds : SRr segs W (@cfg_at fx segs (transport_sigma TS_take) regs memc mdc) Q.
Proof using All.
  pose proof HFF as (WFF & QFF & GFF & T0 & K0 & TK & QR & LR & BL & HDR & GF').
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  pose proof tkw_o16 as (O16 & ONEG & OBUD & OAL).
  unfold TW.S_queue_N in QR. unfold TS0.DIGINET_MAX_BODY_LEN in LR. unfold amem_range in BM, LM, HM.
  destruct (tkw_jf _ _ _ _ _ HJ) as (HAR0 & _ & _ & HPRES & _).
  destruct (tkw_stkf _ _ _ _ _ HJ) as (STKa & STKb & RFR & SP0 & SP63 & SPLO & SPCE).
  pose proof (tkw_cell_ge blp 8 HTWL HNGL HRDL ltac:(lia)) as L4096.
  pose proof (tkw_cell_ge hdp 4 HTWH HNGH HRDH ltac:(lia)) as H4096.
  pose proof (tkw_cell_ge bp TAKE_BODY HTWB HNGB HRDB ltac:(lia)) as Bp4096.
  pose proof (Permutation_refl (ablocks B lyc Sc)) as PR.
  (* the kept fact at the entry *)
  assert (KE : acall_kept_g segs B G lyc Sc W memc W (gover OUTS memc memc) (sp - TAKE_STK) sp EW).
  { eapply acall_kept_g_mem_ext; [|eapply dk_kept_refl_g].
    - intros x. unfold gover. destruct (inGb OUTS (bv_unsigned x)); reflexivity.
    - intros a Ha. exact (tkw_win_pres lyc Sc W memc mdc a HJ Ha). }
  (* the runtime cells and their footprint *)
  pose proof (TFE.decode_cells_asan B HCELLS lyc Sc W memc mdc HAR0) as CELLS.
  assert (GCK : ov_read_bytes rsegs memc (wa FCs.GOT_CELL_K) 8 = Some (le8 (wa FCs.CELL_K))).
  { exact (tkw_ovr memc FCs.GOT_CELL_K _ 8 (proj1 (proj2 CELLS)) ltac:(reflexivity)). }
  assert (CK : ov_read_bytes rsegs memc (wa FCs.CELL_K) 8 = Some (le8 (wa FCs.ASAN_K))).
  { exact (tkw_ovr memc FCs.CELL_K _ 8 (proj1 CELLS) ltac:(reflexivity)). }
  assert (RGCK : rng (LCK.RNG_W (world segs) (@w_H segs) W) FCs.GOT_CELL_K 8).
  { apply (decode_rng W); [unfold FCs.GOT_CELL_K; lia | unfold FCs.GOT_CELL_K; lia |].
    intros b Hb. apply (decode_vis_seg W b).
    apply (decode_covers_img FCs.GOT_CELL_K 8 b); [vm_compute; reflexivity | exact Hb]. }
  assert (RCK : rng (LCK.RNG_W (world segs) (@w_H segs) W) FCs.CELL_K 8).
  { apply (decode_rng W); [unfold FCs.CELL_K; lia | unfold FCs.CELL_K; lia |].
    intros b Hb. apply (decode_vis_seg W b).
    apply (decode_covers_img FCs.CELL_K 8 b); [vm_compute; reflexivity | exact Hb]. }
  (* the cells and reads of the entry *)
  destruct (tkw_hd_sh lyc Sc W memc mdc HJ PR KE) as (khd & SHD & HKD & RHD).
  destruct (tkw_rdj lyc Sc W memc mdc Bw HAR0 HW) as [RDJ RGJ].
  destruct RDJ as (JA & JB & JC & JD & JE & JF). destruct RGJ as (NA & NB & NC & ND & NE & NF).
  destruct (tkw_cb_of (w_H W) memc hdp 4%nat ltac:(lia) ltac:(lia)
              ltac:(intros ii Hii;
                    exact (proj1 (proj2 (tkw_twr_cur hdp 4 lyc Sc W memc mdc (hdp + ii) HTWH HNGH
                             ltac:(lia) HJ PR))))) as (jh & Ljh & CHD & _).
  destruct (tkw_cb_of (w_H W) memc blp 8%nat ltac:(lia) ltac:(lia)
              ltac:(intros ii Hii;
                    exact (proj1 (proj2 (tkw_twr_cur blp 8 lyc Sc W memc mdc (blp + ii) HTWL HNGL
                             ltac:(lia) HJ PR))))) as (jb0 & Ljb & CBL & _).
  destruct (tkw_cb_of (w_H W) memc bp 1484%nat ltac:(lia) ltac:(lia)
              ltac:(intros ii Hii;
                    exact (proj1 (proj2 (tkw_twr_cur bp TAKE_BODY lyc Sc W memc mdc (bp + ii) HTWB HNGB
                             ltac:(unfold TAKE_BODY; lia) HJ PR))))) as (X0 & LX0 & _ & GX0).
  assert (RHDP : rng (LCK.RNG_W (world segs) (@w_H segs) W) hdp 4)
    by exact (tkw_cell_rng hdp 4 lyc Sc W memc mdc HTWH HNGH HRDH HJ PR).
  assert (TQS : tk_sh TK_QD = 2148222996) by (unfold tk_sh, TK_QD, TK_S, TK_K; reflexivity).
  (* the entry run: the argument registers in the form LCK.ms_of_regs reads *)
  assert (ESP : bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) = sp) by reflexivity.
  assert (G3 : YK11.getr regs (Z_to_bv 5 3) = w64 (as_gp B)) by exact HGP.
  assert (G4 : YK11.getr regs (Z_to_bv 5 4) = w64 (as_tp B)) by exact HTP.
  assert (G10 : YK11.getr regs (Z_to_bv 5 10) = w64 TAKE_S) by exact H10.
  assert (G11 : YK11.getr regs (Z_to_bv 5 11) = w64 bp) by exact H11.
  assert (G12 : YK11.getr regs (Z_to_bv 5 12) = w64 blp) by exact H12.
  assert (G13 : YK11.getr regs (Z_to_bv 5 13) = w64 allow) by exact H13.
  assert (G14 : YK11.getr regs (Z_to_bv 5 14) = w64 hdp) by exact H14.
  destruct (Z.eq_dec (TW.S_queued Bw) 0) as [QZ|QZ].
  - (* s->queued = 0: the prologue goes straight to the exit *)
    eapply (TFE.decode_run W regs memc mdc (transport_sigma TS_take) _ Q).
    { unfold LCK.ms_of_regs. rewrite G3, G4, G10, G11, G12, G13, G14.
      eapply (tk_run_entry_z (LCK.RNG_W (world segs) (@w_H segs) W)) with (lo := sp - TAKE_STK) (khd := khd).
      - exact STKb.
      - lia.
      - exact RFR.
      - exact GCK.
      - exact CK.
      - exact RGCK.
      - exact RCK.
      - exact SHD.
      - exact JC.
      - rewrite <- QZ. exact JF.
      - exact RHD.
      - exact NC.
      - exact NF.
      - exact RHDP.
      - exists jh. exact CHD.
      - unfold off_stk. left. unfold FCs.GOT_CELL_K. lia.
      - unfold off_stk. left. unfold FCs.CELL_K. lia.
      - unfold off_stk. left. apply tkw_sh_lt. lia.
      - unfold off_stk. left. apply tkw_sh_lt. lia.
      - unfold off_stk. left. lia.
      - unfold off_stk. destruct OH as [OH1|OH1]; [left | right]; lia.
      - rewrite TQS. destruct HM as [HMa|HMa]; [left | right]; lia.
      - destruct (Z_le_gt_dec (hdp + 4) TK_QD) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_le_gt_dec (TK_QD + 4) hdp) as [Hr|Hr]; [right; exact Hr|]. exfalso.
        apply (HNGH (Z.max hdp TK_QD) ltac:(lia)). apply tkw_inG_gs. lia.
      - exact HHD4.
      - exact HKD.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HALW.
    }
    intros ms1 ms2 md1 HP1 HE1 HG1 HS1.
      destruct HP1 as (m1 & x11 & x13 & x14 & ws & -> & MU1 & WM1 & ST1 & CH1 & LWS & NTH & FR1).
      rewrite <- G3, <- G4 in HE1.
      cbn [ms_mem] in HG1.
      pose proof HLP as HLP0.
      replace (Z.to_nat (TW.S_queued Bw)) with 0%nat in HLP0 by lia.
      cbn [TS0.take_loop_m] in HLP0.
      destruct (tkw_someq Bw [] 0 0 0 0 HLP0) as (EB & Eb & El & Eh & Et & Ek).
      assert (J1 : ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own lyc Sc W m1 md1 k).
      { apply (tkw_jrun lyc Sc W memc mdc m1 md1
                 (fun a => (SP' <= a < sp) \/ (hdp <= a < hdp + 4)) HJ PR).
        - intros x Hx. cbv beta in Hx. apply MU1. cbn [outside]. tauto.
        - exact HG1.
        - exact HS1.
        - intros a Ha. cbv beta in Ha. destruct Ha as [Ha|Ha]; [left; lia | right; left; apply tkw_outs; right; exact Ha]. }
      eapply (tkw_exit W md1 m1 X0 ws).
      + rewrite <- Et, <- El, <- Ek. exact HE1.
      + pose proof (tkw_inv_mu W memc mdc m1 md1 lyc Sc Bw 0 X0 ws
                 (fun a => (SP' <= a < sp) \/ (hdp <= a < hdp + 4)) HJ eq_refl PR (mle_start MT Sc MTL) KE
                 HW LX0 GX0 ltac:(exists jb0; exact CBL) J1
                 ltac:(intros x Hx; cbv beta in Hx; apply MU1; cbn [outside]; tauto) HG1
                 ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha|Ha]; [left; unfold TK_FRAME; lia | right; exact Ha])
                 LWS FR1 CH1) as IV.
        exact (tkw_inv_eq W m1 md1 Bw BF 0 hd X0 ws IV EB Eh).
      + exact NTH.
      + assert (HZ : firstn (Z.to_nat 0) X0 = []) by reflexivity. rewrite El, Eb in HZ. exact HZ.
  - (* s->queued > 0: the loop *)
    eapply (TFE.decode_run W regs memc mdc (transport_sigma TS_take) _ Q).
    { unfold LCK.ms_of_regs. rewrite G3, G4, G10, G11, G12, G13, G14.
      eapply (tk_run_entry (LCK.RNG_W (world segs) (@w_H segs) W)) with (lo := sp - TAKE_STK) (khd := khd)
          (queued := TW.S_queued Bw).
      - exact STKb.
      - lia.
      - exact RFR.
      - exact GCK.
      - exact CK.
      - exact RGCK.
      - exact RCK.
      - exact SHD.
      - exact JC.
      - exact JF.
      - exact RHD.
      - exact NC.
      - exact NF.
      - exact RHDP.
      - exists jh. exact CHD.
      - unfold off_stk. left. unfold FCs.GOT_CELL_K. lia.
      - unfold off_stk. left. unfold FCs.CELL_K. lia.
      - unfold off_stk. left. apply tkw_sh_lt. lia.
      - unfold off_stk. left. apply tkw_sh_lt. lia.
      - unfold off_stk. left. lia.
      - unfold off_stk. destruct OH as [OH1|OH1]; [left | right]; lia.
      - rewrite TQS. destruct HM as [HMa|HMa]; [left | right]; lia.
      - destruct (Z_le_gt_dec (hdp + 4) TK_QD) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_le_gt_dec (TK_QD + 4) hdp) as [Hr|Hr]; [right; exact Hr|]. exfalso.
        apply (HNGH (Z.max hdp TK_QD) ltac:(lia)). apply tkw_inG_gs. lia.
      - exact HHD4.
      - exact HKD.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact HALW.
    }
    intros ms1 ms2 md1 HP1 HE1 HG1 HS1.
      destruct HP1 as (m1 & x11 & x12 & x13 & -> & MU1 & WM1 & ST1 & CH1 & j38 & FR1).
      rewrite <- G3, <- G4 in HE1.
      cbn [ms_mem] in HG1.
      assert (J1 : ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own lyc Sc W m1 md1 k).
      { apply (tkw_jrun lyc Sc W memc mdc m1 md1
                 (fun a => (SP' <= a < sp) \/ (hdp <= a < hdp + 4)) HJ PR).
        - intros x Hx. cbv beta in Hx. apply MU1. cbn [outside]. tauto.
        - exact HG1.
        - exact HS1.
        - intros a Ha. cbv beta in Ha. destruct Ha as [Ha|Ha]; [left; lia | right; left; apply tkw_outs; right; exact Ha]. }
      eapply (tkw_head (Z.to_nat (TW.S_queued Bw) - 1)%nat W md1 m1 Bw 0 X0 j38 0 0 0 0 []).
      + replace (Datatypes.S (Z.to_nat (TW.S_queued Bw) - 1)) with (Z.to_nat (TW.S_queued Bw)) by lia.
        exact HE1.
      + apply (tkw_inv_mu W memc mdc m1 md1 lyc Sc Bw 0 X0 (tk_spill bp blp hdp allow j38)
                 (fun a => (SP' <= a < sp) \/ (hdp <= a < hdp + 4)) HJ eq_refl PR (mle_start MT Sc MTL) KE
                 HW LX0 GX0 ltac:(exists jb0; exact CBL) J1
                 ltac:(intros x Hx; cbv beta in Hx; apply MU1; cbn [outside]; tauto) HG1
                 ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha|Ha]; [left; unfold TK_FRAME; lia | right; exact Ha])
                 ltac:(reflexivity) FR1 CH1).
      + assert (WF0 : tkm_wf Bw) by (unfold tkm_wf; rewrite (tw_len _ _ _ HW); unfold TW.W_LEN; reflexivity).
        split; [split; [exact WF0|]; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity|].
        split; [intros jj Hjj; apply HQL; lia|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|].
        split; [lia|]. split; [reflexivity|]. split; [lia|].
        split; [replace (Datatypes.S (Z.to_nat (TW.S_queued Bw) - 1)) with (Z.to_nat (TW.S_queued Bw)) by lia; lia|].
        split; [reflexivity|].
        replace (Datatypes.S (Z.to_nat (TW.S_queued Bw) - 1)) with (Z.to_nat (TW.S_queued Bw)) by lia.
        exact HLP.
Qed.

End Call.
End Walk.

(* The statement of lib/A/Prog/take_cg.v. *)
Theorem transport_take_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_take_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HTC LAWS MTL HGX HGN AIM ABC.
  intros STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs bp blp hdp allow len hd taken body Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE HTWB HRDB HOWB HNGB HBL8 HTWL HRDL
    HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HM HQL HMC HMB HCNT HNEV.
  assert (HWF : tkm_wf Bw).
  { unfold tkm_wf. rewrite (tw_len _ _ _ HW). unfold TW.W_LEN. reflexivity. }
  destruct (tkm_take_m Bw allow Bw' body len hd taken HWF HM)
    as (BF & keptF & HLP & HBW' & WF1 & WF' & Q1 & G1 & G' & QK & T0 & K0 & TK & QR & LR & BL & HDR).
  exact (tkw_holds B MT HCELLS HTC LAWS MTL HGX HGN AIM ABC STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs
    bp blp hdp allow len hd taken body Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 H13 H14 HAL HWLO HWHI HALW HBP0 HFAKE
    HTWB HRDB HOWB HNGB HBL8 HTWL HRDL HOWL HNGL HHD4 HTWH HRDH HOWH HNGH SEP1 SEP2 SEP3 HW HGF HQL HMC HMB HCNT HNEV
    BF keptF HLP HBW'
    (conj WF1 (conj Q1 (conj G1 (conj T0 (conj K0 (conj TK (conj QR (conj LR (conj BL (conj HDR G'))))))))))).
Qed.

