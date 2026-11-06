(* diginet_session_poll_seg_grecv: the call of io_recv of the image-B walk of diginet_session_poll
   (lib/B/Prog/diginet_session_poll_segs.v; the jalr at 0x8acd4 and 0x8ad50), from a state of pw_run at the
   realigned sp1, at io_recv's entry (TI.ti_io_recv timg_B) with ra the return address, through its statement
   (io_recv_cg.v transport_io_recv_cg, a G-form callee in the same G journal), at bp = buf = frame + 32 and
   cap = 1514. It returns with a0 = r, pw_run at the world io_recv_m leaves (the run invariants and g_rx by pw_keep's
   iorecv_m_run_inv and iorecv_m_g_rx), and buf's 1514 bytes agreeing with the bytes it handed over (io_recv's X). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma pw_recv_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word)
    (B1 : list byte) (r1 : Z) (got : list byte),
  pw_rt B MT -> pw_keep -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  YK11.getr regsC 11 = w64 (pw_F c pos + 32) -> YK11.getr regsC 12 = w64 TS0.DIGINET_MAX_FRAME_LEN ->
  TC.io_recv_m timg_B (cx_TF c) Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) ->
  SRr segs W2 (@cfg_at fx segs (TI.ti_io_recv timg_B) regsC mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\ YK11.getr regs3 10 = w64 r1 /\
       (exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
          garr8 segs (mrestrict (w_H W3) mem3) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got) /\
       pw_run B MT c pos ly3 S3 W3 mem3 md3 B1).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC B1 r1 got HRT HKP HOK HRUN H2 H3 H4 HRA HRA4 H11 H12 HM.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
  pose proof HKP as (_ & _ & _ & _ & KRI & KGR).
  pose proof HRUN as (HCUR & _).
  pose proof HCUR as (HJ & HFR & HPERM & _ & _ & _ & _ & _ & _ & _ & HTW & HGF & HINV & HGRX).
  pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTF0 & HTFG & _ & HAP & HRX &
    _ & _ & _ & _ & _ & _ & _ & HEV).
  (* pw_ok_sp's statement names no meter: MT is its argument only while the kit's section keeps it *)
  pose proof (pw_ok_sp B) as SPK. try specialize (SPK MT).
  pose proof (SPK c HOK) as (HAR0 & HSPr & _ & _ & _ & HSP1 & HM0 & HSTK & HSP0 & HPS & HEI & HIS & _). clear SPK.
  pose proof (pw_cur_frame B MT c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR)
    as (HAR2 & _ & HFA & HFAall & _ & _ & _ & _ & _ & _ & _).
  assert (USP : spZ regsC = pw_sp1 c).
  { change (spZ regsC) with (bv_unsigned (YK11.getr regsC 2)). rewrite H2. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (M16 : pw_sp1 c mod 16 = 0).
  { unfold pw_sp1.
    replace (32 * ((pw_SP c - POLL_FRAME) / 32)) with (2 * ((pw_SP c - POLL_FRAME) / 32) * 16) by ring.
    apply Z_mod_mult. }
  assert (CAP : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity.
  assert (K0 : 0 <= IORECV_STK) by (unfold ESTACK in HEI; lia).
  assert (KW1 : pw_SP c - POLL_STK <= pw_sp1 c - IORECV_STK) by lia.
  assert (KW : pw_SP c - POLL_STK <= spZ regsC - IORECV_STK) by (rewrite USP; exact KW1).
  (* buf's 1514 bytes, the current heap frame and the read-only bytes at io_recv's window *)
  pose proof (pw_buf_at B MT c pos ly2 S2 W2 mem2 md2 Bx regsC IORECV_STK TS0.DIGINET_MAX_FRAME_LEN HRT HOK HRUN USP
    K0 KW ltac:(rewrite CAP; lia)) as (HFAKE & HRD & _ & HTWR & HOFF & HNG).
  pose proof (pw_tf_at B MT c pos ly2 S2 W2 mem2 md2 Bx regsC IORECV_STK HRT HOK HCUR KW ltac:(rewrite USP; lia))
    as HTF.
  pose proof (pw_rom_at B MT c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR) as HROM.
  (* no byte io_recv may store is a byte of TF: its G rows are poll_wr rows (poll_apart), and buf lies in the own
     frame, which is apart from TF's placement at the entry (trans_src_ok_disj_own) *)
  assert (HAPART : iorecv_apart (cx_TF c) Bx (pw_F c pos + 32) TS0.DIGINET_MAX_FRAME_LEN).
  { intros x Hx fr Efr Hin. unfold iorecv_wr in Hx.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
    - exact (HAP x (or_introl Hx) fr Efr Hin).
    - exact (HAP x (or_intror (or_introl Hx)) fr Efr Hin).
    - exact (HAP x (or_intror (or_intror (or_introl Hx))) fr Efr Hin).
    - exact (HAP x (or_intror (or_intror (or_intror (or_introl (ex_intro _ (iorecv_w1 Bx) Hx))))) fr Efr Hin).
    - rewrite Efr in HTF0. unfold trans_tframe_at in HTF0. destruct HTF0 as (_ & _ & HSRC & _).
      pose proof (trans_src_ok_disj_own B LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) ly2 S2 W2 mem2 md2
        POLL_CID pos (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) HAR0 HAR2 HFR HPERM HFAall HSRC
        ltac:(lia)) as D.
      rewrite HFA, poll_fbytes in D. unfold POLL_FBYTES in D. rewrite CAP in Hx. lia. }
  (* g_rx is the entry's, so it points into TF as at the entry *)
  assert (HRXIN : iorecv_rx_in (cx_TF c) Bx) by (unfold iorecv_rx_in; rewrite HGRX; exact HRX).
  assert (HEV2 : st_nev (cx_S c) + cx_k c + IORECV_EV <= EV_MAX) by (unfold IORECV_EV; unfold POLL_EV in HEV; lia).
  assert (HS16 : spZ regsC mod 16 = 0) by (rewrite USP; exact M16).
  assert (HSW : cx_sp0 c - cx_STK c <= spZ regsC - IORECV_STK) by (rewrite USP; lia).
  assert (HS0 : spZ regsC <= cx_sp0 c) by (rewrite USP; lia).
  assert (HCAP : 0 <= TS0.DIGINET_MAX_FRAME_LEN < 2 ^ 32) by (rewrite CAP; lia).
  (* io_recv's statement in the walk's G journal, then pw_run at the world it leaves *)
  eapply SRr_mono.
  { exact (HREC fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
      ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c) regsC (pw_F c pos + 32) TS0.DIGINET_MAX_FRAME_LEN r1 got
      (cx_TF c) Bx B1 HJ HRA HRA4 H3 H4 H11 H12 HS16 HSW HS0 HCAP HFAKE HTWR HRD HOFF HNG HTF HTFG HAPART HRXIN HROM
      HTW HGF HM HEV2). }
  intros W3 c3 _ HPOST.
  unfold transport_io_recv_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & HFR3 & HPERM3 & HK3 & HMO3 &
    HR10 & HTW3 & HGF3 & HX).
  assert (E0 : e = 0) by (unfold IORECV_EV in He; lia). subst e.
  pose proof (tw_len _ _ _ HTW) as HLEN.
  exists ly3, S3, regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HP3|]. split; [exact HR10|]. split; [exact HX|].
  apply (pw_run_gcall B MT c pos ly2 S2 W2 mem2 md2 Bx regsC IORECV_STK
    (iorecv_wr Bx (pw_F c pos + 32) TS0.DIGINET_MAX_FRAME_LEN) ly3 S3 W3 mem3 md3 B1 HRT HOK HRUN USP K0 KW1).
  - intros a Ha. unfold iorecv_wr in Ha. unfold poll_wr.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
    + left. left. exact Ha.
    + left. right. left. exact Ha.
    + left. right. right. left. exact Ha.
    + left. right. right. right. left. exists (iorecv_w1 Bx). exact Ha.
    + right. exact Ha.
  - exact HJ3.
  - exact HFR3.
  - exact HPERM3.
  - exact HK3.
  - exact HMO3.
  - exact HTW3.
  - exact HGF3.
  - exact (KRI timg_B (cx_TF c) Bx TS0.DIGINET_MAX_FRAME_LEN B1 r1 got HLEN HINV HM).
  - rewrite (KGR timg_B (cx_TF c) Bx TS0.DIGINET_MAX_FRAME_LEN B1 r1 got HLEN HM). exact HGRX.
Qed.

End c.
