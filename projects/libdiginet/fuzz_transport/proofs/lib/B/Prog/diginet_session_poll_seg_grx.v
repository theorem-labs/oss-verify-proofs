(* diginet_session_poll_seg_grx: the calls of diginet_session_rx (the jal at 0x8ad18 and 0x8ad90) and
   diginet_session_tick (the jal at 0x8ad28) of the image-B walk of diginet_session_poll
   (lib/B/Prog/diginet_session_poll_segs.v), from a state of pw_run at the realigned sp1, at the callee's entry with ra
   the return address, through its statement (diginet_session_rx_cg.v, diginet_session_tick_cg.v; G-form callees in
   the same G journal). rx reads the bytes io_recv handed over at buf (io_recv's X: buf's 1514 bytes agree with them),
   and its premise (3) comes from poll_dn_in at the call's world and bytes (the walk's poll_rx_each / poll_drain_rx)
   with the current heap frame's placement (pw_tf_at). Each returns with pw_run at the world its model call leaves
   (the run invariants and g_rx by pw_keep). *)
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

(* garr8 of a list gives garr8 of each of its prefixes. *)
Lemma pw_garr8_firstn : forall (m : word -> option byte) (base : Z) (l : list Z) (n : nat),
  garr8 segs m base l -> garr8 segs m base (firstn n l).
Proof using All.
  intros m base l n H j Hj.
  assert (E : nth j (firstn n l) 0 = nth j l 0).
  { rewrite <- (app_nth1 (firstn n l) (skipn n l) 0 Hj). rewrite firstn_skipn. reflexivity. }
  rewrite E. apply (H j). rewrite length_firstn in Hj. lia.
Qed.

(* The byte values of a prefix are the prefix of the byte values. *)
Lemma pw_zs_firstn : forall (n : nat) (l : list byte), TW.zs (firstn n l) = firstn n (TW.zs l).
Proof using All.
  unfold TW.zs. induction n as [|n IH]; intros [|x l]; cbn [firstn map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

(* The bytes io_recv handed over, from its X form: buf's DIGINET_MAX_FRAME_LEN bytes are X and got is a prefix of X,
   so got lies at buf and has at most DIGINET_MAX_FRAME_LEN bytes. *)
Lemma pw_got_prefix : forall (m : word -> option byte) (base : Z) (got X : list byte),
  length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN -> garr8 segs m base (TW.zs X) -> firstn (length got) X = got ->
  garr8 segs m base (TW.zs got) /\ 0 <= Z.of_nat (length got) <= TS0.DIGINET_MAX_FRAME_LEN.
Proof using All.
  intros m base got X HL HG HF.
  pose proof (length_firstn (length got) X) as HN. rewrite HF, HL in HN.
  split.
  - rewrite <- HF. rewrite pw_zs_firstn. apply pw_garr8_firstn. exact HG.
  - assert (E : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity. rewrite E in HN |- *. lia.
Qed.

(* A class count of the frames with the own class-5 frame on top: the own frame counts for class 5 only. *)
Lemma pw_count_own : forall pos l, count_cid POLL_CID ((POLL_CID, pos) :: l) = 1 + count_cid POLL_CID l.
Proof using All. intros pos l. reflexivity. Qed.
Lemma pw_count_other : forall cid pos l, POLL_CID <> cid -> count_cid cid ((POLL_CID, pos) :: l) = count_cid cid l.
Proof using All. intros cid pos l H. cbn [count_cid]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

(* The call's sp is the realigned sp1 (sp = sp1 at 0x8ad18, 0x8ad28 and 0x8ad90): 16-aligned, below the entry sp,
   and both callee windows [sp1 - SRX_STK, sp1) and [sp1 - TICK_STK, sp1) inside the statement's and the caller's
   (pw_ok_sp: POLL_STK = 176 + SRX_STK, TICK_STK <= SRX_STK, sp1 at most 176 below the entry sp). *)
Lemma pw_call_win : forall c (regsC : bvmap 5 word), pw_ok B c -> YK11.getr regsC 2 = w64 (pw_sp1 c) ->
  spZ regsC = pw_sp1 c /\ spZ regsC mod 16 = 0 /\ spZ regsC <= cx_sp0 c /\ spZ regsC <= pw_SP c /\
  0 <= SRX_STK /\ 0 <= TICK_STK /\
  cx_sp0 c - cx_STK c <= spZ regsC - SRX_STK /\ pw_SP c - POLL_STK <= spZ regsC - SRX_STK /\
  pw_SP c - POLL_STK <= pw_sp1 c - SRX_STK /\
  cx_sp0 c - cx_STK c <= spZ regsC - TICK_STK /\ pw_SP c - POLL_STK <= spZ regsC - TICK_STK /\
  pw_SP c - POLL_STK <= pw_sp1 c - TICK_STK.
Proof using All.
  intros c regsC HOK R2.
  pose proof (pw_ok_sp B MT c HOK) as (_ & HSP & _ & _ & HM32 & HS1 & _ & HSTK & HSP0 & HPS & _ & _ & HTK).
  assert (H0S : 0 <= SRX_STK) by (cbv; congruence).
  assert (H0T : 0 <= TICK_STK) by (cbv; congruence).
  assert (USP : spZ regsC = pw_sp1 c) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (M16 : pw_sp1 c mod 16 = 0) by lia.
  rewrite USP. refine (conj eq_refl (conj M16 _)). repeat split; lia.
Qed.

(* The call of diginet_session_rx at 0x8ad18 or 0x8ad90: its statement at the call state in the same G journal
   (own = the own frame :: the caller's), with buf = frame + 32 holding got (a prefix of io_recv's X), buf's
   placement, TF's and the read-only bytes at the call state (the kit), srx_apart from poll_apart, the run invariants
   from TRI.run_inv, premise (3) from poll_dn_in with TF's placement at the call (a sub-range of TF), and the class
   counts of the frames with the own class-5 frame on top (class 1 with room for two frames: the caller's
   count_cid SRX_CID + 1 < fs_frames SRX_CID). Its post gives pw_run at its world B2 (pw_run_gcall; TRI.run_inv and
   g_rx by pw_keep). *)
Lemma pw_rx_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word)
    (got : list byte) (now : Z) (B2 : list byte) (r2 : Z),
  pw_rt B MT -> pw_keep -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  YK11.getr regsC 10 = w64 POLL_S -> YK11.getr regsC 11 = w64 (pw_F c pos + 32) ->
  YK11.getr regsC 12 = w64 (Z.of_nat (length got)) -> YK11.getr regsC 13 = w64 now ->
  0 <= now < 2 ^ 64 -> (0 < length got)%nat ->
  (exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
     garr8 segs (mrestrict (w_H W2) mem2) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got) ->
  TSS.diginet_session_rx_m timg_B (cx_TF c) Bx got now = Some (B2, r2) ->
  poll_dn_in (cx_TF c) Bx got ->
  SRr segs W2 (@cfg_at fx segs (transportb_sigma TB_diginet_session_rx) regsC mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\
       pw_run B MT c pos ly3 S3 W3 mem3 md3 B2).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC got now B2 r2 HRT HKP HOK HRUN R2 R3 R4 RA RAZ R10 R11 R12 R13 Hnow
    Hgot0 HX HM HDN.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRXc & _ & _).
  pose proof HKP as (HK1 & _ & HK3 & _ & _ & _).
  pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOFF & _ & HAP & _ & _ & _ &
    HC5 & HC1 & HC4 & HC0 & HC2 & HEV).
  pose proof HRUN as (HCUR & _ & _ & _).
  pose proof HCUR as (HJ & HFRS & _ & _ & _ & _ & _ & _ & _ & _ & HTW & HGF & HINV & HGRX).
  pose proof HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  destruct (pw_call_win c regsC HOK R2) as (USP & SP16 & SPLE0 & SPLE & HS0 & _ & WS1 & WS2 & WS3 & _).
  (* buf: got at frame + 32, its placement, outside G and the window *)
  destruct HX as (X & HXl & HXg & HXf).
  destruct (pw_got_prefix _ _ got X HXl HXg HXf) as (HG8 & HGL).
  pose proof (pw_buf_at B MT c pos ly2 S2 W2 mem2 md2 Bx regsC SRX_STK (Z.of_nat (length got)) HRT HOK HRUN USP
    HS0 WS2 HGL) as (_ & _ & HSRC & _ & HOFFW & HNG).
  pose proof (pw_cur_frame B MT c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR) as (_ & _ & _ & _ & _ & _ & HF4096 & _).
  assert (HB0 : 0 < pw_F c pos + 32) by (clear - HF4096; lia).
  (* TF and the read-only bytes at the call state *)
  pose proof (pw_tf_at B MT c pos ly2 S2 W2 mem2 md2 Bx regsC SRX_STK HRT HOK HCUR WS2 SPLE) as HTFs.
  pose proof (pw_rom_at B MT c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR) as HROM.
  (* srx_wr got is a row of poll_wr *)
  assert (HSAP : srx_apart (cx_TF c) got).
  { intros x Hx fr Hfr.
    exact (HAP x (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ got Hx)))))) fr Hfr). }
  (* premise (3): the OW.dn range lies in TF's, placed at the call state *)
  assert (HP3 : DSpec.fr_code got = 0 -> srx_mac_bad Bx got = false -> TW.S_desk_known Bx <> 0 ->
     TS0.memeq 6 (DSpec.fr_src got) (TW.S_desk_mac Bx) = true -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
     DSpec.fr_cmd got = TS0.DIGINET_CMD_DATA -> ondata_dup Bx got = false -> DSpec.fr_keepalive got = false ->
       trans_src_ok B ly2 S2 W2 mem2 (TC.OW_dn_body Bx (TW.GOT_ndata Bx)) (DSpec.fr_body_len got) /\
       decode_off_win regsC SRX_STK (TC.OW_dn_body Bx (TW.GOT_ndata Bx)) (DSpec.fr_body_len got)).
  { intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8.
    destruct (HDN Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8) as (fr & Hfr & Hlo & Hhi).
    pose proof (DSpec.fr_code_ok got Q1) as (_ & _ & Hnb & _).
    assert (Hbl : 0 <= DSpec.fr_body_len got) by (unfold DSpec.fr_body_len; clear - Hnb; lia).
    pose proof HTFs as HTF1. rewrite Hfr in HTF1. unfold trans_tframe_at in HTF1.
    destruct HTF1 as (_ & _ & Hsrc & Hwin).
    split.
    - eapply trans_src_ok_sub_ge0; [exact Hsrc | exact Hlo | exact Hbl | exact Hhi].
    - eapply decode_off_win_sub; [exact Hwin | exact Hlo | exact Hhi | exact Hbl]. }
  (* the class counts at the call state *)
  assert (C1 : count_cid SRX_CID (frames S2) + 1 < fs_frames SRX_CID)
    by (rewrite HFRS, pw_count_other by (cbv; congruence); exact HC1).
  assert (C4 : count_cid ONANN_CID (frames S2) < fs_frames ONANN_CID)
    by (rewrite HFRS, pw_count_other by (cbv; congruence); exact HC4).
  assert (C0 : count_cid SENDDATA_CID (frames S2) < fs_frames SENDDATA_CID)
    by (rewrite HFRS, pw_count_other by (cbv; congruence); exact HC0).
  assert (C2 : count_cid ONDATA_CID (frames S2) + 2 < fs_frames ONDATA_CID)
    by (rewrite HFRS, pw_count_other by (cbv; congruence); exact HC2).
  assert (C5 : count_cid TICK_CID (frames S2) < fs_frames TICK_CID).
  { change TICK_CID with POLL_CID. rewrite HFRS, pw_count_own. clear - HC5. lia. }
  assert (HEVr : st_nev (cx_S c) + cx_k c + SRX_EV <= EV_MAX) by (rewrite srx_ev_zero; exact HEV).
  pose proof (HRXc fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c) regsC (pw_F c pos + 32) now r2 got (cx_TF c) Bx B2
    HJ RA RAZ R3 R4 R10 R11 R12 R13 SP16 WS1 SPLE0 Hnow HB0 HG8 HSRC HOFFW HNG HTW HGF HM HTFs HOFF HROM HSAP
    I1 I2 I7 I3 I6 I4 I5 HP3 C1 C4 C5 C0 C2 HEVr) as HCALL.
  eapply SRr_mono; [exact HCALL|].
  intros W3 c3 _ HPOST.
  unfold transport_srx_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HPR3 & Hfr3 & Hperm3 & HK3c & Hmo3 & _ &
    Htw3 & Hgf3).
  rewrite srx_ev_zero in He. assert (He0 : e = 0) by (clear - He; lia). subst e.
  exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HPR3|].
  pose proof (tw_len _ _ _ HTW) as HLB.
  apply (pw_run_gcall B MT c pos ly2 S2 W2 mem2 md2 Bx regsC SRX_STK (srx_wr got) ly3 S3 W3 mem3 md3 B2
    HRT HOK HRUN USP HS0 WS3).
  - intros a Ha. left. exact (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ got Ha)))))).
  - exact HJ3.
  - exact Hfr3.
  - exact Hperm3.
  - exact HK3c.
  - exact Hmo3.
  - exact Htw3.
  - exact Hgf3.
  - exact (HK1 timg_B (cx_TF c) Bx got now B2 r2 HLB HINV HM).
  - rewrite (HK3 timg_B (cx_TF c) Bx got now B2 r2 HLB HM). exact HGRX.
Qed.

(* The call of diginet_session_tick at 0x8ad28: its statement at the call state in the same G journal, with TF and
   the read-only bytes at the call state (the kit), tick_apart from poll_apart, the run invariants from TRI.run_inv,
   and the class counts (class 5 with the own frame on top; class 0 and class 2 those of the caller's frames). Its
   post gives pw_run at its world B3 (pw_run_gcall; TRI.run_inv and g_rx by pw_keep). *)
Lemma pw_tick_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word)
    (now : Z) (B3 : list byte) (r3 : Z),
  pw_rt B MT -> pw_keep -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  YK11.getr regsC 10 = w64 POLL_S -> YK11.getr regsC 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  TSS.diginet_session_tick_m timg_B (cx_TF c) Bx now = Some (B3, r3) ->
  SRr segs W2 (@cfg_at fx segs (transportb_sigma TB_diginet_session_tick) regsC mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\
       pw_run B MT c pos ly3 S3 W3 mem3 md3 B3).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC now B3 r3 HRT HKP HOK HRUN R2 R3 R4 RA RAZ R10 R11 Hnow HM.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTKc & _).
  pose proof HKP as (_ & HK2 & _ & HK4 & _ & _).
  pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAP & _ & _ & _ &
    HC5 & _ & _ & HC0 & HC2 & HEV).
  pose proof HRUN as (HCUR & _ & _ & _).
  pose proof HCUR as (HJ & HFRS & _ & _ & _ & _ & _ & _ & _ & _ & HTW & HGF & HINV & HGRX).
  pose proof HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  destruct (pw_call_win c regsC HOK R2) as (USP & SP16 & SPLE0 & SPLE & _ & HT0 & _ & _ & _ & WT1 & WT2 & WT3).
  pose proof (pw_tf_at B MT c pos ly2 S2 W2 mem2 md2 Bx regsC TICK_STK HRT HOK HCUR WT2 SPLE) as HTFs.
  pose proof (pw_rom_at B MT c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR) as HROM.
  (* tick_wr Bx is a row of poll_wr *)
  assert (HTAP : tick_apart (cx_TF c) Bx).
  { intros x Hx fr Hfr.
    exact (HAP x (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ Bx Hx)))))) fr Hfr). }
  (* the class counts at the call state *)
  assert (C5 : count_cid TICK_CID (frames S2) < fs_frames TICK_CID).
  { change TICK_CID with POLL_CID. rewrite HFRS, pw_count_own. clear - HC5. lia. }
  assert (C0 : count_cid SENDDATA_CID (frames S2) < fs_frames SENDDATA_CID)
    by (rewrite HFRS, pw_count_other by (cbv; congruence); exact HC0).
  assert (CB : count_cid TRANS_BC_CID (frames S2) < fs_frames TRANS_BC_CID).
  { change TRANS_BC_CID with ONDATA_CID. rewrite HFRS, pw_count_other by (cbv; congruence). clear - HC2. lia. }
  assert (HEVt : st_nev (cx_S c) + cx_k c + TICK_EV <= EV_MAX) by (change TICK_EV with POLL_EV; exact HEV).
  pose proof (HTKc fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c) regsC now r3 (cx_TF c) Bx B3
    HJ RA RAZ R3 R4 R10 R11 SP16 WT1 SPLE0 Hnow HTW HGF HM HTFs HROM HTAP
    I1 I2 I7 I3 I6 I4 I5 C5 C0 CB HEVt) as HCALL.
  eapply SRr_mono; [exact HCALL|].
  intros W3 c3 _ HPOST.
  unfold transport_tick_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HPR3 & Hfr3 & Hperm3 & HK3c & Hmo3 & _ &
    Htw3 & Hgf3).
  unfold TICK_EV in He. assert (He0 : e = 0) by (clear - He; lia). subst e.
  exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HPR3|].
  pose proof (tw_len _ _ _ HTW) as HLB.
  apply (pw_run_gcall B MT c pos ly2 S2 W2 mem2 md2 Bx regsC TICK_STK (tick_wr Bx) ly3 S3 W3 mem3 md3 B3
    HRT HOK HRUN USP HT0 WT3).
  - intros a Ha. left. exact (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ Bx Ha)))))).
  - exact HJ3.
  - exact Hfr3.
  - exact Hperm3.
  - exact HK3c.
  - exact Hmo3.
  - exact Htw3.
  - exact Hgf3.
  - exact (HK2 timg_B (cx_TF c) Bx now B3 r3 HLB HINV HM).
  - rewrite (HK4 timg_B (cx_TF c) Bx now B3 r3 HLB HM). exact HGRX.
Qed.

End c.
