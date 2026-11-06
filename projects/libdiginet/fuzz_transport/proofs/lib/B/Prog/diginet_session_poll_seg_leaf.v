(* diginet_session_poll_seg_leaf: the two leaf calls of the image-B walk of diginet_session_poll
   (lib/B/Prog/diginet_session_poll_segs.v), from a state of pw_run at the realigned sp1, each at the callee's entry
   with ra the return address, through the callee's statement read at this unit's model (DgnTransportBCg.v
   transport_leaf_at), TransportGCg.v gx_call_leaf and the leaf bridge (DgnTransportBLeafb.v):
   - pw_now_call: io_now (io_now_cg.v transport_io_now_cg at TI.ti_io_now timg_B; the jalr at 0x8ac5c, 0x8acfc and
     0x8ad7c): a0 = io_now_m of the world;
   - pw_deadline_call: diginet_session_deadline (diginet_session_deadline_cg.v at transportb_sigma
     TB_diginet_session_deadline; the jal at 0x8ac6c): a0 = the model's deadline.
   Each returns at the same state and world with pw_run at the new memory, the callee-saved registers kept, and every
   byte outside the leaf's window [sp1 - ESTACK, sp1) kept. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg DgnTransportBLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBCgRun LeafCgKit AsanKA check_state_wake_c io_now_c diginet_session_deadline_c.
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
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_now_cg.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_cg.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
Module PCR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBCgRun.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LINc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_now_c.
Module LSDc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_c.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* Every byte of the harness globals' hull lies in a loaded segment of image B, so no world hides it. *)
Lemma pcl_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. replace x with (TG.G_HARNESS_B_LO + (x - TG.G_HARNESS_B_LO)) by lia.
  apply (LB.decode_leafb_covers_visible (w_H W) TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO));
    [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory (the leaves' csw_view). *)
Lemma pcl_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_B (CSW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  unfold CSW.csw_view. rewrite (PCR.decode_aview_mrd W mem x (pcl_hull_vis W x (TMAP_B_hull x Hx))).
  reflexivity.
Qed.

(* A leaf's footprint holds every range of the hull. *)
Lemma pcl_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  LB.LExecF.rng (LB.LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply LB.decode_leafb_rng;
    [unfold TG.G_HARNESS_B_LO in H1; lia | unfold TG.G_HARNESS_B_HI in H2; lia |].
  intros a Ha. apply pcl_hull_vis. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* g_s's payload is addressable at every AR state: the shadow of its whole granules is 0 (trans_poll_cells). *)
Lemma pcl_gs_ra : forall ly S (W : world segs) mem md,
  trans_poll_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TB_g_s TW.SZ_g_s.
Proof using All.
  intros ly S W mem md HZ HAR x Hx. unfold TB_g_s, TW.SZ_g_s in Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md TB_g_s (TB_g_s + TW.SZ_g_s) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TB_g_s; lia) ltac:(unfold TB_g_s, TW.SZ_g_s; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* A leaf called at the realigned sp1 from a state of pw_run, in the walk's G journal: TransportGCg.v gx_call_leaf
   lifts the leaf bridge DgnTransportBLeafb.v decode_leafb_journal (the callee's dleaf_post with WR = [] and result
   v), whose premise is the callee's statement at the call state, given here with the facts every leaf asks: sp = sp1,
   sp1 far above the image and alloc_ceiling, the ESTACK bytes below sp1 present (stk) and visible (rng), AR, and the
   world relation at the raw memory. The leaf keeps every byte outside [sp1 - ESTACK, sp1), so pw_run holds at the
   memory it returns (pw_run_win). *)
Lemma pw_leaf_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word) (PC v : Z),
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) ->
  (LB.decode_leafb_ecall_pre B ly2 S2 W2 regsC mem2 md2 ->
   bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = pw_sp1 c ->
   2 ^ 45 <= pw_sp1 c -> alloc_ceiling + ESTACK <= pw_sp1 c -> pw_sp1 c + 160 <= 2 ^ 47 ->
   LB.LFrame.stk segs mem2 (pw_sp1 c - ESTACK) (pw_sp1 c) ->
   (forall lo len, pw_sp1 c - ESTACK <= lo -> lo + len <= pw_sp1 c ->
      LB.LExecF.rng (LB.LCK.RNG_W (world segs) (@w_H segs) W2) lo len) ->
   @AR rc segs B ly2 S2 W2 mem2 md2 ->
   tw_at TMAP_B (CSW.csw_view mem2) Bx ->
   SRr segs W2 (@LCK.cfg_at fx PC regsC mem2 md2)
     (@LB.decode_leafb_post fx rc B ly2 S2 W2 regsC mem2 md2 (Some v) [] (fun _ => True))) ->
  SRr segs W2 (@cfg_at fx segs PC regsC mem2 md2)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\ YK11.getr regs3 10 = w64 v /\
       pw_run B MT c pos ly2 S2 W2 mem3 md3 Bx /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (pw_sp1 c - ESTACK <= a < pw_sp1 c) ->
          aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) /\
       (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC PC v HRT HOK HRUN H2 H3 H4 HRA HLEAF.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
  pose proof HRUN as ((HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTW & _) & _).
  (* pw_ok_sp's statement names no meter: MT is its argument only while the kit's section keeps it *)
  pose proof (pw_ok_sp B) as SPK. try specialize (SPK MT).
  pose proof (SPK c HOK) as (_ & HSPr & HCE & _ & _ & HSP1 & HM0 & HSTK & HSP0 & HPS & HEI & HIS & _). clear SPK.
  assert (USP : spZ regsC = pw_sp1 c).
  { change (spZ regsC) with (bv_unsigned (YK11.getr regsC 2)). rewrite H2. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (SPU : bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = pw_sp1 c) by exact USP.
  assert (M16 : pw_sp1 c mod 16 = 0).
  { unfold pw_sp1.
    replace (32 * ((pw_SP c - POLL_FRAME) / 32)) with (2 * ((pw_SP c - POLL_FRAME) / 32) * 16) by ring.
    apply Z_mod_mult. }
  assert (HSO : (pw_sp1 c - cx_sp0 c) mod 16 = 0) by (rewrite Zminus_mod, M16, HM0; reflexivity).
  assert (WIN : cx_sp0 c - cx_STK c <= pw_sp1 c - ESTACK) by lia.
  assert (SP0 : pw_sp1 c <= cx_sp0 c) by lia.
  assert (LO : 2 ^ 45 <= pw_sp1 c) by lia.
  assert (CE : alloc_ceiling + ESTACK <= pw_sp1 c) by lia.
  assert (TOP : pw_sp1 c + 160 <= 2 ^ 47) by lia.
  eapply SRr_mono.
  { eapply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c)
      (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c) _
      (YK11.getr regsC 1) _ HJ).
    intros memS HJS.
    apply (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W2 regsC mem2 (cx_STK c) (cx_sp0 c) (cx_FP c)
      (cx_ly c) (cx_S c) (cx_W0 c) memS (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly2 S2 md2 (cx_k c)
      (pw_sp1 c - cx_sp0 c) PC (Some v) [] (fun _ => True) HJS).
    - rewrite USP. lia.
    - exact HSO.
    - lia.
    - lia.
    - exact HRA.
    - exact H3.
    - exact H4.
    - intros a Ha. inversion Ha.
    - intros HPRE. apply HLEAF.
      + exact HPRE.
      + exact SPU.
      + exact LO.
      + exact CE.
      + exact TOP.
      + apply (LB.decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS); [exact WIN | exact SP0].
      + intros lo len Hlo Hhi.
        apply (LB.decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS); lia.
      + exact (proj1 HJS).
      + exact (pcl_tw_csw W2 mem2 Bx HTW). }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HR3 & HK3 & HG3 & _).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (pw_sp1 c - ESTACK <= a < pw_sp1 c) ->
            aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. apply HK3; [exact Ha | rewrite USP; exact Hn | intros Hw; inversion Hw]. }
  split; [reflexivity|]. exists regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HP3|]. split; [exact (HR3 v eq_refl)|].
  split; [exact (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 Bx mem3 md3 HRT HOK HRUN HJ3 KEEP HG3)|].
  split; [exact KEEP | exact HG3].
Qed.

Lemma pw_now_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word),
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  SRr segs W2 (@cfg_at fx segs (TI.ti_io_now timg_B) regsC mem2 md2)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\ YK11.getr regs3 10 = w64 (TC.io_now_m Bx) /\
       pw_run B MT c pos ly2 S2 W2 mem3 md3 Bx /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (pw_sp1 c - ESTACK <= a < pw_sp1 c) ->
          aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) /\
       (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC HRT HOK HRUN H2 H3 H4 HRA _.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNOW & _).
  rewrite <- LIN.io_now_at_timg.
  apply (pw_leaf_call c pos ly2 S2 W2 mem2 md2 Bx regsC LINc.IO_NOW (TC.io_now_m Bx) HRT HOK HRUN H2 H3 H4 HRA).
  intros HPRE SPU LO CE TOP HSTK HRNG HAR HTW.
  pose proof (HNOW fx) as LF. unfold transport_leaf_at, LIN.transport_io_now_cg in LF.
  specialize (LF ly2 S2 W2 regsC mem2 md2 (pw_sp1 c - ESTACK) Bx HPRE). cbv zeta in LF.
  rewrite SPU in LF.
  apply LF; clear LF.
  - exact HTW.
  - exact HSTK.
  - unfold LINc.IO_NOW_FRAME, ESTACK. lia.
  - apply pcl_rng_hull; unfold LINc.IO_NOW_G_NOW, TB_g_now, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
Qed.

Lemma pw_deadline_call : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word) (now due : Z),
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  YK11.getr regsC 2 = w64 (pw_sp1 c) -> YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  YK11.getr regsC 10 = w64 POLL_S -> YK11.getr regsC 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  TS0.diginet_session_deadline_m Bx now = Some due ->
  SRr segs W2 (@cfg_at fx segs (transportb_sigma TB_diginet_session_deadline) regsC mem2 md2)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsC 1) mem3 (YK11.seg_rom segs)) md3 /\
       aregs_preserved regsC regs3 /\ YK11.getr regs3 10 = w64 due /\
       pw_run B MT c pos ly2 S2 W2 mem3 md3 Bx /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (pw_sp1 c - ESTACK <= a < pw_sp1 c) ->
          aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) /\
       (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)).
Proof using All.
  intros c pos ly2 S2 W2 mem2 md2 Bx regsC now due HRT HOK HRUN H2 H3 H4 HRA _ H10 H11 Hnow HD.
  pose proof HRT as (_ & HCELLS & HPC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDL & _).
  rewrite <- LSD.diginet_session_deadline_at_sigma.
  apply (pw_leaf_call c pos ly2 S2 W2 mem2 md2 Bx regsC LSDc.DIGINET_SESSION_DEADLINE due HRT HOK HRUN H2 H3 H4 HRA).
  intros HPRE SPU LO CE TOP HSTK HRNG HAR HTW.
  pose proof (pcl_gs_ra ly2 S2 W2 mem2 md2 HPC HAR) as HRAD.
  pose proof (LB.decode_leafb_asan_cells B HCELLS ly2 S2 W2 mem2 md2 HAR) as HAC.
  pose proof (LB.decode_leafb_rng_cells W2) as (RGOT & RCELL).
  pose proof (HDL fx) as LF. unfold transport_leaf_at, LSD.transport_diginet_session_deadline_cg in LF.
  specialize (LF ly2 S2 W2 regsC mem2 md2 (pw_sp1 c - ESTACK) now due Bx HPRE). cbv zeta in LF.
  unfold AKA.off_stk in LF. rewrite SPU in LF.
  apply LF; clear LF.
  - exact H10.
  - exact H11.
  - exact Hnow.
  - exact HTW.
  - exact HD.
  - exact HSTK.
  - unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, ESTACK. lia.
  - left. unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
  - apply (@LB.decode_leafb_app_stack rc). unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, ESTACK in *. lia.
  - apply (@LB.decode_leafb_app_stack rc). unfold ESTACK in *. lia.
  - exact HAC.
  - left. unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, FCells.GOT_CELL_K. lia.
  - left. unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, FCells.CELL_K. lia.
  - apply (LB.decode_leafb_addressable W2 mem2 TB_g_s TW.SZ_g_s HRAD);
      [unfold TB_g_s; lia | unfold TW.SZ_g_s; lia | unfold TB_g_s, TW.SZ_g_s, FCells.APPMEM_END; lia |].
    intros i Hi. unfold FCells.app_mem, FCells.LOWMEM_END, TB_g_s, TW.SZ_g_s in *. lia.
  - apply HRNG; unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, ESTACK; lia.
  - exact RGOT.
  - exact RCELL.
  - apply pcl_rng_hull; unfold LSDc.DIGINET_SESSION_DEADLINE_S, LSDc.DIGINET_SESSION_DEADLINE_SN, TB_g_s,
      TW.SZ_g_s, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
  - apply (LB.decode_leafb_rng_shadow W2 mem2 TB_g_s TW.SZ_g_s HRAD); unfold TB_g_s, TW.SZ_g_s; lia.
Qed.

End c.
