(* LLVMFuzzerTestOneInput_kit_dn_each: the kit statement K5 of the image-B walk of LLVMFuzzerTestOneInput
   (LLVMFuzzerTestOneInput_segs.v lc_dn_each_stmt): receive's run invariant (3), receive_cg.v recv_dn_each, at a world
   where TSim/Agree.v agree timg_B holds. The proof is about the model only (TModel, TSim); it reads no memory and no
   journal, and no image constant: every lemma below holds at any image I, and K5 takes I = timg_B.

   - dn_core: one reception. At the world m_rx starts from (TSim/RxBase.v rx_pre_g), when m_rx returns Bx and the
     guards of diginet_session_poll_cg.v poll_dn_in hold at Bx (the library accepts a data frame that is not a
     duplicate and not a keepalive), the model took the same path: the guards are library fields (g_s), which m_rx
     does not write (rx_ok_g's frame R_mod) and which agree_st ties to the model's fields, so they give
     rx_accepts. On that path (RxFlt.v rx_accept_path_g, RxData.v rx_data_g for the quiet tick) m_rx's DATA arm
     (RxData.v rxdata_m_eq, rxdata_mB4_ok, rxdata_mtail_ok) wrote OW.dn[OW.ndata].body = tf_addr + 30, and m_rx does
     not write GOT, so GOT.ndata = OW.ndata (ow_room). The body ends inside the frame (RxFrame.v rf_blen).
   - dn_recv0: the by_poll = 0 path, at the world RxOpLib.v rxop_begin gives.
   - dn_poll: the by-poll path with g_rx_fail = 0 (diginet_session_poll_cg.v poll_rx_each). It walks the hand-overs
     as RxOpLib.v rxop_poll_ok's proof does: io_recv (rxop_io_recv) runs m_rx from the world Y1 = g_rx_times - 1, so
     the first hand-over's P is dn_core at Y1 (rx_pre_g from rxop_pre_poll); the library's rx and the tick follow
     (rx_ok_g, TickOk.v tick_quiet_keep); with g_rx_times = 2 the drain's one turn hands the frame over again from
     Y2 = set_g_rx_times W2 0, with the rx_pre_g of rxop_poll_ok's proof (ow_room_after, rx_accepts_same,
     tick_quiet_off) carried to Y2 by rxop_pre_g_poll, and its P is dn_core at Y2. An empty frame hands nothing over
     (r = 0).
   - dn_fail_set: g_rx_fail = 1, io_recv answers -EIO at once, and poll_rx_each asks nothing.
   Each world-carrying option is inverted by dn_some1 / dn_some2 / dn_some3. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  receive_cg diginet_session_poll_cg diginet_session_rx_cg on_data_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0
  TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links LinksProof SimLib QueueFacts
  SettleOk Deadline TickDefs TickOk SubmitLib RxDefs RxBase RxList RxFrame RxW RxCore RxFlt RxData RxOk RxOpLib.
Import ListNotations.
Open Scope Z_scope.
Module RCG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.receive_cg.
Module PCG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_poll_cg.
Module SRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_rx_cg.
Module ODC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_cg.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

(* ---- inversions of an option, applied by name ---- *)

Lemma dn_some1 : forall {A : Type} {x y : A}, Some x = Some y -> x = y.
Proof. intros A x y H. injection H as E. exact E. Qed.

Lemma dn_some2 : forall {A C : Type} {x x' : A} {y y' : C}, Some (x, y) = Some (x', y') -> x = x' /\ y = y'.
Proof. intros A C x x' y y' H. injection H as E1 E2. exact (conj E1 E2). Qed.

Lemma dn_some3 : forall {A C D : Type} {x x' : A} {y y' : C} {z z' : D},
  Some (x, y, z) = Some (x', y', z') -> x = x' /\ y = y' /\ z = z'.
Proof. intros A C D x x' y y' z z' H. injection H as E1 E2 E3. exact (conj E1 (conj E2 E3)). Qed.

(* ---- one reception: poll_dn_in at the world m_rx leaves ---- *)

Lemma dn_core : forall I ops fr n B Bx t,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_pre_g I ops B (rxbuf fr n) -> m_rx_m I (Some fr) B n = Some (Bx, t) ->
  PCG.poll_dn_in (Some fr) Bx (rxbuf fr n).
Proof.
  intros I ops fr n B Bx t Hn Ha Hpre Em.
  pose proof links_holds as HL.
  unfold PCG.poll_dn_in. intros Gc Gmac Gk Gsrc Gst Gcmd Gdup Gka.
  pose proof Hpre as [Hcore Hka Hroom _ _].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (wr_og _ Hroom) as Hog.
  (* m_rx writes M and OW (and GOT's range) only: the library's fields at Bx are those at B *)
  destruct (rx_ok_g HL I ops fr n B Hn Ha Hpre) as (Bx0 & t0 & Em0 & _ & HfM & _).
  rewrite Em in Em0. destruct (dn_some2 Em0) as [EB _]. subst Bx0.
  assert (S1 : S_desk_known Bx = S_desk_known B) by fget HfM.
  assert (S2 : S_desk_mac Bx = S_desk_mac B) by fget HfM.
  assert (S3 : S_state Bx = S_state B) by fget HfM.
  assert (S4 : S_cfg_host_mac Bx = S_cfg_host_mac B) by fget HfM.
  assert (S5 : S_desk_counter_valid Bx = S_desk_counter_valid B) by fget HfM.
  assert (S6 : S_desk_counter Bx = S_desk_counter B) by fget HfM.
  (* the guards give rx_accepts B *)
  assert (Hcode : fr_code (rxbuf fr n) = DIGINET_OK) by exact Gc.
  pose proof (rx_frame_ok HL fr n Hn Hcode) as Hf.
  assert (Hk1 : M_desk_known B = 1).
  { rewrite S1, (b2_desk_known _ Hst) in Gk.
    destruct (b2_desk_known01 _ Hst) as [E|E]; [exfalso; exact (Gk E) | exact E]. }
  assert (Ldm : length (M_desk B) = 6%nat).
  { unfold M_desk. apply length_sub; [wnum | rewrite HB; wnum]. }
  assert (Esrc : fr_src (rxbuf fr n) = M_desk B).
  { rewrite S2, (b2_desk_mac _ Hst Hk1), (rx_memeq_src fr n (M_desk B) Hn Hcode Ldm) in Gsrc.
    exact (RxFlt_beq_eq _ _ Gsrc). }
  assert (LH : length HOST = 6%nat) by reflexivity.
  assert (LBc : length BROADCAST = 6%nat) by reflexivity.
  unfold SRX.srx_mac_bad in Gmac.
  rewrite S4, (a2_host_mac B Hcfg) in Gmac.
  rewrite (rx_memeq_src fr n HOST Hn Hcode LH), (rx_memeq_dst fr n HOST Hn Hcode LH),
    (rx_memeq_dst fr n BROADCAST Hn Hcode LBc), rx_broadcast in Gmac.
  apply orb_false_iff in Gmac. destruct Gmac as [Ms Md].
  rewrite S3, (b1_state _ Hst) in Gst.
  assert (Hacc : rx_accepts B (rxbuf fr n)).
  { constructor.
    - exact Hcode.
    - exact Ms.
    - apply andb_false_iff in Md. destruct Md as [Md|Md]; apply negb_false_iff in Md; [left | right]; exact Md.
    - intros _. exact Esrc.
    - intros E. exfalso. rewrite Hk1 in E. discriminate E.
    - exact Gst. }
  (* the model's accept path: the DATA switch and its quiet tick *)
  destruct (rx_accept_path_g HL I ops fr n B Hn Hpre Hacc) as [Ep _].
  pose proof (rx_data_g HL I ops fr n B) as Hdg. cbv zeta in Hdg.
  destruct (Hdg Hn Ha Hpre Hacc Gcmd) as (Bm & Esw & Etk & _). clear Hdg.
  rewrite (RxFlt_learnM_1 B (rxbuf fr n) Hk1) in Ep, Esw.
  rewrite Ep, Esw in Em. cbv beta iota in Em. rewrite Etk in Em. cbv beta iota in Em.
  destruct (dn_some2 Em) as [EBm _]. subst Bx.
  (* the DATA arm (FT:344-365), as rx_data_g computes it *)
  remember (set_M_last_rx B (g_now B)) as X eqn:EX.
  assert (HX : length X = WN) by (subst X; wlen).
  assert (HBX : wframe (in_rs [(A_M_last_rx, 8)]) B X) by (subst X; wfrs).
  assert (A0 : OW_acks X = OW_acks B) by fget HBX.
  assert (N0 : OW_ndata X = OW_ndata B) by fget HBX.
  assert (XMv : M_desk_counter_valid X = M_desk_counter_valid B) by fget HBX.
  assert (XMc : M_desk_counter X = M_desk_counter B) by fget HBX.
  assert (Rak : 0 <= OW_acks B <= 1).
  { pose proof (og_acks_range _ Hog) as R1. pose proof (wr_acks _ Hroom) as R2. clear - R1 R2. lia. }
  assert (Rak2 : 0 <= OW_acks B + 1 <= 2) by (clear - Rak; lia).
  assert (Rnd : 0 <= OW_ndata B <= 1).
  { pose proof (og_ndata_range _ Hog) as R1. pose proof (wr_ndata _ Hroom) as R2. clear - R1 R2. lia. }
  assert (Hcm : sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_DATA)
    by (rewrite (rf_cmd _ _ Hf); exact Gcmd).
  rewrite (rxdata_m_eq I fr n X Hcm), A0, (rxdata_inc (OW_acks B) Rak) in Esw. cbv beta iota in Esw.
  rewrite (rf_retry _ _ Hf) in Esw.
  destruct (rxdata_mB4_ok X (fr_retry (rxbuf fr n)) (OW_acks B + 1) HX Rak2) as (Hf4 & _ & _ & _).
  destruct (rxdata_mtail_ok fr n X (rxdata_mB4 X (fr_retry (rxbuf fr n)) (OW_acks B + 1)) (OW_ndata B) Hn Ha Hf
              Gcmd Hf4 HX N0 Rnd) as (Bm' & Em' & Hfm & _ & _ & _ & _ & Md').
  rewrite Em' in Esw. destruct (dn_some2 Esw) as [EBm' _]. subst Bm'.
  pose proof (wframe_trans_rs _ _ _ _ _ Hf4 Hfm) as HXm.
  pose proof (wframe_trans_rs _ _ _ _ _ HBX HXm) as Hm.
  assert (GN : GOT_ndata Bm = OW_ndata B).
  { transitivity (GOT_ndata B); [fget Hm | exact (og_ndata _ Hog)]. }
  (* the library's duplicate test is the model's (B6) *)
  assert (Edup : rxdata_dupM X (rxbuf fr n) = false).
  { unfold rxdata_dupM. rewrite XMv, XMc.
    unfold ODC.ondata_dup in Gdup. rewrite S5, S6, (b6_valid _ Hst) in Gdup.
    rewrite (rxdata_dup_eq _ _ _ _ _ (b6_valid01 _ Hst) (b6_counter _ Hst)) in Gdup. exact Gdup. }
  destruct (Md' Edup Gka) as (_ & DB & _).
  exists fr. split; [reflexivity|].
  rewrite GN, DB. pose proof (rf_blen _ _ Hf) as Hbl. clear - Hbl Hn. lia.
Qed.

(* ---- receive (p, n, 0, 0): the call of diginet_session_rx at the world m_rx leaves ---- *)

Lemma dn_recv0 : forall I ops B1 a bytes Bx t,
  0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  rx_pre I ops (set_g_rx_send B1 (rxop_v bytes)) bytes ->
  m_rx_m I (Some (TFrame a bytes)) (set_g_rx_send B1 (rxop_v bytes)) (Z.of_nat (length bytes)) = Some (Bx, t) ->
  PCG.poll_dn_in (Some (TFrame a bytes)) Bx bytes.
Proof.
  intros I ops B1 a bytes Bx t Ha0 Ha1 Hpre Em.
  assert (Hpre0 : rx_pre_g I ops (set_g_rx_send B1 (rxop_v bytes))
                    (rxbuf (TFrame a bytes) (Z.of_nat (length bytes)))).
  { apply rx_pre_g_of. rewrite (rxbuf_all a bytes). exact Hpre. }
  assert (Hn : 0 <= Z.of_nat (length bytes) <= Z.of_nat (length (tf_bytes (TFrame a bytes))))
    by (cbn [tf_bytes]; lia).
  assert (Hfa : 0 < tf_addr (TFrame a bytes) /\
                tf_addr (TFrame a bytes) + Z.of_nat (length (tf_bytes (TFrame a bytes))) < 2 ^ 64)
    by (cbn [tf_addr tf_bytes]; lia).
  pose proof (dn_core I ops (TFrame a bytes) (Z.of_nat (length bytes)) _ Bx t Hn Hfa Hpre0 Em) as H.
  rewrite (rxbuf_all a bytes) in H. exact H.
Qed.

(* ---- receive (p, n, 1, flags) ---- *)

(* flags bit 1 set: io_recv fails at once (FT:910-913), so no call of diginet_session_rx follows *)
Lemma dn_fail_set : forall I F P X, length X = WN -> PCG.poll_rx_each I F P (set_g_rx_fail X 1).
Proof.
  intros I F P X HX. unfold PCG.poll_rx_each. intros B1 r1 g1 Hr Hr0. exfalso.
  assert (Hf : g_rx_fail (set_g_rx_fail X 1) = 1) by wget.
  unfold call_recv in Hr. revert Hr.
  destruct (S_io_recv (set_g_rx_fail X 1) =? ti_io_recv I); intros Hr; [|discriminate Hr].
  unfold io_recv_m in Hr. rewrite Hf in Hr. change (truth 1) with true in Hr. cbv beta iota in Hr.
  destruct (dn_some3 Hr) as (_ & Er & _). subst r1. unfold EIO in Hr0. clear - Hr0. lia.
Qed.

(* flags bit 1 clear: the hand-overs of the poll (DS:505-527), as RxOpLib.v rxop_poll_ok walks them *)
Lemma dn_poll : forall I ops a bytes got times B2a,
  0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 -> 0 <= got <= 1514 -> got <= Z.of_nat (length bytes) ->
  (times = 1 \/ times = 2) -> rx_pre I ops B2a (rxbuf (TFrame a bytes) got) ->
  PCG.poll_rx_each I (Some (TFrame a bytes)) (PCG.poll_dn_in (Some (TFrame a bytes)))
    (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 0).
Proof.
  intros I ops a bytes got times B2a Ha0 Ha1 Hg Hgl Htm Hpre.
  pose proof links_holds as HL.
  assert (Ht12 : 1 <= times <= 2) by (destruct Htm; lia).
  pose proof (rp_core _ _ _ _ Hpre) as Hc.
  assert (HBa : length B2a = WN) by exact (ac_len _ _ _ Hc).
  pose proof (ac_io _ _ _ Hc) as Hio.
  assert (Ha64 : a < 18446744073709551616) by lia.
  assert (Hn : 0 <= got <= Z.of_nat (length (tf_bytes (TFrame a bytes)))) by (cbn [tf_bytes]; lia).
  assert (Hfa : 0 < tf_addr (TFrame a bytes) /\
                tf_addr (TFrame a bytes) + Z.of_nat (length (tf_bytes (TFrame a bytes))) < 2 ^ 64)
    by (cbn [tf_addr tf_bytes]; lia).
  set (B2c := set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a a) got) times) 0).
  assert (HBc : length B2c = WN) by (unfold B2c; wlen).
  assert (HfP : wframe (in_rs R_poll) B2a B2c) by (unfold B2c; wfrs).
  assert (Cf : g_rx_fail B2c = 0) by (unfold B2c; wget).
  assert (Cr : g_rx B2c = a) by (unfold B2c; wget).
  assert (Ct : g_rx_times B2c = times) by (unfold B2c; wget).
  assert (Cl : g_rx_len B2c = got) by (unfold B2c; wget).
  assert (Ic : S_io_recv B2c = S_io_recv B2a) by fget HfP.
  (* the world of the first hand-over (FT:916: g_rx_times decremented) *)
  set (Y1 := set_g_rx_times B2c (times - 1)).
  assert (HY1 : wframe (in_rs R_poll) B2a Y1) by (unfold Y1, B2c; wfrs).
  pose proof (rxop_pre_poll I ops B2a Y1 _ Hpre HY1) as Hpre1.
  pose proof (rp_core _ _ _ _ Hpre1) as Hc1.
  assert (R1 : g_rx Y1 = a) by (transitivity (g_rx B2c); [unfold Y1; wget | exact Cr]).
  assert (F1 : g_rx_fail Y1 = 0) by (transitivity (g_rx_fail B2c); [unfold Y1; wget | exact Cf]).
  assert (T1 : g_rx_times Y1 = times - 1) by (unfold Y1; wget).
  assert (L1 : g_rx_len Y1 = got) by (transitivity (g_rx_len B2c); [unfold Y1; wget | exact Cl]).
  assert (I1 : S_io_now_us Y1 = S_io_now_us B2a) by fget HY1.
  (* a tick's writes miss the receive's scalars, g_rx_send, OW and GOT (TickDefs.v R_tick) *)
  assert (HRt : forall x, OFF_g_rx_send <= x < OFF_g_cfg -> ~ R_tick x)
    by (intros x Hx; unfold R_tick; revert Hx; wunf_off; intros; lia).
  assert (HRo : forall x, OFF_GOT <= x < OFF_OW + SZ_OW -> ~ R_tick x)
    by (intros x Hx; unfold R_tick; revert Hx; wunf_off; intros; lia).
  unfold PCG.poll_rx_each. intros B1 r1 g1 Hr1 Hr1n.
  destruct (Z.eqb_spec got 0) as [G0|G0].
  - (* an empty frame: io_recv runs m_tick (FT:925-926) and hands nothing over; then the poll's tick *)
    assert (Tq1 : m_tick_m Y1 = Some (Y1, tt)) by exact (rxop_tick_quiet I ops Y1 Hc1).
    assert (Er : call_recv I (Some (TFrame a bytes)) B2c DIGINET_MAX_FRAME_LEN = Some (Y1, 0, [])).
    { unfold call_recv. rewrite Ic, (a3_io_recv _ _ Hio), (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
      exact (rxop_io_recv I a bytes B2c 0 times Y1 HBc Cf Cr Ct Ht12 ltac:(rewrite Cl; exact G0) Ha0
               ltac:(lia) ltac:(lia) Tq1 R1). }
    rewrite Er in Hr1. destruct (dn_some3 Hr1) as (E1 & E2 & E3). subst B1 r1 g1.
    split; [intros Hlt; exfalso; exact (Z.lt_irrefl 0 Hlt) |].
    intros now B2 B3 r3 Hnow Hb2 Htick.
    change (0 <? 0) with false in Hb2. cbv beta iota in Hb2. subst B2.
    assert (Pn1 : call_now I Y1 = Some (g_now Y1)).
    { unfold call_now. rewrite I1, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
      unfold io_now_m. reflexivity. }
    rewrite Pn1 in Hnow. pose proof (dn_some1 Hnow) as En. subst now.
    destruct (tick_quiet_keep HL I (Some (TFrame a bytes)) ops Y1 Hc1) as (W2 & r2 & Etk & Htp & _).
    rewrite Etk in Htick. destruct (dn_some2 Htick) as [E4 _]. subst B3.
    pose proof (tp_frame _ _ _ _ Htp) as HfT.
    pose proof (tp_core _ _ _ _ Htp) as Hc2.
    assert (HW2n : length W2 = WN) by exact (ac_len _ _ _ Hc2).
    assert (T2 : g_rx_times W2 = times - 1) by (rewrite <- T1; rxop_rg HfT HRt).
    assert (F2 : g_rx_fail W2 = 0) by (transitivity (g_rx_fail Y1); [rxop_rg HfT HRt | exact F1]).
    assert (R2 : g_rx W2 = a) by (transitivity (g_rx Y1); [rxop_rg HfT HRt | exact R1]).
    assert (L2 : g_rx_len W2 = 0) by (transitivity (g_rx_len Y1); [rxop_rg HfT HRt | rewrite L1; exact G0]).
    assert (Ti2 : S_io_recv W2 = ti_io_recv I) by exact (a3_io_recv _ _ (ac_io _ _ _ Hc2)).
    rewrite T2.
    destruct Htm as [Et|Et]; subst times.
    + (* one hand-over: the drain loop has no fuel *)
      change (Z.to_nat (1 - 1)) with O. exact Logic.I.
    + (* two: the second hand-over of the empty frame runs m_tick again and hands nothing over *)
      set (Y2 := set_g_rx_times W2 0).
      assert (HY2 : wframe (in_rs R_poll) W2 Y2) by (unfold Y2; wfrs).
      pose proof (grx_poll _ _ HY2) as HG2.
      assert (Hc3 : agree_core I ops Y2) by exact (grx_core _ _ HG2 I ops Hc2).
      assert (R3 : g_rx Y2 = a) by (transitivity (g_rx W2); [unfold Y2; wget | exact R2]).
      assert (Er2 : call_recv I (Some (TFrame a bytes)) W2 DIGINET_MAX_FRAME_LEN = Some (Y2, 0, [])).
      { unfold call_recv. rewrite Ti2, (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
        exact (rxop_io_recv I a bytes W2 0 1 Y2 HW2n F2 R2 T2 ltac:(lia) L2 Ha0 ltac:(lia) ltac:(lia)
                 (rxop_tick_quiet I ops Y2 Hc3) R3). }
      change (Z.to_nat (2 - 1)) with (S O). cbn [PCG.poll_drain_rx].
      intros B1' r' g' Hr' Hpos.
      rewrite Er2 in Hr'. destruct (dn_some3 Hr') as (_ & E5 & _). subst r'.
      exfalso. exact (Z.lt_irrefl 0 Hpos).
  - (* the first hand-over: m_rx (FT:923-924), the library's rx (DS:521), the poll's tick (DS:522) *)
    destruct (rx_ok_g HL I ops (TFrame a bytes) got Y1 Hn Hfa (rx_pre_g_of _ _ _ _ Hpre1))
      as (Bx & t1 & Em & _ & Hf & Hl).
    destruct (Hl Bx (wframe_refl _ _)) as (W1 & q1 & Es & Hd).
    pose proof (rk_done _ _ _ _ _ _ _ Hd) as Hd0.
    assert (Rx : g_rx Bx = a) by (transitivity (g_rx Y1); [fget Hf | exact R1]).
    assert (Er : call_recv I (Some (TFrame a bytes)) B2c DIGINET_MAX_FRAME_LEN =
                 Some (Bx, got, rxbuf (TFrame a bytes) got)).
    { unfold call_recv. rewrite Ic, (a3_io_recv _ _ Hio), (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
      rewrite (rxop_io_recv I a bytes B2c got times Bx HBc Cf Cr Ct Ht12 Cl Ha0 Hg Hgl).
      - destruct (Z.ltb_spec 0 got); [reflexivity | lia].
      - destruct (Z.eqb_spec got 0) as [E|E]; [lia|]. cbv beta iota. exists t1. exact Em.
      - exact Rx. }
    rewrite Er in Hr1. destruct (dn_some3 Hr1) as (E1 & E2 & E3). subst B1 r1 g1.
    split.
    + (* P at the first hand-over *)
      intros _. exact (dn_core I ops (TFrame a bytes) got Y1 Bx t1 Hn Hfa (rx_pre_g_of _ _ _ _ Hpre1) Em).
    + intros now B2 B3 r3 Hnow Hb2 Htick.
      assert (Pg : (0 <? got) = true) by (apply Z.ltb_lt; lia).
      rewrite Pg in Hb2. destruct Hb2 as (q2 & Hb2).
      assert (Nx : g_now Bx = g_now Y1) by fget Hf.
      assert (Pnx : call_now I Bx = Some (g_now Y1)).
      { unfold call_now. assert (Jx : S_io_now_us Bx = S_io_now_us B2a) by (rewrite <- I1; fget Hf).
        rewrite Jx, (a3_io_now _ _ Hio), (Z.eqb_refl (ti_io_now I)). cbv beta iota.
        unfold io_now_m. rewrite Nx. reflexivity. }
      rewrite Pnx in Hnow. pose proof (dn_some1 Hnow) as En. subst now.
      rewrite Es in Hb2. destruct (dn_some2 Hb2) as [E4 _]. subst B2.
      pose proof (rd_core _ _ _ _ _ Hd0) as Hc1'.
      destruct (tick_quiet_keep HL I (Some (TFrame a bytes)) ops W1 Hc1') as (W2 & r2 & Etk & Htp & K1 & K2 & K3).
      assert (Nw1 : g_now W1 = g_now Y1) by (rewrite (rd_now _ _ _ _ _ Hd0); exact Nx).
      rewrite <- Nw1, Etk in Htick. destruct (dn_some2 Htick) as [E5 _]. subst B3.
      pose proof (tp_frame _ _ _ _ Htp) as HfT.
      pose proof (tp_core _ _ _ _ Htp) as Hc2.
      assert (HW2n : length W2 = WN) by exact (ac_len _ _ _ Hc2).
      assert (T2 : g_rx_times W2 = times - 1).
      { rewrite <- T1. transitivity (g_rx_times W1); [rxop_rg HfT HRt|].
        rewrite (rd_rx_times _ _ _ _ _ Hd0). fget Hf. }
      assert (F2 : g_rx_fail W2 = 0).
      { transitivity (g_rx_fail W1); [rxop_rg HfT HRt|].
        rewrite (rd_rx_fail _ _ _ _ _ Hd0). transitivity (g_rx_fail Y1); [fget Hf | exact F1]. }
      assert (R2 : g_rx W2 = a).
      { transitivity (g_rx W1); [rxop_rg HfT HRt|]. rewrite (rd_rx _ _ _ _ _ Hd0). exact Rx. }
      assert (L2 : g_rx_len W2 = got).
      { transitivity (g_rx_len W1); [rxop_rg HfT HRt|].
        rewrite (rd_rx_len _ _ _ _ _ Hd0). transitivity (g_rx_len Y1); [fget Hf | exact L1]. }
      assert (Ti2 : S_io_recv W2 = ti_io_recv I) by exact (a3_io_recv _ _ (ac_io _ _ _ Hc2)).
      rewrite T2.
      destruct Htm as [Et|Et]; subst times.
      * (* one hand-over: the drain loop has no fuel *)
        change (Z.to_nat (1 - 1)) with O. exact Logic.I.
      * (* two hand-overs: the drain loop's turn (DS:524-525) runs m_rx again from Y2 = W2 with
           g_rx_times = 0; rx_pre_g there as in rxop_poll_ok *)
        set (Y2 := set_g_rx_times W2 0).
        assert (HY2 : wframe (in_rs R_poll) W2 Y2) by (unfold Y2; wfrs).
        assert (Hpg2 : rx_pre_g I ops W2 (rxbuf (TFrame a bytes) got)).
        { constructor.
          - exact Hc2.
          - exact (tp_keepalive _ _ _ _ Htp).
          - exact (ow_room_frR R_tick W1 W2 HfT HRo
                     (ow_room_after Y1 W1 (rp_zero _ _ _ _ Hpre1) (rd_og _ _ _ _ _ Hd0) (rk_step _ _ _ _ _ _ _ Hd))).
          - intros Hac2 Hw.
            pose proof (rk_acc _ _ _ _ _ _ _ Hd (rx_accepts_same W2 W1 _ Hac2 (eq_sym K2) (eq_sym K3) (eq_sym K1)))
              as Hac1.
            destruct (rk_wake _ _ _ _ _ _ _ Hd Hac1 Hw) as [Efl Eon].
            pose proof (tick_quiet_off I (Some (TFrame a bytes)) ops W1 Hc1' Eon) as Eq.
            rewrite Etk in Eq. destruct (dn_some2 Eq) as [EW _]. rewrite EW. exact Efl.
          - intros Hcode. transitivity (g_rx_send W1); [rxop_rg HfT HRt|].
            rewrite (rk_rx_send _ _ _ _ _ _ _ Hd). transitivity (g_rx_send Y1); [fget Hf |].
            exact (rp_rx_send _ _ _ _ Hpre1 Hcode). }
        pose proof (rxop_pre_g_poll I ops W2 Y2 _ Hpg2 HY2) as Hpre2.
        destruct (rx_ok_g HL I ops (TFrame a bytes) got Y2 Hn Hfa Hpre2) as (Bx2 & t2 & Em2 & _ & Hf2 & _).
        assert (R3 : g_rx Y2 = a) by (transitivity (g_rx W2); [unfold Y2; wget | exact R2]).
        assert (Rx2 : g_rx Bx2 = a) by (transitivity (g_rx Y2); [fget Hf2 | exact R3]).
        assert (Er2 : call_recv I (Some (TFrame a bytes)) W2 DIGINET_MAX_FRAME_LEN =
                      Some (Bx2, got, rxbuf (TFrame a bytes) got)).
        { unfold call_recv. rewrite Ti2, (Z.eqb_refl (ti_io_recv I)). cbv beta iota.
          rewrite (rxop_io_recv I a bytes W2 got 1 Bx2 HW2n F2 R2 T2 ltac:(lia) L2 Ha0 Hg Hgl).
          - destruct (Z.ltb_spec 0 got); [reflexivity | lia].
          - destruct (Z.eqb_spec got 0) as [E|E]; [lia|]. cbv beta iota. exists t2. exact Em2.
          - exact Rx2. }
        change (Z.to_nat (2 - 1)) with (S O). cbn [PCG.poll_drain_rx].
        intros B1' r' g' Hr' _.
        rewrite Er2 in Hr'. destruct (dn_some3 Hr') as (E6 & E7 & E8). subst B1' r' g'.
        split.
        -- (* P at the second hand-over *)
           exact (dn_core I ops (TFrame a bytes) got Y2 Bx2 t2 Hn Hfa Hpre2 Em2).
        -- intros _ _ _ _ _. exact Logic.I.
Qed.

(* receive (p, n, 1, flags) from the world rxop_begin gives: the world handed to the poll (FT:1005-1015) *)
Lemma dn_recv8 : forall I ops B1 a bytes pf, length B1 = WN -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  rx_pre I ops (set_g_rx_send B1 (rxop_v bytes)) bytes ->
  PCG.poll_rx_each I (Some (TFrame a bytes)) (PCG.poll_dn_in (Some (TFrame a bytes)))
    (set_g_rx_fail
       (set_g_rx_times
          (set_g_rx_len
             (set_g_rx (set_g_rx_send (set_g_rx_send B1 (rxop_v bytes))
                          (rxop_v (rxbuf (TFrame a bytes) (rxop_got bytes)))) a)
             (rxop_got bytes))
          (if Z.land pf 1 =? 0 then 1 else 2))
       (Z.land (Z.shiftr pf 1) 1)).
Proof.
  intros I ops B1 a bytes pf HB1 Ha0 Ha1 Hpre.
  destruct (rxop_got_ok bytes) as [Hg Hgl].
  pose proof (rxop_pre_again I ops _ bytes (rxbuf (TFrame a bytes) (rxop_got bytes)) Hpre) as Hpre2.
  assert (Htm : (if Z.land pf 1 =? 0 then 1 else 2) = 1 \/ (if Z.land pf 1 =? 0 then 1 else 2) = 2)
    by (destruct (Z.land pf 1 =? 0); [left | right]; reflexivity).
  destruct (rxop_land01 (Z.shiftr pf 1)) as [Ef|Ef]; rewrite Ef.
  - exact (dn_poll I ops a bytes (rxop_got bytes) _ _ Ha0 Ha1 Hg Hgl Htm Hpre2).
  - apply dn_fail_set. wlen.
Qed.

(* ---- K5 ---- *)

Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LLVMFuzzerTestOneInput_segs.

Lemma lc_dn_each_ok : lc_dn_each_stmt.
Proof.
  unfold lc_dn_each_stmt.
  intros ops Bw bytes bp pf HA Hops Hbp Hpf Hlen.
  unfold RCG.recv_dn_each. intros a Haok. destruct Haok as [Ha0 Ha1].
  assert (Ha2 : a + Z.of_nat (length bytes) < 2 ^ 64) by (clear - Ha1 Hlen; lia).
  destruct (rxop_begin _ ops Bw bytes HA) as (B1 & Eob & Hpre & _).
  assert (HB1 : length B1 = WN)
    by exact (ac_len _ _ _ (agree_core_op_begin _ ops Bw B1 (ag_core _ _ _ HA) Eob)).
  assert (Ew2 : RCG.recv_w2 Bw bytes = set_g_rx_send B1 (rxop_v bytes)).
  { unfold RCG.recv_w2, RCG.recv_w1. rewrite Eob. reflexivity. }
  destruct Hbp as [Eb|Eb]; subst bp.
  - (* by_poll = 0: m_rx at the world after op_begin and g_rx_send *)
    change (0 =? 0) with true. cbv beta iota.
    intros Bx ticked Em. rewrite Ew2 in Em.
    exact (dn_recv0 _ ops B1 a bytes Bx ticked Ha0 Ha2 Hpre Em).
  - (* by-poll: every call of diginet_session_rx the poll makes *)
    change (1 =? 0) with false. cbv beta iota.
    unfold RCG.recv_w2c. rewrite Ew2.
    exact (dn_recv8 _ ops B1 a bytes pf HB1 Ha0 Ha2 Hpre).
Qed.
