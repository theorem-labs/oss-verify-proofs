(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module names and numbers changed; 599 of its 698 lines of code are new or changed and 1890 lines of the source are left out. *)
(* diginet_session_poll_seg_kit: the facts every piece of the image-A walk of diginet_session_poll shares
   (lib/A/Prog/diginet_session_poll_segs.v), no run:
   - the model: diginet_session_poll_m and poll_drain_m at the code's branches (TPoll.v poll_cases,
     poll_drain_cases, with the pointer tests of call_now / call_recv read off), and (3) along the run
     (poll_rx_each, poll_drain_rx) at each recv;
   - the context: the stack window and the realigned sp (pw_ok_sp), the frame and the layout at a state of pw_cur
     (pw_cur_frame);
   - pw_run carried over a step that changes only the bytes of the window [sp1 - ESTACK, sp1) (pw_run_win: a leaf,
     a runtime entry, or no byte at all) and over a G-form callee called at sp1 (pw_run_gcall: its transport_cg_post
     over a written range inside poll_wr);
   - what a callee asks of the current heap frame and of the read-only bytes at a state of pw_cur: trans_tframe_at
     at any window inside the statement's (pw_tf_at; DgnTransportCg.v trans_src_ok_acall_g's argument with
     trans_tf_off_g in place of gx_kept) and trans_rom_view_rd (pw_rom_at);
   - buf, the 1514 bytes at frame + 32 (pw_buf_at): placed in the own frame (decode_in_fake, trans_src_ok),
     readable (decode_rd_ok), writable by a callee (transport_twr_ok_g), outside G and outside a callee's window. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg notice_cg io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The pair inside a Some, by name (no injection on a world-carrying option). *)
Lemma pw_some_inv : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> Bx = By /\ x = y.
Proof.
intros Bx By x y H. split.
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (p, _) => p | None => Bx end) H).
- exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, q) => q | None => x end) H).
Qed.

(* The result inside a Some of a recv's triple, by name. *)
Lemma pw_some3_r : forall (Bx By gx gy : list byte) (x y : Z), Some (Bx, x, gx) = Some (By, y, gy) -> x = y.
Proof.
intros Bx By gx gy x y H.
exact (f_equal (fun o : option (list byte * Z * list byte) => match o with Some (_, q, _) => q | None => x end) H).
Qed.

(* :508-509: a NULL pointer returns DIGINET_E_ARG with the world unchanged. *)
Lemma pw_m_arg : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (w : Z) (Bw' : list byte) (r : Z),
  TSS.diginet_session_poll_m I F Bw w = Some (Bw', r) ->
  (TW.S_io_recv Bw = 0 \/ TW.S_io_now_us Bw = 0) -> Bw' = Bw /\ r = TS0.DIGINET_E_ARG.
Proof.
intros I F Bw w Bw' r H Hz.
destruct (TPL.poll_cases I F Bw w Bw' r H) as [(_ & E1 & E2) | (N1 & N2 & _)].
- split; [exact E1 | exact E2].
- exfalso. destruct Hz as [Z0 | Z0]; [exact (N1 Z0) | exact (N2 Z0)].
Qed.

(* :510-516 with both pointers set: they are the image's io_now and io_recv (call_now, call_recv), the deadline is
   the model's at now = io_now_m Bw, and the first recv at Bw is followed by pw_rest1. *)
Lemma pw_m_go : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (w : Z) (Bw' : list byte) (r : Z),
  TSS.diginet_session_poll_m I F Bw w = Some (Bw', r) -> TW.S_io_recv Bw <> 0 -> TW.S_io_now_us Bw <> 0 ->
  TW.S_io_now_us Bw = TI.ti_io_now I /\ TW.S_io_recv Bw = TI.ti_io_recv I /\
  exists due B1 r1 got,
    TS0.diginet_session_deadline_m Bw (TC.io_now_m Bw) = Some due /\
    TC.io_recv_m I F Bw TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) /\
    pw_rest1 I F B1 r1 got Bw' r.
Proof.
intros I F Bw w Bw' r H N1 N2.
destruct (TPL.poll_cases I F Bw w Bw' r H)
  as [(Z0 & _) | (_ & _ & now & due & B1 & r1 & got & CN & DD & CR & REST)].
- exfalso. destruct Z0 as [Z0 | Z0]; [exact (N1 Z0) | exact (N2 Z0)].
- destruct (TPL.call_now_inv I Bw now CN) as [En Hnow].
  destruct (TPL.call_recv_inv I F Bw TS0.DIGINET_MAX_FRAME_LEN B1 r1 got CR) as [Er Hrecv].
  split; [exact En |]. split; [exact Er |].
  exists due, B1, r1, got.
  split; [rewrite <- Hnow; exact DD |]. split; [exact Hrecv |].
  unfold pw_rest1. exact REST.
Qed.

(* (3) along the run at the first recv (poll_rx_each): the guarded premise of the rx call after it, and the drain's
   from the world tick leaves. *)
Lemma pw_rx_first : forall (I : TI.timg) (F : option TI.tframe) (P : list byte -> list byte -> Prop) (Bw : list byte)
    (B1 : list byte) (r1 : Z) (got : list byte),
  poll_rx_each I F P Bw -> TW.S_io_recv Bw = TI.ti_io_recv I ->
  TC.io_recv_m I F Bw TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) -> 0 <= r1 ->
  (0 < r1 -> P B1 got) /\
  (forall now B2 B3 r3,
     TSS.call_now I B1 = Some now ->
     (if 0 <? r1 then exists r2, TSS.diginet_session_rx_m I F B1 got now = Some (B2, r2) else B2 = B1) ->
     TSS.diginet_session_tick_m I F B2 now = Some (B3, r3) ->
     poll_drain_rx I F P B3 (Z.to_nat (TW.g_rx_times B3))).
Proof.
intros I F P Bw B1 r1 got EACH Er HR Hr.
assert (CR : TSS.call_recv I F Bw TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got)).
{ unfold TSS.call_recv. rewrite Er, Z.eqb_refl. exact HR. }
exact (EACH B1 r1 got CR Hr).
Qed.

(* One turn of the drain (:524-526): the recv at Bx through the image's io_recv; r <= 0 returns r with the recv's
   world; else one less fuel, now through the image's io_now, and rx at the recv's world. *)
Lemma pw_drain_step : forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (fuel : nat) (Bw' : list byte) (r : Z),
  TSS.poll_drain_m I F Bx fuel = Some (Bw', r) ->
  TW.S_io_recv Bx = TI.ti_io_recv I /\
  exists B1 r1 got, TC.io_recv_m I F Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) /\
    ((r1 <= 0 /\ Bw' = B1 /\ r = r1) \/
     (0 < r1 /\ exists f B2 r2, fuel = S f /\ TW.S_io_now_us B1 = TI.ti_io_now I /\
        TSS.diginet_session_rx_m I F B1 got (TC.io_now_m B1) = Some (B2, r2) /\
        TSS.poll_drain_m I F B2 f = Some (Bw', r))).
Proof.
intros I F Bx fuel Bw' r H.
destruct (TPL.poll_drain_cases I F Bx fuel Bw' r H) as (B1 & r1 & got & CR & CASES).
destruct (TPL.call_recv_inv I F Bx TS0.DIGINET_MAX_FRAME_LEN B1 r1 got CR) as [Er Hrecv].
split; [exact Er |]. exists B1, r1, got. split; [exact Hrecv |].
destruct CASES as [L | (P & f & now & B2 & r2 & Ef & CN & RX & DR)].
- left. exact L.
- right. split; [exact P |].
  destruct (TPL.call_now_inv I B1 now CN) as [En Hnow].
  exists f, B2, r2. split; [exact Ef |]. split; [exact En |].
  split; [rewrite <- Hnow; exact RX | exact DR].
Qed.

(* (3) along the drain: at a turn that hands over a frame, P at the recv's world and bytes, and the rest of the
   drain from rx's world. *)
Lemma pw_drain_rx_step : forall (I : TI.timg) (F : option TI.tframe) (P : list byte -> list byte -> Prop)
    (Bx : list byte) (f : nat) (B1 : list byte) (r1 : Z) (got : list byte) (B2 : list byte) (r2 : Z),
  poll_drain_rx I F P Bx (S f) -> TW.S_io_recv Bx = TI.ti_io_recv I ->
  TC.io_recv_m I F Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) -> 0 < r1 ->
  TW.S_io_now_us B1 = TI.ti_io_now I ->
  TSS.diginet_session_rx_m I F B1 got (TC.io_now_m B1) = Some (B2, r2) ->
  P B1 got /\ poll_drain_rx I F P B2 f.
Proof.
intros I F P Bx f B1 r1 got B2 r2 D Er HR Hr En RX.
assert (CR : TSS.call_recv I F Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got)).
{ unfold TSS.call_recv. rewrite Er, Z.eqb_refl. exact HR. }
assert (CN : TSS.call_now I B1 = Some (TC.io_now_m B1)).
{ unfold TSS.call_now. rewrite En, Z.eqb_refl. reflexivity. }
cbn [poll_drain_rx] in D.
destruct (D B1 r1 got CR Hr) as [HP HN].
split; [exact HP | exact (HN (TC.io_now_m B1) B2 r2 CN RX)].
Qed.

(* io_recv's result: an int, and when it is > 0 the length of the bytes it handed over, at most the cap. *)
Lemma pw_recv_ret : forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (B1 : list byte) (r1 : Z)
    (got : list byte),
  TC.io_recv_m I F Bx TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) ->
  - 2 ^ 31 <= r1 < 2 ^ 31 /\ (0 < r1 -> Z.of_nat (length got) = r1 /\ r1 <= TS0.DIGINET_MAX_FRAME_LEN).
Proof.
intros I F Bx B1 r1 got H.
assert (Hm : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity.
assert (Hc : 0 <= TS0.DIGINET_MAX_FRAME_LEN < 2 ^ 31) by (rewrite Hm; lia).
destruct (TPL.io_recv_m_ret I F Bx TS0.DIGINET_MAX_FRAME_LEN B1 r1 got Hc H) as [R L].
split; [exact R |]. intros Hr. split; [exact (L Hr) |]. clear L R Hc.
(* r1 <= cap: io_recv_m's case analysis again; the copy's length is min (g_rx_len, cap) *)
unfold TC.io_recv_m in H. revert H.
destruct (TC.truth (TW.g_rx_fail Bx)); intros H; cbv beta iota in H.
{ apply pw_some3_r in H. unfold TC.EIO in H. lia. }
revert H. destruct ((TW.g_rx Bx =? 0) || (TW.g_rx_times Bx =? 0)); intros H; cbv beta iota in H.
{ apply pw_some3_r in H. lia. }
revert H. destruct (TC.int_dec (TW.g_rx_times Bx)) as [t|]; intros H; cbv beta iota zeta in H; [|discriminate H].
set (B1' := TW.set_g_rx_times Bx t) in H.
assert (Hn : 0 <= (if TW.g_rx_len B1' <? TS0.DIGINET_MAX_FRAME_LEN then TW.g_rx_len B1'
                   else TS0.DIGINET_MAX_FRAME_LEN) <= TS0.DIGINET_MAX_FRAME_LEN).
{ pose proof (TWL.u_at_range B1' TW.OFF_g_rx_len 8) as RR.
  change (TW.u_at B1' TW.OFF_g_rx_len 8) with (TW.g_rx_len B1') in RR.
  destruct (Z.ltb_spec (TW.g_rx_len B1') TS0.DIGINET_MAX_FRAME_LEN); lia. }
revert H Hn.
generalize (if TW.g_rx_len B1' <? TS0.DIGINET_MAX_FRAME_LEN then TW.g_rx_len B1' else TS0.DIGINET_MAX_FRAME_LEN).
intros n H Hn.
revert H. lazymatch goal with |- (match ?e with Some _ => _ | None => _ end = _) -> _ => destruct e as [B2|] end;
  intros H; cbv beta iota zeta in H; [|discriminate H].
revert H. destruct (TC.frame_read F (TW.g_rx B2) n) as [bytes|]; intros H; cbv beta iota zeta in H;
  [|discriminate H].
apply pw_some3_r in H.
assert (Sw : bv_swrap 32 n = n).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia. }
lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The written range poll_wr lies in G's hull, image bytes             *)
(* ------------------------------------------------------------------ *)

(* The bounds of a byte of one row twa_fld o b A n of a harness global: computed when every argument is closed, else
   (an array entry at an index) the row's address unfolded to the index. *)
Ltac pwh_fld H :=
  lazymatch type of H with
  | twa_fld _ _ (TW.A_OW_t_state _) _ _ => unfold twa_fld, TW.A_OW_t_state, TW.OW_t_ESZ, TW.OFF_OW, TA_OW in H
  | twa_fld _ _ (TC.A_OW_dn_body _) _ _ => unfold twa_fld, TC.A_OW_dn_body, TW.OFF_OW, TA_OW in H
  | twa_fld _ _ (TW.A_Cmd_st _) _ _ => unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TA_g_cmd in H
  | twa_fld _ _ (TW.A_S_queue_bytes _) _ _ =>
      unfold twa_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s, TA_g_s in H
  | twa_fld ?o ?b ?A ?n ?x =>
      let lo := eval vm_compute in (b + (A - o)) in
      let ln := eval vm_compute in n in
      change (lo <= x < lo + ln) in H
  end.

(* Each written-range predicate unfolded down to its rows; a notice's rows by TransportGNotice.v notice_wr_G. *)
Ltac pwh_go H :=
  lazymatch type of H with
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [pwh_go H1 | pwh_go H2]
  | ex _ => let x := fresh "i" in let H1 := fresh "Hw" in destruct H as [x H1]; pwh_go H1
  | (_ <= _ < _) /\ _ => let H1 := fresh "Hb" in let H2 := fresh "Hw" in destruct H as [H1 H2]; pwh_go H2
  | _ /\ _ => let H2 := fresh "Hw" in destruct H as [_ H2]; pwh_go H2
  | notice_wr _ _ _ => exact (inG_G_HARNESS_hull _ (notice_wr_G _ _ _ H))
  | twa_fld _ _ _ _ _ =>
      pwh_fld H; unfold TC.TRANS_MAX, TW.OW_dn_N, TC.CMDS_MAX, TW.S_queue_N, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *;
      lia
  | poll_wr _ => unfold poll_wr in H; pwh_go H
  | mrx_wr _ => unfold mrx_wr in H; pwh_go H
  | mtick_wr _ _ => unfold mtick_wr in H; pwh_go H
  | mlost_wr _ _ => unfold mlost_wr in H; pwh_go H
  | mset_wr _ _ => unfold mset_wr in H; pwh_go H
  | srx_wr _ _ => unfold srx_wr in H; pwh_go H
  | tick_wr _ _ => unfold tick_wr in H; pwh_go H
  | onann_wr _ _ _ => unfold onann_wr in H; pwh_go H
  | onack_wr _ _ _ => unfold onack_wr in H; pwh_go H
  | ondata_wr _ _ _ => unfold ondata_wr in H; pwh_go H
  | slost_wr _ _ _ => unfold slost_wr in H; pwh_go H
  | wake_wr _ _ => unfold wake_wr in H; pwh_go H
  | maybeon_wr _ _ => unfold maybeon_wr in H; pwh_go H
  | iosend_wr _ _ => unfold iosend_wr in H; pwh_go H
  | senddata_wr _ => unfold senddata_wr in H; pwh_go H
  end.

(* Every byte some path of the call stores (poll_wr) lies in G's hull [G_HARNESS_LO, G_HARNESS_HI). *)
Lemma pw_wr_hull : forall a, poll_wr a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI.
Proof. intros a H. pwh_go H. Qed.

(* G's hull lies inside one loaded segment of the image (decided by vm_compute). *)
Lemma pw_hull_img : forall a, TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI -> in_img tfibsegs a.
Proof.
intros a Ha.
apply (decode_seg_covers_img [(TG.G_HARNESS_LO, TG.G_HARNESS_HI - TG.G_HARNESS_LO)] a).
- vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* 2. The context                                                      *)
(* ------------------------------------------------------------------ *)

(* The entry's stack window: AR at the call state, the sp's range, the window above alloc_ceiling and present; the
   realigned sp1 32-aligned, 160 .. 176 below the entry sp, and every callee window [sp1 - K, sp1) with
   K <= SRX_STK inside the statement's. *)
Lemma pw_ok_sp : forall c, pw_ok B c ->
  @AR rc segs B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) /\
  2 ^ 46 <= pw_SP c <= 2 ^ 47 /\ alloc_ceiling <= pw_SP c - POLL_STK /\
  (forall a, pw_SP c - POLL_STK <= a < pw_SP c -> apresent (w_H (cx_W c)) (cx_memc c) a) /\
  pw_sp1 c mod 32 = 0 /\ pw_SP c - 176 <= pw_sp1 c <= pw_SP c - 160 /\
  cx_sp0 c mod 16 = 0 /\ cx_sp0 c - cx_STK c <= pw_SP c - POLL_STK /\ pw_SP c <= cx_sp0 c /\
  POLL_STK = 176 + SRX_STK /\ ESTACK <= IORECV_STK /\ IORECV_STK <= SRX_STK /\ TICK_STK <= SRX_STK.
Proof using All.
intros c HOK. destruct HOK as (HJ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EPS : POLL_STK = 176 + SRX_STK) by (rewrite poll_stk_eq; reflexivity).
assert (ESR : SRX_STK = ltac:(let v := eval vm_compute in SRX_STK in exact v)) by (vm_compute; reflexivity).
assert (M1 : ESTACK <= IORECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (M2 : IORECV_STK <= SRX_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (M3 : TICK_STK <= SRX_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hx : 0 <= pw_SP c - 160) by (unfold pw_SP in *; lia).
assert (Hx16 : (pw_SP c - 160) mod 16 = 0)
  by (unfold pw_SP in *; rewrite Zminus_mod, Hsp16; reflexivity).
destruct (can_sp1_facts (pw_SP c - 160) Hx Hx16) as (Hr & Ha32 & _).
assert (E1 : pw_sp1 c = 32 * ((pw_SP c - 160) / 32)) by reflexivity.
rewrite <- E1 in Hr, Ha32.
split; [exact HAR|]. split; [unfold pw_SP in *; lia|]. split; [unfold pw_SP in *; lia|].
split; [intros a Ha; apply Hpres0; unfold pw_SP in *; lia|].
split; [exact Ha32|]. split; [lia|].
split; [exact Hsp0a|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [exact EPS|]. split; [exact M1|]. split; [exact M2 | exact M3].
Qed.

(* The frame at a state of pw_cur: AR there, the frame live at the call's layout's address, 64-aligned, below
   alloc_ceiling, in application memory, apart from the image; the layout's frames and machine stack where the
   call's are. *)
Lemma pw_cur_frame : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx,
  pw_rt B MT -> pw_ok B c -> pw_cur B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  @AR rc segs B ly2 S2 W2 mem2 md2 /\
  In (POLL_CID, pos) (frames S2) /\ frame_addr ly2 POLL_CID pos = pw_F c pos /\
  (forall cid p, frame_addr ly2 cid p = frame_addr (cx_lyc c) cid p) /\
  ly_stk_lo ly2 = ly_stk_lo (cx_lyc c) /\ ly_stk_hi ly2 = ly_stk_hi (cx_lyc c) /\
  4096 <= pw_F c pos /\ pw_F c pos mod 64 = 0 /\ pw_F c pos + POLL_FBYTES <= alloc_ceiling /\
  in_app (pw_F c pos) POLL_FBYTES /\
  (forall a, pw_F c pos <= a < pw_F c pos + POLL_FBYTES -> ~ in_img segs a).
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR.
destruct HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
destruct HOK as (HJc & _).
destruct HCUR as (HJ2 & Hfrs & _ & HlyF & _).
pose proof HJc as (_ & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
pose proof HJic as (_ & Hlylec & _). pose proof Hlylec as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLOc & ESHIc & _).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (HAR2 & Hlyle2 & _). pose proof Hlyle2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO2 & ESHI2 & _).
clear HJic HJi2 memSc memS2 Hlylec Hlyle2.
assert (Hfa : forall cid p, frame_addr ly2 cid p = frame_addr (cx_lyc c) cid p)
  by (intros cid p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hin : In (POLL_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ POLL_CID pos HAR2 Hin) as (_ & HFapp & _ & _).
destruct (frames_bounds segs B LAWS _ _ _ _ _ POLL_CID pos HAR2 Hin) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ POLL_CID pos HAR2 Hin) as (HF64 & _ & _).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ POLL_CID pos a HAR2 Hin Ha) as HFimg.
rewrite (Hfa POLL_CID pos) in HFapp, HF0, HFc, HF64, HFimg.
rewrite poll_fbytes in HFapp, HFc, HFimg.
change (frame_addr (cx_lyc c) POLL_CID pos) with (pw_F c pos) in HFapp, HF0, HFc, HF64, HFimg.
split; [exact HAR2|]. split; [exact Hin|]. split; [exact (Hfa POLL_CID pos)|]. split; [exact Hfa|].
split; [rewrite ESLO2, ESLOc; reflexivity|]. split; [rewrite ESHI2, ESHIc; reflexivity|].
split; [exact HF0|]. split; [exact HF64|]. split; [exact HFc|]. split; [exact HFapp|].
exact HFimg.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. pw_run carried                                                   *)
(* ------------------------------------------------------------------ *)

(* The 13 saved words lie in [entry sp - 104, entry sp). *)
Lemma pw_saved_off : forall o, In o POLL_SAVED -> 8 <= fst o <= 104.
Proof.
intros o Ho. unfold POLL_SAVED in Ho. cbn [In] in Ho.
repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
Qed.

(* Over a step at the same state that changes only bytes of [sp1 - ESTACK, sp1) (a leaf, a runtime entry that
   writes nothing else, or a run that stores nothing: then every byte is kept), with the journal at the new memory. *)
Lemma pw_run_win : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx mem3 md3,
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem3 md3 (cx_k c) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pw_sp1 c - ESTACK <= a < pw_sp1 c) ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  pw_run B MT c pos ly2 S2 W2 mem3 md3 Bx.
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx mem3 md3 HRT HOK HRUN HJ3 KD GR.
pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & FFL & HGX & _).
pose proof (pw_ok_sp c HOK) as (HARc & Hsp & Hce & _ & _ & Hsp1 & _ & _ & _ & EPS & M1 & M2 & _).
destruct HRUN as (HCUR & HSH0 & HSH2 & HS24).
pose proof (pw_cur_frame c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR)
  as (HAR2 & _ & _ & _ & _ & _ & HF0 & _ & HFc & _ & _).
destruct HCUR as (_ & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL & H8 & H16 & Htw & Hfn & Hinv & Hrx).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold POLL_FBYTES in HFc.
assert (HF8 : 0 <= pw_F c pos / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (KLO : forall a, 0 <= a < pw_sp1 c - ESTACK -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KD; lia).
assert (KHI : forall a, pw_sp1 c <= a < 2 ^ 64 -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KD; lia).
assert (HK3 : acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) W2 mem3 (pw_SP c - POLL_STK) (pw_SP c)
  poll_wr).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low G (cx_lyc c) (cx_Sc c) ly2 S2 (cx_W c) (cx_memc c) (cx_mdc c)
    W2 mem2 md2 mem2 mem3 (pw_SP c - POLL_STK) (pw_SP c) POLL_CID pos (pw_F c pos) (flag_addr (cx_lyc c) POLL_CID pos)
    poll_wr (fun a => pw_sp1 c - ESTACK <= a < pw_sp1 c) HGX HARc HAR2 Hfrs
    (fun bm Hb => Permutation_in bm (Permutation_sym Hperm) Hb) HlyF eq_refl eq_refl FFL);
  [lia | lia | intros a Ha; left; cbv beta in Ha; lia | exact HK | exact KD | exact GR]. }
split; [|split; [|split]].
- split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|]. split; [exact HMO|].
  split; [exact HK3|].
  split.
  { rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
    pose proof (pw_saved_off o Ho) as Hob.
    apply rdword_ext. intros k Hk. apply KHI. lia. }
  split.
  { rewrite <- HFL. apply rdword_ext. intros k Hk. apply KLO. unfold POLL_FBYTES. lia. }
  split; [rewrite <- H8; apply rdword_ext; intros k Hk; apply KHI; lia|].
  split; [rewrite <- H16; apply rdword_ext; intros k Hk; apply KHI; lia|].
  split.
  { apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KLO. lia. }
  split; [exact Hfn|]. split; [exact Hinv | exact Hrx].
- intros i Hi. rewrite KLO by (unfold SHADOW_OFF; lia). exact (HSH0 i Hi).
- rewrite KLO by (unfold SHADOW_OFF; lia). exact HSH2.
- rewrite <- HS24. apply rdword_ext. intros k Hk. apply KHI. lia.
Qed.

(* Over a G-form callee called at sp1 from a state of pw_run (its transport_cg_post, unfolded, with no event): its
   window [sp1 - K, sp1) inside the statement's, its written range inside poll_wr, and the world facts at the world
   Bx' it returns. *)
Lemma pw_run_gcall : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regsC : bvmap 5 word) (K : Z) (E : Z -> Prop)
    ly3 S3 (W3 : world segs) mem3 md3 Bx',
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  spZ regsC = pw_sp1 c -> 0 <= K -> pw_SP c - POLL_STK <= pw_sp1 c - K ->
  (forall a, E a -> poll_wr a \/ (pw_F c pos + 32 <= a < pw_F c pos + 32 + TS0.DIGINET_MAX_FRAME_LEN)) ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly3 S3 W3 mem3 md3 (cx_k c + 0) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  acall_kept_g segs B G ly2 S2 W2 mem2 W3 mem3 (spZ regsC - K) (spZ regsC) E ->
  mo_le MT S2 S3 0 ->
  tw_at TMAP_A (aview segs (w_H W3) mem3) Bx' -> TW.g_fail_next Bx' <= 1 -> srx_inv Bx' ->
  TW.g_rx Bx' = TW.g_rx (cx_Bw c) ->
  pw_run B MT c pos ly3 S3 W3 mem3 md3 Bx'.
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx regsC K E ly3 S3 W3 mem3 md3 Bx' HRT HOK HRUN USPC HK0 HKw HE HJ3 Hfr3 Hperm3
  HKC Hmo3 Htw3 Hfn3 Hinv3 Hrx3.
pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & _ & _ & FFL & HGX & _).
pose proof (pw_ok_sp c HOK) as (HARc & Hsp & Hce & _ & _ & Hsp1 & _ & _ & _ & EPS & M1 & M2 & _).
destruct HRUN as (HCUR & HSH0 & HSH2 & HS24).
pose proof (pw_cur_frame c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR)
  as (HAR2 & Hin & EF2 & Hfa & _ & _ & HF0 & HF64 & HFc & HFapp & HFimg).
destruct HCUR as (_ & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL & H8 & H16 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold POLL_FBYTES in HFc, HFapp, HFimg.
rewrite Z.add_0_r in HJ3.
(* the frames where the call's layout puts them, at the callee's return *)
pose proof (proj1 HOK) as HJc.
pose proof HJc as (_ & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
pose proof HJic as (_ & Hlylec & _). pose proof Hlylec as (_ & _ & _ & _ & _ & ELFc & _).
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJic HJi3 memSc memS3 Hlylec Hlyle3 HJc.
assert (HlyF3 : ly_F ly3 = ly_F (cx_lyc c)) by (rewrite ELF3, ELFc; reflexivity).
(* the own frame and its shadow bytes: apart, and apart from G's hull *)
assert (HF8 : 0 <= pw_F c pos / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (DF8 : pw_F c pos = 8 * (pw_F c pos / 8)).
{ pose proof (Z.div_mod (pw_F c pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  pose proof (Z.div_mod (pw_F c pos) 8 ltac:(lia)) as D8.
  assert (M8 : pw_F c pos mod 8 = 0).
  { rewrite D. replace (64 * (pw_F c pos / 64)) with ((8 * (pw_F c pos / 64)) * 8) by ring.
    apply Z.mod_mul. lia. }
  rewrite M8, Z.add_0_r in D8. exact D8. }
assert (HSHF : SHADOW_OFF + pw_F c pos / 8 + 256 <= pw_F c pos \/ pw_F c pos + 2048 <= SHADOW_OFF + pw_F c pos / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  destruct HFapp as (_ & [HL | (HH1 & HH2)]); [right | left]; unfold SHADOW_OFF; lia. }
assert (NE : forall x, E x ->
  (pw_F c pos + 32 <= x < pw_F c pos + 1546) \/ (TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI /\ in_img segs x)).
{ intros x Hx. destruct (HE x Hx) as [Hw | Hb].
  - right. pose proof (pw_wr_hull x Hw) as Hh. split; [exact Hh | exact (pw_hull_img x Hh)].
  - left. change TS0.DIGINET_MAX_FRAME_LEN with 1514 in Hb. lia. }
assert (NEF : forall a, pw_F c pos + 1546 <= a < pw_F c pos + 2048 -> ~ E a).
{ intros a Ha Hx. destruct (NE a Hx) as [Hb | (_ & Hi)]; [lia | exact (HFimg a ltac:(lia) Hi)]. }
assert (NES : forall i, 0 <= i < 256 -> ~ E (SHADOW_OFF + pw_F c pos / 8 + i)).
{ intros i Hi Hx. destruct (NE _ Hx) as [Hb | (Hh & _)].
  - destruct HSHF as [HS1 | HS1]; lia.
  - unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI, SHADOW_OFF in *. lia. }
(* what the call keeps, from its entry to the callee's return *)
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low (cx_lyc c) (cx_Sc c) ly2 S2 W2 mem2 md2 POLL_CID pos
  (pw_F c pos) (flag_addr (cx_lyc c) POLL_CID pos) HAR2 Hfrs (fun bm Hb => Permutation_in bm (Permutation_sym Hperm) Hb)
  HlyF eq_refl eq_refl FFL) as (N1 & _ & N3 & _).
assert (KC3 : acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) W3 mem3 (pw_SP c - POLL_STK) (pw_SP c)
  poll_wr).
{ apply (dk_kept_trans_nf_g segs B G (cx_lyc c) (cx_Sc c) ly2 S2 (cx_W c) (cx_memc c) W2 mem2 W3 mem3
    (pw_SP c - POLL_STK) (pw_SP c) (spZ regsC - K) (spZ regsC) poll_wr E
    (dkg_nf POLL_CID (pw_F c pos) (flag_addr (cx_lyc c) POLL_CID pos))).
  - lia.
  - lia.
  - exact Hfa.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hb. exact (Permutation_in bm (Permutation_sym Hperm) Hb).
  - exact N1.
  - exact N3.
  - exact HK.
  - exact HKC.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. destruct (HE a Ha) as [Hw | Hb]; [left; exact Hw | right].
    unfold dkg_nf. left. rewrite poll_fbytes. unfold POLL_FBYTES.
    change TS0.DIGINET_MAX_FRAME_LEN with 1514 in Hb. lia. }
pose proof HKC as (L1 & _ & _ & L4 & _).
rewrite USPC in L1.
assert (KHI : forall a, pw_sp1 c <= a < 2 ^ 64 -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply L1; lia).
assert (KFR : forall a,
  (pw_F c pos <= a < pw_F c pos + 2048 \/ SHADOW_OFF + pw_F c pos / 8 <= a < SHADOW_OFF + pw_F c pos / 8 + 256) ->
  ~ E a -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (L4 POLL_CID pos a Hin); [|exact Hn].
  unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. rewrite EF2.
  change (fs_frame_bytes POLL_CID / 8) with 256. change (fs_frame_bytes POLL_CID) with 2048.
  destruct Ha as [Ha | Ha]; [left | right]; lia. }
split; [|split; [|split]].
- split; [exact HJ3|].
  split; [rewrite Hfr3; exact Hfrs|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [exact HlyF3|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ HMO Hmo3)|].
  split; [exact KC3|].
  split.
  { rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
    pose proof (pw_saved_off o Ho) as Hob.
    apply rdword_ext. intros k Hk. apply KHI. lia. }
  split.
  { rewrite <- HFL. apply rdword_ext. intros k Hk. unfold POLL_FBYTES.
    apply KFR; [left; lia | apply NEF; lia]. }
  split; [rewrite <- H8; apply rdword_ext; intros k Hk; apply KHI; lia|].
  split; [rewrite <- H16; apply rdword_ext; intros k Hk; apply KHI; lia|].
  split; [exact Htw3|]. split; [exact Hfn3|]. split; [exact Hinv3 | exact Hrx3].
- intros i Hi. rewrite KFR; [exact (HSH0 i Hi) | right; lia | apply NES; lia].
- rewrite KFR; [exact HSH2 | right; lia | apply NES; lia].
- rewrite <- HS24. apply rdword_ext. intros k Hk. apply KHI. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. What a callee asks, at a state of pw_cur                         *)
(* ------------------------------------------------------------------ *)

(* TransportGNotice.v trans_src_ok_kept_gx without its gx_kept_ex: a range with no byte of G (here the current heap
   frame, by trans_tf_off_g) is placed in G only when it is empty, so its bytes are kept by the block, frame, stack
   and image clauses of the walk's acall_kept_g alone. *)
Lemma pw_src_ok_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B -> AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> ~ inG G a) ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
intros HRU HRE LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk
  (K1 & K2 & K3 & K4 & _) HnG HnE HnEs Hoff Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
{ intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
    + exfalso. exact (HnG a Ha (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TransportG.G_HARNESS_LO in Gh. lia. }
split; [|exact KV].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
{ left. exists bA, nA. split; [exact (Hbl _ Hin) | lia]. }
assert (Hrd2 : decode_rd_ok W2 mem2 q n).
{ destruct (Z.eq_dec n 0) as [En | Hn0].
  - subst n. destruct Hrd as (_ & _ & _ & R4 & R5 & R6).
    assert (HH : shadow_hull_vis (aview segs (w_H W2) mem2) q 0).
    { destruct HL as [(cid & pos & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - assert (Hin2 : In (cid, pos) (frames S2)) by exact (Hfr _ Hin).
        destruct (dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (A1 & A2 & A3).
        destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & _ & HSh).
        destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (G1 & G2 & _).
        rewrite Hfa in A1, HSh, G1, G2.
        set (x := if q <? frame_addr lyc cid pos + fs_frame_bytes cid then q else q - 1).
        assert (Hx : frame_addr lyc cid pos <= x /\ x + 1 <= frame_addr lyc cid pos + fs_frame_bytes cid /\
                     x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec q (frame_addr lyc cid pos + fs_frame_bytes cid)); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        apply (frame_hull_vis _ (frame_addr lyc cid pos) (fs_frame_bytes cid) x 1); try lia.
        intros i Hi. apply aview_some_of_apresent. exact (proj1 (HSh i Hi)).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
      - set (x := if ly_stk_lo lyc <? q then q - 1 else q).
        assert (Hx : ly_stk_lo lyc <= x /\ x + 1 <= ly_stk_hi lyc /\ x <= q /\ q <= x + 1).
        { unfold x. destruct (Z.ltb_spec (ly_stk_lo lyc) q); lia. }
        apply (trans_hull_sub _ x 1 q 0); [|lia|lia].
        exact (proj2 (stack_zshadow_ra B ly2 S2 W2 mem2 md2 x 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
          ltac:(rewrite Ehi; lia))).
      - exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)). }
    split; [intros a Ha; lia|]. split; [intros x Hx; lia|]. split; [exact HH|]. exact (conj R4 (conj R5 R6)).
  - assert (Hnp : 0 < n) by lia.
    destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    + apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hnp KV).
      intros cid pos s Hin Hs'. exact (KS cid pos s Hin Hs').
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hnp ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
        as [Ha Hh].
      exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
    + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* TransportGNotice.v trans_tframe_at_kept_gx without its gx_kept_ex, for a frame with no byte of G. *)
Lemma pw_tframe_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B -> AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 (E : Z -> Prop)
    (regs regs2 : bvmap 5 word) K K2 (TF : option TI.tframe),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 (spZ regs - K) (spZ regs) E ->
  trans_tf_off_g TF ->
  (forall fr, TF = Some fr ->
     forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) -> ~ E a) ->
  (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  spZ regs - K <= spZ regs2 - K2 -> spZ regs2 <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs K TF -> trans_tframe_at B ly2 S2 W2 mem2 regs2 K2 TF.
Proof.
intros HRU HRE LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 E regs regs2 K K2 TF HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk
  HK HOFF HnE HnEs Hw1 Hw2 HTF.
destruct TF as [fr|]; [|exact I].
destruct HTF as (H0 & Hg & Hs & Ho).
destruct (pw_src_ok_kept HRU HRE LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (spZ regs - K) (spZ regs) E
  (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) HAR HAR2 Hbl Hfr Hfa Elo Ehi Hstk HK (HOFF fr eq_refl)
  (HnE fr eq_refl) HnEs Ho Hs (Nat2Z.is_nonneg _)) as [Hs2 KV].
split; [exact H0|]. split.
- apply (garr8_frame segs _ _ _ _ Hg). intros a Ha. rewrite length_map in Ha.
  apply mbyte_of_aview. exact (KV a Ha).
- split; [exact Hs2|]. unfold decode_off_win in *. lia.
Qed.

(* The current heap frame at a callee's window [sp' - K, sp') inside the statement's. *)
Lemma pw_tf_at : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regs' : bvmap 5 word) (K : Z),
  pw_rt B MT -> pw_ok B c -> pw_cur B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  pw_SP c - POLL_STK <= spZ regs' - K -> spZ regs' <= pw_SP c ->
  trans_tframe_at B ly2 S2 W2 mem2 regs' K (cx_TF c).
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx regs' K HRT HOK HCUR Hw1 Hw2.
pose proof HRT as (_ & _ & _ & _ & _ & HRU & HRE & LAWS & _).
pose proof (pw_ok_sp c HOK) as (HARc & _ & _ & _ & _ & _ & _ & HloSTK & HhiSP & EPS & M1 & M2 & _).
pose proof (pw_cur_frame c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR) as (HAR2 & _ & _ & Hfa & Elo & Ehi & _).
destruct HCUR as (_ & Hfrs & Hperm & _ & _ & HK & _).
destruct HOK as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTF & HOFF & _ & HAP & _).
(* the machine stack of the call's layout is not empty: the statement's window lies in it *)
pose proof HJc as (_ & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
pose proof HJic as (_ & Hlylec & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hlylec as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
pose proof Hstk as (_ & _ & _ & Hslo & Hshi & _).
clear HJic memSc Hlylec Hstk.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTKLT : ly_stk_lo (cx_lyc c) < ly_stk_hi (cx_lyc c)) by (rewrite ESLO, ESHI; lia).
assert (HnEs : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ poll_wr a).
{ intros a Ha Hw. pose proof (pw_wr_hull a Hw) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI, kLowMemEnd in *. lia. }
assert (Hfin : forall f, In f (frames (cx_Sc c)) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs; right; exact Hf).
exact (pw_tframe_kept HRU HRE LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) ly2 S2 W2 mem2 md2 poll_wr
  (cx_regs c) regs' POLL_STK K (cx_TF c) HARc HAR2 (fun bm Hb => Permutation_in bm (Permutation_sym Hperm) Hb)
  Hfin Hfa Elo Ehi HSTKLT HK HOFF (fun fr Efr a Ha Hw => HAP a Hw fr Efr Ha) HnEs Hw1 Hw2 HTF).
Qed.

(* The read-only bytes. *)
Lemma pw_rom_at : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx,
  pw_rt B MT -> pw_ok B c -> pw_cur B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  trans_rom_view_rd W2 mem2.
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR.
pose proof HRT as (_ & _ & _ & _ & _ & HRU & HRE & _).
destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
destruct HCUR as (_ & _ & _ & _ & _ & HK & _).
pose proof HK as (_ & _ & K3 & _).
intros a Ha. rewrite <- (Hrom a Ha).
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* buf's first n bytes (n <= 1514), at a state of pw_run and a callee's window [sp' - K, sp') inside the
   statement's: in the own frame, placed and readable, writable by the callee, outside G and the window. *)
Lemma pw_buf_at : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regs' : bvmap 5 word) (K n : Z),
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx ->
  spZ regs' = pw_sp1 c -> 0 <= K -> pw_SP c - POLL_STK <= spZ regs' - K -> 0 <= n <= TS0.DIGINET_MAX_FRAME_LEN ->
  decode_in_fake ly2 S2 (pw_F c pos + 32) n /\
  decode_rd_ok W2 mem2 (pw_F c pos + 32) n /\
  trans_src_ok B ly2 S2 W2 mem2 (pw_F c pos + 32) n /\
  transport_twr_ok_g segs B G (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) ly2 S2
    ((POLL_CID, pos) :: cx_own c) W2 mem2 (spZ regs') (pw_F c pos + 32) n /\
  decode_off_win regs' K (pw_F c pos + 32) n /\
  (forall x, pw_F c pos + 32 <= x < pw_F c pos + 32 + n -> ~ inG G x).
Proof using All.
intros c pos ly2 S2 W2 mem2 md2 Bx regs' K n HRT HOK HRUN USP HK0 HKw Hn.
pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
pose proof (pw_ok_sp c HOK) as (HARc & Hsp & Hce & _ & _ & Hsp1 & _ & _ & _ & EPS & M1 & M2 & _).
destruct HRUN as (HCUR & HSH0 & HSH2 & _).
pose proof (pw_cur_frame c pos ly2 S2 W2 mem2 md2 Bx HRT HOK HCUR)
  as (HAR2 & Hin & EF2 & _ & _ & _ & HF0 & HF64 & HFc & HFapp & HFimg).
destruct HCUR as (HJ2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hm : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity.
rewrite Hm in Hn.
unfold POLL_FBYTES in HFc, HFapp, HFimg.
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 POLL_CID pos HAR2 Hin) as (_ & _ & HFpres & HFsh).
rewrite EF2, poll_fbytes in HFpres, HFsh. unfold POLL_FBYTES in HFpres, HFsh.
change (2048 / 8) with 256 in HFsh.
assert (DF8 : pw_F c pos = 8 * (pw_F c pos / 8)).
{ pose proof (Z.div_mod (pw_F c pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  pose proof (Z.div_mod (pw_F c pos) 8 ltac:(lia)) as D8.
  assert (M8 : pw_F c pos mod 8 = 0).
  { rewrite D. replace (64 * (pw_F c pos / 64)) with ((8 * (pw_F c pos / 64)) * 8) by ring.
    apply Z.mod_mul. lia. }
  rewrite M8, Z.add_0_r in D8. exact D8. }
(* placed in the own frame *)
assert (HDF : decode_in_fake ly2 S2 (pw_F c pos + 32) n).
{ exists POLL_CID, pos. rewrite EF2, poll_fbytes. unfold POLL_FBYTES. split; [exact Hin | lia]. }
(* addressable: the shadow bytes 4 .. 192 are 0 (whole granules), byte 193 is 2 (frame + 1544, + 1545) *)
assert (HRA : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (pw_F c pos + 32) n).
{ intros x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = pw_F c pos / 8 + (x - pw_F c pos) / 8).
  { replace x with (pw_F c pos / 8 * 8 + (x - pw_F c pos)) at 1 by lia. apply Z.div_add_l. lia. }
  rewrite Ex, Z.add_assoc.
  destruct (Z_lt_ge_dec x (pw_F c pos + 1544)) as [Hlt | Hge].
  - exists 0. split; [|left; reflexivity].
    apply HSH0. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - assert (Eq : (x - pw_F c pos) / 8 = 193)
      by (symmetry; apply (Z.div_unique _ _ _ (x - pw_F c pos - 1544)); lia).
    rewrite Eq. exists 2. split; [exact HSH2|]. right.
    assert (Em : x mod 8 = x - pw_F c pos - 1544)
      by (symmetry; apply (Z.mod_unique _ _ (pw_F c pos / 8 + 193)); lia).
    rewrite Em. lia. }
assert (HH1 : forall m, 1 <= m -> pw_F c pos + 32 + m <= pw_F c pos + 2048 ->
  shadow_hull_vis (aview segs (w_H W2) mem2) (pw_F c pos + 32) m).
{ intros m Hm1 Hm2. apply (frame_hull_vis _ (pw_F c pos) 2048 (pw_F c pos + 32) m);
    [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. change (2048 / 8) with 256 in Hi. apply aview_some_of_apresent. exact (proj1 (HFsh i Hi)). }
assert (HRD : decode_rd_ok W2 mem2 (pw_F c pos + 32) n).
{ split; [intros a Ha; apply aview_some_of_apresent; exact (proj1 (HFpres a ltac:(lia)))|].
  split; [exact HRA|].
  split.
  { destruct (Z.eq_dec n 0) as [-> | Hn0].
    - apply (trans_hull_sub _ (pw_F c pos + 32) 1 (pw_F c pos + 32) 0); [apply HH1; lia | lia | lia].
    - apply HH1; lia. }
  split; [apply (amem_range_sub_app (pw_F c pos) 2048); [exact HFapp | lia | lia | lia | lia]|].
  split; lia. }
split; [exact HDF|].
split; [exact HRD|].
split; [right; split; [left; exact HDF | exact HRD]|].
split.
{ eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
  intros a Ha. left. split.
  - unfold awr_byte. right; right; right. unfold in_frames. exists POLL_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF2, poll_fbytes. unfold POLL_FBYTES. lia.
  - rewrite USP. lia. }
split; [unfold decode_off_win; left; lia|].
intros x Hx Hg. exact (HFimg x ltac:(lia) (trans_g_img x Hg)).
Qed.

End kit.
