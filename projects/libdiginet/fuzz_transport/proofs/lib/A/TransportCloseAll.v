(* The closing instantiation of lib/A/TransportClose.v (rule 24: no function proved; this file is assembly).

   lib/A/TransportClose.v proves TFIB_T (transport_TFIB) and the two ASan statements of image A
   (transport_asan_agrees_of_parts, transport_asan_halts_of_parts) inside its Section close, whose hypotheses are
   the 64 program walks (H_PROG_<X>, rows AW1-AW72), 5 runtime texts (H_RT_<X>) and the plain side PLAIN. This file
   gives each hypothesis the theorem that proves it, under the same name:
   - a footprint leaf <leaf> (H_PROG_<X>_F): <leaf>_holds_F of lib/A/Prog/<leaf>_F.v;
   - a caller-journal function <f>: transport_<f>_cg_holds of its walk file, at TransportB and ameter_triv
     (lib/A/Prog/<f>_cgW.v, or the file its row named: diginet_frame_build_walk.v, diginet_frame_parse_walk.v,
     diginet_msg_next_walk.v, diginet_session_config_default.v, m_tick.v);
   - a runtime text (H_RT_<X>, rows RT1-RT5): the theorem of its file lib/A/Rt/Rt<X>Cg.v, stated as the hypothesis
     is;
   - PLAIN: lib/A/TransportPlainRz.v transport_plain_rz at lib/Theorems.v plain_walk, the plain walk of
     LLVMFuzzerTestOneInput.
   No hypothesis is left open: the three tops after Section close_all take no premise. *)
From Stdlib Require Import ZArith.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05 YCbp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AD2l TransportShape TransportTFIB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr
  TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportClose TransportAFacts TransportPlainRz.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Theorems.
(* The statement files the hypotheses quote. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_ack_frame_F_c
  diginet_announce_parse_F_c check_ack_settle_F_c diginet_cursor_init_F_c check_inflight_acked_F_c
  check_inflight_lost_F_c check_inflight_new_F_c io_now_F_c diginet_frame_is_keepalive_F_c check_keepalive_due_F_c
  check_keepalive_settle_F_c check_latest_control_F_c check_latest_display_F_c check_latest_drain_F_c
  check_latest_frame_F_c check_latest_submit_F_c diginet_mac_is_digidesign_F_c check_refusal_submit_F_c
  diginet_session_deadline_F_c check_state_online_F_c check_state_settle_F_c check_state_wake_F_c
  check_state_wake_code_F_c build_and_receive_cg diginet_body_check_cg check_inflight_retry_cg
  check_inflight_settle_cg check_latest_queue_cg check_latest_sent_cg check_state_data_cg check_state_desk_cg
  check_sent_frame_cg desk_named_cg diginet_frame_build_cg diginet_frame_parse_cg io_recv_cg io_send_cg
  LLVMFuzzerTestOneInput_cg maybe_online_cg m_lost_cg diginet_msg_next_cg m_maybe_online_cg m_rx_cg m_tick_cg
  m_wake_cg notice_cg on_ack_cg on_announce_cg on_data_cg diginet_personality_from_name_cg diginet_session_poll_cg
  receive_cg diginet_session_config_default_cg diginet_session_close_cg send_control_cg send_data_cg settle_cg
  diginet_session_init_cg session_lost_cg diginet_session_rx_cg diginet_session_submit_cg take_cg
  diginet_session_tick_cg diginet_session_wake_cg.
(* The walk files of the landed rows. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_ack_frame_F check_ack_settle_F
  check_inflight_acked_F check_inflight_lost_F check_inflight_new_F check_inflight_retry_cgW check_keepalive_due_F
  check_keepalive_settle_F check_latest_control_F check_latest_display_F check_latest_drain_F check_latest_frame_F
  check_latest_queue_cgW check_latest_submit_F check_refusal_submit_F check_sent_frame_cgW check_state_data_cgW
  check_state_desk_cgW check_state_online_F check_state_settle_F check_state_wake_F check_state_wake_code_F
  desk_named_cgW diginet_cursor_init_F diginet_frame_is_keepalive_F diginet_mac_is_digidesign_F diginet_msg_next_walk
  diginet_personality_from_name_cgW diginet_session_config_default diginet_session_deadline_F
  diginet_session_init_cgW io_now_F m_lost_cgW check_inflight_settle_cgW check_latest_sent_cgW
  diginet_announce_parse_F diginet_body_check_cgW diginet_frame_parse_walk m_maybe_online_cgW m_tick m_wake_cgW
  notice_cgW diginet_frame_build_walk diginet_session_submit_cgW io_send_cgW m_rx_cgW session_lost_cgW settle_cgW
  io_recv_cgW maybe_online_cgW send_control_cgW send_data_cgW diginet_session_close_cgW diginet_session_tick_cgW
  diginet_session_wake_cgW on_ack_cgW on_data_cgW on_announce_cgW diginet_session_rx_cgW diginet_session_poll_cgW
  receive_cgW build_and_receive_cgW take_cgW LLVMFuzzerTestOneInput_cgW.
(* AW72's segment CFG, for its audit below. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LLVMFuzzerTestOneInput_seg_cfg.
(* The runtime texts. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require RtStrcmpCg RtStrlenCg RtSSF8Cg RtSS00Cg RtSSF5Cg.
Open Scope Z_scope.

Module TSt := OSSVerify.libdiginet.fuzz_transport.Statements.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportClose.
Module AF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportAFacts.
Module TPR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportPlainRz.
Module TH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Theorems.
Module FAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_F_c.
Module FAP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_announce_parse_F_c.
Module FAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_settle_F_c.
Module FCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_cursor_init_F_c.
Module FIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_acked_F_c.
Module FIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_lost_F_c.
Module FINW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_F_c.
Module FION := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_now_F_c.
Module FKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_is_keepalive_F_c.
Module FKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_F_c.
Module FKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_settle_F_c.
Module FLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_F_c.
Module FLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_F_c.
Module FLDR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_drain_F_c.
Module FLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_F_c.
Module FLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_submit_F_c.
Module FMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_mac_is_digidesign_F_c.
Module FRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_F_c.
Module FSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_deadline_F_c.
Module FSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_online_F_c.
Module FSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_settle_F_c.
Module FSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_F_c.
Module FSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_code_F_c.
Module PBAR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.build_and_receive_cg.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
Module PCIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_retry_cg.
Module PCIS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_settle_cg.
Module PCLQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_queue_cg.
Module PCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_sent_cg.
Module PCSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_data_cg.
Module PCSDK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_desk_cg.
Module PCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_sent_frame_cg.
Module PDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.desk_named_cg.
Module PFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_build_cg.
Module PFP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_parse_cg.
Module PIOR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_recv_cg.
Module PIOS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_send_cg.
Module PL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_cg.
Module PMAYBEON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.maybe_online_cg.
Module PMLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_lost_cg.
Module PMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_cg.
Module PMON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_maybe_online_cg.
Module PMRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_cg.
Module PMTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_tick_cg.
Module PMWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_wake_cg.
Module PNOTICE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.notice_cg.
Module PONACK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_cg.
Module PONANN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_announce_cg.
Module PONDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_data_cg.
Module PPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_personality_from_name_cg.
Module PPOLL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_poll_cg.
Module PRECV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_cg.
Module PSCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_config_default_cg.
Module PSCL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_cg.
Module PSENDCTL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_control_cg.
Module PSENDDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_data_cg.
Module PSETTLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.settle_cg.
Module PSINIT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_init_cg.
Module PSLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.session_lost_cg.
Module PSRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_rx_cg.
Module PSSUB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_cg.
Module PTAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_cg.
Module PTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_tick_cg.
Module PWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_wake_cg.
Module WAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_F.
Module WAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_settle_F.
Module WIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_acked_F.
Module WIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_lost_F.
Module WINW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_F.
Module WCIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_retry_cgW.
Module WKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_F.
Module WKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_settle_F.
Module WLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_F.
Module WLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_F.
Module WLDR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_drain_F.
Module WLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_F.
Module WCLQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_queue_cgW.
Module WLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_submit_F.
Module WRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_F.
Module WCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_sent_frame_cgW.
Module WCSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_data_cgW.
Module WCSDK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_desk_cgW.
Module WSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_online_F.
Module WSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_settle_F.
Module WSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_F.
Module WSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_code_F.
Module WDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.desk_named_cgW.
Module WCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_cursor_init_F.
Module WKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_is_keepalive_F.
Module WMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_mac_is_digidesign_F.
Module WMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_walk.
Module WPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_personality_from_name_cgW.
Module WSCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_config_default.
Module WSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_deadline_F.
Module WSINIT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_init_cgW.
Module WION := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_now_F.
Module WMLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_lost_cgW.
Module WCIS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_settle_cgW.
Module WCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_sent_cgW.
Module WAP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_announce_parse_F.
Module WBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cgW.
Module WFP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_parse_walk.
Module WMON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_maybe_online_cgW.
Module WMTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_tick.
Module WMWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_wake_cgW.
Module WNOTICE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.notice_cgW.
Module WFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_build_walk.
Module WSSUB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_cgW.
Module WIOS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_send_cgW.
Module WMRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_cgW.
Module WSLOST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.session_lost_cgW.
Module WSETTLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.settle_cgW.
Module WTAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.take_cgW.
Module WIOR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_recv_cgW.
Module WMAYBEON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.maybe_online_cgW.
Module WSENDCTL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_control_cgW.
Module WSENDDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.send_data_cgW.
Module WSCL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_cgW.
Module WTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_tick_cgW.
Module WWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_wake_cgW.
Module WONACK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_cgW.
Module WONDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_data_cgW.
Module WONANN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_announce_cgW.
Module WSRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_rx_cgW.
Module WPOLL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_poll_cgW.
Module WRECV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_cgW.
Module WBAR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.build_and_receive_cgW.
Module RSTRCMP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt.RtStrcmpCg.
Module RSTRLEN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt.RtStrlenCg.
Module RSSF8 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt.RtSSF8Cg.
Module RSS00 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt.RtSS00Cg.
Module RSSF5 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt.RtSSF5Cg.
Module WLLVMF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_cgW.
Module WLCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_seg_cfg.

Section close_all.

(* ===================================================================================================== *)
(* CLOSED. Each landed walk and runtime text at the hypothesis it discharges.                            *)
(* ===================================================================================================== *)
(* AW1 check_ack_frame: lib/A/Prog/check_ack_frame_F.v check_ack_frame_holds_F. *)
Lemma H_PROG_C_ACK_FRAME_F : FAF.check_ack_frame_contract_F.
Proof. exact WAF.check_ack_frame_holds_F. Qed.
(* AW2 check_ack_settle: lib/A/Prog/check_ack_settle_F.v check_ack_settle_holds_F. *)
Lemma H_PROG_C_ACK_SETTLE_F : FAS.check_ack_settle_contract_F.
Proof. exact WAS.check_ack_settle_holds_F. Qed.
(* AW3 check_inflight_acked: lib/A/Prog/check_inflight_acked_F.v check_inflight_acked_holds_F. *)
Lemma H_PROG_C_INFLIGHT_ACKED_F : FIA.check_inflight_acked_contract_F.
Proof. exact WIA.check_inflight_acked_holds_F. Qed.
(* AW4 check_inflight_lost: lib/A/Prog/check_inflight_lost_F.v check_inflight_lost_holds_F. *)
Lemma H_PROG_C_INFLIGHT_LOST_F : FIL.check_inflight_lost_contract_F.
Proof. exact WIL.check_inflight_lost_holds_F. Qed.
(* AW5 check_inflight_new: lib/A/Prog/check_inflight_new_F.v check_inflight_new_holds_F. *)
Lemma H_PROG_C_INFLIGHT_NEW_F : FINW.check_inflight_new_contract_F.
Proof. exact WINW.check_inflight_new_holds_F. Qed.
(* AW6 check_inflight_retry: lib/A/Prog/check_inflight_retry_cgW.v transport_check_inflight_retry_cg_holds. *)
Lemma H_PROG_C_INFLIGHT_RETRY : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIR.transport_check_inflight_retry_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCIR.transport_check_inflight_retry_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW7 check_keepalive_due: lib/A/Prog/check_keepalive_due_F.v check_keepalive_due_holds_F. *)
Lemma H_PROG_C_KEEPALIVE_DUE_F : FKD.check_keepalive_due_contract_F.
Proof. exact WKD.check_keepalive_due_holds_F. Qed.
(* AW8 check_keepalive_settle: lib/A/Prog/check_keepalive_settle_F.v check_keepalive_settle_holds_F. *)
Lemma H_PROG_C_KEEPALIVE_SETTLE_F : FKS.check_keepalive_settle_contract_F.
Proof. exact WKS.check_keepalive_settle_holds_F. Qed.
(* AW9 check_latest_control: lib/A/Prog/check_latest_control_F.v check_latest_control_holds_F. *)
Lemma H_PROG_C_LATEST_CONTROL_F : FLC.check_latest_control_contract_F.
Proof. exact WLC.check_latest_control_holds_F. Qed.
(* AW10 check_latest_display: lib/A/Prog/check_latest_display_F.v check_latest_display_holds_F. *)
Lemma H_PROG_C_LATEST_DISPLAY_F : FLD.check_latest_display_contract_F.
Proof. exact WLD.check_latest_display_holds_F. Qed.
(* AW11 check_latest_drain: lib/A/Prog/check_latest_drain_F.v check_latest_drain_holds_F. *)
Lemma H_PROG_C_LATEST_DRAIN_F : FLDR.check_latest_drain_contract_F.
Proof. exact WLDR.check_latest_drain_holds_F. Qed.
(* AW12 check_latest_frame: lib/A/Prog/check_latest_frame_F.v check_latest_frame_holds_F. *)
Lemma H_PROG_C_LATEST_FRAME_F : FLF.check_latest_frame_contract_F.
Proof. exact WLF.check_latest_frame_holds_F. Qed.
(* AW13 check_latest_queue: lib/A/Prog/check_latest_queue_cgW.v transport_check_latest_queue_cg_holds. *)
Lemma H_PROG_C_LATEST_QUEUE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLQ.transport_check_latest_queue_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCLQ.transport_check_latest_queue_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW14 check_latest_submit: lib/A/Prog/check_latest_submit_F.v check_latest_submit_holds_F. *)
Lemma H_PROG_C_LATEST_SUBMIT_F : FLS.check_latest_submit_contract_F.
Proof. exact WLS.check_latest_submit_holds_F. Qed.
(* AW15 check_refusal_submit: lib/A/Prog/check_refusal_submit_F.v check_refusal_submit_holds_F. *)
Lemma H_PROG_C_REFUSAL_SUBMIT_F : FRS.check_refusal_submit_contract_F.
Proof. exact WRS.check_refusal_submit_holds_F. Qed.
(* AW16 check_sent_frame: lib/A/Prog/check_sent_frame_cgW.v transport_check_sent_frame_cg_holds. *)
Lemma H_PROG_C_SENT_FRAME : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSF.transport_check_sent_frame_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSF.transport_check_sent_frame_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW17 check_state_data: lib/A/Prog/check_state_data_cgW.v transport_check_state_data_cg_holds. *)
Lemma H_PROG_C_STATE_DATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSD.transport_check_state_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSD.transport_check_state_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW18 check_state_desk: lib/A/Prog/check_state_desk_cgW.v transport_check_state_desk_cg_holds. *)
Lemma H_PROG_C_STATE_DESK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSDK.transport_check_state_desk_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSDK.transport_check_state_desk_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW19 check_state_online: lib/A/Prog/check_state_online_F.v check_state_online_holds_F. *)
Lemma H_PROG_C_STATE_ONLINE_F : FSO.check_state_online_contract_F.
Proof. exact WSO.check_state_online_holds_F. Qed.
(* AW20 check_state_settle: lib/A/Prog/check_state_settle_F.v check_state_settle_holds_F. *)
Lemma H_PROG_C_STATE_SETTLE_F : FSS.check_state_settle_contract_F.
Proof. exact WSS.check_state_settle_holds_F. Qed.
(* AW21 check_state_wake: lib/A/Prog/check_state_wake_F.v check_state_wake_holds_F. *)
Lemma H_PROG_C_STATE_WAKE_F : FSW.check_state_wake_contract_F.
Proof. exact WSW.check_state_wake_holds_F. Qed.
(* AW22 check_state_wake_code: lib/A/Prog/check_state_wake_code_F.v check_state_wake_code_holds_F. *)
Lemma H_PROG_C_STATE_WAKE_CODE_F : FSWC.check_state_wake_code_contract_F.
Proof. exact WSWC.check_state_wake_code_holds_F. Qed.
(* AW24 desk_named: lib/A/Prog/desk_named_cgW.v transport_desk_named_cg_holds. *)
Lemma H_PROG_DESKNAMED : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PDN.transport_desk_named_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WDN.transport_desk_named_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW25 diginet_cursor_init: lib/A/Prog/diginet_cursor_init_F.v diginet_cursor_init_holds_F. *)
Lemma H_PROG_CINIT_F : FCI.diginet_cursor_init_contract_F.
Proof. exact WCI.diginet_cursor_init_holds_F. Qed.
(* AW26 diginet_frame_is_keepalive: lib/A/Prog/diginet_frame_is_keepalive_F.v diginet_frame_is_keepalive_holds_F. *)
Lemma H_PROG_KA_F : FKA.diginet_frame_is_keepalive_contract_F.
Proof. exact WKA.diginet_frame_is_keepalive_holds_F. Qed.
(* AW27 diginet_mac_is_digidesign: lib/A/Prog/diginet_mac_is_digidesign_F.v diginet_mac_is_digidesign_holds_F. *)
Lemma H_PROG_MACD_F : FMD.diginet_mac_is_digidesign_contract_F.
Proof. exact WMD.diginet_mac_is_digidesign_holds_F. Qed.
(* AW28 diginet_msg_next: lib/A/Prog/diginet_msg_next_walk.v transport_diginet_msg_next_cg_holds. *)
Lemma H_PROG_MNEXT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMN.transport_diginet_msg_next_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMN.transport_diginet_msg_next_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW29 diginet_personality_from_name: lib/A/Prog/diginet_personality_from_name_cgW.v
   transport_diginet_personality_from_name_cg_holds. *)
Lemma H_PROG_PFROM : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPF.transport_diginet_personality_from_name_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WPF.transport_diginet_personality_from_name_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW30 diginet_session_config_default: lib/A/Prog/diginet_session_config_default.v
   transport_diginet_session_config_default_cg_holds. *)
Lemma H_PROG_SCFG : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCFG.transport_diginet_session_config_default_cg_holds_stmt fx rc TransportB ameter_triv.
Proof.
  intros fx rc.
  exact (@WSCFG.transport_diginet_session_config_default_cg_holds fx rc TransportB ameter_triv).
Qed.
(* AW31 diginet_session_deadline: lib/A/Prog/diginet_session_deadline_F.v diginet_session_deadline_holds_F. *)
Lemma H_PROG_SDEAD_F : FSD.diginet_session_deadline_contract_F.
Proof. exact WSD.diginet_session_deadline_holds_F. Qed.
(* AW32 diginet_session_init: lib/A/Prog/diginet_session_init_cgW.v transport_diginet_session_init_cg_holds. *)
Lemma H_PROG_SINIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSINIT.transport_diginet_session_init_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSINIT.transport_diginet_session_init_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW35 io_now: lib/A/Prog/io_now_F.v io_now_holds_F. *)
Lemma H_PROG_IONOW_F : FION.io_now_contract_F.
Proof. exact WION.io_now_holds_F. Qed.
(* AW36 m_lost: lib/A/Prog/m_lost_cgW.v transport_m_lost_cg_holds. *)
Lemma H_PROG_MLOST : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMLOST.transport_m_lost_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMLOST.transport_m_lost_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW41 check_inflight_settle: lib/A/Prog/check_inflight_settle_cgW.v transport_check_inflight_settle_cg_holds. *)
Lemma H_PROG_C_INFLIGHT_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIS.transport_check_inflight_settle_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCIS.transport_check_inflight_settle_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW42 check_latest_sent: lib/A/Prog/check_latest_sent_cgW.v transport_check_latest_sent_cg_holds. *)
Lemma H_PROG_C_LATEST_SENT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLS.transport_check_latest_sent_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCLS.transport_check_latest_sent_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW43 diginet_announce_parse: lib/A/Prog/diginet_announce_parse_F.v diginet_announce_parse_holds_F. *)
Lemma H_PROG_ANNP_F : FAP.diginet_announce_parse_contract_F.
Proof. exact WAP.diginet_announce_parse_holds_F. Qed.
(* AW44 diginet_body_check: lib/A/Prog/diginet_body_check_cgW.v transport_diginet_body_check_cg_holds. *)
Lemma H_PROG_BCHK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBC.transport_diginet_body_check_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WBC.transport_diginet_body_check_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW45 diginet_frame_parse: lib/A/Prog/diginet_frame_parse_walk.v transport_diginet_frame_parse_cg_holds. *)
Lemma H_PROG_FPARSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFP.transport_diginet_frame_parse_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WFP.transport_diginet_frame_parse_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW46 m_maybe_online: lib/A/Prog/m_maybe_online_cgW.v transport_m_maybe_online_cg_holds. *)
Lemma H_PROG_MONLINE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMON.transport_m_maybe_online_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMON.transport_m_maybe_online_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW47 m_tick: lib/A/Prog/m_tick.v transport_m_tick_cg_holds. *)
Lemma H_PROG_MTICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMTICK.transport_m_tick_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMTICK.transport_m_tick_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW48 m_wake: lib/A/Prog/m_wake_cgW.v transport_m_wake_cg_holds. *)
Lemma H_PROG_MWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMWAKE.transport_m_wake_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMWAKE.transport_m_wake_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW49 notice: lib/A/Prog/notice_cgW.v transport_notice_cg_holds. *)
Lemma H_PROG_NOTICE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PNOTICE.transport_notice_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WNOTICE.transport_notice_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW50 diginet_frame_build: lib/A/Prog/diginet_frame_build_walk.v transport_diginet_frame_build_cg_holds. *)
Lemma H_PROG_FBUILD : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFB.transport_diginet_frame_build_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WFB.transport_diginet_frame_build_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW51 diginet_session_submit: lib/A/Prog/diginet_session_submit_cgW.v transport_diginet_session_submit_cg_holds. *)
Lemma H_PROG_SSUBMIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSSUB.transport_diginet_session_submit_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSSUB.transport_diginet_session_submit_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW52 io_send: lib/A/Prog/io_send_cgW.v transport_io_send_cg_holds. *)
Lemma H_PROG_IOSEND : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOS.transport_io_send_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WIOS.transport_io_send_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW53 m_rx: lib/A/Prog/m_rx_cgW.v transport_m_rx_cg_holds. *)
Lemma H_PROG_MRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMRX.transport_m_rx_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMRX.transport_m_rx_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW54 session_lost: lib/A/Prog/session_lost_cgW.v transport_session_lost_cg_holds. *)
Lemma H_PROG_SLOST : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSLOST.transport_session_lost_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSLOST.transport_session_lost_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW56 settle: lib/A/Prog/settle_cgW.v transport_settle_cg_holds. *)
Lemma H_PROG_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSETTLE.transport_settle_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSETTLE.transport_settle_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW57 take: lib/A/Prog/take_cgW.v transport_take_cg_holds. *)
Lemma H_PROG_TAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTAKE.transport_take_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WTAKE.transport_take_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW58 io_recv: lib/A/Prog/io_recv_cgW.v transport_io_recv_cg_holds. *)
Lemma H_PROG_IORECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOR.transport_io_recv_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WIOR.transport_io_recv_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW59 maybe_online: lib/A/Prog/maybe_online_cgW.v transport_maybe_online_cg_holds. *)
Lemma H_PROG_MAYBEON : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMAYBEON.transport_maybe_online_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMAYBEON.transport_maybe_online_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW60 send_control: lib/A/Prog/send_control_cgW.v transport_send_control_cg_holds. *)
Lemma H_PROG_SENDCTL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDCTL.transport_send_control_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSENDCTL.transport_send_control_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW61 send_data: lib/A/Prog/send_data_cgW.v transport_send_data_cg_holds. *)
Lemma H_PROG_SENDDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDDATA.transport_send_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSENDDATA.transport_send_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW62 diginet_session_close: lib/A/Prog/diginet_session_close_cgW.v transport_diginet_session_close_cg_holds. *)
Lemma H_PROG_SCLOSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCL.transport_diginet_session_close_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSCL.transport_diginet_session_close_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW63 diginet_session_tick: lib/A/Prog/diginet_session_tick_cgW.v transport_diginet_session_tick_cg_holds. *)
Lemma H_PROG_STICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTICK.transport_diginet_session_tick_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WTICK.transport_diginet_session_tick_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW64 diginet_session_wake: lib/A/Prog/diginet_session_wake_cgW.v transport_diginet_session_wake_cg_holds. *)
Lemma H_PROG_SWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PWAKE.transport_diginet_session_wake_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WWAKE.transport_diginet_session_wake_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW65 on_ack: lib/A/Prog/on_ack_cgW.v transport_on_ack_cg_holds. *)
Lemma H_PROG_ONACK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONACK.transport_on_ack_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONACK.transport_on_ack_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW66 on_data: lib/A/Prog/on_data_cgW.v transport_on_data_cg_holds. *)
Lemma H_PROG_ONDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONDATA.transport_on_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONDATA.transport_on_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW67 on_announce: lib/A/Prog/on_announce_cgW.v transport_on_announce_cg_holds. *)
Lemma H_PROG_ONANN : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONANN.transport_on_announce_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONANN.transport_on_announce_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW68 diginet_session_rx: lib/A/Prog/diginet_session_rx_cgW.v transport_diginet_session_rx_cg_holds. *)
Lemma H_PROG_SRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSRX.transport_diginet_session_rx_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSRX.transport_diginet_session_rx_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW69 diginet_session_poll: lib/A/Prog/diginet_session_poll_cgW.v transport_diginet_session_poll_cg_holds. *)
Lemma H_PROG_SPOLL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPOLL.transport_diginet_session_poll_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WPOLL.transport_diginet_session_poll_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW70 receive: lib/A/Prog/receive_cgW.v transport_receive_cg_holds. *)
Lemma H_PROG_RECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PRECV.transport_receive_cg_holds_stmt fx rc TransportB ameter_triv PL.CTX_receive.
Proof. intros fx rc. exact (@WRECV.transport_receive_cg_holds fx rc TransportB ameter_triv PL.CTX_receive). Qed.
(* AW71 build_and_receive: lib/A/Prog/build_and_receive_cgW.v transport_build_and_receive_cg_holds. *)
Lemma H_PROG_BAR : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBAR.transport_build_and_receive_cg_holds_stmt fx rc TransportB ameter_triv PL.CTX_build_and_receive.
Proof.
  intros fx rc.
  exact (@WBAR.transport_build_and_receive_cg_holds fx rc TransportB ameter_triv PL.CTX_build_and_receive).
Qed.
(* AW72 LLVMFuzzerTestOneInput: lib/A/Prog/LLVMFuzzerTestOneInput_cgW.v transport_LLVMFuzzerTestOneInput_cg_holds,
   at the slot's XL, RLO and RHI. *)
Lemma H_PROG_LLVMF : forall rc : YM05.RunCeil,
  @PL.transport_LLVMFuzzerTestOneInput_cg_holds_stmt rc TransportB ameter_triv TC.transport_XL0 AF.TRANSPORT_RLO
    AF.TRANSPORT_RHI.
Proof.
  intros rc.
  exact (@WLLVMF.transport_LLVMFuzzerTestOneInput_cg_holds rc TransportB ameter_triv TC.transport_XL0
    AF.TRANSPORT_RLO AF.TRANSPORT_RHI).
Qed.
(* RT1, the strcmp wrapper (trampoline 0x42cec): lib/A/Rt/RtStrcmpCg.v transport_strcmp_realizes. *)
Lemma H_RT_STRCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PPF.astrcmp_realizes fx rc tfibsegs TransportB (transport_sigma TS___interceptor_trampoline_strcmp).
Proof. exact RSTRCMP.transport_strcmp_realizes. Qed.
(* RT2, the strlen wrapper (trampoline 0x42ce4): lib/A/Rt/RtStrlenCg.v transport_strlen_realizes. *)
Lemma H_RT_STRLEN : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astrlen_realizes fx rc tfibsegs TransportB (transport_sigma TS___interceptor_trampoline_strlen).
Proof. exact RSTRLEN.transport_strlen_realizes. Qed.
(* RT3, __asan_set_shadow_f8 (0x55390): lib/A/Rt/RtSSF8Cg.v set_shadow_f8_realizes. *)
Lemma H_RT_SET_SHADOW_F8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc tfibsegs TransportB (transport_sigma TS___asan_set_shadow_f8) 0xf8.
Proof. exact RSSF8.set_shadow_f8_realizes. Qed.
(* RT4, __asan_set_shadow_00 (0x55270): lib/A/Rt/RtSS00Cg.v set_shadow_00_realizes. *)
Lemma H_RT_SET_SHADOW_00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc tfibsegs TransportB (transport_sigma TS___asan_set_shadow_00) 0.
Proof. exact RSS00.set_shadow_00_realizes. Qed.
(* RT5, __asan_set_shadow_f5 (0x55378): lib/A/Rt/RtSSF5Cg.v set_shadow_f5_realizes. *)
Lemma H_RT_SET_SHADOW_F5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc tfibsegs TransportB (transport_sigma TS___asan_set_shadow_f5) 0xf5.
Proof. exact RSSF5.set_shadow_f5_realizes. Qed.
(* PLAIN: the plain build realizes SPECX at transport_shape, from the plain walk of LLVMFuzzerTestOneInput. *)
Lemma PLAIN : transport_plain_rz_stmt.
Proof. exact (TPR.transport_plain_rz TH.plain_walk). Qed.

(* ===================================================================================================== *)
(* The tops: lib/A/TransportClose.v at every hypothesis, in its declaration order.                       *)
(* ===================================================================================================== *)
Theorem transport_TFIB_all : TFIB_T.
Proof.
  exact (TC.transport_TFIB
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_DESKNAMED H_PROG_CINIT_F
    H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT H_PROG_PFROM
    H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT H_PROG_IONOW_F
    H_PROG_MLOST H_PROG_C_INFLIGHT_SETTLE H_PROG_C_LATEST_SENT H_PROG_ANNP_F
    H_PROG_BCHK H_PROG_FPARSE H_PROG_MONLINE H_PROG_MTICK
    H_PROG_MWAKE H_PROG_NOTICE H_PROG_FBUILD H_PROG_SSUBMIT
    H_PROG_IOSEND H_PROG_MRX H_PROG_SLOST H_PROG_SETTLE
    H_PROG_TAKE H_PROG_IORECV H_PROG_MAYBEON H_PROG_SENDCTL
    H_PROG_SENDDATA H_PROG_SCLOSE H_PROG_STICK H_PROG_SWAKE
    H_PROG_ONACK H_PROG_ONDATA H_PROG_ONANN H_PROG_SRX
    H_PROG_SPOLL H_PROG_RECV H_PROG_BAR H_PROG_LLVMF
    H_RT_STRCMP H_RT_STRLEN H_RT_SET_SHADOW_F8 H_RT_SET_SHADOW_00
    H_RT_SET_SHADOW_F5).
Qed.
Theorem transport_asan_agrees_all : TSt.asan_agrees.
Proof.
  exact (TC.transport_asan_agrees_of_parts
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_DESKNAMED H_PROG_CINIT_F
    H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT H_PROG_PFROM
    H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT H_PROG_IONOW_F
    H_PROG_MLOST H_PROG_C_INFLIGHT_SETTLE H_PROG_C_LATEST_SENT H_PROG_ANNP_F
    H_PROG_BCHK H_PROG_FPARSE H_PROG_MONLINE H_PROG_MTICK
    H_PROG_MWAKE H_PROG_NOTICE H_PROG_FBUILD H_PROG_SSUBMIT
    H_PROG_IOSEND H_PROG_MRX H_PROG_SLOST H_PROG_SETTLE
    H_PROG_TAKE H_PROG_IORECV H_PROG_MAYBEON H_PROG_SENDCTL
    H_PROG_SENDDATA H_PROG_SCLOSE H_PROG_STICK H_PROG_SWAKE
    H_PROG_ONACK H_PROG_ONDATA H_PROG_ONANN H_PROG_SRX
    H_PROG_SPOLL H_PROG_RECV H_PROG_BAR H_PROG_LLVMF
    H_RT_STRCMP H_RT_STRLEN H_RT_SET_SHADOW_F8 H_RT_SET_SHADOW_00
    H_RT_SET_SHADOW_F5
    PLAIN).
Qed.
Theorem transport_asan_halts_all : TSt.asan_halts.
Proof.
  exact (TC.transport_asan_halts_of_parts
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_DESKNAMED H_PROG_CINIT_F
    H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT H_PROG_PFROM
    H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT H_PROG_IONOW_F
    H_PROG_MLOST H_PROG_C_INFLIGHT_SETTLE H_PROG_C_LATEST_SENT H_PROG_ANNP_F
    H_PROG_BCHK H_PROG_FPARSE H_PROG_MONLINE H_PROG_MTICK
    H_PROG_MWAKE H_PROG_NOTICE H_PROG_FBUILD H_PROG_SSUBMIT
    H_PROG_IOSEND H_PROG_MRX H_PROG_SLOST H_PROG_SETTLE
    H_PROG_TAKE H_PROG_IORECV H_PROG_MAYBEON H_PROG_SENDCTL
    H_PROG_SENDDATA H_PROG_SCLOSE H_PROG_STICK H_PROG_SWAKE
    H_PROG_ONACK H_PROG_ONDATA H_PROG_ONANN H_PROG_SRX
    H_PROG_SPOLL H_PROG_RECV H_PROG_BAR H_PROG_LLVMF
    H_RT_STRCMP H_RT_STRLEN H_RT_SET_SHADOW_F8 H_RT_SET_SHADOW_00
    H_RT_SET_SHADOW_F5).
Qed.
End close_all.

(* AW72's segment CFG and the composition that uses it, and the axioms each rests on. *)
About WLCFG.lc_cfg_ok.
Print Assumptions WLCFG.lc_cfg_ok.
About WLLVMF.transport_LLVMFuzzerTestOneInput_cg_holds.
Print Assumptions WLLVMF.transport_LLVMFuzzerTestOneInput_cg_holds.

(* Each top, its type (no premise) and the axioms it rests on. *)
About transport_TFIB_all.
Print Assumptions transport_TFIB_all.
About transport_asan_agrees_all.
Print Assumptions transport_asan_agrees_all.
About transport_asan_halts_all.
Print Assumptions transport_asan_halts_all.
