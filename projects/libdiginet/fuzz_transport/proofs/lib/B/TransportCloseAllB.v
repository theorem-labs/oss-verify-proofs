(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from libdiginet/fuzz_frame lib/A/FrameClose.v (file sha256 db13ebe967ec;
   donor not released; itself made from proofs/libreac/fuzz_decode/lib/A/DecodeClose.v and
   proofs/libreac/fuzz_grant/lib/A/AGrantT.v) for libdiginet/fuzz_transport's ASan image (e89be137db17): the program
   walks not yet proved, and the runtime texts no landed file proves, are the named Section hypotheses; every other part
   is a Lemma; the slot is the core's G form (lib/A/ACfn.v at G := lib/A/TransportG.v G_HARNESS, lib/A/AD1q.v with
   G_HULL); module paths and names changed. *)
(* Modified by Theorem Labs, 2026-10: made from this unit's lib/A/TransportClose.v (file sha256 80cd5ca563f9) for
   libdiginet/fuzz_transport's ASan+UBSan image (fuzz_transport.asan-ubsan 41113a03c82f): the 70 image-B program walks
   are the only Section hypotheses (no runtime text is one: the strcmp / strlen wrappers, __asan_set_shadow_f8 / _00 /
   _f5, the side-stack classes 0, 1, 2, 3, 5 and the class-5 release are proved in lib/B/Rt); the record facts are
   lib/B/TransportBFacts.v's; the slot is the image-B core's G form (lib/B/YCfn.v at G := lib/B/TransportGB.v
   G_HARNESS_B, lib/B/YD1q.v, which takes no hull premise); the conclusion is lib/B/TransportTFIBB.v TFIB_TB and the two
   ASan+UBSan statements of lib/B/AsanUbsanTop.v; module paths and names changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/TransportCloseB.v, with its module names changed; 383 of its 454 lines of code are new or changed and 716 lines of the source are left out. *)
(* The closing instantiation of lib/B/TransportCloseB.v (rule 24: no function proved; this file is assembly).

   lib/B/TransportCloseB.v proves TFIB_TB (transport_TFIB_B) and the two ASan+UBSan statements of image B
   (transport_asan_ubsan_agrees_of_parts, transport_asan_ubsan_halts_of_parts) inside its Section closeb, whose only
   hypotheses are the 70 image-B program walks (H_PROG_<X>, rows AW1-AW72 without AW36 / AW54; every runtime text is
   proved inside it); the agreement also takes the plain side transport_plain_rz_stmt as a premise of its own. This
   file gives each hypothesis the theorem that proves it, under the same name:
   - a footprint leaf <leaf> (H_PROG_<X>_F): <leaf>_holds_F of lib/B/Prog/<leaf>_F.v;
   - a caller-journal function <f>: transport_<f>_cg_holds of its walk file, at TransportB and ameter_triv
     (lib/B/Prog/<f>_cgW.v, or the file its row named: diginet_frame_parse_walk.v, diginet_session_config_default.v,
     m_tick.v; diginet_msg_next_cgW.v names its theorem transport_diginet_msg_next_cg_holds_any); receive and
     build_and_receive at the entry's contexts LLVMFuzzerTestOneInput_cg.v CTX_receive and CTX_build_and_receive;
   - the entry LLVMFuzzerTestOneInput (H_PROG_LLVMF_B): transport_LLVMFuzzerTestOneInput_cg_holds of
     lib/B/Prog/LLVMFuzzerTestOneInput_cgW.v at transportb_XL0, TRANSPORTB_RLO and TRANSPORTB_RHI;
   - the plain side PLAIN: lib/A/TransportPlainRz.v transport_plain_rz at lib/Theorems.v plain_walk, the plain walk of
     LLVMFuzzerTestOneInput.
   Every hypothesis is proved, so the three tops below take no premise. *)
From Stdlib Require Import ZArith.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05 YCbp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YD2l TransportTFIBB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportCloseB TransportBFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportPlainRz.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Theorems.
(* The statement files the hypotheses quote. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require check_ack_frame_F_c check_ack_settle_F_c
  check_inflight_acked_F_c check_inflight_lost_F_c check_inflight_new_F_c check_keepalive_due_F_c
  check_keepalive_settle_F_c check_latest_control_F_c check_latest_display_F_c check_latest_drain_F_c
  check_latest_frame_F_c check_latest_submit_F_c check_refusal_submit_F_c check_state_online_F_c
  check_state_settle_F_c check_state_wake_F_c check_state_wake_code_F_c copy_strz_F_c diginet_cursor_init_F_c
  diginet_frame_is_keepalive_F_c diginet_mac_is_digidesign_F_c diginet_session_deadline_F_c diginet_sum16_F_c
  io_now_F_c rd32_F_c tagged_of_F_c check_inflight_retry_cg check_latest_queue_cg check_sent_frame_cg
  check_state_data_cg check_state_desk_cg desk_named_cg diginet_msg_next_cg diginet_personality_from_name_cg
  diginet_session_config_default_cg diginet_session_init_cg host_offset_cg m_set_cg spec_read_frame_cg
  check_inflight_settle_cg check_latest_sent_cg diginet_announce_parse_cg diginet_body_check_cg diginet_frame_parse_cg
  m_maybe_online_cg m_tick_cg m_wake_cg notice_cg diginet_frame_build_cg diginet_session_submit_cg io_send_cg m_rx_cg
  set_state_cg settle_cg take_cg io_recv_cg maybe_online_cg send_control_cg send_data_cg diginet_session_close_cg
  diginet_session_tick_cg diginet_session_wake_cg on_ack_cg on_data_cg on_announce_cg diginet_session_rx_cg
  diginet_session_poll_cg receive_cg build_and_receive_cg LLVMFuzzerTestOneInput_cg.
(* The walk files of the landed rows. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require check_ack_frame_F check_ack_settle_F
  check_inflight_acked_F check_inflight_lost_F check_inflight_new_F check_keepalive_due_F check_keepalive_settle_F
  check_latest_control_F check_latest_display_F check_latest_drain_F check_latest_frame_F check_latest_submit_F
  check_refusal_submit_F check_state_online_F check_state_settle_F check_state_wake_F check_state_wake_code_F
  copy_strz_F diginet_cursor_init_F diginet_frame_is_keepalive_F diginet_mac_is_digidesign_F
  diginet_session_deadline_F diginet_sum16_F io_now_F rd32_F tagged_of_F check_inflight_retry_cgW
  check_latest_queue_cgW check_sent_frame_cgW check_state_data_cgW check_state_desk_cgW desk_named_cgW
  diginet_msg_next_cgW diginet_personality_from_name_cgW diginet_session_config_default diginet_session_init_cgW
  host_offset_cgW m_set_cgW spec_read_frame_cgW check_inflight_settle_cgW check_latest_sent_cgW
  diginet_announce_parse_cgW diginet_body_check_cgW diginet_frame_parse_walk m_maybe_online_cgW m_tick m_wake_cgW
  notice_cgW diginet_frame_build_cgW diginet_session_submit_cgW io_send_cgW m_rx_cgW set_state_cgW settle_cgW take_cgW
  io_recv_cgW maybe_online_cgW send_control_cgW send_data_cgW diginet_session_close_cgW diginet_session_tick_cgW
  diginet_session_wake_cgW on_ack_cgW on_data_cgW on_announce_cgW diginet_session_rx_cgW diginet_session_poll_cgW
  receive_cgW build_and_receive_cgW LLVMFuzzerTestOneInput_cgW.
Open Scope Z_scope.

Module TSt := OSSVerify.libdiginet.fuzz_transport.Statements.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportCloseB.
Module BF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportBFacts.
Module TPR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportPlainRz.
Module TH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Theorems.
Module FAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_frame_F_c.
Module FAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_settle_F_c.
Module FIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_F_c.
Module FIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_F_c.
Module FINW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_F_c.
Module FKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_due_F_c.
Module FKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_settle_F_c.
Module FLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_F_c.
Module FLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_display_F_c.
Module FLDR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_drain_F_c.
Module FLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_F_c.
Module FLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_submit_F_c.
Module FRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_F_c.
Module FSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_F_c.
Module FSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_settle_F_c.
Module FSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_F_c.
Module FSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_F_c.
Module FCSZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.copy_strz_F_c.
Module FCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_F_c.
Module FKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_F_c.
Module FMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_F_c.
Module FSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_F_c.
Module FSUM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_sum16_F_c.
Module FION := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_now_F_c.
Module FRD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.rd32_F_c.
Module FTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_F_c.
Module PCIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_retry_cg.
Module PCLQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_queue_cg.
Module PCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_sent_frame_cg.
Module PCSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_data_cg.
Module PCSDK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_desk_cg.
Module PDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.desk_named_cg.
Module PMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
Module PPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_personality_from_name_cg.
Module PSCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_config_default_cg.
Module PSINIT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_init_cg.
Module PHOFF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.host_offset_cg.
Module PMSET := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_set_cg.
Module PSRF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.spec_read_frame_cg.
Module PCIS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_settle_cg.
Module PCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_sent_cg.
Module PANP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_announce_parse_cg.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_body_check_cg.
Module PFP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_parse_cg.
Module PMON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_maybe_online_cg.
Module PMTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_tick_cg.
Module PMWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_wake_cg.
Module PNOTICE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.notice_cg.
Module PFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_cg.
Module PSSUB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_submit_cg.
Module PIOS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_send_cg.
Module PMRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_rx_cg.
Module PSSTATE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.set_state_cg.
Module PSETTLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.settle_cg.
Module PTAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.take_cg.
Module PIOR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_recv_cg.
Module PMAYBEON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.maybe_online_cg.
Module PSENDCTL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.send_control_cg.
Module PSENDDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.send_data_cg.
Module PSCL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_close_cg.
Module PTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_tick_cg.
Module PWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_wake_cg.
Module PONACK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_cg.
Module PONDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_cg.
Module PONANN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_cg.
Module PSRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_rx_cg.
Module PPOLL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_poll_cg.
Module PRECV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.receive_cg.
Module PBAR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.build_and_receive_cg.
Module PL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module WAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_frame_F.
Module WAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_settle_F.
Module WIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_F.
Module WIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_F.
Module WINW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_F.
Module WKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_due_F.
Module WKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_settle_F.
Module WLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_F.
Module WLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_display_F.
Module WLDR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_drain_F.
Module WLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_F.
Module WLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_submit_F.
Module WRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_F.
Module WSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_F.
Module WSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_settle_F.
Module WSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_F.
Module WSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_F.
Module WCSZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.copy_strz_F.
Module WCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_F.
Module WKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_F.
Module WMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_F.
Module WSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_F.
Module WSUM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_sum16_F.
Module WION := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_now_F.
Module WRD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.rd32_F.
Module WTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_F.
Module WCIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_retry_cgW.
Module WCLQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_queue_cgW.
Module WCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_sent_frame_cgW.
Module WCSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_data_cgW.
Module WCSDK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_desk_cgW.
Module WDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.desk_named_cgW.
Module WMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cgW.
Module WPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_personality_from_name_cgW.
Module WSCFG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_config_default.
Module WSINIT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_init_cgW.
Module WHOFF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.host_offset_cgW.
Module WMSET := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_set_cgW.
Module WSRF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.spec_read_frame_cgW.
Module WCIS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_settle_cgW.
Module WCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_sent_cgW.
Module WANP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_announce_parse_cgW.
Module WBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_body_check_cgW.
Module WFP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_parse_walk.
Module WMON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_maybe_online_cgW.
Module WMTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_tick.
Module WMWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_wake_cgW.
Module WNOTICE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.notice_cgW.
Module WFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_cgW.
Module WSSUB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_submit_cgW.
Module WIOS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_send_cgW.
Module WMRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_rx_cgW.
Module WSSTATE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.set_state_cgW.
Module WSETTLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.settle_cgW.
Module WTAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.take_cgW.
Module WIOR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_recv_cgW.
Module WMAYBEON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.maybe_online_cgW.
Module WSENDCTL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.send_control_cgW.
Module WSENDDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.send_data_cgW.
Module WSCL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_close_cgW.
Module WTICK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_tick_cgW.
Module WWAKE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_wake_cgW.
Module WONACK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_cgW.
Module WONDATA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_cgW.
Module WONANN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_cgW.
Module WSRX := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_rx_cgW.
Module WPOLL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_poll_cgW.
Module WRECV := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.receive_cgW.
Module WBAR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.build_and_receive_cgW.
Module WL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LLVMFuzzerTestOneInput_cgW.

Section close_allB.

(* ===================================================================================================== *)
(* CLOSED. Each landed walk at the hypothesis it discharges.                                             *)
(* ===================================================================================================== *)
(* AW1 check_ack_frame: lib/B/Prog/check_ack_frame_F.v check_ack_frame_holds_F. *)
Lemma H_PROG_C_ACK_FRAME_F : FAF.check_ack_frame_contract_F.
Proof. exact WAF.check_ack_frame_holds_F. Qed.
(* AW2 check_ack_settle: lib/B/Prog/check_ack_settle_F.v check_ack_settle_holds_F. *)
Lemma H_PROG_C_ACK_SETTLE_F : FAS.check_ack_settle_contract_F.
Proof. exact WAS.check_ack_settle_holds_F. Qed.
(* AW3 check_inflight_acked: lib/B/Prog/check_inflight_acked_F.v check_inflight_acked_holds_F. *)
Lemma H_PROG_C_INFLIGHT_ACKED_F : FIA.check_inflight_acked_contract_F.
Proof. exact WIA.check_inflight_acked_holds_F. Qed.
(* AW4 check_inflight_lost: lib/B/Prog/check_inflight_lost_F.v check_inflight_lost_holds_F. *)
Lemma H_PROG_C_INFLIGHT_LOST_F : FIL.check_inflight_lost_contract_F.
Proof. exact WIL.check_inflight_lost_holds_F. Qed.
(* AW5 check_inflight_new: lib/B/Prog/check_inflight_new_F.v check_inflight_new_holds_F. *)
Lemma H_PROG_C_INFLIGHT_NEW_F : FINW.check_inflight_new_contract_F.
Proof. exact WINW.check_inflight_new_holds_F. Qed.
(* AW6 check_inflight_retry: lib/B/Prog/check_inflight_retry_cgW.v transport_check_inflight_retry_cg_holds. *)
Lemma H_PROG_C_INFLIGHT_RETRY : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIR.transport_check_inflight_retry_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCIR.transport_check_inflight_retry_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW7 check_keepalive_due: lib/B/Prog/check_keepalive_due_F.v check_keepalive_due_holds_F. *)
Lemma H_PROG_C_KEEPALIVE_DUE_F : FKD.check_keepalive_due_contract_F.
Proof. exact WKD.check_keepalive_due_holds_F. Qed.
(* AW8 check_keepalive_settle: lib/B/Prog/check_keepalive_settle_F.v check_keepalive_settle_holds_F. *)
Lemma H_PROG_C_KEEPALIVE_SETTLE_F : FKS.check_keepalive_settle_contract_F.
Proof. exact WKS.check_keepalive_settle_holds_F. Qed.
(* AW9 check_latest_control: lib/B/Prog/check_latest_control_F.v check_latest_control_holds_F. *)
Lemma H_PROG_C_LATEST_CONTROL_F : FLC.check_latest_control_contract_F.
Proof. exact WLC.check_latest_control_holds_F. Qed.
(* AW10 check_latest_display: lib/B/Prog/check_latest_display_F.v check_latest_display_holds_F. *)
Lemma H_PROG_C_LATEST_DISPLAY_F : FLD.check_latest_display_contract_F.
Proof. exact WLD.check_latest_display_holds_F. Qed.
(* AW11 check_latest_drain: lib/B/Prog/check_latest_drain_F.v check_latest_drain_holds_F. *)
Lemma H_PROG_C_LATEST_DRAIN_F : FLDR.check_latest_drain_contract_F.
Proof. exact WLDR.check_latest_drain_holds_F. Qed.
(* AW12 check_latest_frame: lib/B/Prog/check_latest_frame_F.v check_latest_frame_holds_F. *)
Lemma H_PROG_C_LATEST_FRAME_F : FLF.check_latest_frame_contract_F.
Proof. exact WLF.check_latest_frame_holds_F. Qed.
(* AW13 check_latest_queue: lib/B/Prog/check_latest_queue_cgW.v transport_check_latest_queue_cg_holds. *)
Lemma H_PROG_C_LATEST_QUEUE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLQ.transport_check_latest_queue_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCLQ.transport_check_latest_queue_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW14 check_latest_submit: lib/B/Prog/check_latest_submit_F.v check_latest_submit_holds_F. *)
Lemma H_PROG_C_LATEST_SUBMIT_F : FLS.check_latest_submit_contract_F.
Proof. exact WLS.check_latest_submit_holds_F. Qed.
(* AW15 check_refusal_submit: lib/B/Prog/check_refusal_submit_F.v check_refusal_submit_holds_F. *)
Lemma H_PROG_C_REFUSAL_SUBMIT_F : FRS.check_refusal_submit_contract_F.
Proof. exact WRS.check_refusal_submit_holds_F. Qed.
(* AW16 check_sent_frame: lib/B/Prog/check_sent_frame_cgW.v transport_check_sent_frame_cg_holds. *)
Lemma H_PROG_C_SENT_FRAME : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSF.transport_check_sent_frame_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSF.transport_check_sent_frame_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW17 check_state_data: lib/B/Prog/check_state_data_cgW.v transport_check_state_data_cg_holds. *)
Lemma H_PROG_C_STATE_DATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSD.transport_check_state_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSD.transport_check_state_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW18 check_state_desk: lib/B/Prog/check_state_desk_cgW.v transport_check_state_desk_cg_holds. *)
Lemma H_PROG_C_STATE_DESK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSDK.transport_check_state_desk_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCSDK.transport_check_state_desk_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW19 check_state_online: lib/B/Prog/check_state_online_F.v check_state_online_holds_F. *)
Lemma H_PROG_C_STATE_ONLINE_F : FSO.check_state_online_contract_F.
Proof. exact WSO.check_state_online_holds_F. Qed.
(* AW20 check_state_settle: lib/B/Prog/check_state_settle_F.v check_state_settle_holds_F. *)
Lemma H_PROG_C_STATE_SETTLE_F : FSS.check_state_settle_contract_F.
Proof. exact WSS.check_state_settle_holds_F. Qed.
(* AW21 check_state_wake: lib/B/Prog/check_state_wake_F.v check_state_wake_holds_F. *)
Lemma H_PROG_C_STATE_WAKE_F : FSW.check_state_wake_contract_F.
Proof. exact WSW.check_state_wake_holds_F. Qed.
(* AW22 check_state_wake_code: lib/B/Prog/check_state_wake_code_F.v check_state_wake_code_holds_F. *)
Lemma H_PROG_C_STATE_WAKE_CODE_F : FSWC.check_state_wake_code_contract_F.
Proof. exact WSWC.check_state_wake_code_holds_F. Qed.
(* AW23 copy_strz: lib/B/Prog/copy_strz_F.v copy_strz_holds_F. *)
Lemma H_PROG_COPYSTRZ_F : FCSZ.copy_strz_contract_F.
Proof. exact WCSZ.copy_strz_holds_F. Qed.
(* AW24 desk_named: lib/B/Prog/desk_named_cgW.v transport_desk_named_cg_holds. *)
Lemma H_PROG_DESKNAMED : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PDN.transport_desk_named_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WDN.transport_desk_named_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW25 diginet_cursor_init: lib/B/Prog/diginet_cursor_init_F.v diginet_cursor_init_holds_F. *)
Lemma H_PROG_CINIT_F : FCI.diginet_cursor_init_contract_F.
Proof. exact WCI.diginet_cursor_init_holds_F. Qed.
(* AW26 diginet_frame_is_keepalive: lib/B/Prog/diginet_frame_is_keepalive_F.v diginet_frame_is_keepalive_holds_F. *)
Lemma H_PROG_KA_F : FKA.diginet_frame_is_keepalive_contract_F.
Proof. exact WKA.diginet_frame_is_keepalive_holds_F. Qed.
(* AW27 diginet_mac_is_digidesign: lib/B/Prog/diginet_mac_is_digidesign_F.v diginet_mac_is_digidesign_holds_F. *)
Lemma H_PROG_MACD_F : FMD.diginet_mac_is_digidesign_contract_F.
Proof. exact WMD.diginet_mac_is_digidesign_holds_F. Qed.
(* AW28 diginet_msg_next: lib/B/Prog/diginet_msg_next_cgW.v transport_diginet_msg_next_cg_holds_any. *)
Lemma H_PROG_MNEXT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMN.transport_diginet_msg_next_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMN.transport_diginet_msg_next_cg_holds_any fx rc TransportB ameter_triv). Qed.
(* AW29 diginet_personality_from_name: lib/B/Prog/diginet_personality_from_name_cgW.v
   transport_diginet_personality_from_name_cg_holds. *)
Lemma H_PROG_PFROM : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPF.transport_diginet_personality_from_name_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WPF.transport_diginet_personality_from_name_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW30 diginet_session_config_default: lib/B/Prog/diginet_session_config_default.v
   transport_diginet_session_config_default_cg_holds. *)
Lemma H_PROG_SCFG : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCFG.transport_diginet_session_config_default_cg_holds_stmt fx rc TransportB ameter_triv.
Proof.
  intros fx rc.
  exact (@WSCFG.transport_diginet_session_config_default_cg_holds fx rc TransportB ameter_triv).
Qed.
(* AW31 diginet_session_deadline: lib/B/Prog/diginet_session_deadline_F.v diginet_session_deadline_holds_F. *)
Lemma H_PROG_SDEAD_F : FSD.diginet_session_deadline_contract_F.
Proof. exact WSD.diginet_session_deadline_holds_F. Qed.
(* AW32 diginet_session_init: lib/B/Prog/diginet_session_init_cgW.v transport_diginet_session_init_cg_holds. *)
Lemma H_PROG_SINIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSINIT.transport_diginet_session_init_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSINIT.transport_diginet_session_init_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW33 diginet_sum16: lib/B/Prog/diginet_sum16_F.v diginet_sum16_holds_F. *)
Lemma H_PROG_SUM16_F : FSUM.diginet_sum16_contract_F.
Proof. exact WSUM.diginet_sum16_holds_F. Qed.
(* AW34 host_offset: lib/B/Prog/host_offset_cgW.v transport_host_offset_cg_holds. *)
Lemma H_PROG_HOSTOFF : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PHOFF.transport_host_offset_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WHOFF.transport_host_offset_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW35 io_now: lib/B/Prog/io_now_F.v io_now_holds_F. *)
Lemma H_PROG_IONOW_F : FION.io_now_contract_F.
Proof. exact WION.io_now_holds_F. Qed.
(* AW37 m_set: lib/B/Prog/m_set_cgW.v transport_m_set_cg_holds. *)
Lemma H_PROG_MSET : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMSET.transport_m_set_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMSET.transport_m_set_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW38 rd32: lib/B/Prog/rd32_F.v rd32_holds_F. *)
Lemma H_PROG_RD32_F : FRD.rd32_contract_F.
Proof. exact WRD.rd32_holds_F. Qed.
(* AW39 spec_read_frame: lib/B/Prog/spec_read_frame_cgW.v transport_spec_read_frame_cg_holds. *)
Lemma H_PROG_SPECRF : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSRF.transport_spec_read_frame_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSRF.transport_spec_read_frame_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW40 tagged_of: lib/B/Prog/tagged_of_F.v tagged_of_holds_F. *)
Lemma H_PROG_TAGGED_F : FTO.tagged_of_contract_F.
Proof. exact WTO.tagged_of_holds_F. Qed.
(* AW41 check_inflight_settle: lib/B/Prog/check_inflight_settle_cgW.v transport_check_inflight_settle_cg_holds. *)
Lemma H_PROG_C_INFLIGHT_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIS.transport_check_inflight_settle_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCIS.transport_check_inflight_settle_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW42 check_latest_sent: lib/B/Prog/check_latest_sent_cgW.v transport_check_latest_sent_cg_holds. *)
Lemma H_PROG_C_LATEST_SENT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLS.transport_check_latest_sent_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WCLS.transport_check_latest_sent_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW43 diginet_announce_parse: lib/B/Prog/diginet_announce_parse_cgW.v transport_diginet_announce_parse_cg_holds. *)
Lemma H_PROG_ANNP : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PANP.transport_diginet_announce_parse_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WANP.transport_diginet_announce_parse_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW44 diginet_body_check: lib/B/Prog/diginet_body_check_cgW.v transport_diginet_body_check_cg_holds. *)
Lemma H_PROG_BCHK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBC.transport_diginet_body_check_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WBC.transport_diginet_body_check_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW45 diginet_frame_parse: lib/B/Prog/diginet_frame_parse_walk.v transport_diginet_frame_parse_cg_holds. *)
Lemma H_PROG_FPARSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFP.transport_diginet_frame_parse_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WFP.transport_diginet_frame_parse_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW46 m_maybe_online: lib/B/Prog/m_maybe_online_cgW.v transport_m_maybe_online_cg_holds. *)
Lemma H_PROG_MONLINE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMON.transport_m_maybe_online_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMON.transport_m_maybe_online_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW47 m_tick: lib/B/Prog/m_tick.v transport_m_tick_cg_holds. *)
Lemma H_PROG_MTICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMTICK.transport_m_tick_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMTICK.transport_m_tick_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW48 m_wake: lib/B/Prog/m_wake_cgW.v transport_m_wake_cg_holds. *)
Lemma H_PROG_MWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMWAKE.transport_m_wake_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMWAKE.transport_m_wake_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW49 notice: lib/B/Prog/notice_cgW.v transport_notice_cg_holds. *)
Lemma H_PROG_NOTICE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PNOTICE.transport_notice_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WNOTICE.transport_notice_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW50 diginet_frame_build: lib/B/Prog/diginet_frame_build_cgW.v transport_diginet_frame_build_cg_holds. *)
Lemma H_PROG_FBUILD : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFB.transport_diginet_frame_build_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WFB.transport_diginet_frame_build_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW51 diginet_session_submit: lib/B/Prog/diginet_session_submit_cgW.v transport_diginet_session_submit_cg_holds. *)
Lemma H_PROG_SSUBMIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSSUB.transport_diginet_session_submit_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSSUB.transport_diginet_session_submit_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW52 io_send: lib/B/Prog/io_send_cgW.v transport_io_send_cg_holds. *)
Lemma H_PROG_IOSEND : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOS.transport_io_send_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WIOS.transport_io_send_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW53 m_rx: lib/B/Prog/m_rx_cgW.v transport_m_rx_cg_holds. *)
Lemma H_PROG_MRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMRX.transport_m_rx_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMRX.transport_m_rx_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW55 set_state: lib/B/Prog/set_state_cgW.v transport_set_state_cg_holds. *)
Lemma H_PROG_SETSTATE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSSTATE.transport_set_state_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSSTATE.transport_set_state_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW56 settle: lib/B/Prog/settle_cgW.v transport_settle_cg_holds. *)
Lemma H_PROG_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSETTLE.transport_settle_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSETTLE.transport_settle_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW57 take: lib/B/Prog/take_cgW.v transport_take_cg_holds. *)
Lemma H_PROG_TAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTAKE.transport_take_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WTAKE.transport_take_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW58 io_recv: lib/B/Prog/io_recv_cgW.v transport_io_recv_cg_holds. *)
Lemma H_PROG_IORECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOR.transport_io_recv_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WIOR.transport_io_recv_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW59 maybe_online: lib/B/Prog/maybe_online_cgW.v transport_maybe_online_cg_holds. *)
Lemma H_PROG_MAYBEON : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMAYBEON.transport_maybe_online_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WMAYBEON.transport_maybe_online_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW60 send_control: lib/B/Prog/send_control_cgW.v transport_send_control_cg_holds. *)
Lemma H_PROG_SENDCTL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDCTL.transport_send_control_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSENDCTL.transport_send_control_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW61 send_data: lib/B/Prog/send_data_cgW.v transport_send_data_cg_holds. *)
Lemma H_PROG_SENDDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDDATA.transport_send_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSENDDATA.transport_send_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW62 diginet_session_close: lib/B/Prog/diginet_session_close_cgW.v transport_diginet_session_close_cg_holds. *)
Lemma H_PROG_SCLOSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCL.transport_diginet_session_close_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSCL.transport_diginet_session_close_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW63 diginet_session_tick: lib/B/Prog/diginet_session_tick_cgW.v transport_diginet_session_tick_cg_holds. *)
Lemma H_PROG_STICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTICK.transport_diginet_session_tick_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WTICK.transport_diginet_session_tick_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW64 diginet_session_wake: lib/B/Prog/diginet_session_wake_cgW.v transport_diginet_session_wake_cg_holds. *)
Lemma H_PROG_SWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PWAKE.transport_diginet_session_wake_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WWAKE.transport_diginet_session_wake_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW65 on_ack: lib/B/Prog/on_ack_cgW.v transport_on_ack_cg_holds. *)
Lemma H_PROG_ONACK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONACK.transport_on_ack_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONACK.transport_on_ack_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW66 on_data: lib/B/Prog/on_data_cgW.v transport_on_data_cg_holds. *)
Lemma H_PROG_ONDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONDATA.transport_on_data_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONDATA.transport_on_data_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW67 on_announce: lib/B/Prog/on_announce_cgW.v transport_on_announce_cg_holds. *)
Lemma H_PROG_ONANN : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONANN.transport_on_announce_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WONANN.transport_on_announce_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW68 diginet_session_rx: lib/B/Prog/diginet_session_rx_cgW.v transport_diginet_session_rx_cg_holds. *)
Lemma H_PROG_SRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSRX.transport_diginet_session_rx_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WSRX.transport_diginet_session_rx_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW69 diginet_session_poll: lib/B/Prog/diginet_session_poll_cgW.v transport_diginet_session_poll_cg_holds. *)
Lemma H_PROG_SPOLL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPOLL.transport_diginet_session_poll_cg_holds_stmt fx rc TransportB ameter_triv.
Proof. intros fx rc. exact (@WPOLL.transport_diginet_session_poll_cg_holds fx rc TransportB ameter_triv). Qed.
(* AW70 receive: lib/B/Prog/receive_cgW.v transport_receive_cg_holds. *)
Lemma H_PROG_RECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PRECV.transport_receive_cg_holds_stmt fx rc TransportB ameter_triv PL.CTX_receive.
Proof. intros fx rc. exact (@WRECV.transport_receive_cg_holds fx rc TransportB ameter_triv PL.CTX_receive). Qed.
(* AW71 build_and_receive: lib/B/Prog/build_and_receive_cgW.v transport_build_and_receive_cg_holds. *)
Lemma H_PROG_BAR : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBAR.transport_build_and_receive_cg_holds_stmt fx rc TransportB ameter_triv PL.CTX_build_and_receive.
Proof.
  intros fx rc.
  exact (@WBAR.transport_build_and_receive_cg_holds fx rc TransportB ameter_triv PL.CTX_build_and_receive).
Qed.
(* AW72 LLVMFuzzerTestOneInput: lib/B/Prog/LLVMFuzzerTestOneInput_cgW.v transport_LLVMFuzzerTestOneInput_cg_holds. *)
Lemma H_PROG_LLVMF_B : forall rc : YM05.RunCeil,
  @PL.transport_LLVMFuzzerTestOneInput_cg_holds_stmt rc TransportB ameter_triv TCB.transportb_XL0 BF.TRANSPORTB_RLO
    BF.TRANSPORTB_RHI.
Proof.
  intros rc.
  exact (@WL.transport_LLVMFuzzerTestOneInput_cg_holds rc TransportB ameter_triv TCB.transportb_XL0
    BF.TRANSPORTB_RLO BF.TRANSPORTB_RHI).
Qed.
(* PLAIN: the plain build realizes SPECX at transport_shape, from the plain walk of LLVMFuzzerTestOneInput. *)
Lemma PLAIN : transport_plain_rz_stmt.
Proof. exact (TPR.transport_plain_rz TH.plain_walk). Qed.

(* ===================================================================================================== *)
(* The tops: lib/B/TransportCloseB.v at every hypothesis, in its declaration order.                      *)
(* ===================================================================================================== *)
Theorem transport_TFIB_B_all : TFIB_TB.
Proof.
  exact (TCB.transport_TFIB_B
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_COPYSTRZ_F H_PROG_DESKNAMED
    H_PROG_CINIT_F H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT
    H_PROG_PFROM H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT
    H_PROG_SUM16_F H_PROG_HOSTOFF H_PROG_IONOW_F H_PROG_MSET
    H_PROG_RD32_F H_PROG_SPECRF H_PROG_TAGGED_F H_PROG_C_INFLIGHT_SETTLE
    H_PROG_C_LATEST_SENT H_PROG_ANNP H_PROG_BCHK H_PROG_FPARSE
    H_PROG_MONLINE H_PROG_MTICK H_PROG_MWAKE H_PROG_NOTICE
    H_PROG_FBUILD H_PROG_SSUBMIT H_PROG_IOSEND H_PROG_MRX
    H_PROG_SETSTATE H_PROG_SETTLE H_PROG_TAKE H_PROG_IORECV
    H_PROG_MAYBEON H_PROG_SENDCTL H_PROG_SENDDATA H_PROG_SCLOSE
    H_PROG_STICK H_PROG_SWAKE H_PROG_ONACK H_PROG_ONDATA
    H_PROG_ONANN H_PROG_SRX H_PROG_SPOLL H_PROG_RECV
    H_PROG_BAR H_PROG_LLVMF_B).
Qed.
Theorem transport_asan_ubsan_agrees_all : TSt.asan_ubsan_agrees.
Proof.
  exact (TCB.transport_asan_ubsan_agrees_of_parts
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_COPYSTRZ_F H_PROG_DESKNAMED
    H_PROG_CINIT_F H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT
    H_PROG_PFROM H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT
    H_PROG_SUM16_F H_PROG_HOSTOFF H_PROG_IONOW_F H_PROG_MSET
    H_PROG_RD32_F H_PROG_SPECRF H_PROG_TAGGED_F H_PROG_C_INFLIGHT_SETTLE
    H_PROG_C_LATEST_SENT H_PROG_ANNP H_PROG_BCHK H_PROG_FPARSE
    H_PROG_MONLINE H_PROG_MTICK H_PROG_MWAKE H_PROG_NOTICE
    H_PROG_FBUILD H_PROG_SSUBMIT H_PROG_IOSEND H_PROG_MRX
    H_PROG_SETSTATE H_PROG_SETTLE H_PROG_TAKE H_PROG_IORECV
    H_PROG_MAYBEON H_PROG_SENDCTL H_PROG_SENDDATA H_PROG_SCLOSE
    H_PROG_STICK H_PROG_SWAKE H_PROG_ONACK H_PROG_ONDATA
    H_PROG_ONANN H_PROG_SRX H_PROG_SPOLL H_PROG_RECV
    H_PROG_BAR H_PROG_LLVMF_B
    PLAIN).
Qed.
Theorem transport_asan_ubsan_halts_all : TSt.asan_ubsan_halts.
Proof.
  exact (TCB.transport_asan_ubsan_halts_of_parts
    H_PROG_C_ACK_FRAME_F H_PROG_C_ACK_SETTLE_F H_PROG_C_INFLIGHT_ACKED_F H_PROG_C_INFLIGHT_LOST_F
    H_PROG_C_INFLIGHT_NEW_F H_PROG_C_INFLIGHT_RETRY H_PROG_C_KEEPALIVE_DUE_F H_PROG_C_KEEPALIVE_SETTLE_F
    H_PROG_C_LATEST_CONTROL_F H_PROG_C_LATEST_DISPLAY_F H_PROG_C_LATEST_DRAIN_F H_PROG_C_LATEST_FRAME_F
    H_PROG_C_LATEST_QUEUE H_PROG_C_LATEST_SUBMIT_F H_PROG_C_REFUSAL_SUBMIT_F H_PROG_C_SENT_FRAME
    H_PROG_C_STATE_DATA H_PROG_C_STATE_DESK H_PROG_C_STATE_ONLINE_F H_PROG_C_STATE_SETTLE_F
    H_PROG_C_STATE_WAKE_F H_PROG_C_STATE_WAKE_CODE_F H_PROG_COPYSTRZ_F H_PROG_DESKNAMED
    H_PROG_CINIT_F H_PROG_KA_F H_PROG_MACD_F H_PROG_MNEXT
    H_PROG_PFROM H_PROG_SCFG H_PROG_SDEAD_F H_PROG_SINIT
    H_PROG_SUM16_F H_PROG_HOSTOFF H_PROG_IONOW_F H_PROG_MSET
    H_PROG_RD32_F H_PROG_SPECRF H_PROG_TAGGED_F H_PROG_C_INFLIGHT_SETTLE
    H_PROG_C_LATEST_SENT H_PROG_ANNP H_PROG_BCHK H_PROG_FPARSE
    H_PROG_MONLINE H_PROG_MTICK H_PROG_MWAKE H_PROG_NOTICE
    H_PROG_FBUILD H_PROG_SSUBMIT H_PROG_IOSEND H_PROG_MRX
    H_PROG_SETSTATE H_PROG_SETTLE H_PROG_TAKE H_PROG_IORECV
    H_PROG_MAYBEON H_PROG_SENDCTL H_PROG_SENDDATA H_PROG_SCLOSE
    H_PROG_STICK H_PROG_SWAKE H_PROG_ONACK H_PROG_ONDATA
    H_PROG_ONANN H_PROG_SRX H_PROG_SPOLL H_PROG_RECV
    H_PROG_BAR H_PROG_LLVMF_B).
Qed.
End close_allB.

(* Each top, which takes no premise, and the axioms it rests on. *)
About transport_TFIB_B_all.
Print Assumptions transport_TFIB_B_all.
About transport_asan_ubsan_agrees_all.
Print Assumptions transport_asan_ubsan_agrees_all.
About transport_asan_ubsan_halts_all.
Print Assumptions transport_asan_ubsan_halts_all.
