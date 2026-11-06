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
(* The closing side of fuzz_transport's two ASan+UBSan statements of image B (rule 24: no function proved; this file is
   assembly).

   TFIB_TB (lib/B/TransportTFIBB.v) is closed as image A's TFIB_T is closed (lib/A/TransportClose.v): lib/B/YD1q.v
   tfib_srealizesX joins the start-up certificate and the driver's closed walk over the program contract at the harness
   globals (lib/B/YCfn.v tfib_lib_contract_x_all at G := G_HARNESS_B) and the runtime walks. The slot is LIB_CONTRACT
   below: the entry function's statement (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v
   transport_LLVMFuzzerTestOneInput_cg_holds_stmt) applied to every callee's statement and every fact about the
   record. From TFIB_TB, lib/B/AsanUbsanTop.v gives Statements.asan_ubsan_agrees (with the plain build's realization
   lib/A/TransportShape.v transport_plain_rz_stmt, a premise of that conclusion alone) and Statements.asan_ubsan_halts.

   The Section's hypotheses are the 70 image-B program walks, named as the row table names them (H_PROG_<X>): for each
   of the 44 caller-journal functions the `_holds_stmt` of its lib/B/Prog/<f>_cg.v, and for each of the 26 footprint
   leaves the `<leaf>_contract_F` of its lib/B/Prog/<leaf>_F_c.v. Every other part is a Lemma:
   - the facts about the record, computed at TransportB in lib/B/TransportBFacts.v;
   - the kit rows (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME, H_LEAF_GLUE), from lib/B/Prog/LeafCgClose.v, and each leaf's
     translation lib/B/Prog/<leaf>_cg.v transport_<leaf>_cg_of_F over them;
   - the runtime walks of the relocated core and of lib/B/Rt at TransportB (malloc, free, memcpy, memset, bcmp, the
     strcmp and strlen wrappers, __asan_set_shadow_f8 / _00 / _f5, the stack-malloc classes 0, 1, 2, 3, 5, the class-5
     release) and the call rules of receive (amalloc04_rule / afree04_rule);
   - every other row: one application of a core lemma at TransportB.
   TFIB_TB, Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts occur only as the conclusions below. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.libdiginet.fuzz_transport.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n YA02 YG00 YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YI00 YO05 YO09 YO06
YO01 YF0p.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YE00 YE01 YG05 YG0t.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1h YB1v YF0m YCfn YD2l YCeg YD1v YD1w YD1x
YD1i YD1k YD1l YD1o YD1j YD2m YF0w YF0q YE2k YD1u YCej YD1q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportTFIBB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2r YE2q YE2s AsanUbsanTop TransportGB
  TransportBFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Rt Require StackMalloc0 StackMalloc1 StackMalloc2 RtSM3
  RtSM5 RtSF5CgB RtSS00CgB RtSSF5CgB RtSSF8CgB RtStrcmpCgB RtStrlenCgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr
  DgnTransportBCg TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBImg LeafCgKit LeafCgClose.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LLVMFuzzerTestOneInput_cg
  build_and_receive_cg check_inflight_retry_cg check_inflight_settle_cg check_latest_queue_cg check_latest_sent_cg
  check_sent_frame_cg check_state_data_cg check_state_desk_cg desk_named_cg diginet_announce_parse_cg
  diginet_body_check_cg diginet_frame_build_cg diginet_frame_parse_cg diginet_msg_next_cg
  diginet_personality_from_name_cg diginet_session_close_cg diginet_session_config_default_cg diginet_session_init_cg
  diginet_session_poll_cg diginet_session_rx_cg diginet_session_submit_cg diginet_session_tick_cg
  diginet_session_wake_cg host_offset_cg io_recv_cg io_send_cg m_maybe_online_cg m_rx_cg m_set_cg m_tick_cg m_wake_cg
  maybe_online_cg notice_cg on_ack_cg on_announce_cg on_data_cg receive_cg send_control_cg send_data_cg set_state_cg
  settle_cg spec_read_frame_cg take_cg check_ack_frame_cg check_ack_settle_cg check_inflight_acked_cg
  check_inflight_lost_cg check_inflight_new_cg check_keepalive_due_cg check_keepalive_settle_cg
  check_latest_control_cg check_latest_display_cg check_latest_drain_cg check_latest_frame_cg check_latest_submit_cg
  check_refusal_submit_cg check_state_online_cg check_state_settle_cg check_state_wake_cg check_state_wake_code_cg
  copy_strz_cg diginet_cursor_init_cg diginet_frame_is_keepalive_cg diginet_mac_is_digidesign_cg
  diginet_session_deadline_cg diginet_sum16_cg io_now_cg rd32_cg tagged_of_cg check_ack_frame_F_c
  check_ack_settle_F_c check_inflight_acked_F_c check_inflight_lost_F_c check_inflight_new_F_c
  check_keepalive_due_F_c check_keepalive_settle_F_c check_latest_control_F_c check_latest_display_F_c
  check_latest_drain_F_c check_latest_frame_F_c check_latest_submit_F_c check_refusal_submit_F_c
  check_state_online_F_c check_state_settle_F_c check_state_wake_F_c check_state_wake_code_F_c copy_strz_F_c
  diginet_cursor_init_F_c diginet_frame_is_keepalive_F_c diginet_mac_is_digidesign_F_c diginet_session_deadline_F_c
  diginet_sum16_F_c io_now_F_c rd32_F_c tagged_of_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance transport_shape.

Module TSt := OSSVerify.libdiginet.fuzz_transport.Statements.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module YE00 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YE00.
Module YE01 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YE01.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module BF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportBFacts.
Module LK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LClose := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgClose.
Module DImg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBImg.
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
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_frame_cg.
Module LAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_settle_cg.
Module LIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_cg.
Module LIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_cg.
Module LINW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_new_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_due_cg.
Module LKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_settle_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_display_cg.
Module LLDR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_drain_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_frame_cg.
Module LLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_submit_cg.
Module LRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_cg.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_cg.
Module LSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_settle_cg.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_cg.
Module LSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_cg.
Module LCSZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.copy_strz_cg.
Module LCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_cg.
Module LKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_is_keepalive_cg.
Module LMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_cg.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_cg.
Module LSUM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_sum16_cg.
Module LION := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.io_now_cg.
Module LRD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.rd32_cg.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
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

(* The guard (libreac/fuzz_grant's lib/A/GrantTop.v:45-53): the plain build's sink hints are out of the way, so no
   `{SK}` of a walk or of a contract can be filled with the plain build's head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

(* The meter the walks carry: it counts nothing (fuzz_frame's frame_XL0, fuzz_grant's lib/A/AGrantT.v XL0). *)
Definition transportb_XL0 : Z -> Z := fun _ => 0.
(* The stack-pointer window, from valid_sp (fuzz_frame's valid_sp_windowF). *)
Lemma valid_sp_windowTB : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section closeb.
Local Notation segs := tfibsegs.
(* B: the image's symbol and trace record, the image-B core's lib/B/YD2l.v TransportB (TransportB_syms :
   TransportSyms TransportB). *)
Local Notation B := TransportB.
Local Notation MT := ameter_triv.
Local Notation XL := transportb_XL0.
Local Notation RLO := BF.TRANSPORTB_RLO.
Local Notation RHI := BF.TRANSPORTB_RHI.
Local Notation SK := YE2k.tfib_sink_head.
Local Notation KS := YE2k.tfib_K.

(* ===================================================================================================== *)
(* HYPOTHESES. The program walks (the row table's names; rows AW1-AW72 without AW36 / AW54, image B)      *)
(* ===================================================================================================== *)
(* AW1 check_ack_frame: lib/B/Prog/check_ack_frame_F_c.v check_ack_frame_contract_F. *)
Hypothesis H_PROG_C_ACK_FRAME_F : FAF.check_ack_frame_contract_F.
(* AW2 check_ack_settle: lib/B/Prog/check_ack_settle_F_c.v check_ack_settle_contract_F. *)
Hypothesis H_PROG_C_ACK_SETTLE_F : FAS.check_ack_settle_contract_F.
(* AW3 check_inflight_acked: lib/B/Prog/check_inflight_acked_F_c.v check_inflight_acked_contract_F. *)
Hypothesis H_PROG_C_INFLIGHT_ACKED_F : FIA.check_inflight_acked_contract_F.
(* AW4 check_inflight_lost: lib/B/Prog/check_inflight_lost_F_c.v check_inflight_lost_contract_F. *)
Hypothesis H_PROG_C_INFLIGHT_LOST_F : FIL.check_inflight_lost_contract_F.
(* AW5 check_inflight_new: lib/B/Prog/check_inflight_new_F_c.v check_inflight_new_contract_F. *)
Hypothesis H_PROG_C_INFLIGHT_NEW_F : FINW.check_inflight_new_contract_F.
(* AW6 check_inflight_retry: lib/B/Prog/check_inflight_retry_cg.v transport_check_inflight_retry_cg_holds_stmt. *)
Hypothesis H_PROG_C_INFLIGHT_RETRY : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIR.transport_check_inflight_retry_cg_holds_stmt fx rc B MT.
(* AW7 check_keepalive_due: lib/B/Prog/check_keepalive_due_F_c.v check_keepalive_due_contract_F. *)
Hypothesis H_PROG_C_KEEPALIVE_DUE_F : FKD.check_keepalive_due_contract_F.
(* AW8 check_keepalive_settle: lib/B/Prog/check_keepalive_settle_F_c.v check_keepalive_settle_contract_F. *)
Hypothesis H_PROG_C_KEEPALIVE_SETTLE_F : FKS.check_keepalive_settle_contract_F.
(* AW9 check_latest_control: lib/B/Prog/check_latest_control_F_c.v check_latest_control_contract_F. *)
Hypothesis H_PROG_C_LATEST_CONTROL_F : FLC.check_latest_control_contract_F.
(* AW10 check_latest_display: lib/B/Prog/check_latest_display_F_c.v check_latest_display_contract_F. *)
Hypothesis H_PROG_C_LATEST_DISPLAY_F : FLD.check_latest_display_contract_F.
(* AW11 check_latest_drain: lib/B/Prog/check_latest_drain_F_c.v check_latest_drain_contract_F. *)
Hypothesis H_PROG_C_LATEST_DRAIN_F : FLDR.check_latest_drain_contract_F.
(* AW12 check_latest_frame: lib/B/Prog/check_latest_frame_F_c.v check_latest_frame_contract_F. *)
Hypothesis H_PROG_C_LATEST_FRAME_F : FLF.check_latest_frame_contract_F.
(* AW13 check_latest_queue: lib/B/Prog/check_latest_queue_cg.v transport_check_latest_queue_cg_holds_stmt. *)
Hypothesis H_PROG_C_LATEST_QUEUE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLQ.transport_check_latest_queue_cg_holds_stmt fx rc B MT.
(* AW14 check_latest_submit: lib/B/Prog/check_latest_submit_F_c.v check_latest_submit_contract_F. *)
Hypothesis H_PROG_C_LATEST_SUBMIT_F : FLS.check_latest_submit_contract_F.
(* AW15 check_refusal_submit: lib/B/Prog/check_refusal_submit_F_c.v check_refusal_submit_contract_F. *)
Hypothesis H_PROG_C_REFUSAL_SUBMIT_F : FRS.check_refusal_submit_contract_F.
(* AW16 check_sent_frame: lib/B/Prog/check_sent_frame_cg.v transport_check_sent_frame_cg_holds_stmt. *)
Hypothesis H_PROG_C_SENT_FRAME : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSF.transport_check_sent_frame_cg_holds_stmt fx rc B MT.
(* AW17 check_state_data: lib/B/Prog/check_state_data_cg.v transport_check_state_data_cg_holds_stmt. *)
Hypothesis H_PROG_C_STATE_DATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSD.transport_check_state_data_cg_holds_stmt fx rc B MT.
(* AW18 check_state_desk: lib/B/Prog/check_state_desk_cg.v transport_check_state_desk_cg_holds_stmt. *)
Hypothesis H_PROG_C_STATE_DESK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCSDK.transport_check_state_desk_cg_holds_stmt fx rc B MT.
(* AW19 check_state_online: lib/B/Prog/check_state_online_F_c.v check_state_online_contract_F. *)
Hypothesis H_PROG_C_STATE_ONLINE_F : FSO.check_state_online_contract_F.
(* AW20 check_state_settle: lib/B/Prog/check_state_settle_F_c.v check_state_settle_contract_F. *)
Hypothesis H_PROG_C_STATE_SETTLE_F : FSS.check_state_settle_contract_F.
(* AW21 check_state_wake: lib/B/Prog/check_state_wake_F_c.v check_state_wake_contract_F. *)
Hypothesis H_PROG_C_STATE_WAKE_F : FSW.check_state_wake_contract_F.
(* AW22 check_state_wake_code: lib/B/Prog/check_state_wake_code_F_c.v check_state_wake_code_contract_F. *)
Hypothesis H_PROG_C_STATE_WAKE_CODE_F : FSWC.check_state_wake_code_contract_F.
(* AW23 copy_strz: lib/B/Prog/copy_strz_F_c.v copy_strz_contract_F. *)
Hypothesis H_PROG_COPYSTRZ_F : FCSZ.copy_strz_contract_F.
(* AW24 desk_named: lib/B/Prog/desk_named_cg.v transport_desk_named_cg_holds_stmt. *)
Hypothesis H_PROG_DESKNAMED : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PDN.transport_desk_named_cg_holds_stmt fx rc B MT.
(* AW25 diginet_cursor_init: lib/B/Prog/diginet_cursor_init_F_c.v diginet_cursor_init_contract_F. *)
Hypothesis H_PROG_CINIT_F : FCI.diginet_cursor_init_contract_F.
(* AW26 diginet_frame_is_keepalive: lib/B/Prog/diginet_frame_is_keepalive_F_c.v diginet_frame_is_keepalive_contract_F. *)
Hypothesis H_PROG_KA_F : FKA.diginet_frame_is_keepalive_contract_F.
(* AW27 diginet_mac_is_digidesign: lib/B/Prog/diginet_mac_is_digidesign_F_c.v diginet_mac_is_digidesign_contract_F. *)
Hypothesis H_PROG_MACD_F : FMD.diginet_mac_is_digidesign_contract_F.
(* AW28 diginet_msg_next: lib/B/Prog/diginet_msg_next_cg.v transport_diginet_msg_next_cg_holds_stmt. *)
Hypothesis H_PROG_MNEXT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMN.transport_diginet_msg_next_cg_holds_stmt fx rc B MT.
(* AW29 diginet_personality_from_name: lib/B/Prog/diginet_personality_from_name_cg.v transport_diginet_personality_from_name_cg_holds_stmt. *)
Hypothesis H_PROG_PFROM : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPF.transport_diginet_personality_from_name_cg_holds_stmt fx rc B MT.
(* AW30 diginet_session_config_default: lib/B/Prog/diginet_session_config_default_cg.v transport_diginet_session_config_default_cg_holds_stmt. *)
Hypothesis H_PROG_SCFG : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCFG.transport_diginet_session_config_default_cg_holds_stmt fx rc B MT.
(* AW31 diginet_session_deadline: lib/B/Prog/diginet_session_deadline_F_c.v diginet_session_deadline_contract_F. *)
Hypothesis H_PROG_SDEAD_F : FSD.diginet_session_deadline_contract_F.
(* AW32 diginet_session_init: lib/B/Prog/diginet_session_init_cg.v transport_diginet_session_init_cg_holds_stmt. *)
Hypothesis H_PROG_SINIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSINIT.transport_diginet_session_init_cg_holds_stmt fx rc B MT.
(* AW33 diginet_sum16: lib/B/Prog/diginet_sum16_F_c.v diginet_sum16_contract_F. *)
Hypothesis H_PROG_SUM16_F : FSUM.diginet_sum16_contract_F.
(* AW34 host_offset: lib/B/Prog/host_offset_cg.v transport_host_offset_cg_holds_stmt. *)
Hypothesis H_PROG_HOSTOFF : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PHOFF.transport_host_offset_cg_holds_stmt fx rc B MT.
(* AW35 io_now: lib/B/Prog/io_now_F_c.v io_now_contract_F. *)
Hypothesis H_PROG_IONOW_F : FION.io_now_contract_F.
(* AW37 m_set: lib/B/Prog/m_set_cg.v transport_m_set_cg_holds_stmt. *)
Hypothesis H_PROG_MSET : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMSET.transport_m_set_cg_holds_stmt fx rc B MT.
(* AW38 rd32: lib/B/Prog/rd32_F_c.v rd32_contract_F. *)
Hypothesis H_PROG_RD32_F : FRD.rd32_contract_F.
(* AW39 spec_read_frame: lib/B/Prog/spec_read_frame_cg.v transport_spec_read_frame_cg_holds_stmt. *)
Hypothesis H_PROG_SPECRF : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSRF.transport_spec_read_frame_cg_holds_stmt fx rc B MT.
(* AW40 tagged_of: lib/B/Prog/tagged_of_F_c.v tagged_of_contract_F. *)
Hypothesis H_PROG_TAGGED_F : FTO.tagged_of_contract_F.
(* AW41 check_inflight_settle: lib/B/Prog/check_inflight_settle_cg.v transport_check_inflight_settle_cg_holds_stmt. *)
Hypothesis H_PROG_C_INFLIGHT_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCIS.transport_check_inflight_settle_cg_holds_stmt fx rc B MT.
(* AW42 check_latest_sent: lib/B/Prog/check_latest_sent_cg.v transport_check_latest_sent_cg_holds_stmt. *)
Hypothesis H_PROG_C_LATEST_SENT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PCLS.transport_check_latest_sent_cg_holds_stmt fx rc B MT.
(* AW43 diginet_announce_parse: lib/B/Prog/diginet_announce_parse_cg.v transport_diginet_announce_parse_cg_holds_stmt. *)
Hypothesis H_PROG_ANNP : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PANP.transport_diginet_announce_parse_cg_holds_stmt fx rc B MT.
(* AW44 diginet_body_check: lib/B/Prog/diginet_body_check_cg.v transport_diginet_body_check_cg_holds_stmt. *)
Hypothesis H_PROG_BCHK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBC.transport_diginet_body_check_cg_holds_stmt fx rc B MT.
(* AW45 diginet_frame_parse: lib/B/Prog/diginet_frame_parse_cg.v transport_diginet_frame_parse_cg_holds_stmt. *)
Hypothesis H_PROG_FPARSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFP.transport_diginet_frame_parse_cg_holds_stmt fx rc B MT.
(* AW46 m_maybe_online: lib/B/Prog/m_maybe_online_cg.v transport_m_maybe_online_cg_holds_stmt. *)
Hypothesis H_PROG_MONLINE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMON.transport_m_maybe_online_cg_holds_stmt fx rc B MT.
(* AW47 m_tick: lib/B/Prog/m_tick_cg.v transport_m_tick_cg_holds_stmt. *)
Hypothesis H_PROG_MTICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMTICK.transport_m_tick_cg_holds_stmt fx rc B MT.
(* AW48 m_wake: lib/B/Prog/m_wake_cg.v transport_m_wake_cg_holds_stmt. *)
Hypothesis H_PROG_MWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMWAKE.transport_m_wake_cg_holds_stmt fx rc B MT.
(* AW49 notice: lib/B/Prog/notice_cg.v transport_notice_cg_holds_stmt. *)
Hypothesis H_PROG_NOTICE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PNOTICE.transport_notice_cg_holds_stmt fx rc B MT.
(* AW50 diginet_frame_build: lib/B/Prog/diginet_frame_build_cg.v transport_diginet_frame_build_cg_holds_stmt. *)
Hypothesis H_PROG_FBUILD : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PFB.transport_diginet_frame_build_cg_holds_stmt fx rc B MT.
(* AW51 diginet_session_submit: lib/B/Prog/diginet_session_submit_cg.v transport_diginet_session_submit_cg_holds_stmt. *)
Hypothesis H_PROG_SSUBMIT : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSSUB.transport_diginet_session_submit_cg_holds_stmt fx rc B MT.
(* AW52 io_send: lib/B/Prog/io_send_cg.v transport_io_send_cg_holds_stmt. *)
Hypothesis H_PROG_IOSEND : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOS.transport_io_send_cg_holds_stmt fx rc B MT.
(* AW53 m_rx: lib/B/Prog/m_rx_cg.v transport_m_rx_cg_holds_stmt. *)
Hypothesis H_PROG_MRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMRX.transport_m_rx_cg_holds_stmt fx rc B MT.
(* AW55 set_state: lib/B/Prog/set_state_cg.v transport_set_state_cg_holds_stmt. *)
Hypothesis H_PROG_SETSTATE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSSTATE.transport_set_state_cg_holds_stmt fx rc B MT.
(* AW56 settle: lib/B/Prog/settle_cg.v transport_settle_cg_holds_stmt. *)
Hypothesis H_PROG_SETTLE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSETTLE.transport_settle_cg_holds_stmt fx rc B MT.
(* AW57 take: lib/B/Prog/take_cg.v transport_take_cg_holds_stmt. *)
Hypothesis H_PROG_TAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTAKE.transport_take_cg_holds_stmt fx rc B MT.
(* AW58 io_recv: lib/B/Prog/io_recv_cg.v transport_io_recv_cg_holds_stmt. *)
Hypothesis H_PROG_IORECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PIOR.transport_io_recv_cg_holds_stmt fx rc B MT.
(* AW59 maybe_online: lib/B/Prog/maybe_online_cg.v transport_maybe_online_cg_holds_stmt. *)
Hypothesis H_PROG_MAYBEON : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PMAYBEON.transport_maybe_online_cg_holds_stmt fx rc B MT.
(* AW60 send_control: lib/B/Prog/send_control_cg.v transport_send_control_cg_holds_stmt. *)
Hypothesis H_PROG_SENDCTL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDCTL.transport_send_control_cg_holds_stmt fx rc B MT.
(* AW61 send_data: lib/B/Prog/send_data_cg.v transport_send_data_cg_holds_stmt. *)
Hypothesis H_PROG_SENDDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSENDDATA.transport_send_data_cg_holds_stmt fx rc B MT.
(* AW62 diginet_session_close: lib/B/Prog/diginet_session_close_cg.v transport_diginet_session_close_cg_holds_stmt. *)
Hypothesis H_PROG_SCLOSE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSCL.transport_diginet_session_close_cg_holds_stmt fx rc B MT.
(* AW63 diginet_session_tick: lib/B/Prog/diginet_session_tick_cg.v transport_diginet_session_tick_cg_holds_stmt. *)
Hypothesis H_PROG_STICK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PTICK.transport_diginet_session_tick_cg_holds_stmt fx rc B MT.
(* AW64 diginet_session_wake: lib/B/Prog/diginet_session_wake_cg.v transport_diginet_session_wake_cg_holds_stmt. *)
Hypothesis H_PROG_SWAKE : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PWAKE.transport_diginet_session_wake_cg_holds_stmt fx rc B MT.
(* AW65 on_ack: lib/B/Prog/on_ack_cg.v transport_on_ack_cg_holds_stmt. *)
Hypothesis H_PROG_ONACK : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONACK.transport_on_ack_cg_holds_stmt fx rc B MT.
(* AW66 on_data: lib/B/Prog/on_data_cg.v transport_on_data_cg_holds_stmt. *)
Hypothesis H_PROG_ONDATA : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONDATA.transport_on_data_cg_holds_stmt fx rc B MT.
(* AW67 on_announce: lib/B/Prog/on_announce_cg.v transport_on_announce_cg_holds_stmt. *)
Hypothesis H_PROG_ONANN : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PONANN.transport_on_announce_cg_holds_stmt fx rc B MT.
(* AW68 diginet_session_rx: lib/B/Prog/diginet_session_rx_cg.v transport_diginet_session_rx_cg_holds_stmt. *)
Hypothesis H_PROG_SRX : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PSRX.transport_diginet_session_rx_cg_holds_stmt fx rc B MT.
(* AW69 diginet_session_poll: lib/B/Prog/diginet_session_poll_cg.v transport_diginet_session_poll_cg_holds_stmt. *)
Hypothesis H_PROG_SPOLL : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PPOLL.transport_diginet_session_poll_cg_holds_stmt fx rc B MT.
(* AW70 receive: lib/B/Prog/receive_cg.v transport_receive_cg_holds_stmt, at the contexts the entry statement
   names (LLVMFuzzerTestOneInput_cg.v CTX_receive, which holds build_and_receive's bar_recv_ctx CTX_build_and_receive). *)
Hypothesis H_PROG_RECV : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PRECV.transport_receive_cg_holds_stmt fx rc B MT PL.CTX_receive.
(* AW71 build_and_receive: lib/B/Prog/build_and_receive_cg.v transport_build_and_receive_cg_holds_stmt, at the
   entry's contexts (LLVMFuzzerTestOneInput_cg.v CTX_build_and_receive). *)
Hypothesis H_PROG_BAR : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @PBAR.transport_build_and_receive_cg_holds_stmt fx rc B MT PL.CTX_build_and_receive.
(* AW72 LLVMFuzzerTestOneInput: lib/B/Prog/LLVMFuzzerTestOneInput_cg.v
   transport_LLVMFuzzerTestOneInput_cg_holds_stmt (the slot at G_HARNESS_B); the row table's H_PROG_LLVMF, named with
   _B here to keep it apart from image A's entry hypothesis (lib/A/TransportClose.v H_PROG_LLVMF). *)
Hypothesis H_PROG_LLVMF_B : forall rc : YM05.RunCeil,
  @PL.transport_LLVMFuzzerTestOneInput_cg_holds_stmt rc B MT XL RLO RHI.

(* ===================================================================================================== *)
(* 1. The kit rows (lib/B/Prog/LeafCgClose.v)                                                              *)
(* ===================================================================================================== *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact LClose.dec_b_kit_aview_ext. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact LClose.dec_b_kit_aview_some. Qed.
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @transport_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. exact (LClose.dec_b_leaf_glue B). Qed.

(* ===================================================================================================== *)
(* 2. The runtime walks at TransportB (relocated core, lib/B/Rt)                                           *)
(* ===================================================================================================== *)
(* The side-stack classes 0, 1, 2 (lib/B/Rt/StackMalloc0.v, StackMalloc1.v, StackMalloc2.v ctrl_stack_malloc0 / 1 /
   2), 3 (lib/B/Rt/RtSM3.v cmd_stack_malloc3_contract) and 5 (lib/B/Rt/RtSM5.v cmd_stack_malloc5_contract). *)
Lemma H_RT_STACK_MALLOC0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 0.
Proof. intros rc fx. exact (StackMalloc0.ctrl_stack_malloc0 fx B (AR_laws_ok segs B) TransportB_syms). Qed.
Lemma H_RT_STACK_MALLOC1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 1.
Proof. intros rc fx. exact (StackMalloc1.ctrl_stack_malloc1 fx B (AR_laws_ok segs B) TransportB_syms). Qed.
Lemma H_RT_STACK_MALLOC2 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 2.
Proof. intros rc fx. exact (StackMalloc2.ctrl_stack_malloc2 fx B (AR_laws_ok segs B) TransportB_syms). Qed.
Lemma H_RT_STACK_MALLOC3 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 3.
Proof. intros rc fx. exact (RtSM3.cmd_stack_malloc3_contract B (AR_laws_ok segs B) TransportB_syms). Qed.
Lemma H_RT_STACK_MALLOC5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 5.
Proof. intros rc fx. exact (RtSM5.cmd_stack_malloc5_contract B (AR_laws_ok segs B) TransportB_syms). Qed.
(* The class-5 release (0x3df4c): lib/B/Rt/RtSF5CgB.v stack_free5_realizes_B. *)
Remark transportb_stack_free5_pc : transportb_sigma TB___asan_stack_free_5 = 0x3df4c.
Proof. reflexivity. Qed.
Lemma H_RT_STACK_FREE5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astack_free_cls_realizes fx rc segs B (transportb_sigma TB___asan_stack_free_5) 5.
Proof.
  intros rc fx. rewrite transportb_stack_free5_pc.
  exact (RtSF5CgB.stack_free5_realizes_B B (AR_laws_ok segs B) TransportB_syms).
Qed.
(* H_RT_MALLOC / H_RT_FREE: lib/B/YF0w.v tfib_amalloc_realizes and lib/B/YF0q.v afree_realizes_closed. *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. intros rc fx. exact (@tfib_amalloc_realizes fx rc B TransportB_syms (fun t => eq_refl)). Qed.
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. intros rc fx. exact (@afree_realizes_closed fx rc B TransportB_syms (fun t => eq_refl)). Qed.
(* The listing's addresses of the runtime entries the program calls are the pcs the core's contracts are stated
   at. *)
Remark transportb_asan_memset_pc : transportb_sigma TB___asan_memset = 0x52888.
Proof. reflexivity. Qed.
Remark transportb_asan_memcpy_pc : transportb_sigma TB___asan_memcpy = 0x523ec.
Proof. reflexivity. Qed.
Remark transportb_bcmp_pc : transportb_sigma TB___interceptor_trampoline_bcmp = 0x42d34.
Proof. reflexivity. Qed.
(* H_RT_ASAN_MEMSET / H_RT_ASAN_MEMCPY / H_RT_BCMP: lib/B/YE2r.v asan_memset_realizes, lib/B/YE2q.v
   asan_memcpy_realizes and lib/B/YE2s.v bcmp_icpt_contract at TransportB. *)
Lemma H_RT_ASAN_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OSet (transportb_sigma TB___asan_memset).
Proof.
  intros rc fx. rewrite transportb_asan_memset_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (YE2r.asan_memset_realizes B (AR_laws_ok tfibsegs B) TransportB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (transportb_sigma TB___asan_memcpy).
Proof.
  intros rc fx. rewrite transportb_asan_memcpy_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (YE2q.asan_memcpy_realizes B (AR_laws_ok tfibsegs B) TransportB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Proof.
  intros rc fx. rewrite transportb_bcmp_pc. exact (YE2s.bcmp_icpt_contract B (AR_laws_ok tfibsegs B) TransportB_syms).
Qed.
(* The strcmp wrapper (the trampoline 0x42d28), diginet_personality_from_name_cg.v astrcmp_realizes:
   lib/B/Rt/RtStrcmpCgB.v transport_strcmp_realizes_B. *)
Lemma H_RT_STRCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PPF.astrcmp_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strcmp).
Proof. exact RtStrcmpCgB.transport_strcmp_realizes_B. Qed.
(* The strlen wrapper (the trampoline 0x42d20), TransportRtCg.v astrlen_realizes: lib/B/Rt/RtStrlenCgB.v
   transport_strlen_realizes_B. *)
Lemma H_RT_STRLEN : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astrlen_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strlen).
Proof. exact RtStrlenCgB.transport_strlen_realizes_B. Qed.
(* __asan_set_shadow_f8 / _00 / _f5, TransportRtCg.v aset_shadow_realizes: lib/B/Rt/RtSSF8CgB.v, RtSS00CgB.v,
   RtSSF5CgB.v set_shadow_{f8,00,f5}_realizes_B. *)
Lemma H_RT_SET_SHADOW_F8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc segs B (transportb_sigma TB___asan_set_shadow_f8) 0xf8.
Proof. exact RtSSF8CgB.set_shadow_f8_realizes_B. Qed.
Lemma H_RT_SET_SHADOW_00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc segs B (transportb_sigma TB___asan_set_shadow_00) 0.
Proof. exact RtSS00CgB.set_shadow_00_realizes_B. Qed.
Lemma H_RT_SET_SHADOW_F5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc segs B (transportb_sigma TB___asan_set_shadow_f5) 0xf5.
Proof. exact RtSSF5CgB.set_shadow_f5_realizes_B. Qed.

(* ===================================================================================================== *)
(* 3. The laws, at TransportB                                                                              *)
(* ===================================================================================================== *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact ameter_triv_fs_laws. Qed.
(* HB_SMP / HB_ASF / HB_FFL: Reusable/YG05.v stack_malloc_progress, Reusable/YG0t.v astack_free_law_ok, and AR_laws's
   al_flag / al_client_img with the image cover lib/B/YCeg.v tfib_img_cover (fuzz_frame's HB_SMP / HB_ASF / HB_FFL). *)
Lemma HB_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (YG05.stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma HB_ASF : forall (rc : YM05.RunCeil), astack_free_law segs B.
Proof. intros rc. exact (YG0t.astack_free_law_ok (rc := rc) segs B). Qed.
Lemma HB_FFL : forall (rc : YM05.RunCeil), frame_flag_lawP segs B.
Proof.
intros rc ly S W mem md cid pos HAR Hin.
pose proof (AR_laws_ok segs B) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04: the call-rule form receive takes, Reusable/YCbp.v amalloc04_rule_triv /
   afree04_rule_triv at the image's segments (lib/B/Prog/DgnTransportBImg.v transportb_segs_low), api_env, AR_laws_ok
   and model_laws (lib/B/TransportBFacts.v). *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc segs B -> @amalloc04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AM. apply (amalloc04_rule_triv (SK := SK) segs B).
  - exact DImg.transportb_segs_low.
  - exact BF.api_env_TB.
  - apply AR_laws_ok.
  - exact BF.model_laws_TB.
  - exact AM.
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc segs B -> @afree04_rule fx rc SK segs B MT.
Proof.
  intros rc fx AF0. apply (afree04_rule_triv (SK := SK) segs B).
  - exact DImg.transportb_segs_low.
  - exact BF.api_env_TB.
  - apply AR_laws_ok.
  - exact BF.model_laws_TB.
  - exact AF0.
Qed.
(* HB_COST: the meter bound of one call of the entry function, at MT = ameter_triv (every malloc and free costs 0)
   and XL = transportb_XL0. *)
Lemma HB_COST : forall n, 0 <= n -> PL.transport_llvmf_cost MT n <= XL n.
Proof. intros n _. unfold PL.transport_llvmf_cost, transportb_XL0, ameter_triv. cbn [mo_malloc mo_free]. lia. Qed.

(* ===================================================================================================== *)
(* The composition, bottom-up                                                                             *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.

(* The 26 leaves, each from its translation transport_<leaf>_cg_of_F (lib/B/Prog/<leaf>_cg.v) over the kit's generic
   translation H_LEAF_GLUE, applied to its footprint contract (fuzz_frame's LEAF_* form). *)
Lemma LEAF_C_ACK_FRAME : forall fx : YK11.FPState, @transport_leaf_at rc B (@LAF.transport_check_ack_frame_cg) fx.
Proof.
  intros fx. exact (@LAF.transport_check_ack_frame_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_ACK_FRAME_F).
Qed.
Lemma LEAF_C_ACK_SETTLE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LAS.transport_check_ack_settle_cg) fx.
Proof.
  intros fx. exact (@LAS.transport_check_ack_settle_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_ACK_SETTLE_F).
Qed.
Lemma LEAF_C_INFLIGHT_ACKED : forall fx : YK11.FPState, @transport_leaf_at rc B (@LIA.transport_check_inflight_acked_cg) fx.
Proof.
  intros fx. exact (@LIA.transport_check_inflight_acked_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_INFLIGHT_ACKED_F).
Qed.
Lemma LEAF_C_INFLIGHT_LOST : forall fx : YK11.FPState, @transport_leaf_at rc B (@LIL.transport_check_inflight_lost_cg) fx.
Proof.
  intros fx. exact (@LIL.transport_check_inflight_lost_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_INFLIGHT_LOST_F).
Qed.
Lemma LEAF_C_INFLIGHT_NEW : forall fx : YK11.FPState, @transport_leaf_at rc B (@LINW.transport_check_inflight_new_cg) fx.
Proof.
  intros fx. exact (@LINW.transport_check_inflight_new_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_INFLIGHT_NEW_F).
Qed.
Lemma LEAF_C_KEEPALIVE_DUE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LKD.transport_check_keepalive_due_cg) fx.
Proof.
  intros fx. exact (@LKD.transport_check_keepalive_due_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_KEEPALIVE_DUE_F).
Qed.
Lemma LEAF_C_KEEPALIVE_SETTLE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LKS.transport_check_keepalive_settle_cg) fx.
Proof.
  intros fx. exact (@LKS.transport_check_keepalive_settle_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_KEEPALIVE_SETTLE_F).
Qed.
Lemma LEAF_C_LATEST_CONTROL : forall fx : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx.
Proof.
  intros fx. exact (@LLC.transport_check_latest_control_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_LATEST_CONTROL_F).
Qed.
Lemma LEAF_C_LATEST_DISPLAY : forall fx : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_display_cg) fx.
Proof.
  intros fx. exact (@LLD.transport_check_latest_display_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_LATEST_DISPLAY_F).
Qed.
Lemma LEAF_C_LATEST_DRAIN : forall fx : YK11.FPState, @transport_leaf_at rc B (@LLDR.transport_check_latest_drain_cg) fx.
Proof.
  intros fx. exact (@LLDR.transport_check_latest_drain_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_LATEST_DRAIN_F).
Qed.
Lemma LEAF_C_LATEST_FRAME : forall fx : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx.
Proof.
  intros fx. exact (@LLF.transport_check_latest_frame_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_LATEST_FRAME_F).
Qed.
Lemma LEAF_C_LATEST_SUBMIT : forall fx : YK11.FPState, @transport_leaf_at rc B (@LLS.transport_check_latest_submit_cg) fx.
Proof.
  intros fx. exact (@LLS.transport_check_latest_submit_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_LATEST_SUBMIT_F).
Qed.
Lemma LEAF_C_REFUSAL_SUBMIT : forall fx : YK11.FPState, @transport_leaf_at rc B (@LRS.transport_check_refusal_submit_cg) fx.
Proof.
  intros fx. exact (@LRS.transport_check_refusal_submit_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_REFUSAL_SUBMIT_F).
Qed.
Lemma LEAF_C_STATE_ONLINE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSO.transport_check_state_online_cg) fx.
Proof.
  intros fx. exact (@LSO.transport_check_state_online_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_STATE_ONLINE_F).
Qed.
Lemma LEAF_C_STATE_SETTLE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSS.transport_check_state_settle_cg) fx.
Proof.
  intros fx. exact (@LSS.transport_check_state_settle_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_STATE_SETTLE_F).
Qed.
Lemma LEAF_C_STATE_WAKE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx.
Proof.
  intros fx. exact (@LSW.transport_check_state_wake_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_STATE_WAKE_F).
Qed.
Lemma LEAF_C_STATE_WAKE_CODE : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSWC.transport_check_state_wake_code_cg) fx.
Proof.
  intros fx. exact (@LSWC.transport_check_state_wake_code_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_C_STATE_WAKE_CODE_F).
Qed.
Lemma LEAF_COPYSTRZ : forall fx : YK11.FPState, @transport_leaf_wr_at rc B (@LCSZ.transport_copy_strz_cg) fx.
Proof.
  intros fx. exact (@LCSZ.transport_copy_strz_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_COPYSTRZ_F).
Qed.
Lemma LEAF_CINIT : forall fx : YK11.FPState, @transport_leaf_wr_at rc B (@LCI.transport_diginet_cursor_init_cg) fx.
Proof.
  intros fx. exact (@LCI.transport_diginet_cursor_init_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_CINIT_F).
Qed.
Lemma LEAF_KA : forall fx : YK11.FPState, @transport_leaf_at rc B (@LKA.transport_diginet_frame_is_keepalive_cg) fx.
Proof.
  intros fx. exact (@LKA.transport_diginet_frame_is_keepalive_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_KA_F).
Qed.
Lemma LEAF_MACD : forall fx : YK11.FPState, @transport_leaf_at rc B (@LMD.transport_diginet_mac_is_digidesign_cg) fx.
Proof.
  intros fx. exact (@LMD.transport_diginet_mac_is_digidesign_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_MACD_F).
Qed.
Lemma LEAF_SDEAD : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSD.transport_diginet_session_deadline_cg) fx.
Proof.
  intros fx. exact (@LSD.transport_diginet_session_deadline_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_SDEAD_F).
Qed.
Lemma LEAF_SUM16 : forall fx : YK11.FPState, @transport_leaf_at rc B (@LSUM.transport_diginet_sum16_cg) fx.
Proof.
  intros fx. exact (@LSUM.transport_diginet_sum16_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_SUM16_F).
Qed.
Lemma LEAF_IONOW : forall fx : YK11.FPState, @transport_leaf_at rc B (@LION.transport_io_now_cg) fx.
Proof.
  intros fx. exact (@LION.transport_io_now_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_IONOW_F).
Qed.
Lemma LEAF_RD32 : forall fx : YK11.FPState, @transport_leaf_at rc B (@LRD.transport_rd32_cg) fx.
Proof.
  intros fx. exact (@LRD.transport_rd32_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_RD32_F).
Qed.
Lemma LEAF_TAGGED : forall fx : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx.
Proof.
  intros fx. exact (@LTO.transport_tagged_of_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate
      (@AR rc segs B) (aview segs) same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B)
      (aowned B) (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) H_PROG_TAGGED_F).
Qed.

(* Every premise of a program statement that is not a callee's statement is one of the rows above or a fact of
   lib/B/TransportBFacts.v; the tactic tries each (fuzz_frame's frame_close form), so the composition does not depend
   on the order in which a statement lists its premises. *)
Ltac tclose :=
  first [ exact BF.transport_cells_TB | exact BF.trans_scfg_cells_TB | exact BF.trans_recv_cells_TB
        | exact BF.trans_settle_cells_TB | exact BF.trans_llvmf_cells_TB | exact BF.trans_cir_cells_TB
        | exact BF.trans_cis_cells_TB | exact BF.trans_clq_cells_TB | exact BF.trans_cls_cells_TB
        | exact BF.trans_csf_cells_TB | exact BF.trans_csdata_cells_TB | exact BF.trans_dnamed_cells_TB
        | exact BF.trans_pfrom_cells_TB | exact BF.trans_close_cells_TB | exact BF.trans_sinit_cells_TB
        | exact BF.trans_poll_cells_TB | exact BF.trans_srx_cells_TB | exact BF.trans_ssubmit_cells_TB
        | exact BF.trans_tick_cells_TB | exact BF.trans_wake_cells_TB | exact BF.trans_hoff_cells_TB
        | exact BF.trans_iosend_cells_TB | exact BF.trans_ow_cells_TB | exact BF.trans_mrx_cells_TB
        | exact BF.trans_maybeon_cells_TB | exact BF.trans_notice_cells_TB | exact BF.trans_onack_cells_TB
        | exact BF.trans_onann_cells_TB | exact BF.trans_ondata_cells_TB | exact BF.trans_sendctl_cells_TB
        | exact BF.trans_senddata_cells_TB | exact BF.trans_sstate_cells_TB | exact BF.trans_take_cells_TB
        | exact BF.trans_g_unowned_TB | exact BF.trans_g_no_errno_TB | exact BF.gx_ok_TB | exact BF.gx_noerrno_TB
        | exact BF.trans_ro_rd_unowned_TB | exact BF.trans_rom_no_errno_TB | exact BF.trans_rlo_le
        | exact BF.trans_rhi_le | exact BF.ro_below_ofl_TB | exact BF.pc_stack_malloc0_TB
        | exact BF.pc_stack_malloc1_TB | exact BF.pc_stack_malloc2_TB | exact BF.pc_stack_malloc3_TB
        | exact BF.pc_stack_malloc5_TB | exact BF.pc_wrap_malloc_TB | exact BF.pc_wrap_free_TB
        | exact BF.transport_llvmf_utraces_TB | exact (AR_laws_ok segs B) | exact HB_METER_LAWS
        | exact HB_METER_FS_LAWS | exact HB_SMP | exact (HB_ASF rc) | exact (HB_FFL rc) | exact BF.sink_img_laws_TB
        | exact (@BF.HSINK_KEPT_G rc) | exact (@BF.HMETA_KEPT_G rc) | exact HB_COST
        | intros ?fx'; exact (H_RT_STACK_MALLOC0 rc fx') | intros ?fx'; exact (H_RT_STACK_MALLOC1 rc fx')
        | intros ?fx'; exact (H_RT_STACK_MALLOC2 rc fx') | intros ?fx'; exact (H_RT_STACK_MALLOC3 rc fx')
        | intros ?fx'; exact (H_RT_STACK_MALLOC5 rc fx') | intros ?fx'; exact (H_RT_STACK_FREE5 rc fx')
        | intros ?fx'; exact (H_RT_ASAN_MEMSET rc fx') | intros ?fx'; exact (H_RT_ASAN_MEMCPY rc fx')
        | intros ?fx'; exact (H_RT_BCMP rc fx') | intros ?fx'; exact (H_RT_STRCMP rc fx')
        | intros ?fx'; exact (H_RT_STRLEN rc fx') | intros ?fx'; exact (H_RT_SET_SHADOW_F8 rc fx')
        | intros ?fx'; exact (H_RT_SET_SHADOW_00 rc fx') | intros ?fx'; exact (H_RT_SET_SHADOW_F5 rc fx')
        | intros ?fx'; exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx'))
        | intros ?fx'; exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')) ].

(* The library and harness functions, each from its walk and its callees, bottom-up (callees first). *)
Lemma C_INFLIGHT_RETRY_HOLDS : forall fx : YK11.FPState,
  @PCIR.transport_check_inflight_retry_cg fx rc B MT (transportb_sigma TB_check_inflight_retry).
Proof. intros fx. apply (H_PROG_C_INFLIGHT_RETRY fx rc); tclose. Qed.
Lemma C_LATEST_QUEUE_HOLDS : forall fx : YK11.FPState,
  @PCLQ.transport_check_latest_queue_cg fx rc B MT (transportb_sigma TB_check_latest_queue).
Proof. intros fx. apply (H_PROG_C_LATEST_QUEUE fx rc); tclose. Qed.
Lemma C_SENT_FRAME_HOLDS : forall fx : YK11.FPState,
  @PCSF.transport_check_sent_frame_cg fx rc B MT (transportb_sigma TB_check_sent_frame).
Proof. intros fx. apply (H_PROG_C_SENT_FRAME fx rc); tclose. Qed.
Lemma C_STATE_DATA_HOLDS : forall fx : YK11.FPState,
  @PCSD.transport_check_state_data_cg fx rc B MT (transportb_sigma TB_check_state_data).
Proof. intros fx. apply (H_PROG_C_STATE_DATA fx rc); tclose. Qed.
Lemma C_STATE_DESK_HOLDS : forall fx : YK11.FPState,
  @PCSDK.transport_check_state_desk_cg fx rc B MT (transportb_sigma TB_check_state_desk).
Proof. intros fx. apply (H_PROG_C_STATE_DESK fx rc); tclose. Qed.
Lemma DESKNAMED_HOLDS : forall fx : YK11.FPState,
  @PDN.transport_desk_named_cg fx rc B MT (transportb_sigma TB_desk_named).
Proof. intros fx. apply (H_PROG_DESKNAMED fx rc); tclose. Qed.
Lemma MNEXT_HOLDS : forall fx : YK11.FPState,
  @PMN.transport_diginet_msg_next_cg fx rc B MT (transportb_sigma TB_diginet_msg_next).
Proof. intros fx. apply (H_PROG_MNEXT fx rc); tclose. Qed.
Lemma PFROM_HOLDS : forall fx : YK11.FPState,
  @PPF.transport_diginet_personality_from_name_cg fx rc B MT (transportb_sigma TB_diginet_personality_from_name).
Proof. intros fx. apply (H_PROG_PFROM fx rc); tclose. Qed.
Lemma SCFG_HOLDS : forall fx : YK11.FPState,
  @PSCFG.transport_diginet_session_config_default_cg fx rc B MT (transportb_sigma TB_diginet_session_config_default).
Proof. intros fx. apply (H_PROG_SCFG fx rc); tclose. Qed.
Lemma SINIT_HOLDS : forall fx : YK11.FPState,
  @PSINIT.transport_diginet_session_init_cg fx rc B MT (transportb_sigma TB_diginet_session_init).
Proof. intros fx. apply (H_PROG_SINIT fx rc); tclose. Qed.
Lemma HOSTOFF_HOLDS : forall fx : YK11.FPState,
  @PHOFF.transport_host_offset_cg fx rc B MT (transportb_sigma TB_host_offset).
Proof. intros fx. apply (H_PROG_HOSTOFF fx rc); tclose. Qed.
Lemma MSET_HOLDS : forall fx : YK11.FPState,
  @PMSET.transport_m_set_cg fx rc B MT (transportb_sigma TB_m_set).
Proof. intros fx. apply (H_PROG_MSET fx rc); tclose. Qed.
Lemma SPECRF_HOLDS : forall fx : YK11.FPState,
  @PSRF.transport_spec_read_frame_cg fx rc B MT (transportb_sigma TB_spec_read_frame).
Proof. intros fx. apply (H_PROG_SPECRF fx rc); tclose. Qed.
Lemma C_INFLIGHT_SETTLE_HOLDS : forall fx : YK11.FPState,
  @PCIS.transport_check_inflight_settle_cg fx rc B MT (transportb_sigma TB_check_inflight_settle).
Proof. intros fx. apply (H_PROG_C_INFLIGHT_SETTLE fx rc); first [tclose | exact LEAF_SDEAD]. Qed.
Lemma C_LATEST_SENT_HOLDS : forall fx : YK11.FPState,
  @PCLS.transport_check_latest_sent_cg fx rc B MT (transportb_sigma TB_check_latest_sent).
Proof. intros fx. apply (H_PROG_C_LATEST_SENT fx rc); first [tclose | exact LEAF_TAGGED]. Qed.
Lemma ANNP_HOLDS : forall fx : YK11.FPState,
  @PANP.transport_diginet_announce_parse_cg fx rc B MT (transportb_sigma TB_diginet_announce_parse).
Proof. intros fx. apply (H_PROG_ANNP fx rc); first [tclose | exact LEAF_COPYSTRZ]. Qed.
Lemma BCHK_HOLDS : forall fx : YK11.FPState,
  @PBC.transport_diginet_body_check_cg fx rc B MT (transportb_sigma TB_diginet_body_check).
Proof. intros fx. apply (H_PROG_BCHK fx rc); first [tclose | exact MNEXT_HOLDS | exact LEAF_CINIT]. Qed.
Lemma FPARSE_HOLDS : forall fx : YK11.FPState,
  @PFP.transport_diginet_frame_parse_cg fx rc B MT (transportb_sigma TB_diginet_frame_parse).
Proof. intros fx. apply (H_PROG_FPARSE fx rc); first [tclose | exact LEAF_RD32 | exact LEAF_SUM16]. Qed.
Lemma MONLINE_HOLDS : forall fx : YK11.FPState,
  @PMON.transport_m_maybe_online_cg fx rc B MT (transportb_sigma TB_m_maybe_online).
Proof. intros fx. apply (H_PROG_MONLINE fx rc); first [tclose | exact MSET_HOLDS]. Qed.
Lemma MTICK_HOLDS : forall fx : YK11.FPState,
  @PMTICK.transport_m_tick_cg fx rc B MT (transportb_sigma TB_m_tick).
Proof. intros fx. apply (H_PROG_MTICK fx rc); first [tclose | exact MSET_HOLDS]. Qed.
Lemma MWAKE_HOLDS : forall fx : YK11.FPState,
  @PMWAKE.transport_m_wake_cg fx rc B MT (transportb_sigma TB_m_wake).
Proof. intros fx. apply (H_PROG_MWAKE fx rc); first [tclose | exact MSET_HOLDS]. Qed.
Lemma NOTICE_HOLDS : forall fx : YK11.FPState,
  @PNOTICE.transport_notice_cg fx rc B MT (TI.ti_notice timg_B).
Proof. intros fx. apply (H_PROG_NOTICE fx rc); first [tclose | exact C_STATE_DESK_HOLDS | exact C_STATE_DATA_HOLDS | exact LEAF_C_INFLIGHT_LOST | exact LEAF_C_INFLIGHT_ACKED | exact LEAF_C_STATE_ONLINE]. Qed.
Lemma FBUILD_HOLDS : forall fx : YK11.FPState,
  @PFB.transport_diginet_frame_build_cg fx rc B MT (transportb_sigma TB_diginet_frame_build).
Proof. intros fx. apply (H_PROG_FBUILD fx rc); first [tclose | exact BCHK_HOLDS | exact LEAF_SUM16]. Qed.
Lemma SSUBMIT_HOLDS : forall fx : YK11.FPState,
  @PSSUB.transport_diginet_session_submit_cg fx rc B MT (transportb_sigma TB_diginet_session_submit).
Proof. intros fx. apply (H_PROG_SSUBMIT fx rc); first [tclose | exact BCHK_HOLDS]. Qed.
Lemma IOSEND_HOLDS : forall fx : YK11.FPState,
  @PIOS.transport_io_send_cg fx rc B MT (TI.ti_io_send timg_B).
Proof. intros fx. apply (H_PROG_IOSEND fx rc); first [tclose | exact SPECRF_HOLDS | exact C_SENT_FRAME_HOLDS | exact C_INFLIGHT_RETRY_HOLDS | exact C_LATEST_SENT_HOLDS | exact LEAF_C_ACK_FRAME | exact LEAF_C_LATEST_CONTROL | exact LEAF_C_STATE_WAKE | exact LEAF_C_INFLIGHT_NEW | exact LEAF_TAGGED | exact LEAF_C_LATEST_FRAME | exact LEAF_C_KEEPALIVE_DUE | exact LEAF_C_LATEST_DISPLAY]. Qed.
Lemma MRX_HOLDS : forall fx : YK11.FPState,
  @PMRX.transport_m_rx_cg fx rc B MT (transportb_sigma TB_m_rx).
Proof. intros fx. apply (H_PROG_MRX fx rc); first [tclose | exact SPECRF_HOLDS | exact HOSTOFF_HOLDS | exact MSET_HOLDS | exact DESKNAMED_HOLDS | exact MWAKE_HOLDS | exact MONLINE_HOLDS | exact MTICK_HOLDS]. Qed.
Lemma SETSTATE_HOLDS : forall fx : YK11.FPState,
  @PSSTATE.transport_set_state_cg fx rc B MT (transportb_sigma TB_set_state).
Proof. intros fx. apply (H_PROG_SETSTATE fx rc); first [tclose | exact NOTICE_HOLDS]. Qed.
Lemma SETTLE_HOLDS : forall fx : YK11.FPState,
  @PSETTLE.transport_settle_cg fx rc B MT (transportb_sigma TB_settle).
Proof. intros fx. apply (H_PROG_SETTLE fx rc); first [tclose | exact C_INFLIGHT_SETTLE_HOLDS | exact C_LATEST_QUEUE_HOLDS | exact LEAF_C_ACK_SETTLE | exact LEAF_C_STATE_SETTLE | exact LEAF_C_KEEPALIVE_SETTLE | exact LEAF_C_LATEST_DRAIN]. Qed.
Lemma TAKE_HOLDS : forall fx : YK11.FPState,
  @PTAKE.transport_take_cg fx rc B MT (transportb_sigma TB_take).
Proof. intros fx. apply (H_PROG_TAKE fx rc); first [tclose | exact BCHK_HOLDS]. Qed.
Lemma IORECV_HOLDS : forall fx : YK11.FPState,
  @PIOR.transport_io_recv_cg fx rc B MT (TI.ti_io_recv timg_B).
Proof. intros fx. apply (H_PROG_IORECV fx rc); first [tclose | exact MRX_HOLDS | exact MTICK_HOLDS]. Qed.
Lemma MAYBEON_HOLDS : forall fx : YK11.FPState,
  @PMAYBEON.transport_maybe_online_cg fx rc B MT (transportb_sigma TB_maybe_online).
Proof. intros fx. apply (H_PROG_MAYBEON fx rc); first [tclose | exact SETSTATE_HOLDS]. Qed.
Lemma SENDCTL_HOLDS : forall fx : YK11.FPState,
  @PSENDCTL.transport_send_control_cg fx rc B MT (transportb_sigma TB_send_control).
Proof. intros fx. apply (H_PROG_SENDCTL fx rc); first [tclose | exact FBUILD_HOLDS | exact IOSEND_HOLDS]. Qed.
Lemma SENDDATA_HOLDS : forall fx : YK11.FPState,
  @PSENDDATA.transport_send_data_cg fx rc B MT (transportb_sigma TB_send_data).
Proof. intros fx. apply (H_PROG_SENDDATA fx rc); first [tclose | exact FBUILD_HOLDS | exact IOSEND_HOLDS]. Qed.
Lemma SCLOSE_HOLDS : forall fx : YK11.FPState,
  @PSCL.transport_diginet_session_close_cg fx rc B MT (transportb_sigma TB_diginet_session_close).
Proof. intros fx. apply (H_PROG_SCLOSE fx rc); first [tclose | exact SETSTATE_HOLDS | exact SENDCTL_HOLDS]. Qed.
Lemma STICK_HOLDS : forall fx : YK11.FPState,
  @PTICK.transport_diginet_session_tick_cg fx rc B MT (transportb_sigma TB_diginet_session_tick).
Proof. intros fx. apply (H_PROG_STICK fx rc); first [tclose | exact IOSEND_HOLDS | exact SETSTATE_HOLDS | exact NOTICE_HOLDS | exact SENDDATA_HOLDS | exact TAKE_HOLDS]. Qed.
Lemma SWAKE_HOLDS : forall fx : YK11.FPState,
  @PWAKE.transport_diginet_session_wake_cg fx rc B MT (transportb_sigma TB_diginet_session_wake).
Proof. intros fx. apply (H_PROG_SWAKE fx rc); first [tclose | exact SENDCTL_HOLDS | exact SETSTATE_HOLDS]. Qed.
Lemma ONACK_HOLDS : forall fx : YK11.FPState,
  @PONACK.transport_on_ack_cg fx rc B MT (transportb_sigma TB_on_ack).
Proof. intros fx. apply (H_PROG_ONACK fx rc); first [tclose | exact NOTICE_HOLDS | exact MAYBEON_HOLDS]. Qed.
Lemma ONDATA_HOLDS : forall fx : YK11.FPState,
  @PONDATA.transport_on_data_cg fx rc B MT (transportb_sigma TB_on_data).
Proof. intros fx. apply (H_PROG_ONDATA fx rc); first [tclose | exact SENDCTL_HOLDS | exact NOTICE_HOLDS | exact LEAF_KA]. Qed.
Lemma ONANN_HOLDS : forall fx : YK11.FPState,
  @PONANN.transport_on_announce_cg fx rc B MT (transportb_sigma TB_on_announce).
Proof. intros fx. apply (H_PROG_ONANN fx rc); first [tclose | exact ANNP_HOLDS | exact PFROM_HOLDS | exact NOTICE_HOLDS | exact SETSTATE_HOLDS | exact SWAKE_HOLDS | exact MAYBEON_HOLDS]. Qed.
Lemma SRX_HOLDS : forall fx : YK11.FPState,
  @PSRX.transport_diginet_session_rx_cg fx rc B MT (transportb_sigma TB_diginet_session_rx).
Proof. intros fx. apply (H_PROG_SRX fx rc); first [tclose | exact FPARSE_HOLDS | exact ONANN_HOLDS | exact ONACK_HOLDS | exact SETSTATE_HOLDS | exact ONDATA_HOLDS | exact STICK_HOLDS | exact LEAF_MACD]. Qed.
Lemma SPOLL_HOLDS : forall fx : YK11.FPState,
  @PPOLL.transport_diginet_session_poll_cg fx rc B MT (transportb_sigma TB_diginet_session_poll).
Proof. intros fx. apply (H_PROG_SPOLL fx rc); first [tclose | exact IORECV_HOLDS | exact SRX_HOLDS | exact STICK_HOLDS | exact LEAF_IONOW | exact LEAF_SDEAD]. Qed.

(* receive at the entry's contexts CTX_receive; at build_and_receive's contexts bar_recv_ctx CTX_build_and_receive,
   which CTX_receive holds (LLVMFuzzerTestOneInput_cg.v ctx_receive_bar), since the contract names its contexts only
   in its premise In (raZ regs :: spine ch) CTX. *)
Lemma RECV_HOLDS : forall fx : YK11.FPState,
  @PRECV.transport_receive_cg fx rc B MT (transportb_sigma TB_receive) PL.CTX_receive.
Proof.
  intros fx. apply (H_PROG_RECV fx rc);
    first [tclose | exact SPECRF_HOLDS | exact SPOLL_HOLDS | exact MRX_HOLDS | exact SRX_HOLDS | exact SETTLE_HOLDS].
Qed.
Lemma recv_cg_incl : forall (fx : YK11.FPState) (a : Z) (C1 C2 : list (list Z)), incl C1 C2 ->
  @PRECV.transport_receive_cg fx rc B MT a C2 -> @PRECV.transport_receive_cg fx rc B MT a C1.
Proof.
  intros fx a C1 C2 HI H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch
    HJ H1 H2 H3 H4 H5 H6 H7 H8 Hch Hin.
  exact (H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch
    HJ H1 H2 H3 H4 H5 H6 H7 H8 Hch (HI _ Hin)).
Qed.
Lemma RECV_HOLDS_BAR : forall fx : YK11.FPState,
  @PRECV.transport_receive_cg fx rc B MT (transportb_sigma TB_receive) (PBAR.bar_recv_ctx PL.CTX_build_and_receive).
Proof. intros fx. exact (recv_cg_incl fx _ _ _ PL.ctx_receive_bar (RECV_HOLDS fx)). Qed.
Lemma BAR_HOLDS : forall fx : YK11.FPState,
  @PBAR.transport_build_and_receive_cg fx rc B MT (transportb_sigma TB_build_and_receive) PL.CTX_build_and_receive.
Proof. intros fx. apply (H_PROG_BAR fx rc); first [tclose | exact RECV_HOLDS_BAR]. Qed.

(* The program contract of the entry function (the slot at G_HARNESS_B), from its walk and every callee it names. *)
Lemma LIB_CONTRACT : @tfib_lib_contract_x_all rc transport_shape TG.G_HARNESS_B B MT XL XL RLO RHI.
Proof.
  apply (H_PROG_LLVMF_B rc);
    first [tclose | exact SCFG_HOLDS | exact SINIT_HOLDS | exact MWAKE_HOLDS | exact SWAKE_HOLDS | exact MSET_HOLDS | exact SCLOSE_HOLDS | exact SETTLE_HOLDS | exact RECV_HOLDS | exact MTICK_HOLDS | exact STICK_HOLDS | exact BAR_HOLDS | exact SSUBMIT_HOLDS | exact LEAF_C_STATE_WAKE_CODE | exact LEAF_C_REFUSAL_SUBMIT | exact LEAF_C_LATEST_SUBMIT].
Qed.

(* The start-up and the driver over the slot: lib/B/YD1q.v tfib_srealizesX at TransportB, G := G_HARNESS_B, with the
   driver-site facts of the image-B core's lib/B/YD1k.v / YD1l.v / YD1o.v / YD1j.v (fuzz_frame's Lets). *)
Let HB : TransportSyms B := TransportB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO := tfib_fprintf_open_site B HB LAWS HB.
Let FPR := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma transportb_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL XL RLO RHI MT_FREE BF.trans_ro_in
    LIB_CONTRACT xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.

(* TFIB_TB (lib/B/TransportTFIBB.v), at the run ceiling of the start's stack pointer (fuzz_frame's
   frame_TFIB_T_of_parts). *)
Theorem transport_TFIB_B : TFIB_TB.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@transportb_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowTB sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan+UBSan statements of record of image B (lib/B/AsanUbsanTop.v section b): agreement from TFIB_TB and the
   plain build's realization lib/A/TransportShape.v transport_plain_rz_stmt (a premise of this conclusion, not a
   Section hypothesis: the closing file gives lib/A/TransportPlainRz.v transport_plain_rz of the plain walk), halting
   from TFIB_TB alone. *)
Theorem transport_asan_ubsan_agrees_of_parts : transport_plain_rz_stmt -> TSt.asan_ubsan_agrees.
Proof. intros PLAIN. exact (AsanUbsanTop.transport_asan_ubsan_agrees_of_tfib PLAIN transport_TFIB_B). Qed.
Theorem transport_asan_ubsan_halts_of_parts : TSt.asan_ubsan_halts.
Proof. exact (AsanUbsanTop.transport_asan_ubsan_halts_of_tfib transport_TFIB_B). Qed.
End closeb.

(* After the Section, each conclusion is a function of the hypotheses it uses; Print Assumptions lists what it rests
   on, which must be only the axioms toolchain/allowed-axioms.txt allows. *)
About transport_TFIB_B.
Print Assumptions transport_TFIB_B.
About transport_asan_ubsan_agrees_of_parts.
Print Assumptions transport_asan_ubsan_agrees_of_parts.
About transport_asan_ubsan_halts_of_parts.
Print Assumptions transport_asan_ubsan_halts_of_parts.
