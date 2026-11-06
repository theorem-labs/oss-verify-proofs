(* Every own function's contract in the ubsan image, each from its walk <f>_holds applied to its callees'
   contracts, down to the kit's libc walks (U/Prog/memcpy.v, ...) and the relocated src/ walks; and from them
   llvm_walk_all and llvm_walk_all_cf: the walk contracts of LLVMFuzzerTestOneInput at the frame's allocator
   (src0_msyms, zlib_API rc) and sink words, which U/Prog/T/SlotFrame.v turns into the slot contracts through the
   bridges (U/Prog/T/SlotBridgeProof.v).
   The Section hypotheses are the walks not yet in the tree, each stated as what that walk will prove:
     LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_walk and
       LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_walk_cf (the SRcf form):
       the walk of LLVMFuzzerTestOneInput, from the contracts of its callees (U/Prog/T/LLVMFuzzerTestOneInput_c.v
       header) to its walk contract at the frame's allocator and sink words. receive and build_and_receive are
       given at every FP state: the loop calls them again at the FP state the previous call returned
       (receive_ret's `exists fx'`). receive's SR / SRcf contracts take the allocator's malloc and free contracts
       from U/FrameProof.v / U/AllocCf.v.
   When a walk lands, its hypothesis becomes a lemma here: its <f>_holds applied to the c_<g> of its callees. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YM05 YH02 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require FrameProof AllocCf.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c bcmp_ro_c copy_strz_c
  diginet_announce_parse_c diginet_body_check_c diginet_body_check_w_c diginet_cursor_init_c diginet_frame_build_c
  diginet_frame_build_w_c diginet_frame_is_keepalive_c diginet_frame_parse_c diginet_mac_is_digidesign_c
  diginet_msg_next_c diginet_msg_next_w_c diginet_personality_from_name_c diginet_sum16_c diginet_sum16_w_c memchr_c
  memchr_ro_c memcmp_c memcmp_ro_c memcpy_c memcpy_ro_c memcpy_same_c memcpy_same_ro_c memset_c memset_ro_c rd32_c
  strcmp_c strlen_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import LLVMFuzzerTestOneInput_c
  build_and_receive_c check_ack_frame_c check_ack_settle_c check_inflight_acked_c check_inflight_lost_c
  check_inflight_new_c check_inflight_retry_c check_inflight_settle_c check_keepalive_due_c check_keepalive_settle_c
  check_latest_control_c check_latest_display_c check_latest_drain_c check_latest_frame_c check_latest_queue_c
  check_latest_sent_c check_latest_submit_c check_refusal_submit_c check_sent_frame_c check_state_data_c
  check_state_desk_c check_state_online_c check_state_settle_c check_state_wake_c check_state_wake_code_c desk_named_c
  diginet_session_close_c diginet_session_config_default_c diginet_session_deadline_c diginet_session_init_c
  diginet_session_poll_c diginet_session_rx_c diginet_session_submit_c diginet_session_tick_c diginet_session_wake_c
  host_offset_c io_now_c io_recv_c io_send_c m_maybe_online_c m_rx_c m_set_c m_tick_c m_wake_c maybe_online_c notice_c
  on_ack_c on_announce_c on_data_c receive_c send_control_c send_data_c set_state_c settle_c spec_read_frame_c
  tagged_of_c take_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require bcmp bcmp_ro copy_strz diginet_announce_parse
  diginet_body_check diginet_body_check_w diginet_cursor_init diginet_frame_build diginet_frame_build_w
  diginet_frame_is_keepalive diginet_frame_parse diginet_mac_is_digidesign diginet_msg_next diginet_msg_next_w
  diginet_personality_from_name diginet_sum16 diginet_sum16_w memchr memchr_ro memcmp memcmp_ro memcpy memcpy_ro
  memcpy_same memcpy_same_ro memset memset_ro rd32 strcmp strlen.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require check_ack_frame check_ack_settle
  check_inflight_acked check_inflight_lost check_inflight_new check_inflight_retry check_inflight_settle
  check_keepalive_due check_keepalive_settle check_latest_control check_latest_display check_latest_drain
  check_latest_frame check_latest_queue check_latest_sent check_latest_submit check_refusal_submit check_sent_frame
  check_state_data check_state_desk check_state_online check_state_settle check_state_wake check_state_wake_code
  desk_named diginet_session_close diginet_session_config_default diginet_session_deadline diginet_session_init
  diginet_session_poll diginet_session_rx diginet_session_tick diginet_session_wake host_offset io_now io_recv io_send
  m_maybe_online m_rx m_set m_tick m_wake maybe_online notice on_ack on_announce on_data send_control send_data
  set_state settle spec_read_frame tagged_of build_and_receive diginet_session_submit receive take.

(* What the walks of receive and build_and_receive prove at the frame's allocator. *)
Definition receive_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState), receive_contract (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc).

Definition receive_cf_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState), receive_contract_cf (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc).

Definition build_and_receive_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState), build_and_receive_contract (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc).

Definition build_and_receive_cf_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState), build_and_receive_contract_cf (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc).

(* What the walk of LLVMFuzzerTestOneInput proves at the frame's allocator and sink words: from the
   contracts of its callees to its walk contract. *)
Definition LLVMFuzzerTestOneInput_walk : Prop :=
  forall (rc : RunCeil) (fx : FPState),
  memcpy_contract -> memset_contract -> strlen_contract -> diginet_session_config_default_contract ->
  diginet_session_init_contract -> m_wake_contract -> diginet_session_wake_contract ->
  check_state_wake_code_contract -> diginet_session_close_contract -> m_set_contract -> m_tick_contract ->
  diginet_session_tick_contract -> settle_contract ->
  (forall fx' : FPState, build_and_receive_contract (fx:=fx') (rc:=rc) src0_msyms (@zlib_API rc)) ->
  diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
  (forall fx' : FPState, receive_contract (fx:=fx') (rc:=rc) src0_msyms (@zlib_API rc)) ->
  LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc).

Definition llvm_walk_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState),
  LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc).

(* What the walk of LLVMFuzzerTestOneInput (cut-free form) proves at the frame's allocator and sink words: from the
   contracts of its callees to its walk contract. *)
Definition LLVMFuzzerTestOneInput_walk_cf : Prop :=
  forall (rc : RunCeil) (fx : FPState),
  memcpy_contract -> memset_contract -> strlen_contract -> diginet_session_config_default_contract ->
  diginet_session_init_contract -> m_wake_contract -> diginet_session_wake_contract ->
  check_state_wake_code_contract -> diginet_session_close_contract -> m_set_contract -> m_tick_contract ->
  diginet_session_tick_contract -> settle_contract ->
  (forall fx' : FPState, build_and_receive_contract_cf (fx:=fx') (rc:=rc) src0_msyms (@zlib_API rc)) ->
  diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
  (forall fx' : FPState, receive_contract_cf (fx:=fx') (rc:=rc) src0_msyms (@zlib_API rc)) ->
  LLVMFuzzerTestOneInput_walk_contract_cf (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc).

Definition llvm_walk_cf_at_frame : Prop :=
  forall (rc : RunCeil) (fx : FPState),
  LLVMFuzzerTestOneInput_walk_contract_cf (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc).

Section W.
Hypothesis LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_walk.
Hypothesis LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_walk_cf.

Lemma c_bcmp : bcmp_contract.
Proof. exact bcmp.bcmp_holds. Qed.
Lemma c_bcmp_ro : bcmp_ro_contract.
Proof. exact bcmp_ro.bcmp_ro_holds. Qed.
Lemma c_check_ack_frame : check_ack_frame_contract.
Proof. exact check_ack_frame.check_ack_frame_holds. Qed.
Lemma c_check_ack_settle : check_ack_settle_contract.
Proof. exact check_ack_settle.check_ack_settle_holds. Qed.
Lemma c_check_inflight_acked : check_inflight_acked_contract.
Proof. exact check_inflight_acked.check_inflight_acked_holds. Qed.
Lemma c_check_inflight_lost : check_inflight_lost_contract.
Proof. exact check_inflight_lost.check_inflight_lost_holds. Qed.
Lemma c_check_inflight_new : check_inflight_new_contract.
Proof. exact check_inflight_new.check_inflight_new_holds. Qed.
Lemma c_check_inflight_retry : check_inflight_retry_contract.
Proof. exact (check_inflight_retry.check_inflight_retry_holds c_bcmp). Qed.
Lemma c_check_keepalive_due : check_keepalive_due_contract.
Proof. exact check_keepalive_due.check_keepalive_due_holds. Qed.
Lemma c_check_keepalive_settle : check_keepalive_settle_contract.
Proof. exact check_keepalive_settle.check_keepalive_settle_holds. Qed.
Lemma c_check_latest_control : check_latest_control_contract.
Proof. exact check_latest_control.check_latest_control_holds. Qed.
Lemma c_check_latest_display : check_latest_display_contract.
Proof. exact check_latest_display.check_latest_display_holds. Qed.
Lemma c_check_latest_drain : check_latest_drain_contract.
Proof. exact check_latest_drain.check_latest_drain_holds. Qed.
Lemma c_check_latest_frame : check_latest_frame_contract.
Proof. exact check_latest_frame.check_latest_frame_holds. Qed.
Lemma c_check_latest_queue : check_latest_queue_contract.
Proof. exact (check_latest_queue.check_latest_queue_holds c_bcmp). Qed.
Lemma c_check_latest_submit : check_latest_submit_contract.
Proof. exact check_latest_submit.check_latest_submit_holds. Qed.
Lemma c_check_refusal_submit : check_refusal_submit_contract.
Proof. exact check_refusal_submit.check_refusal_submit_holds. Qed.
Lemma c_check_sent_frame : check_sent_frame_contract.
Proof. exact (check_sent_frame.check_sent_frame_holds c_bcmp). Qed.
Lemma c_check_state_data : check_state_data_contract.
Proof. exact (check_state_data.check_state_data_holds c_bcmp). Qed.
Lemma c_check_state_desk : check_state_desk_contract.
Proof. exact (check_state_desk.check_state_desk_holds c_bcmp). Qed.
Lemma c_check_state_online : check_state_online_contract.
Proof. exact check_state_online.check_state_online_holds. Qed.
Lemma c_check_state_settle : check_state_settle_contract.
Proof. exact check_state_settle.check_state_settle_holds. Qed.
Lemma c_check_state_wake_code : check_state_wake_code_contract.
Proof. exact check_state_wake_code.check_state_wake_code_holds. Qed.
Lemma c_check_state_wake : check_state_wake_contract.
Proof. exact check_state_wake.check_state_wake_holds. Qed.
Lemma c_copy_strz : copy_strz_contract.
Proof. exact copy_strz.copy_strz_holds. Qed.
Lemma c_desk_named : desk_named_contract.
Proof. exact (desk_named.desk_named_holds c_bcmp). Qed.
Lemma c_diginet_announce_parse : diginet_announce_parse_contract.
Proof. exact (diginet_announce_parse.diginet_announce_parse_holds c_copy_strz). Qed.
Lemma c_diginet_cursor_init : diginet_cursor_init_contract.
Proof. exact diginet_cursor_init.diginet_cursor_init_holds. Qed.
Lemma c_diginet_frame_is_keepalive : diginet_frame_is_keepalive_contract.
Proof. exact diginet_frame_is_keepalive.diginet_frame_is_keepalive_holds. Qed.
Lemma c_diginet_mac_is_digidesign : diginet_mac_is_digidesign_contract.
Proof. exact diginet_mac_is_digidesign.diginet_mac_is_digidesign_holds. Qed.
Lemma c_diginet_msg_next : diginet_msg_next_contract.
Proof. exact diginet_msg_next.diginet_msg_next_holds. Qed.
Lemma c_diginet_body_check : diginet_body_check_contract.
Proof. exact (diginet_body_check.diginet_body_check_holds c_diginet_cursor_init c_diginet_msg_next). Qed.
Lemma c_diginet_msg_next_w : diginet_msg_next_contract_w.
Proof. exact diginet_msg_next_w.diginet_msg_next_holds_w. Qed.
Lemma c_diginet_body_check_w : diginet_body_check_contract_w.
Proof. exact (diginet_body_check_w.diginet_body_check_holds_w c_diginet_cursor_init c_diginet_msg_next_w). Qed.
Lemma c_diginet_session_deadline : diginet_session_deadline_contract.
Proof. exact diginet_session_deadline.diginet_session_deadline_holds. Qed.
Lemma c_check_inflight_settle : check_inflight_settle_contract.
Proof. exact (check_inflight_settle.check_inflight_settle_holds c_diginet_session_deadline). Qed.
Lemma c_diginet_sum16 : diginet_sum16_contract.
Proof. exact diginet_sum16.diginet_sum16_holds. Qed.
Lemma c_diginet_sum16_w : diginet_sum16_contract_w.
Proof. exact diginet_sum16_w.diginet_sum16_holds_w. Qed.
Lemma c_host_offset : host_offset_contract.
Proof. exact (host_offset.host_offset_holds c_bcmp). Qed.
Lemma c_io_now : io_now_contract.
Proof. exact io_now.io_now_holds. Qed.
Lemma c_m_set : m_set_contract.
Proof. exact m_set.m_set_holds. Qed.
Lemma c_m_maybe_online : m_maybe_online_contract.
Proof. exact (m_maybe_online.m_maybe_online_holds c_m_set). Qed.
Lemma c_m_tick : m_tick_contract.
Proof. exact (m_tick.m_tick_holds c_m_set). Qed.
Lemma c_m_wake : m_wake_contract.
Proof. exact (m_wake.m_wake_holds c_m_set). Qed.
Lemma c_memchr : memchr_contract.
Proof. exact memchr.memchr_holds. Qed.
Lemma c_memchr_ro : memchr_ro_contract.
Proof. exact memchr_ro.memchr_ro_holds. Qed.
Lemma c_memcmp : memcmp_contract.
Proof. exact memcmp.memcmp_holds. Qed.
Lemma c_memcmp_ro : memcmp_ro_contract.
Proof. exact memcmp_ro.memcmp_ro_holds. Qed.
Lemma c_memcpy : memcpy_contract.
Proof. exact memcpy.memcpy_holds. Qed.
Lemma c_take : take_contract.
Proof. exact (take.take_holds c_diginet_body_check c_memcpy). Qed.
Lemma c_diginet_session_submit : diginet_session_submit_contract.
Proof. exact (diginet_session_submit.diginet_session_submit_holds c_diginet_body_check c_memcpy). Qed.
Lemma c_memcpy_ro : memcpy_ro_contract.
Proof. exact memcpy_ro.memcpy_ro_holds. Qed.
Lemma c_memcpy_same : memcpy_same_contract.
Proof. exact memcpy_same.memcpy_same_holds. Qed.
Lemma c_memcpy_same_ro : memcpy_same_ro_contract.
Proof. exact memcpy_same_ro.memcpy_same_ro_holds. Qed.
Lemma c_memset : memset_contract.
Proof. exact memset.memset_holds. Qed.
Lemma c_diginet_frame_build : diginet_frame_build_contract.
Proof. exact (diginet_frame_build.diginet_frame_build_holds c_diginet_body_check c_memcpy c_diginet_sum16
    c_memset). Qed.
Lemma c_diginet_frame_build_w : diginet_frame_build_contract_w.
Proof. exact (diginet_frame_build_w.diginet_frame_build_holds_w c_diginet_body_check_w c_memcpy c_diginet_sum16_w
    c_memset). Qed.
Lemma c_diginet_session_config_default : diginet_session_config_default_contract.
Proof. exact (diginet_session_config_default.diginet_session_config_default_holds c_memset). Qed.
Lemma c_diginet_session_init : diginet_session_init_contract.
Proof. exact (diginet_session_init.diginet_session_init_holds c_memset c_memcpy). Qed.
Lemma c_memset_ro : memset_ro_contract.
Proof. exact memset_ro.memset_ro_holds. Qed.
Lemma c_notice : notice_contract.
Proof. exact (notice.notice_holds c_check_state_online c_check_inflight_acked c_check_inflight_lost c_check_state_desk
    c_check_state_data). Qed.
Lemma c_rd32 : rd32_contract.
Proof. exact rd32.rd32_holds. Qed.
Lemma c_diginet_frame_parse : diginet_frame_parse_contract.
Proof. exact (diginet_frame_parse.diginet_frame_parse_holds c_memcpy c_rd32 c_diginet_sum16). Qed.
Lemma c_set_state : set_state_contract.
Proof. exact (set_state.set_state_holds c_memset c_notice). Qed.
Lemma c_maybe_online : maybe_online_contract.
Proof. exact (maybe_online.maybe_online_holds c_set_state). Qed.
Lemma c_on_ack : on_ack_contract.
Proof. exact (on_ack.on_ack_holds c_memset c_notice c_maybe_online). Qed.
Lemma c_settle : settle_contract.
Proof. exact (settle.settle_holds c_check_ack_settle c_check_state_settle c_check_inflight_settle
    c_check_keepalive_settle c_check_latest_queue c_check_latest_drain). Qed.
Lemma c_spec_read_frame : spec_read_frame_contract.
Proof. exact (spec_read_frame.spec_read_frame_holds c_memset). Qed.
Lemma c_m_rx : m_rx_contract.
Proof. exact (m_rx.m_rx_holds c_bcmp c_memcpy c_spec_read_frame c_host_offset c_desk_named c_m_set c_m_wake
    c_m_maybe_online c_m_tick). Qed.
Lemma c_io_recv : io_recv_contract.
Proof. exact (io_recv.io_recv_holds c_m_rx c_m_tick c_memcpy). Qed.
Lemma c_strcmp : strcmp_contract.
Proof. exact strcmp.strcmp_holds. Qed.
Lemma c_diginet_personality_from_name : diginet_personality_from_name_contract.
Proof. exact (diginet_personality_from_name.diginet_personality_from_name_holds c_strcmp). Qed.
Lemma c_strlen : strlen_contract.
Proof. exact strlen.strlen_holds. Qed.
Lemma c_tagged_of : tagged_of_contract.
Proof. exact tagged_of.tagged_of_holds. Qed.
Lemma c_check_latest_sent : check_latest_sent_contract.
Proof. exact (check_latest_sent.check_latest_sent_holds c_bcmp c_tagged_of). Qed.
Lemma c_io_send : io_send_contract.
Proof. exact (io_send.io_send_holds c_spec_read_frame c_tagged_of c_memcpy c_check_sent_frame c_check_ack_frame
    c_check_latest_control c_check_inflight_retry c_check_state_wake c_check_inflight_new c_check_latest_frame
    c_check_keepalive_due c_check_latest_sent c_check_latest_display). Qed.
Lemma c_send_control : send_control_contract.
Proof. exact (send_control.send_control_holds c_diginet_frame_build_w c_io_send c_memcpy). Qed.
Lemma c_diginet_session_close : diginet_session_close_contract.
Proof. exact (diginet_session_close.diginet_session_close_holds c_send_control c_set_state). Qed.
Lemma c_diginet_session_wake : diginet_session_wake_contract.
Proof. exact (diginet_session_wake.diginet_session_wake_holds c_send_control c_memcpy c_set_state). Qed.
Lemma c_on_announce : on_announce_contract.
Proof. exact (on_announce.on_announce_holds c_bcmp c_memset c_diginet_announce_parse c_diginet_personality_from_name
    c_diginet_session_wake c_maybe_online c_set_state c_notice). Qed.
Lemma c_on_data : on_data_contract.
Proof. exact (on_data.on_data_holds c_send_control c_diginet_frame_is_keepalive c_notice). Qed.
Lemma c_send_data : send_data_contract.
Proof. exact (send_data.send_data_holds c_diginet_frame_build_w c_io_send). Qed.
Lemma c_diginet_session_tick : diginet_session_tick_contract.
Proof. exact (diginet_session_tick.diginet_session_tick_holds c_take c_send_data c_notice c_io_send c_memset
    c_set_state). Qed.
Lemma c_diginet_session_rx : diginet_session_rx_contract.
Proof. exact (diginet_session_rx.diginet_session_rx_holds c_bcmp c_diginet_frame_parse c_diginet_mac_is_digidesign
    c_on_announce c_on_ack c_on_data c_set_state c_diginet_session_tick). Qed.
Lemma c_diginet_session_poll : diginet_session_poll_contract.
Proof. exact (diginet_session_poll.diginet_session_poll_holds c_io_now c_io_recv c_diginet_session_deadline
    c_diginet_session_rx c_diginet_session_tick). Qed.
Lemma c_receive : receive_at_frame.
Proof.
  intros rc fx.
  exact (receive.receive_holds (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc)
    (fun fx' => proj1 (FrameProof.zlib_frame_allocator rc fx'))
    (fun fx' => proj1 (proj2 (FrameProof.zlib_frame_allocator rc fx')))
    c_memset c_memcpy c_spec_read_frame c_diginet_session_poll c_m_rx c_diginet_session_rx c_settle).
Qed.
Lemma c_receive_cf : receive_cf_at_frame.
Proof.
  intros rc fx.
  exact (receive.receive_holds_cf (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc)
    (fun fx' => @AllocCf.zlib_malloc_contract_cf fx' rc) (fun fx' => @AllocCf.zlib_free_contract_cf fx' rc)
    c_memset c_memcpy c_spec_read_frame c_diginet_session_poll c_m_rx c_diginet_session_rx c_settle).
Qed.
Lemma c_build_and_receive : build_and_receive_at_frame.
Proof.
  intros rc fx.
  exact (build_and_receive.build_and_receive_holds (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc) (c_receive rc fx)
    c_memset c_memcpy).
Qed.
Lemma c_build_and_receive_cf : build_and_receive_cf_at_frame.
Proof.
  intros rc fx.
  exact (build_and_receive.build_and_receive_holds_cf (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc)
    (c_receive_cf rc fx) c_memset c_memcpy).
Qed.

Theorem llvm_walk_all : llvm_walk_at_frame.
Proof.
  intros rc fx.
  exact (LLVMFuzzerTestOneInput_holds rc fx c_memcpy c_memset c_strlen c_diginet_session_config_default
    c_diginet_session_init c_m_wake c_diginet_session_wake c_check_state_wake_code c_diginet_session_close c_m_set
    c_m_tick c_diginet_session_tick c_settle (fun fx' => c_build_and_receive rc fx') c_diginet_session_submit
    c_check_refusal_submit c_check_latest_submit (fun fx' => c_receive rc fx')).
Qed.

Theorem llvm_walk_all_cf : llvm_walk_cf_at_frame.
Proof.
  intros rc fx.
  exact (LLVMFuzzerTestOneInput_holds_cf rc fx c_memcpy c_memset c_strlen c_diginet_session_config_default
    c_diginet_session_init c_m_wake c_diginet_session_wake c_check_state_wake_code c_diginet_session_close c_m_set
    c_m_tick c_diginet_session_tick c_settle (fun fx' => c_build_and_receive_cf rc fx') c_diginet_session_submit
    c_check_refusal_submit c_check_latest_submit (fun fx' => c_receive_cf rc fx')).
Qed.

End W.
