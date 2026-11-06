From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept
  AllocPack3 SlotPack3 FrameProof.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes SlotLoop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3 SlotEntryRun SlotEntry SlotPass0 SlotPass1 SlotPass1w SlotPass7P SlotPass9 SlotResReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c check_shape_event_c check_shape_done_c next_line_c strnlen_c memcpy_c memchr_c memmove_c memset_c strlen_c bcmp_c __errno_location_c pthread_mutex_lock_c pthread_mutex_unlock_c wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import op_add_c source_reset_c list_free_c relay_add_b_c list_push_c send_line_b_c relay_event_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import list_find_c has_prefix_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded check_shape_event check_shape_done next_line strnlen memcpy memchr memmove memset strlen bcmp __errno_location pthread_mutex_lock pthread_mutex_unlock wake.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import op_add source_reset list_free relay_add_b list_push send_line_b relay_event_b gesture_end_b gestures_end_b relay_finish_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import list_find has_prefix.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotExitMove SlotExitFin SlotExitScan SlotExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c strndup_rt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr_c strcmp_c memrchr_c strncmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr strcmp memrchr strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_remove_b_c check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read_c memcpy_same_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import gesture_model_c list_drop_c relay_remove_b check_no_loss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read memcpy_same.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import gesture_model list_drop SlotPass4 SlotPass2 SlotPass2P.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import snprintf_c snprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_source_c relay_source relay_reads_c relay_reads SlotP2Res3 SlotP4Res3 SlotP5Res3 SlotP5Res3Full SlotPass5V SlotPass5V2 SlotPass5G SlotPass5GH SlotPass5C SlotPass5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM0b YH00 YH02 YI5b YI5c YL0k YL0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import FrameProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotAll.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3P SlotResReplyP SlotP2Res3P SlotP4Res3P SlotP5ResP SlotP5ResN SlotPass7ResP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPackGSF AllocPack3Cf AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import ZAllocator AgreeZlib SlotTopG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AgreeLim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import SlotAgreeP3.
(* The ubsan frame's cut-free allocator contracts live at pack3_ag_formT = pack3P GSF RM_ag, whose room bounds the
   live bytes by LIM_AG = 2 ^ 39 (lib/U/Prog/SlotFitAg.v live3c_fit: the ubsan run does not fit under SRC_LIM_MIN).
   Turning that room into room_cf_pack3 needs LIM_AG <= vm_limit of the run (U AllocPack3Ag.room_cf_of_ag), and
   U AgreeZlib.zlib_limit gives only SRC_LIM_MIN = 2 ^ 34 at every run ceiling. So the frame's allocator is not a fact
   about every rc, and the U CF frame_facts takes the run ceiling it speaks about: the slot's own, the one the
   agreement top (lib/AgreeRoomP3.ubsan_agrees_room_of_slots_p3) hands over together with limlaw_at LIM_AG. The plain
   twin needs no such premise because there RM_ag's bound is SRC_LIM_MIN itself. *)

Lemma cf_frame_allocator_src0 (rc : RunCeil) (fx : FPState)
    (LIM : limlaw_at LIM_AG src0_msyms (@zlib_API rc)) :
  @SRCF3.frame_allocator rc fx src0_msyms (@zlib_API rc).
Proof.
  pose proof (FrameProof.zlib_frame_allocator rc fx) as
    (_ & _ & _ & _ & _ & SLK & CTX & LOW & NDP & BW & EU & GRW & AX & NG & NR).
  split.
  { exact (ag_malloc_contract src0_msyms (@zlib_API rc) LIM zlib_pack3_malloc_contract_cf). }
  split.
  { exact (ag_free_contract src0_msyms (@zlib_API rc) zlib_pack3_free_contract_cf). }
  split.
  { first [exact zlib_pack3_free_null_contract_cf
          | exact (free_null_contract_of_cf src0_msyms zlib_pack3_free_null_contract_cf)
          | apply free_null_contract_of_cf; exact zlib_pack3_free_null_contract_cf]. }
  split.
  { intros pc Hpc. split.
    - exact (ag_realloc_contract src0_msyms (@zlib_API rc) LIM pc
        (zlib_pack3_realloc_contract_cf pc Hpc)).
    - exact (ag_realloc_null_contract src0_msyms (@zlib_API rc) LIM pc
        (zlib_pack3_realloc_null_contract_cf pc Hpc)). }
  split.
  { intros pc Hpc. vm_compute in Hpc. discriminate Hpc. }
  split; [exact SLK|]. split; [exact CTX|]. split; [exact LOW|]. split; [exact NDP|].
  split; [exact BW|]. split; [exact EU|]. split; [exact GRW|]. split; [exact AX|].
  split; [exact NG|exact NR].
Qed.

Lemma cf_frame_src0 (rc : RunCeil) (LS : lib_shape) :
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall n b, @lib_delta LS n b = b) ->
  limlaw_at LIM_AG src0_msyms (@zlib_API rc) ->
  @frame_facts rc src0_msyms (@zlib_API) LS src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  intros HK HD LIM.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact FrameProof.errno_below_ceiling|].
  do 18 (split; [reflexivity|]).
  split; [split; vm_compute; reflexivity|].
  split; [exact FrameProof.ctx_not_ro|].
  split; [exact FrameProof.frame_G_facts|].
  split; [exact FrameProof.frame_RELRO_facts|].
  split; [exact HK|].
  split; [exact HD|].
  intros fx. exact (cf_frame_allocator_src0 rc fx LIM).
Qed.

Lemma RI3P_start_ok : RI_start (RI3P GSF) CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E HF C G CAP OUT HT HC HCAP HOUT.
  split; [exact (CF.SlotRI3.RI3_start_ok B API LS SH SK ra empty rc fx j E HF C G CAP OUT HT HC HCAP HOUT)|].
  destruct HF as (_ & _ & (_ & (_ & HG) & _) & _). exact HG.
Qed.

Lemma RI3P_end_ok : RI_end (RI3P GSF) CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E (_ & _ & HP & _) k V L A T' (HRI & HOK) HND HPV HT'l HT's.
  destruct HP as (PRE & HR0 & (HPE & _) & _ & _ & HTL0 & _).
  destruct PRE as ((_ & HW & _) & _).
  split; [|exact HOK].
  exact (CF.SlotRI3.RI3_end_x E (ss_b E) k V L A T' HW (proj1 HR0) HPE HTL0 HRI HND HPV HT'l HT's).
Qed.

Theorem fuzz_reply_slot_cgp3 : fuzz_reply_slot_p3 CS_reply frame_MCAP.
Proof.
  apply (slot_of_steps CS_reply (RI3P GSF)).
  - exact (entry_holds CS_reply (RI3P GSF) pack3_ag_formT RI3P_start_ok
      (entry_res_reply_RI3P GSF RM_ag RMH_RM_ag)
      (fun B API LS SH SK ra empty rc fx HF => proj1 (frame_contracts B API LS SH SK ra empty rc fx HF))).
  - intros op Hop.
    assert (H : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
    + exact (pass0_holds pack3_ag_formT check_bounded_holds
        (fun B API LS SH SK ra empty rc fx HF => proj1 (frame_contracts B API LS SH SK ra empty rc fx HF))
        (RI3P GSF) (RI3P_mono GSF) (op0_res_reply_RI3P GSF RM_ag RMH_RM_ag)).
    + exact (pass1_holds pack3_ag_formT check_bounded_holds
        (fun B API LS SH SK ra empty rc fx HF => proj1 (proj2 (frame_contracts B API LS SH SK ra empty rc fx HF)))
        (RI3P GSF) (RI3P_mono GSF) (push_res_reply_RI3P GSF RM_ag RMH_RM_ag)).
    + exact (pass2_holds pack3_ag_formT check_bounded_holds pthread_mutex_lock_holds pthread_mutex_unlock_holds
        drain_contracts check_no_loss_read_holds
        (fun B API LS SH SK ra empty rc fx HF => proj1 (proj2 (p4_contracts B API LS SH SK ra empty rc fx HF)))
        check_shape_done_holds (RI3P GSF) (RI3P_mono GSF)
        (p2_drain_res_s_RI3P GSF RM_ag RMH_RM_ag) (p2_cnl_res_s_RI3P GSF RM_ag RMH_RM_ag)).
    + exact (pass3_holds check_bounded_holds (RI3P GSF) (RI3P_mono GSF)).
    + exact (pass4_holds pack3_ag_formT check_bounded_holds check_no_loss_read_holds check_shape_done_holds
        p4_contracts (RI3P GSF) (RI3P_mono GSF) (p4_res_cf_RI3P GSF RM_ag RMH_RM_ag)).
    + exact (pass5_holds snprintf_holds (relay_reads_holds relay_source_holds) check_no_loss_read_holds
        check_bounded_holds check_shape_done_holds
        (p5c_res3_fullN_holds GSF RM_ag RMH_RM_ag) (l2_res_nl3P_holds GSF RM_ag RMH_RM_ag)
        (l2_res_se3P_holds GSF RM_ag RMH_RM_ag)
        p5v_cnt p5v_ncs p5v_wt p5v_pend p5v_ekc p5v_ekb p5v_old p5v_out p5v_chain gone_partial_holds p5_contracts).
    + exact (pass6_holds check_bounded_holds (RI3P GSF) (RI3P_mono GSF)).
    + exact (pass7_holds pack3_ag_formT (RI3P GSF) (RI3P_mono GSF) (op7_res_s_RI3P GSF RM_ag RMH_RM_ag)
        check_bounded_holds (strnlen_holds memchr_holds) memcpy_holds
        (check_shape_event_holds (next_line_holds memchr_holds) strlen_holds bcmp_holds check_shape_done_holds)
        (fun B API LS SH SK ra empty rc fx HF => proj2 (proj2 (frame_contracts B API LS SH SK ra empty rc fx HF)))).
    + exact (pass8_holds check_bounded_holds (RI3P GSF) (RI3P_mono GSF)).
    + exact (pass9_holds check_bounded_holds pthread_mutex_lock_holds pthread_mutex_unlock_holds (RI3P GSF)
        (RI3P_mono GSF)).
  - exact (exit_holds CS_reply (RI3P GSF) pack3_ag_formT
      (fun B API LS SH SK ra empty rc fx HF => proj1 (exit_contracts B API LS SH SK ra empty rc fx HF))
      (fun B API LS SH SK ra empty rc fx HF => proj1 (proj2 (exit_contracts B API LS SH SK ra empty rc fx HF)))
      (fun B API LS SH SK ra empty rc fx HF => proj2 (proj2 (exit_contracts B API LS SH SK ra empty rc fx HF)))
      check_shape_done_holds (exit_res_fin_RI3P GSF RM_ag RMH_RM_ag) (exit_res_ends_RI3P GSF RM_ag RMH_RM_ag)
      (exit_res_reset_RI3P GSF RM_ag RMH_RM_ag) RI3P_end_ok).
Qed.

Theorem fuzz_reply_slot_cgp3_src0 : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil), limlaw_at LIM_AG src0_msyms (@zlib_API rc) ->
  forall (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_cgp3 fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    CS_reply frame_MCAP G_reply frame_RELRO GI_t j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HK HD rc HLIM fx j Hj.
  exact (fuzz_reply_slot_cgp3 CS_reply_ok src0_msyms (@zlib_API) LS src0_sink_head src0_sink RA_LIB EMPTY rc
    (cf_frame_src0 rc LS HK HD HLIM) fx j Hj).
Qed.
