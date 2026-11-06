(* The ubsan slots at the frame: from the walk contracts of LLVMFuzzerTestOneInput at the frame's allocator
   (zlib_API rc, src0_msyms) and sink words, the slot contract U/FrameAPI.v's frame_ubsan asks for (lib_contract_g
   at G = frame_G, R = frame_RELRO, GI, ENTRY, RA_LIB, EMPTY, SLOT_STACK) and the cut-free one AgreeFrame.v's
   ubsan_agrees_of_slots asks for (U/SlotAgree.v lib_contract_cg at the same arguments), each for every lib_shape
   with the slot's laws; and Statements.ubsan_halts through U/FrameSlotG.v plain_halts_of_frame_slot (the theorem
   U/FrameProof.v's frame_ubsan_holds closes the frame with).
   llvm_binds_src0 discharges the slot's llvm_binds (U/Prog/T/receive_c.v h_binds) at the frame's allocator as the
   plain one does (Prog/T/SlotFrame.v): the RELRO block [RELRO_BASE, RELRO_BASE + RELRO_LEN) = [0x21ef8, 0x21fd0)
   lies in frame_RELRO's first block [0x21ee8, 0x22050). The cut-free slot also needs the allocator's limit law
   (llvm_limlaw), which U/AgreeZlib.v zlib_limit gives (SRC_LIM_MIN = 2 ^ 34). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import
  YK11 YK0s YK15 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import
  ZTraceSpec ZAllocator AllocRoom SlotTopG Contract FrameAPI FrameSlotG Img0 FrameProof SlotAgree AgreeZlib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TContract GI receive_c
  LLVMFuzzerTestOneInput_c SlotBridge SlotBridgeProof.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ctx_below_ceiling : forall rc : RunCeil, ms_ctx src0_msyms + CTX_SIZE <= @alloc_ceiling rc.
Proof.
  intros rc. pose proof (@alloc_ceiling_value rc) as [[H _] _].
  assert (E : ms_ctx src0_msyms + CTX_SIZE <= CEIL_MIN) by (apply Z.leb_le; vm_compute; reflexivity).
  lia.
Qed.

Lemma llvm_binds_src0 : forall rc : RunCeil, llvm_binds (rc:=rc) src0_msyms (@zlib_API rc).
Proof.
  intros rc. unfold llvm_binds, h_binds.
  split; [exact ms_segs_rsegs|].
  do 4 (split; [reflexivity|]).
  split; [exact (@zlib_allocator_extra rc)|].
  split; [exact (errno_below_ceiling rc)|].
  split; [exact (ctx_below_ceiling rc)|].
  split.
  - intros a Ha. apply frame_G_facts. apply frame_G_world. exact Ha.
  - intros a Ha. apply frame_RELRO_facts. exists 0x21ee8, 360. split; [left; reflexivity|].
    unfold RELRO_BASE, RELRO_LEN in Ha. lia.
Qed.

Lemma ret_ok_RA_LIB : YK0s.ret_ok (Z_to_bv 64 RA_LIB).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

Theorem llvm_slot_frame :
  (forall (rc : RunCeil) (fx : FPState),
     LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
       src0_msyms (@zlib_API rc)) ->
  forall (LS : lib_shape),
  (forall pl fs K, t_eq (@LIBK LS pl fs K) (K (LL 0 fs []))) ->
  (forall b n, @lib_room LS b n -> llvm_room b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      frame_G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros WALK LS HK HR HD rc fx j Hj.
  pose proof (@slot_bridge_holds fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    (WALK rc fx) harness_model_ok_holds (slot_world_holds _ _)) as SLOT.
  exact (SLOT (llvm_binds_src0 rc) (conj HK (conj HR HD)) j Hj RA_LIB EMPTY SLOT_STACK LLVM_K_fits ret_ok_RA_LIB).
Qed.

Theorem llvm_slot_frame_cg :
  (forall (rc : RunCeil) (fx : FPState),
     LLVMFuzzerTestOneInput_walk_contract_cf (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
       src0_msyms (@zlib_API rc)) ->
  forall (LS : lib_shape),
  (forall pl fs K, t_eq (@LIBK LS pl fs K) (K (LL 0 fs []))) ->
  (forall b n, @lib_room LS b n -> llvm_room_cf b) ->
  (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      frame_G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros WALK LS HK HR HD rc fx j Hj.
  pose proof (@slot_bridge_cg_holds fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    (WALK rc fx) harness_model_ok_holds (slot_world_holds _ _) (zlib_limit rc)) as SLOT.
  exact (SLOT (llvm_binds_src0 rc) (conj HK (conj HR HD)) j Hj RA_LIB EMPTY SLOT_STACK LLVM_K_fits ret_ok_RA_LIB).
Qed.

Theorem ubsan_halts_of_walk :
  (forall (rc : RunCeil) (fx : FPState),
     LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink)
       src0_msyms (@zlib_API rc)) ->
  Statements.ubsan_halts.
Proof.
  intros WALK.
  apply (plain_halts_of_frame_slot frame_G GI (fun a h => h) (GI_local src0_msyms) (GI_img src0_msyms)).
  apply (llvm_slot_frame WALK checksum_shape).
  - intros pl fs K. apply t_eq_refl.
  - intros b n H. exact H.
  - intros n b. reflexivity.
Qed.
