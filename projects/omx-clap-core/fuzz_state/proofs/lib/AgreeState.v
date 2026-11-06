From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom AgreeShape AgreeFrame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require FrameProof SlotTopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c
  StatementHalts AG.StatementHaltsAg AG.LinkAg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require FrameProof SlotTopG ZAllocator AllocCf ReallocCf
  AgreeZlib FrameAPI SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Ledger GIInit StatementHalts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require SlotCG.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_state's ubsan_agrees, from AgreeFrame.ubsan_agrees_of_slots at LS := ag_shape checksum_shape:
   - the plain halts slot: AG/LinkAg.slot_premise_plain_ag_holds (the plain slot at the agreement room, sb_cap =
     CAP_AG) at the concrete allocator (src0_msyms, zlib_API, src0_sink_head, src0_sink, EMPTY, ra := RA_LIB), with
     the frame facts of FrameProof.v and ag_shape's room;
   - the room fact: AgreeShape.ag_room_calls;
   - the ubsan cut-free slot: U/Prog/CF/SlotCG.fuzz_state_slot_cg at the ubsan build's concrete allocator, with the
     frame facts of U/FrameProof.v, the cut-free allocator contracts of U/AllocCf.v and U/ReallocCf.v and the budget
     law U/AgreeZlib.zlib_limit (SRC_LIM_MIN = 2 ^ 34);
   - the G/GI facts: omx_G_inside, omx_GI_local (StatementHalts.v) and omx_GI_init (GIInit.v) of each build. *)

Lemma state_plain_slot : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc (ag_shape checksum_shape) src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    omx_G frame_RELRO (omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros rc fx j Hj.
  assert (FF : frame_facts_plain_ag src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink EMPTY).
  { unfold frame_facts_plain_ag.
    split; [exact lib.SlotTopG.ms_segs_rsegs|].
    do 4 (split; [reflexivity|]).
    split; [exact lib.FrameProof.errno_below_ceiling|].
    do 14 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact lib.FrameProof.ctx_not_ro|].
    split; [exact lib.FrameProof.frame_G_facts|].
    split; [exact lib.FrameProof.frame_RELRO_facts|].
    split; [intros pl fs K; reflexivity|].
    split; [intros n b; reflexivity|].
    split; [intros b n H; exact H|].
    exact lib.FrameProof.zlib_frame_allocator. }
  exact (slot_premise_plain_ag_holds src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink EMPTY
    FF rc fx j RA_LIB Hj ltac:(vm_compute; reflexivity)).
Qed.

Lemma state_ubsan_slot : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @U.SlotAgree.lib_contract_cg fx rc (ag_shape checksum_shape) U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
    U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
    U.Prog.GIInit.omx_G U.FrameAPI.frame_RELRO (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms) j
    U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY U.FrameAPI.SLOT_STACK.
Proof.
  intros rc fx j Hj.
  assert (FF : U.Prog.CF.SlotCG.frame_facts_ag U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API)
    (ag_shape checksum_shape) U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.EMPTY).
  { unfold U.Prog.CF.SlotCG.frame_facts_ag.
    split; [exact U.SlotTopG.ms_segs_rsegs|].
    do 4 (split; [reflexivity|]).
    split; [exact U.FrameProof.errno_below_ceiling|].
    do 14 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact U.FrameProof.ctx_not_ro|].
    split; [exact U.FrameProof.frame_G_facts|].
    split; [exact U.FrameProof.frame_RELRO_facts|].
    split; [intros pl fs K; reflexivity|].
    split; [intros n b; reflexivity|].
    split; [intros b n H; exact H|].
    exact U.FrameProof.zlib_frame_allocator. }
  refine (U.Prog.CF.SlotCG.fuzz_state_slot_cg U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API)
    (ag_shape checksum_shape) U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.EMPTY FF
    _ _ _ _ _ rc fx j U.Reusable.YL0s.RA_LIB Hj _).
  - intros rc' fx'. exact (@U.AllocCf.zlib_malloc_contract_cf fx' rc').
  - intros rc' fx'. exact (@U.AllocCf.zlib_free_contract_cf fx' rc').
  - intros rc' fx'. exact U.AllocCf.src0_free_null_cf.
  - intros rc' fx' pc Hpc.
    exact (conj (U.ReallocCf.zlib_realloc_contract_cf pc Hpc) (U.ReallocCf.zlib_realloc_null_contract_cf pc Hpc)).
  - intros rc' L A mem md HM. exact (U.AgreeZlib.zlib_limit rc' L A mem md HM).
  - vm_compute. reflexivity.
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots (ag_shape checksum_shape) omx_G (omx_GI src0_msyms)
    U.Prog.GIInit.omx_G (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms)).
  - exact omx_G_inside.
  - exact (omx_GI_local src0_msyms).
  - intros mem HI. apply omx_GI_init; [exact lib.SlotTopG.ms_segs_rsegs | exact HI].
  - exact state_plain_slot.
  - intros data. apply ag_room_calls.
  - exact U.Prog.StatementHalts.omx_G_inside.
  - exact (U.Prog.StatementHalts.omx_GI_local U.Reusable.YH02.src0_msyms).
  - intros mem HI. apply U.Prog.GIInit.omx_GI_init; [exact U.SlotTopG.ms_segs_rsegs | exact HI].
  - exact state_ubsan_slot.
Qed.
