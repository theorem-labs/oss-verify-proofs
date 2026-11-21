From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require RoomShapesDraft.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK0i YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG Img0
  SlotAgree Agree AgreeTop AgreeZlib AgreeShape AllocCf SlotTopG FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger StatementPlain StatementPlainCg
  ManifestEndCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require AgreeZlib AllocCf SlotTopG FrameProof
  FrameAPI SlotAgree ZAllocator.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Ledger StatementUbsan StatementUbsanCg
  ManifestEndCf.
Import ListNotations.
Open Scope Z_scope.

Lemma fm_room : forall data, @room_calls (ag_shape checksum_shape) (payload_len data) (calls data) U.AgreeZlib.SBD_AG.
Proof using. intros data. exact (ag_room_calls checksum_shape _ _). Qed.

Lemma fm_plain_slot : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_cg fx rc (ag_shape checksum_shape) src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    manifest_G frame_RELRO (omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof using.
  apply (slot_fill_cg_holds src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink RA_LIB EMPTY).
  - unfold frame_facts_cg.
    split; [exact ms_segs_rsegs|].
    split; [vm_compute; reflexivity|].
    do 4 (split; [reflexivity|]).
    split; [exact errno_below_ceiling|].
    do 14 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact ctx_not_ro|].
    split; [exact frame_G_facts|].
    split; [exact frame_RELRO_facts|].
    split; [intros pl fs K; reflexivity|].
    split; [intros n b; reflexivity|].
    split; [exact (ag_room_cg checksum_shape)|].
    exact zlib_frame_allocator.
  - intros rc fx. exact (@zlib_malloc_contract_cf fx rc).
  - intros rc fx. exact (@zlib_free_contract_cf fx rc).
  - exact zlib_limit.
Qed.

Lemma fm_ubsan_slot : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @U.SlotAgree.lib_contract_cg fx rc (ag_shape checksum_shape) U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
    U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Prog.StatementUbsan.manifest_G U.FrameAPI.frame_RELRO
    (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms) j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
    U.FrameAPI.SLOT_STACK.
Proof using.
  apply (U.Prog.ManifestEndCf.slot_fill_cg_holds U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API)
    (ag_shape checksum_shape) U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
    U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY).
  - unfold U.Prog.StatementUbsanCg.frame_facts_cg.
    split; [exact U.SlotTopG.ms_segs_rsegs|].
    split; [vm_compute; reflexivity|].
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
    split; [exact (ag_room_cg checksum_shape)|].
    exact U.FrameProof.zlib_frame_allocator.
  - intros rc fx. exact (@U.AllocCf.zlib_malloc_contract_cf fx rc).
  - intros rc fx. exact (@U.AllocCf.zlib_free_contract_cf fx rc).
  - exact U.AgreeZlib.zlib_limit.
Qed.
