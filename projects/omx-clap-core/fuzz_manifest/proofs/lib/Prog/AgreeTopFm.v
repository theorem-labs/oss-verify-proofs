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
  SlotAgree Agree AgreeTop AgreeZlib AgreeCanon AgreeShape AllocCf SlotTopG FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger StatementPlain StatementPlainCg
  ManifestEndCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require AgreeZlib AllocCf SlotTopG FrameProof
  FrameAPI SlotAgree ZAllocator.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Ledger StatementUbsan StatementUbsanCg
  ManifestEndCf.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_manifest's instance of the agreement top AgreeCanon.ubsan_agrees_room_of_slots, at the concrete allocator
   (src0_msyms, zlib_API, src0_sink_head, src0_sink, RA_LIB, EMPTY) of each build and the agreement shape
   ag_shape checksum_shape (AgreeShape.v: lib_room at the SBD_AG form). Proved here from the frame:
   - the room fact: AgreeShape.ag_room_calls;
   - the G/GI facts: manifest_G_sub, omx_GI_local, omx_GI_img (StatementPlain.v, StatementUbsan.v);
   - the cut-free slots: ManifestEndCf.slot_fill_cg_holds of each build (lib/Prog, lib/U/Prog) at the frame facts of
     FrameProof.v with AgreeShape.ag_room_cg, AllocCf.zlib_malloc_contract_cf / zlib_free_contract_cf and
     AgreeZlib.zlib_limit (2^34 <= vm_limit) of that build;
   - plain_canon_complete / ubsan_canon_complete: AgreeCanon.plain_canon_complete_of_placed /
     ubsan_canon_complete_of_placed from the slots, the room fact and placement.
   The Section hypotheses are the premises the frame does not prove yet. *)

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

Section Top.

(* Placement of the plain build (AgreeCanon.plain_placed): every run from a valid entry on a valid input reaches
   only configurations that are not unplaced (RoomShapesDraft.unplaced_at). No frame piece concludes placed_run
   yet; it is the remaining premise of AgreeCanon.plain_canon_complete_of_placed. *)
Hypothesis PPLACED : plain_placed.

(* Placement of the ubsan build (AgreeCanon.ubsan_placed), the same for Images.ubsan at lim_target; the remaining
   premise of AgreeCanon.ubsan_canon_complete_of_placed. *)
Hypothesis UPLACED : ubsan_placed.

Theorem fm_agrees_room :
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof using PPLACED UPLACED.
  pose proof (fun mem => omx_GI_img src0_msyms mem ms_segs_rsegs) as GI0.
  pose proof (fun mem => U.Prog.StatementUbsan.omx_GI_img U.Reusable.YH02.src0_msyms mem U.SlotTopG.ms_segs_rsegs)
    as GI0u.
  apply (ubsan_agrees_room_of_slots (ag_shape checksum_shape) manifest_G (omx_GI src0_msyms)
    U.Prog.StatementUbsan.manifest_G (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms)
    manifest_G_sub (omx_GI_local src0_msyms) GI0 fm_plain_slot fm_room
    U.Prog.StatementUbsan.manifest_G_sub (U.Prog.StatementUbsan.omx_GI_local U.Reusable.YH02.src0_msyms) GI0u
    fm_ubsan_slot).
  - exact (plain_canon_complete_of_placed (ag_shape checksum_shape) manifest_G (omx_GI src0_msyms)
      manifest_G_sub (omx_GI_local src0_msyms) GI0 fm_plain_slot fm_room PPLACED).
  - exact (ubsan_canon_complete_of_placed (ag_shape checksum_shape) U.Prog.StatementUbsan.manifest_G
      (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms) fm_room
      U.Prog.StatementUbsan.manifest_G_sub (U.Prog.StatementUbsan.omx_GI_local U.Reusable.YH02.src0_msyms) GI0u
      fm_ubsan_slot UPLACED).
Qed.

End Top.
