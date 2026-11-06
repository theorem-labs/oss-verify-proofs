From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom AgreeShape AgreeFrame SlotTopG FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger StatementPlain StatementPlainAg
  ManifestEndAg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require AgreeTopFm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require SlotTopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Ledger StatementUbsan.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_manifest's ubsan_agrees, from AgreeFrame.ubsan_agrees_of_slots at LS := ag_shape checksum_shape:
   - the plain halts slot: ManifestEndAg.slot_fill_ag_holds (the bounded-room plain slot) at the concrete allocator
     (src0_msyms, zlib_API, src0_sink_head, src0_sink, RA_LIB, EMPTY), with the frame facts of FrameProof.v and
     AgreeShape.ag_room_g;
   - the room fact and the ubsan cut-free slot: AgreeTopFm.fm_room and AgreeTopFm.fm_ubsan_slot;
   - the G/GI facts: manifest_G_sub, omx_GI_local, omx_GI_img of each build (StatementPlain.v, StatementUbsan.v). *)

Lemma fm_plain_slot_ag : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc (ag_shape checksum_shape) src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    manifest_G frame_RELRO (omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof using.
  apply (slot_fill_ag_holds src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink RA_LIB EMPTY).
  unfold frame_facts_ag.
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
  split; [exact (ag_room_g checksum_shape)|].
  exact zlib_frame_allocator.
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof using.
  exact (ubsan_agrees_of_slots (ag_shape checksum_shape) manifest_G (omx_GI src0_msyms)
    U.Prog.StatementUbsan.manifest_G (U.Prog.Ledger.omx_GI U.Reusable.YH02.src0_msyms)
    manifest_G_sub (omx_GI_local src0_msyms) (fun mem => omx_GI_img src0_msyms mem ms_segs_rsegs)
    fm_plain_slot_ag AgreeTopFm.fm_room
    U.Prog.StatementUbsan.manifest_G_sub (U.Prog.StatementUbsan.omx_GI_local U.Reusable.YH02.src0_msyms)
    (fun mem => U.Prog.StatementUbsan.omx_GI_img U.Reusable.YH02.src0_msyms mem U.SlotTopG.ms_segs_rsegs)
    AgreeTopFm.fm_ubsan_slot).
Qed.
