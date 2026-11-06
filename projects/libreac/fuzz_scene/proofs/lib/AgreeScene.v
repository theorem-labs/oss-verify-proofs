From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_scene Require Statements.
(* The ubsan modules first: a later Require of a plain module rebinds the short names to the plain one. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require SlotAgree AgreeZlib ZAllocator.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.SegCF Require CEntry.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH02 YI5b YI5c YL0g YL0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import AllocSlots Contract FrameAPI ZAllocator FrameProof
  ZTraceSpec AgreeFrame AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require memcpy memset bcmp reac_ctrl_build_scene_step check_step
  reac_ctrl_parse kind_of_link1 reac_ctrl_checksum_verify reac_ctrl_scene_set_mac reac_ctrl_scene_build.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require SInv SSlot SEntry SEarly.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_scene ubsan_agrees from the frame's ubsan_agrees_of_slots (AgreeFrame.v) for the agreement shape (silent
   output, the agreement room SBD_AG), the plain halts slot (Prog/Seg OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SSlot.slot_lib, OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SEntry.slot_entry) and the
   ubsan cut-free slot (U/Prog/SegCF/CEntry.scene_slot_cg_frame), for the frame's agreement shape over the silent
   checksum_shape (AgreeShape.ag_shape). *)

Definition ag_sil_shape : lib_shape := ag_shape checksum_shape.

(* The plain halts slot for the agreement shape. *)
Lemma scene_slot_g_frame : forall (rc : RunCeil) (fx : FPState) (j : nat),
  @OSSVerify.Proofs.libreac.fuzz_scene.lib.Contract.lib_contract_g fx rc ag_sil_shape OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YH02.src0_msyms (@OSSVerify.Proofs.libreac.fuzz_scene.lib.ZAllocator.zlib_API rc)
    OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI5c.src0_sink
    [] OSSVerify.Proofs.libreac.fuzz_scene.lib.FrameAPI.frame_RELRO (fun _ _ => True) j OSSVerify.Proofs.libreac.fuzz_scene.lib.FrameAPI.ENTRY OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YL0s.RA_LIB OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YL0s.EMPTY
    OSSVerify.Proofs.libreac.fuzz_scene.lib.FrameAPI.SLOT_STACK.
Proof.
  intros rc fx j.
  assert (FF : OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SInv.frame_facts src0_msyms (@zlib_API) ag_sil_shape src0_sink_head src0_sink RA_LIB EMPTY).
  { unfold OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SInv.frame_facts.
    split; [reflexivity|].
    split; [vm_compute; reflexivity|].
    do 4 (split; [reflexivity|]).
    split; [exact errno_below_ceiling|].
    do 12 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact ctx_not_ro|].
    split; [exact frame_G_facts|].
    split; [exact frame_RELRO_facts|].
    split; [intros pl fs K; reflexivity|].
    split; [intros n b; reflexivity|].
    split; [exact zlib_frame_allocator|].
    split; reflexivity. }
  pose proof memcpy.memcpy_holds as MEMC. pose proof memset.memset_holds as MEMS. pose proof bcmp.bcmp_holds as BCMP.
  pose proof (reac_ctrl_build_scene_step.reac_ctrl_build_scene_step_holds MEMS MEMC) as BUILD.
  pose proof (check_step.check_step_holds BCMP MEMC
    (reac_ctrl_parse.reac_ctrl_parse_holds MEMS MEMC BCMP kind_of_link1.kind_of_link1_holds)
    reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds) as CHECK.
  pose proof (reac_ctrl_scene_set_mac.reac_ctrl_scene_set_mac_holds MEMC) as SETMAC.
  pose proof (reac_ctrl_scene_build.reac_ctrl_scene_build_holds MEMS MEMC) as SBUILD.
  apply (OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SSlot.slot_lib src0_msyms (@zlib_API) RA_LIB EMPTY FF OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SEarly.scene_early_holds).
  - exact (ag_room_g checksum_shape).
  - destruct (zlib_frame_allocator rc fx) as (HMAL & HFREE & _).
    apply (OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg.SEntry.slot_entry src0_msyms (@zlib_API) RA_LIB EMPTY FF
      HMAL HFREE MEMC MEMS BCMP BUILD CHECK SETMAC SBUILD).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots ag_sil_shape [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j _. exact (scene_slot_g_frame rc fx j).
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (CEntry.scene_slot_cg_frame ag_sil_shape (fun _ _ _ => eq_refl) (fun _ _ => eq_refl) (ag_room_cg checksum_shape)
      rc fx j Hj).
Qed.
