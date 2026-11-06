From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH02 YI5b YI5c YL0g YL0s YM02 YO05 YO06.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import AllocSlots Contract FrameAPI ZAllocator AgreeFrame AgreeShape ZTraceSpec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AllocRoom.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require CodecSlot LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require SlotAgree AgreeZlib Contract FrameAPI ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require CodecSlotCF LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_codec ubsan_agrees: the frame's ubsan_agrees_of_slots (AgreeFrame.v) for the agreement shape (silent output,
   the agreement room of SBD_AG), the plain halts slot (lib/Prog/CodecSlot.codec_slot; the short name CodecSlot is the ubsan one) and the ubsan cut-free slot
   (U/Prog/CodecSlotCF.codec_slot_cg_frame), for the frame's agreement shape over the silent checksum_shape
   (AgreeShape.ag_shape). The slot makes no allocator call, so it needs no room. Each slot takes its build's main
   contract (Prog/LLVMFuzzerTestOneInput_c and U/Prog/LLVMFuzzerTestOneInput_c.codec_main_contract). *)

Definition ag_sil_shape : lib_shape := ag_shape checksum_shape.

Theorem ubsan_agrees_holds :
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.LLVMFuzzerTestOneInput_c.codec_main_contract ->
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.LLVMFuzzerTestOneInput_c.codec_main_contract ->
  Statements.ubsan_agrees.
Proof.
  intros HMP HMU.
  apply (ubsan_agrees_of_slots ag_sil_shape [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j _. rewrite lib_contract_g_gm.
    eapply (@OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecSlot.codec_slot
      OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R.Cfg.AcfgMode fx rc ag_sil_shape);
      first [exact HMP | reflexivity | (intros; reflexivity) | (vm_compute; reflexivity)].
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. exact (CodecSlotCF.codec_slot_cg_frame HMU ag_sil_shape (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
      rc fx j Hj).
Qed.
