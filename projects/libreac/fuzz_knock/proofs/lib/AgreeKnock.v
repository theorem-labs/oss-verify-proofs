From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH02 YI5b YI5c YL0g YL0s YM02 YO05 YO06.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import AllocSlots Contract FrameAPI ZAllocator AgreeFrame AgreeShape ZTraceSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require KnockSlot.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require SlotAgree AgreeZlib Contract FrameAPI ZAllocator.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require KnockSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_knock ubsan_agrees: the frame's ubsan_agrees_of_slots (AgreeFrame.v) for the agreement shape (silent output,
   the agreement room of SBD_AG), the plain halts slot (lib/Prog/KnockSlot.knock_slot; the short name KnockSlot is the ubsan one) and the ubsan cut-free slot
   (U/Prog/KnockSlotCF.knock_slot_cg_frame), for the frame's agreement shape over the silent checksum_shape
   (AgreeShape.ag_shape). The slot makes no allocator call, so it needs no room. *)

Definition ag_sil_shape : lib_shape := ag_shape checksum_shape.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots ag_sil_shape [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j _. rewrite lib_contract_g_gm.
    eapply (@OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog.KnockSlot.knock_slot
      OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R.Cfg.AcfgMode fx rc ag_sil_shape);
      first [reflexivity | (intros; reflexivity) | (vm_compute; reflexivity)].
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. exact (KnockSlotCF.knock_slot_cg_frame ag_sil_shape (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
      rc fx j Hj).
Qed.
