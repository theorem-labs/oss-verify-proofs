(* Statements.ubsan_agrees from the two builds' slots, as the donor's lib/Prog/LLVMFuzzerTestOneInput_agree.v
   (libdiginet/fuzz_decode, after libreac/fuzz_decode's released file): AgreeFrame.v ubsan_agrees_of_slots at
   ag_shape kept_shape, with the plain slot (Prog/T/SlotFrame.v llvm_slot_frame, lib_contract_g) and the ubsan
   cut-free slot (U/Prog/T/SlotFrame.v llvm_slot_frame_cg, lib_contract_cg), both at G = frame_G and GI of the
   build's Prog/T/GI.v. The shape's room laws are AgreeShape.v's ag_room_g (the plain llvm_room) and ag_room_cg (the
   ubsan llvm_room_cf); both slots return 0 (lib_post_g's a0 = 0, from the model's Some (_, 0)), so the kit's 0-only
   agree frame applies as it is. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YM05 YM02 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import AgreeShape AgreeFrame FrameSlotK.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require GI LLVMFuzzerTestOneInput_c SlotFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require GI LLVMFuzzerTestOneInput_c SlotFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require YH02 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YH02 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require ZAllocator.
Import ListNotations.
Local Open Scope Z_scope.

Module PC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.LLVMFuzzerTestOneInput_c.
Module PGI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.GI.
Module PF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.SlotFrame.
Module UC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.LLVMFuzzerTestOneInput_c.
Module UGI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.GI.
Module UF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.SlotFrame.
Module PH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YH02.
Module PSH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.
Module PSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.
Module PZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.ZAllocator.
Module UH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable.YH02.
Module USH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable.YI5b.
Module USK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable.YI5c.
Module UZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.ZAllocator.

Theorem ubsan_agrees_of_walks :
  (forall (rc : RunCeil) (fx : FPState),
     PC.LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=PSH.src0_sink_head) (SK:=PSK.src0_sink)
       PH.src0_msyms (@PZ.zlib_API rc)) ->
  (forall (rc : RunCeil) (fx : FPState),
     UC.LLVMFuzzerTestOneInput_walk_contract_cf (fx:=fx) (rc:=rc) (SH:=USH.src0_sink_head) (SK:=USK.src0_sink)
       UH.src0_msyms (@UZ.zlib_API rc)) ->
  Statements.ubsan_agrees.
Proof.
  intros WP WU.
  refine (ubsan_agrees_of_slots (ag_shape kept_shape) _ PGI.GI _ UGI.GI (fun a h => h)
    (PGI.GI_local _) (PGI.GI_img _) _ _ (fun a h => h) (UGI.GI_local _) (UGI.GI_img _) _).
  - apply (PF.llvm_slot_frame WP).
    + intros pl fs K. apply t_eq_refl.
    + intros b n H. exact (ag_room_g kept_shape b n H).
    + intros n b. reflexivity.
  - intros data. apply ag_room_calls.
  - apply (UF.llvm_slot_frame_cg WU).
    + intros pl fs K. apply t_eq_refl.
    + intros b n H. exact (ag_room_cg kept_shape b n H).
    + intros n b. reflexivity.
Qed.
