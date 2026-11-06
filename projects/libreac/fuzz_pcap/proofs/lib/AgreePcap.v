From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap Require Statements.
(* The ubsan modules first: a later Require of a plain module rebinds the short names to the plain one. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require SlotAgree AgreeZlib ZAllocator AllocCf FrameProof
  SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require UTopCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH02 YI16 YI5b YI5c YL0g YL0s YM02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import AllocSlots Contract FrameAPI OutForm ZAllocator
  FrameProof SlotTopG AgreeFrameO AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk PInv PSlot PHolds PTopCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AllocCf AgreeZlib.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_pcap ubsan_agrees from the frame's output top (AgreeFrameO.ubsan_agrees_of_slots_o) for the agreement
   output shape (the slot writes PWalk.OUT of the payload to stderr; the agreement room SBD_AG), the plain slot
   (Prog/Slot PSlot.slot_contract_ols, PHolds.pcap_entry) and the ubsan cut-free slot (U/Prog/Slot
   UTopCF.pcap_ubsan_slot_cgo). The cut-free slot's malloc steps take the run limit law of the agreement frame
   (LIMLAW, AGREES.md (sha256 49058c34f32b; internal record) 'Slot forms for allocating targets'), a premise here until the frame threads it into
   lib_contract_cgo. *)

Definition ag_out_shape : lib_shape := ag_shape (out_shape OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT).

(* The plain frame instance (FrameProof.frame_plain_holds' allocator and image). *)
Lemma ag_ff_plain : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PInv.frame_facts src0_msyms (@zlib_API) src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  unfold OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PInv.frame_facts.
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
  split; [exact zlib_frame_allocator|].
  split; reflexivity.
Qed.

(* The ubsan frame instance (U.FrameProof). *)
Lemma ag_ff_ubsan : U.Prog.Slot.PInv.frame_facts U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API)
  U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY.
Proof.
  unfold U.Prog.Slot.PInv.frame_facts.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact U.FrameProof.errno_below_ceiling|].
  do 12 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact U.FrameProof.ctx_not_ro|].
  split; [exact U.FrameProof.frame_G_facts|].
  split; [exact U.FrameProof.frame_RELRO_facts|].
  split; [exact U.FrameProof.zlib_frame_allocator|].
  split; reflexivity.
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots_o ag_out_shape OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT frame_G OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PInv.GI
    U.FrameAPI.frame_G U.Prog.Slot.PInv.GI).
  - intros a Ha. exact Ha.
  - exact (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PSlot.GI_local src0_msyms eq_refl).
  - intros mem Hm. exact (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PSlot.GI_img src0_msyms mem eq_refl Hm).
  - intros rc fx j _.
    exact (@OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PSlot.slot_contract_ols fx rc src0_msyms (@zlib_API)
      src0_sink_head src0_sink RA_LIB EMPTY ag_ff_plain ag_out_shape OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
      (ag_room_g _)
      (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PHolds.pcap_entry rc src0_msyms (@zlib_API) src0_sink_head
         src0_sink RA_LIB EMPTY ag_ff_plain)
      OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT_big j).
  - intros data. apply ag_room_calls.
  - intros a Ha. exact Ha.
  - exact (U.Prog.Slot.PSlot.GI_local U.Reusable.YH02.src0_msyms eq_refl).
  - intros mem Hm. exact (U.Prog.Slot.PSlot.GI_img U.Reusable.YH02.src0_msyms mem eq_refl Hm).
  - intros rc fx j _.
    eapply (@U.Prog.Slot.UTopCF.pcap_ubsan_slot_cgo fx rc ag_out_shape U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API));
      first [ exact ag_ff_ubsan
            | exact (fun fx' => @U.AllocCf.zlib_malloc_contract_cf fx' rc)
            | exact (fun fx' => @U.AllocCf.zlib_free_contract_cf fx' rc)
            | exact (fun fx' => @U.AllocCf.src0_free_null_cf fx')
            | exact (U.AgreeZlib.zlib_limit rc)
            | (intros; reflexivity)
            | exact (ag_room_cg _) ].
Qed.

(* The plain cut-free slot (the canonical agreement form needs both runs placement-uniform): lib_contract_cgo of the
   plain build at the frame instance and the agreement output shape. *)
Theorem pcap_plain_slot_cgo_frame : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @OSSVerify.Proofs.libreac.fuzz_pcap.lib.SlotAgreeV.lib_contract_cgo fx rc ag_out_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT frame_G frame_RELRO
    OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PInv.GI j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros rc fx j _.
  eapply (@OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PTopCF.pcap_plain_slot_cgo fx rc ag_out_shape
    src0_msyms (@zlib_API));
    first [ exact ag_ff_plain
          | exact (fun fx' => @AllocCf.zlib_malloc_contract_cf fx' rc)
          | exact (fun fx' => @AllocCf.zlib_free_contract_cf fx' rc)
          | exact (fun fx' => @AllocCf.src0_free_null_cf fx')
          | exact (AgreeZlib.zlib_limit rc)
          | (intros; reflexivity)
          | exact (ag_room_cg _) ].
Qed.
