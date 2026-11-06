(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: decode_plain_rz of libreac/fuzz_decode's lib/A/AsanTop.v for fuzz_frame, at frame_shape, over fuzz_frame's plain slot theorem lib/Prog/LLVMFuzzerTestOneInput_gfr.v frame_slot_g_frame, whose one premise is the plain walk of LLVMFuzzerTestOneInput (lib/Prog/Statement.v slot_sr_all); module paths changed. *)
(* The plain side of fuzz_transport's two ASan agreement statements: the plain build realizes SPECX at transport_shape from
   every valid start at 2^34 (A/TransportShape.v transport_plain_rz_stmt), given the plain walk of LLVMFuzzerTestOneInput
   (llvm_walk_at_frame). It is built as lib/AgreeFrame.v builds the plain side of the ubsan agreement
   (lib/Prog/T/SlotAgreeFrame.v), at transport_shape = ag_shape kept_shape. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_transport Require Images.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require GI SlotFrame WalkAll.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportShape.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module PGI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.GI.
Module PF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.SlotFrame.
Module PW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkAll.

Section p.
Hypothesis W : PW.llvm_walk_at_frame.

Lemma transport_plain_rz : transport_plain_rz_stmt.
Proof.
  unfold transport_plain_rz_stmt.
  assert (Hp : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_g fx rc transport_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      frame_G frame_RELRO PGI.GI j ENTRY RA_LIB EMPTY SLOT_STACK).
  { apply (PF.llvm_slot_frame W).
    - intros pl fs K. apply t_eq_refl.
    - intros b n H. exact (ag_room_g _ b n H).
    - intros n b. reflexivity. }
  assert (HROOMp : forall data, @room_calls transport_shape (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls _ (payload_len data) (calls data))).
  assert (HC : zlib_runtime_contracts_R transport_shape (@RI_G transport_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ PGI.GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G transport_shape) frame_G frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step transport_shape PGI.GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) frame_G frame_RELRO PGI.GI (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) frame_G frame_RELRO PGI.GI j
        LIBPC RA_LIB EMPTY LIB_STACK (Hp rc fx j Hj))). }
  exact (plain_rz_of_contracts_R transport_shape (@RI_G transport_shape) frame_G frame_RELRO
    (fun j T m => T = [] /\ PGI.GI j m) (fun _ => [])
    (driver_RI_AG transport_shape HROOMp) (fun a h => frame_G_src0 a h) frame_RELRO_src0
    (G_local_T_of_G src0segs frame_G PGI.GI (PGI.GI_local src0_msyms))
    (fun mem H => conj eq_refl (PGI.GI_img src0_msyms mem H)) HC).
Qed.
End p.
