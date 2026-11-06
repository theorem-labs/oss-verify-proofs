(* The bridges from the walk of LLVMFuzzerTestOneInput and the simulation theorem to the slot contracts, ubsan
   image: the statements only (their proofs: U/Prog/T/SlotBridgeProof.v). *)
(* Each proof composes three things, as the plain one (Prog/T/SlotBridge.v):
   - the walk contract (U/Prog/T/LLVMFuzzerTestOneInput_c.v): LLVMFuzzerTestOneInput_walk_contract (SR) for the
     halting slot, LLVMFuzzerTestOneInput_walk_contract_cf (SRcf) for the cut-free slot;
   - harness_model_ok_stmt: TSim's top theorem (TSim/TopOk.v harness_model_ok) on the patched
     harness model, with no premise on the input (op 8 with both hand-overs included) and no section hypothesis;
     `exact TopOk.harness_model_ok` proves it (TopOk's heap_ok has llvm_heap_ok's body); the model is
     build-independent, so the plain and the ubsan bridge use the same statement, at timg_ubsan;
   - slot_world: in every memory the slot is entered with, the world [W_BASE_UBSAN, W_BASE_UBSAN + W_LEN) is present
     and writable: an image fact (frame_G is .bss of the image's last writable PT_LOAD, which elf_snapshot zero-fills
     to its page-rounded memsz, so LPS wview is Some there for every memory).
   Given the slot's premises: Bw from slot_world; timg_ok timg_ubsan by computation; length Bw = W_LEN by wm_len;
   harness_model_ok_stmt gives llvm_model_ok Bw pl; the walk contract gives the SR (SRcf) form; its post gives
   lib_post_g as the donor's llvm_g_of_sr / llvm_g_of_sr_cf do (fuzz_decode U/Prog/LLVMFuzzerTestOneInput_g.v,
   U/Prog/LLVMFuzzerTestOneInput_gcg.v). The cut-free bridge also takes llvm_limlaw, which the walk_contract_cf
   asks for (the donor's LLVMFuzzerTestOneInput_cgt.v takes it as a hypothesis too). One clause the donor closed
   vacuously (its G was []) is not vacuous here: lib_post_g's writability of G across the call; it holds by the same
   image fact as slot_world, which the bridges' proofs state as a lemma.
   llvm_binds (= receive_c.v h_binds) is a premise of both the walk contract and the slot contract, so the bridge
   passes it through; whoever applies the slot contract discharges it from U/FrameAPI.v frame_ubsan: the symbol
   values, AllocExtra, errno_addr B + 4 <= alloc_ceiling (a clause of the frame; ms_tp + ms_errno_off lies far below
   CEIL_MIN), and its world clause by U/Prog/T/GI.v frame_G_clause (frame_G_world: in_globals frame_G is
   h_world), and its RELRO clause from the frame's frame_RELRO clause (U/FrameAPI.v:46-48, :75-77: TContract.v's
   [RELRO_BASE, RELRO_BASE + RELRO_LEN) lies inside frame_RELRO's first block). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 SlotAgree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

(* TSim's harness_model_ok (TSim/TopOk.v), for the patched model: no no_twice premise. *)
Definition harness_model_ok_stmt : Prop :=
  forall (I : timg) (Bw : list byte) (A : nat -> Z) (D : list byte),
    timg_ok I -> length Bw = Z.to_nat W_LEN -> llvm_heap_ok A ->
    exists Bw', LLVMFuzzerTestOneInput_m I Bw A D = Some (Bw', 0).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

(* The world in the slot's memory: every memory with the allocator's invariant and intact read-only memory holds
   some world bytes Bw at W_BASE_UBSAN, present and writable. *)
Definition slot_world : Prop :=
  forall L A mem md, aa_MR API L A mem md -> ro_agree (ms_segs B) mem -> exists Bw, wmem rsegs mem Bw.

Definition slot_bridge : Prop :=
  LLVMFuzzerTestOneInput_walk_contract B API ->
  harness_model_ok_stmt ->
  slot_world ->
  LLVMFuzzerTestOneInput_contract B API.

Definition slot_bridge_cg : Prop :=
  LLVMFuzzerTestOneInput_walk_contract_cf B API ->
  harness_model_ok_stmt ->
  slot_world ->
  llvm_limlaw B API ->
  LLVMFuzzerTestOneInput_contract_cg B API.

End K.
