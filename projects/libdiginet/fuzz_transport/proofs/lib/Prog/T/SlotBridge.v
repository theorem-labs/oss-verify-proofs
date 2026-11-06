(* The bridge from the walk of LLVMFuzzerTestOneInput and the simulation theorem to the slot contract, plain image:
   the statement only (its proof: Prog/T/SlotBridgeProof.v). *)
(* Its proof composes three things:
   - LLVMFuzzerTestOneInput_walk_contract (Prog/T/LLVMFuzzerTestOneInput_c.v): the binary meets the SR form of the
     slot from any world Bw in memory, given the model premise llvm_model_ok Bw pl;
   - harness_model_ok_stmt: TSim's top theorem (TSim/TopOk.v harness_model_ok) on the patched
     harness model: for every image table I with timg_ok, every world of the right length, every heap stream with
     llvm_heap_ok (TSim/LoopOk.v heap_ok, the same body) and every input D, the model returns Some (_, 0); no
     premise on the input and no section hypothesis; `exact TopOk.harness_model_ok` proves it;
   - slot_world: in every memory the slot is entered with, the world [W_BASE_PLAIN, W_BASE_PLAIN + W_LEN) is present
     and writable, so wmem holds of its bytes: an image fact (frame_G is .bss of the image's last writable PT_LOAD,
     which elf_snapshot zero-fills to its page-rounded memsz, so LPS wview is Some there for every memory).
   Then: given the slot's premises, take Bw from slot_world; timg_ok timg_plain holds by computation and
   length Bw = W_LEN by wm_len, so harness_model_ok_stmt gives llvm_model_ok Bw pl; the walk contract gives the SR
   form; its post gives lib_post_g as the donor's llvm_g_of_sr does (fuzz_decode Prog/LLVMFuzzerTestOneInput_g.v:41),
   with llvm_ls_laws for LIBK, lib_room and lib_delta. One clause the donor closed vacuously (its G was []) is not
   vacuous here: lib_post_g's writability of G across the call. It holds by the same image fact as slot_world (every
   world address stays writable in every memory), which the bridge's proof states as a lemma.
   llvm_binds (= receive_c.v h_binds) is a premise of both the walk contract and the slot contract, so the bridge
   passes it through; whoever applies the slot contract discharges it from FrameAPI.v frame_plain: the symbol
   values, AllocExtra, errno_addr B + 4 <= alloc_ceiling (a clause of the frame; ms_tp + ms_errno_off lies far below
   CEIL_MIN), and its world clause by Prog/T/GI.v frame_G_clause (frame_G_world: in_globals frame_G is
   h_world), and its RELRO clause from the frame's frame_RELRO clause (FrameAPI.v:46-48, :75-77: TContract.v's
   [RELRO_BASE, RELRO_BASE + RELRO_LEN) lies inside frame_RELRO's first block). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem LLVMFuzzerTestOneInput_c.
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
   some world bytes Bw at W_BASE_PLAIN, present and writable. *)
Definition slot_world : Prop :=
  forall L A mem md, aa_MR API L A mem md -> ro_agree (ms_segs B) mem -> exists Bw, wmem rsegs mem Bw.

Definition slot_bridge : Prop :=
  LLVMFuzzerTestOneInput_walk_contract B API ->
  harness_model_ok_stmt ->
  slot_world ->
  LLVMFuzzerTestOneInput_contract B API.

End K.
