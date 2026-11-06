(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the harness entry contract on the UBSan image, the cut between the driver /
   start-up frame (lib/U/FrameAPI.v, lib/U/FrameProof.v, ported with the kit) and this program's walk. The same text
   as libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_c.v at this image's values, measured from
   fuzz_decode.ubsan (sha256 cfe3a2ee2a54): entry 0x12cfc, frame 0x1f0 bytes (`addi sp, sp, -0x1f0`), malloc 0x15028
   (default_malloc, the one `jal` of fuzz_alloc), free 0x14ee8, the stack guard 0x4ef30 and its GOT slot 0x1d948,
   the file bytes of PT_GNU_RELRO, [0x1d878, +0xe8), less that slot (frame_RELRO of lib/U/FrameAPI.v). The unit links
   no calloc. The deepest callee is the allocator (ALLOC_STACK: measured depth 336 bytes for malloc, 144 for free,
   recursion in the allocator included); every other callee of the harness needs a few hundred bytes of stack at most
   (diginet_decoder_next 144, spec_msg_step 48, check_events_fields 48 + abort 224, check_refusal 16 + body_check 144),
   so LLVM_K is the frame plus ALLOC_STACK. The 34 UBSan guards of the function (unimp at 0x13460) need no premise
   here: data is the driver's block when size > 0, buf the malloc block, DESK a constant. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12cfc.
Definition LLVM_FRAME : Z := 496.
Definition LLVM_K : Z := LLVM_FRAME + ALLOC_STACK.
Definition LLVM_MALLOC : Z := 0x15028.
Definition LLVM_FREE : Z := 0x14ee8.
Definition LLVM_GUARD_GOT : Z := 0x1d948.
Definition LLVM_GUARD : Z := 0x4ef30.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := [(0x1d878, 208); (0x1d950, 16)].
Definition llvm_GI : nat -> (word -> option byte) -> Prop := fun _ _ => True.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition llvm_binds : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = LLVM_MALLOC /\ ms_free B = LLVM_FREE /\
  ms_got_guard B = LLVM_GUARD_GOT /\ ms_guard B = LLVM_GUARD /\ AllocExtra B MR.

Definition llvm_room (b : sbound) : Prop := sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX.

Definition llvm_ls_laws : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room b) /\
  (forall n b, lib_delta n b = b).

Definition LLVMFuzzerTestOneInput_contract : Prop :=
  llvm_binds -> llvm_ls_laws ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_g B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

Definition LLVMFuzzerTestOneInput_sr_contract : Prop :=
  llvm_binds ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b,
    lib_pre B API stk empty L A regs mem md ra p n ->
    n = Z.of_nat (length pl) -> blk_data B mem p pl ->
    sink_none B mem md -> spZ regs <= 2 ^ 47 ->
    res_ok_slots A b ->
    llvm_room b ->
    ro_agree rsegs mem -> G_img_c B llvm_RELRO mem ->
    llvm_GI j mem ->
    frm_zero fp_csr ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' /\
         sink_none B mem' md' /\
         res_ok_slots A' b /\
         (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
         ro_agree rsegs mem' /\
         llvm_GI (S j) mem').

End K.
