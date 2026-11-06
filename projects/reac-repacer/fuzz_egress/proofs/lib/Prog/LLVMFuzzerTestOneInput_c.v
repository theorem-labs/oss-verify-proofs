(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* The harness entry contract of reac-repacer/fuzz_egress (fuzz_egress.c:143-165), the cut between the driver /
   start-up frame (lib/FrameAPI.v, lib/FrameProof.v) and this program's walk. The plain image's values:
   - LLVM_ENTRY 0x12c60: LLVMFuzzerTestOneInput in the unstripped image's .symtab; FrameAPI.ENTRY.
   - LLVM_FRAME 192: its prologue `addi sp, sp, -0xc0` at 0x12c60.
   - LLVM_K: the deepest callee is check_inject, CHECK_INJECT_STACK = its 64-byte frame + ALLOC_STACK (malloc / free);
     check_restamp and check_mute need 48 + ALLOC_STACK, malloc and free ALLOC_STACK, check_gate 80 bytes, memset and
     memcpy no stack.
   - LLVM_MALLOC 0x14010, LLVM_FREE 0x13ed0: malloc and free in .symtab; the values FrameAPI.frame_plain binds.
   - LLVM_GUARD 0x4def0: __stack_chk_guard in .symtab; LLVM_GUARD_GOT 0x1c900: its .got slot (the 8 bytes at 0x1c900
     hold 0x4def0); the values FrameAPI.frame_plain binds.
   - llvm_RELRO: FrameAPI.frame_RELRO, the words of .init_array, .fini_array, .data.rel.ro and .got (PT_GNU_RELRO from
     0x1c860, .got ending at 0x1c918) without the guard's slot.
   fuzz_egress links no calloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import check_inject_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12c60.
Definition LLVM_FRAME : Z := 192.
Definition LLVM_K : Z := LLVM_FRAME + CHECK_INJECT_STACK.
Definition LLVM_MALLOC : Z := 0x14010.
Definition LLVM_FREE : Z := 0x13ed0.
Definition LLVM_GUARD_GOT : Z := 0x1c900.
Definition LLVM_GUARD : Z := 0x4def0.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := [(0x1c860, 160); (0x1c908, 16)].
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

Definition llvm_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

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
