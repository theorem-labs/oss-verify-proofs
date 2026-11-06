(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, module names, addresses and numbers changed; 10 of its 70 lines of code are new or changed and 7 lines of the source are left out. *)
(* Contract of fuzz_frame's LLVMFuzzerTestOneInput (fuzz_frame.c:265-284) in fuzz_frame.ubsan, 0x12d48 (712 bytes),
   in the form of libreac/fuzz_decode's lib/U/Prog/LLVMFuzzerTestOneInput_c.v (bf7779f81ed7). The function returns
   0 on every path that returns (fuzz_frame.c:271 and 283; 0x12fdc: mv a0, zero, then ret at 0x12ff4), so the leaf of
   the driver's shape is decode's LL 0. An input of 2 ^ 26 bytes or more (FUZZ_INPUT_MAX, fuzz.h) returns at once
   (0x12d60: srli a1, a1, 0x1a; bnez). Its UBSan checks of pointer arithmetic trap at 0x1300c (unimp).
   Written by Theorem Labs.

   Image facts of fuzz_frame.ubsan, read with pyelftools from the .symtab and .got of its unstripped twin, whose
   text, RELRO, data and rodata bytes are the pinned image's (sha256 259858a8e23b; the two differ only in the ELF
   header's section-table fields and the build-id note):
     LLVM_ENTRY      0x12d48  symbol LLVMFuzzerTestOneInput (U/FrameAPI.v ENTRY)
     LLVM_FRAME      176      addi sp, sp, -0xb0 at 0x12d48; ra, s0, s1, s2 saved at sp + 0xa8 .. 0x90
     LLVM_MALLOC     0x14f2c  symbol malloc (weak; default_malloc), called at 0x12d74
     LLVM_FREE       0x14dec  symbol free, called at 0x12fd8
     LLVM_GUARD      0x4ee00  symbol __stack_chk_guard
     LLVM_GUARD_GOT  0x1d818  the slot of .got (0x1d798, 152 bytes) whose value is 0x4ee00
     llvm_RELRO      U/FrameAPI.v frame_RELRO, [0x1d778, 0x1d818) and [0x1d820, 0x1d830): the 0xb8 file bytes of
                     PT_GNU_RELRO at 0x1d778 (.init_array, .fini_array, .data.rel.ro, .got) less the guard slot
   They are the values U/FrameAPI.v frame_ubsan binds (ENTRY, ms_malloc, ms_free, ms_guard, ms_got_guard).

   Stack: LLVM_K is LLVM_FRAME plus the deepest stack of a function LLVMFuzzerTestOneInput calls:
     malloc, free          ALLOC_STACK (U/Reusable/YO0d.v, the stack of call_pre)
     memcpy, memset        none: U/Prog/memcpy_c.v and memset_c.v let them write only their destination
     diginet_frame_parse   LLVM_PARSE_STACK, 48: addi sp, sp, -0x30 at 0x13a18; its callees memcpy, rd32 (0x13c00)
                           and diginet_sum16 (0x13944) use no stack
     check_parse_refusal   U_CPR_STACK (U/Prog/CheckStackU.v)
     check_parse_fields    U_CPF_STACK (U/Prog/CheckStackU.v)
     check_round_trip      U_CRT_STACK (U/Prog/CheckStackU.v)
     check_announce        U_CA_STACK (U/Prog/CheckStackU.v) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import CheckStackU.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12d48.
Definition LLVM_FRAME : Z := 176.
Definition LLVM_PARSE_STACK : Z := 48.
Definition LLVM_K : Z :=
  LLVM_FRAME + Z.max ALLOC_STACK (Z.max LLVM_PARSE_STACK
    (Z.max U_CPR_STACK (Z.max U_CPF_STACK (Z.max U_CRT_STACK U_CA_STACK)))).
Definition LLVM_MALLOC : Z := 0x14f2c.
Definition LLVM_FREE : Z := 0x14dec.
Definition LLVM_GUARD_GOT : Z := 0x1d818.
Definition LLVM_GUARD : Z := 0x4ee00.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := frame_RELRO.
Definition llvm_GI : nat -> (word -> option byte) -> Prop := fun _ _ => True.

Lemma llvm_K_slot : LLVM_K <= SLOT_STACK.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

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
