(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_c.v (6874bc78b1f) at fuzz_wire's
   module paths and plain image values. *)
(* The harness entry contract of fuzz_wire plain c8763dfc4e81, the cut between the driver / start-up frame
   (lib/FrameAPI.v, lib/FrameProof.v, ported with the kit) and this program's walk. The text of fuzz_uci's contract (itself
   libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_c.v) at this image's values: entry 0x12d78, frame
   0x40 bytes, malloc 0x14484, free 0x14344, __stack_chk_guard 0x4e4e0 and its GOT slot 0x1cef0, the RELRO list of
   lib/FrameAPI.v. The deepest callee is check_copy (lib/Prog/check_copy_c.v, CC_STACK bytes below its sp), so
   LLVM_K = LLVM_FRAME + CC_STACK. The plain image has no symbol named `calloc` (musl's __libc_calloc is linked), and fuzz_wire always returns 0 (fuzz_wire.c:256-257, :281).
   rule 24: the released LLVMFuzzerTestOneInput proofs are other programs' entries; written new on these templates. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import check_copy_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12d78.
Definition LLVM_FRAME : Z := 64.
Definition LLVM_K : Z := LLVM_FRAME + CC_STACK.
Definition LLVM_MALLOC : Z := 0x14484.
Definition LLVM_FREE : Z := 0x14344.
Definition LLVM_GUARD_GOT : Z := 0x1cef0.
Definition LLVM_GUARD : Z := 0x4e4e0.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := [(0x1ce50, 160); (0x1cef8, 16)].
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
