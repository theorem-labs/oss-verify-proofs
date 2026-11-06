(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths and module names changed; 17 of its 48 lines of code are new or changed and 21 lines of the source are left out. *)
(* Contract of fuzz_lock's harness function check_lookup (fuzz_lock.c:143-179) in fuzz_lock.plain, 0x12da0,
   in the form of libreac/fuzz_decode's lib/Prog/check_round_trip_c.v. The facts on t, n, port and rate are those of
   check_no_overread_contract (check_no_overread_c.v), so LLVMFuzzerTestOneInput calls both with one set of facts.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import check_no_overread_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_LOOKUP : Z := 0x12da0.
(* addi sp, sp, -0xb0 at 0x12da0; the deepest callees are malloc (ALLOC_STACK) and rp_lock_lookup (RP_FRAME = 176
   <= ALLOC_STACK, it calls no allocator); free is a tail call, taken after the frame is released. *)
Definition CL_FRAME : Z := 176.
Definition CL_STACK : Z := CL_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* check_lookup(t, n, port, k, rate): t holds the n bytes T inside a block of the caller (the fuzzer's input), port
   the string P of k bytes and its NUL in the caller's char port[16] above the stack pointer, 8-aligned. *)
Definition check_lookup_contract : Prop :=
  forall L A regs mem md (t n pa k rate : Z) (T P SL : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CL_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 n ->
    getr regs 12 = Z_to_bv 64 pa -> getr regs 13 = Z_to_bv 64 k -> getr regs 14 = Z_to_bv 64 rate ->
    0 <= n < 2 ^ 26 -> Z.of_nat (length T) = n ->
    0 < t < 2 ^ 63 -> in_block L A t n -> blk_data B mem t T ->
    spZ regs <= pa -> pa mod 8 = 0 -> pa + 16 <= 2 ^ 63 ->
    length (P ++ Z_to_bv 8 0 :: SL) = 16%nat -> ~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) = k ->
    blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL) ->
    0 <= rate < 2 ^ 64 ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + (n + 1) <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_LOOKUP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CL_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
