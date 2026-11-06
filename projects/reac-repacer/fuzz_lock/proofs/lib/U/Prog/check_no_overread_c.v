(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths, addresses and numbers changed; 10 of its 49 lines of code are new or changed and 13 lines of the source are left out. *)
(* Contract of fuzz_lock's harness function check_no_overread (fuzz_lock.c:120-141) in fuzz_lock.ubsan, 0x12d2c,
   in the form of libreac/fuzz_decode's lib/Prog/check_round_trip_c.v. The statement of
   lib/Prog/check_no_overread_c.v at the UBSan address, with the same argument facts. The UBSan checks of
   check_no_overread (trap [unimp] at 0x12e30, reached from 0x12da8 [bltu ~a, n] and 0x12dbc [bltu ~b, n], the
   pointer-overflow checks of a + n and b + n) need no premise: a and b are malloc's blocks below alloc_ceiling.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_NO_OVERREAD : Z := 0x12d2c.
(* addi sp, sp, -0x40 at 0x12d2c; the deepest callees are malloc and free (ALLOC_STACK); rp_lock_lookup takes
   RP_FRAME = 160 and memcpy none. *)
Definition CNO_FRAME : Z := 64.
Definition CNO_STACK : Z := CNO_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition in_block (L : layout) (A : astate) (a n : Z) : Prop :=
  exists q k, In (q, k) (blocks L A) /\ q <= a /\ a + n <= q + k.

(* check_no_overread(t, n, port, rate): t holds the n bytes T inside a block of the caller (the fuzzer's input),
   port the string P and its NUL in the caller's char port[16] above the stack pointer, 8-aligned. *)
Definition check_no_overread_contract : Prop :=
  forall L A regs mem md (t n pa rate : Z) (T P SL : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CNO_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 n ->
    getr regs 12 = Z_to_bv 64 pa -> getr regs 13 = Z_to_bv 64 rate ->
    0 <= n < 2 ^ 26 -> Z.of_nat (length T) = n ->
    0 < t < 2 ^ 63 -> in_block L A t n -> blk_data B mem t T ->
    spZ regs <= pa -> pa mod 8 = 0 -> pa + 16 <= 2 ^ 63 ->
    length (P ++ Z_to_bv 8 0 :: SL) = 16%nat -> ~ In (Z_to_bv 8 0) P ->
    blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL) ->
    0 <= rate < 2 ^ 64 ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    sb_live b + 2 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + 2 * (n + 1) <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CNO_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
