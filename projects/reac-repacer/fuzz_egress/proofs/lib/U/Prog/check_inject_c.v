(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths and module names changed; 16 of its 46 lines of code are new or changed and 22 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import check_mute_c.
Import ListNotations.
Local Open Scope Z_scope.

(* check_inject(f, n, slot, v) (fuzz_egress.c:109-141): c = fuzz_dup(f, n) and e = fuzz_dup(f, n), that is twice
   malloc(n ? n : 1), abort if NULL, and memcpy(.., f, n) unless n == 0; nch = want_width(f, n, slot); if nch > 0,
   for each time-sample s < 12, w_put(e, s, slot, nch, v[s]) (fuzz.h: the slot's 6-byte pair group at
   e + 50 + 3 * (s * nch + (slot & ~1)) un-swapped into a stack be[6], v[s]'s low three bytes put big-endian at
   be[at .. at + 2], at = 3 for an odd slot, swapped back); got = rp_slot_write(c, n, slot, v); abort unless
   got == (nch > 0) and bcmp(c, e, n) == 0; free(c); free(e) (a tail call).
   Its caller LLVMFuzzerTestOneInput passes f = fuzz_dup(data + ..., n), a block of its own, n <= 1600 (W_RECV_MAX;
   n may be 0), slot = head[0] - 2 in -2 .. 253 (an int, sign-extended in a2), and v (a3), its own int32 v[12] on its
   stack: at or above check_inject's sp (so outside every heap block and every byte check_inject and its callees
   write), 4-aligned, its 48 bytes present. The contract: from every such call, check_inject returns to its caller
   (it does not abort), with the allocator's state as it was. Two blocks of max(n, 1) bytes are live at once. The
   UBSan image's checks in the w_put loop (v + 4 * s overflows or is not 4-aligned, s * nch or s * nch + (slot & ~1)
   overflows an int, e + w_group or a byte of the group overflows) each branch to an inline `unimp` at 0x132f4; the
   premises rule them out. The frame is 112 bytes; its deepest callee is the allocator (malloc, and free from the
   caller's sp); rp_slot_write needs RP_SLOT_WRITE_STACK = 112 bytes below its sp, less. *)
Definition CHECK_INJECT : Z := 0x130b0.
Definition CHECK_INJECT_FRAME : Z := 112.
Definition CHECK_INJECT_STACK : Z := CHECK_INJECT_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_inject_contract : Prop :=
  forall L A regs mem md (f n slot v : Z) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CHECK_INJECT_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 n ->
    getr regs 12 = Z_to_bv 64 slot -> getr regs 13 = Z_to_bv 64 v ->
    0 <= n <= 1600 -> -2 <= slot <= 253 ->
    in_block L A f n ->
    spZ regs <= v -> v + 48 <= 2 ^ 64 -> v mod 4 = 0 ->
    (forall i, 0 <= i < 48 -> present mem (v + i)) ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    sb_live b + 2 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + 2 * Z.max n 1 <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_INJECT) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CHECK_INJECT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
