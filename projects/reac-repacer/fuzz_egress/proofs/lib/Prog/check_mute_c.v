(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths changed; 13 of its 44 lines of code are new or changed and 21 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract Img0.
Import ListNotations.
Local Open Scope Z_scope.

(* check_mute(f, n) (fuzz_egress.c:63-87): c = fuzz_dup(f, n), that is malloc(n ? n : 1), abort if NULL, and
   memcpy(c, f, n) unless n == 0; rp_mute(c, n); keep = (n > 18 && w_is_audio(f)) ? 18 : n; abort unless
   memcmp(c, f, keep) == 0 and c[i] == 0 for keep <= i < n; free(c) (a tail call).
   Its caller LLVMFuzzerTestOneInput passes f = fuzz_dup(data + ..., n), a block of its own, and n <= 1600
   (W_RECV_MAX); n may be 0. The contract: from every such call, check_mute returns to its caller (it does not
   abort), with the allocator's state as it was. The frame is 48 bytes; its deepest callee is the allocator
   (malloc, and free from the caller's sp). *)
Definition CHECK_MUTE : Z := 0x12eec.
Definition CHECK_MUTE_FRAME : Z := 48.
Definition CHECK_MUTE_STACK : Z := CHECK_MUTE_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* [a, a + n) lies in one block the caller owns. *)
Definition in_block (L : layout) (A : astate) (a n : Z) : Prop :=
  exists q k, In (q, k) (blocks L A) /\ q <= a /\ a + n <= q + k.

Definition check_mute_contract : Prop :=
  forall L A regs mem md (f n : Z) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CHECK_MUTE_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 n ->
    0 <= n <= 1600 ->
    in_block L A f n ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + Z.max n 1 <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_MUTE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CHECK_MUTE_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
