(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths changed; 14 of its 44 lines of code are new or changed and 22 lines of the source are left out. *)
(* check_restamp(f, n, ctr) (fuzz_egress.c:39-61): if n < 18 it returns; else c = fuzz_dup(f, n) (malloc(n),
   abort on NULL, memcpy(c, f, n)), rp_restamp(c, ctr), abort unless c[14], c[15] are ctr's low two bytes, abort unless
   bcmp(c, f, 14) == 0 and bcmp(c + 16, f + 16, n - 16) == 0, then free(c) as a tail call.
   a0 = f (a caller-owned malloc block of n bytes), a1 = n (<= 1600 at its one call site), a2 = ctr.
   It keeps a 48-byte frame; malloc needs ALLOC_STACK below it, the tail call to free ALLOC_STACK below the entry sp.
   The contract says it returns (no abort), with the heap as it was and every caller block unchanged. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_RESTAMP : Z := 0x12e58.
Definition CR_FRAME : Z := 48.
Definition CHECK_RESTAMP_STACK : Z := CR_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition in_block (L : layout) (A : astate) (a n : Z) : Prop :=
  exists q k, In (q, k) (blocks L A) /\ q <= a /\ a + n <= q + k.

Definition check_restamp_contract : Prop :=
  forall L A regs mem md (f n ctr : Z) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CHECK_RESTAMP_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 ctr ->
    0 <= n <= 1600 ->
    in_block L A f n ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    room_slots b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_RESTAMP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CHECK_RESTAMP_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         (st_init_done A = true -> st_init_done A' = true)).

End K.
