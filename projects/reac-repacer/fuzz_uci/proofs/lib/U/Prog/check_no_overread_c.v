(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of check_no_overread (fuzz_uci.c) on the
   UBSan image, at 0x12d54 (frame 48, as the plain image). The UBSan twin of lib/Prog/check_no_overread_c.v, the
   same text at this image's values. Its UBSan checks (0x12dc8 `bltu` on a + n, 0x12ddc `bltu` on b + n, both to
   the unimp at 0x12e44) need no premise: a and b are blocks the allocator returned, below alloc_ceiling. The post
   says the call returns to ra: neither abort (jal abort at 0x12e40) nor a trap runs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import rp_uci_int_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_NO_OVERREAD : Z := 0x12d54.
Definition CNO_FRAME : Z := 48.
Definition CNO_STACK : Z := CNO_FRAME + ALLOC_STACK.

(* a reply of n bytes is at most the 255 the harness can hand over *)
Definition REPLY_MAX : Z := 255.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* [a, a + n) lies inside one live block *)
Definition in_block (L : layout) (A : astate) (a n : Z) : Prop :=
  exists q k, In (q, k) (blocks L A) /\ q <= a /\ a + n <= q + k.

(* room for the two n+1 byte copies check_no_overread holds at once *)
Definition cno_room (b : sbound) (n : Z) : Prop :=
  sb_live b + 2 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + 2 * (n + 1) <= 2 ^ 40.

Definition check_no_overread_contract : Prop :=
  forall L A regs mem md (r n cur : Z) (bs : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CNO_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 r -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 cur ->
    INT_MIN <= cur <= INT_MAX ->
    0 <= n <= REPLY_MAX ->
    Z.of_nat (length bs) = n ->
    blk_data B mem r bs ->
    (0 < n -> in_block L A r n) ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    cno_room b n ->
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
