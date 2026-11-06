(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_wire: the cut-free (SRcf) contract of check_copy on the UBSan image, for the agree
   chain, as libreac/fuzz_decode's released lib/U/Prog/check_round_trip_ccf.v (25e3d17bdb5) is to its
   check_round_trip_c.v: the premises and the post of lib/U/Prog/check_copy_c.v, with SR replaced by SRcf and the room
   of fuzz_dup's one malloc taken at the agree bounds (at most CAP_AG slots, at least 128, bytes within 2^29). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract KindBGlue Img0 SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import rp_copy_untag_c FuzzDup check_copy_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* room for fuzz_dup's malloc(n ? n : 1), at the agree bounds *)
Definition cc_room_cf (b : sbound) (n : Z) : Prop :=
  (sb_live b + 1 <= sb_cap b <= CAP_AG /\ 128 <= sb_cap b) /\ 0 <= sb_bytes b /\
  sb_bytes b + fuzz_dup_size n <= 2 ^ 29.

Definition check_copy_contract_cf : Prop :=
  forall L A regs mem md (c f n kc : Z) (bs : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CC_STACK L A regs mem md ->
    st_init_done A = true ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 f -> getr regs 12 = Z_to_bv 64 n ->
    n <= 1600 -> Z.of_nat (length bs) = n ->
    In (c, kc) (blocks L A) -> n <= kc ->
    (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) ->
    Mem.bytes_at segs mem c bs -> Mem.bytes_at segs mem f bs ->
    ro_agree segs mem ->
    frm_zero fp_csr ->
    res_ok_slots A b -> cc_room_cf b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_COPY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_x B API CC_STACK L A regs mem md (fun a => a = c) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 (copy_untag_result n bs) /\
         Mem.bytes_at segs mem' c (cu_bytes n bs) /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun a => a = c) /\
         guard_kept B mem mem' /\
         ro_agree segs mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
