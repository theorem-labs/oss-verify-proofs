(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of check_clamp (fuzz_uci.c), the plain
   image's 0x12f88. It copies *in onto its own 48-byte frame, calls rp_hot_clamp on the copy, inlines fuzz_uci.c's
   hold five times and aborts, and calls nothing that allocates, so it is stated in the evt / register style of
   libreac/fuzz_decode's released lib/Prog/check_braid_c.v (stack premises included). The post says the call returns
   to ra, which is the statement that none of the five aborts runs: by lib/Spec/UciModel.v's clamp_prefill,
   clamp_adapt_min, clamp_adapt_max, clamp_margin (which needs 0 <= margin_max) and clamp_servo. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_CLAMP : Z := 0x12f88.
Definition CHECK_CLAMP_FRAME : Z := 48.

Definition check_clamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : rp_hot) (mm lo : Z),
    hot_int p ->
    0 <= mm <= INT_MAX ->
    bv_unsigned a1 = mm ->
    ro_cells rsegs m (bv_unsigned a0) (hot_cells p) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_CLAMP_FRAME <= bv_unsigned sp ->
    bv_unsigned sp <= 2 ^ 63 ->
    bv_unsigned a0 + RP_HOT_SIZE <= bv_unsigned sp - CHECK_CLAMP_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CLAMP_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         ro_cells rsegs m' (bv_unsigned a0) (hot_cells p))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CLAMP) fc None m (seg_rom rsegs)).
