(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of check_clamp (fuzz_uci.c) on the UBSan
   image, at 0x1305c (frame 48, as the plain image). The UBSan twin of lib/Prog/check_clamp_c.v: same models, same
   premises, and three premises more for UBSan traps (below): its own alignment check of in, and the two checks of
   rp_hot_clamp on the frame base it passes (finding, owner-approved: without them sp = 0x7fff0001
   traps at 0x13184 and sp = 48, lo = 0 traps at 0x1317c). The post says the call returns to ra, which is the
   statement that none of the five aborts (jal abort at 0x13174) and none of the traps runs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_CLAMP : Z := 0x1305c.
Definition CHECK_CLAMP_FRAME : Z := 48.

Definition check_clamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : rp_hot) (mm lo : Z),
    (* UBSan only: 0x130b0 `andi a0, s0, 3` / 0x130b4 `bnez` trap (unimp at 0x13178) on a misaligned in, the
       alignment check of in->adapt_min_ms (fuzz_uci.c:139). *)
    bv_unsigned a0 mod 4 = 0 ->
    (* UBSan only: the call rp_hot_clamp(&p) at 0x130ac passes a0 = sp - CHECK_CLAMP_FRAME, and rp_hot_clamp's
       0x13180 `andi` / 0x13184 `bnez` trap (unimp at 0x1323c) on a misaligned p: the frame base must be 4-aligned. *)
    bv_unsigned sp mod 4 = 0 ->
    (* UBSan only: through the same call, rp_hot_clamp's 0x1317c `beqz a0` traps (unimp at 0x1323c) on p == NULL:
       the frame base sp - CHECK_CLAMP_FRAME must not be 0. *)
    CHECK_CLAMP_FRAME < bv_unsigned sp ->
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
