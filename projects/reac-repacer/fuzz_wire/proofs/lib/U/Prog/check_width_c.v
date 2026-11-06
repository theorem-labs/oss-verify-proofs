(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_clamp_c.v, with its module paths changed; 12 of its 27 lines of code are new or changed and 18 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* static __attribute__((noinline)) void check_width(size_t n)    fuzz_wire.c:146-168
   {
           if (rp_frame_channels((long)n) != w_width((long)n))
                   abort();
           if (rp_frame_channels(-1 - (long)n) != -1)
                   abort();
   }
   with w_width the frame law's table walk of fuzz.h:55-63 (the even widths 2..40 at 52 + nch * 36 bytes, or two
   bytes more), inlined.
   fuzz_wire ubsan 6e91fe0b5555 at 0x1328c (116 bytes): a 16-byte frame (ra, s0), two calls of rp_frame_channels
   (0x13938), each with its own 16-byte frame below.
   The form is libreac/fuzz_decode's check_braid_c.v (25e3d17bdb5): the check RETURNS NORMALLY from every entry state
   LLVMFuzzerTestOneInput gives it (fuzz_wire.c:270), so its abort() is unreachable; the property it checks is no
   premise.
   Premises: n <= W_RECV_MAX = 1600 (LLVMFuzzerTestOneInput cuts n to it, fuzz_wire.c:261-262), mem_inv
   (rp_frame_channels' premise), the room of the frame and of the callee's frame on the stack. *)
Definition CHECK_WIDTH : Z := 0x1328c.
Definition CHECK_WIDTH_FRAME : Z := 16.
(* the frame plus rp_frame_channels' own 16-byte frame below it *)
Definition CHECK_WIDTH_STACK : Z := CHECK_WIDTH_FRAME + 16.

Definition check_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 <= 1600 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_WIDTH_STACK <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_WIDTH_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_WIDTH) fc None m (seg_rom rsegs)).
