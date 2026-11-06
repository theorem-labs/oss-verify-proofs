(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/check_refusal_c.v, with its module paths changed; 12 of its 28 lines of code are new or changed and 12 lines of the source are left out. *)
(* Contract of check_parse_refusal in fuzz_frame.ubsan, the twin of
   Prog/check_parse_refusal_c.v (fuzz_frame.plain).
   Source: fuzz/fuzz_frame.c:34-63 at 835f336c.
   Address 0x13010, size 76 bytes. Stack frame: 16 bytes (addi sp, sp, -0x10 at 0x1304c), only
   on its path to abort. The function calls only abort (0x14954), at 0x13054. U_CPR_STACK
   (U/Prog/CheckStackU.v) is 16.
   Arguments: a0 is r, the int code that diginet_frame_parse answered, sign-extended; a1 is the
   address w of a struct spec_frame (80 bytes). The caller is LLVMFuzzerTestOneInput; it gives
   r in a0 (the a0 of diginet_frame_parse) and its local spec_frame at its sp in a1.
   Preconditions:
   - a0 is fr_code b, the code of the frame bytes b. The diginet_frame_parse contract gives it;
   - w is 8-aligned;
   - the 4 bytes at w, w->code, are the int fr_code b (ro_cells). The inlined spec_read_frame
     of the caller (fuzz/spec.h:199-223) leaves that code there;
   - the 4 bytes at w are not in the 16 bytes below sp;
   - the stack from lo to sp is writable (stk), and lo + 16 <= sp;
   - mem_inv holds.
   Result: the function returns to ra. It does not call abort: each of its four tests
   (0x13020..0x13044) aborts only when w->code is one of -2, -3, -4, 0 and r is not that
   value, and here r and w->code are both fr_code b.
   The function writes only the 16 bytes below sp. It can change t0..t6 and a0..a7. It keeps
   ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr, and all other memory; the
   stack from lo to sp stays writable.
   UBSan checks: one branch to the trap at 0x13058 (unimp), at 0x13014: w & 7 is not 0 (the
   alignment of struct spec_frame), before it reads w->code. The premise w mod 8 = 0 keeps it
   from firing.
   Difference from the plain statement: the premise w mod 8 = 0, and the stack constant is
   U_CPR_STACK. The caller's spec_frame is at its sp, which is 16-aligned.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import CheckStackU.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_PARSE_REFUSAL : Z := 0x13010.

Definition check_parse_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w lo : Z) (b : list byte),
    w mod 8 = 0 ->
    ro_cells rsegs m w [C4 (Z_to_bv 64 (fr_code b))] ->
    w + 4 <= bv_unsigned sp - U_CPR_STACK \/ bv_unsigned sp <= w ->
    stk rsegs m lo (bv_unsigned sp) -> lo + U_CPR_STACK <= bv_unsigned sp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - U_CPR_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr_code b)) (Z_to_bv 64 w)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PARSE_REFUSAL) fc None m (seg_rom rsegs)).
