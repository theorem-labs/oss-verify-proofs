(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_refusal (fuzz/fuzz_decode.c:265-276) in fuzz_decode.plain.
   Address 0x13a90, size 128 bytes. Stack frame: 16 bytes (ra, s0). It inlines spec_system_at
   (fuzz/spec.h:264-270: the loop at 0x13abc-0x13adc tests b[i] = F0, b[i + 1] = 13, b[i + 3] = 70
   for i + 3 < len), calls diginet_body_check (0x13cec, diginet_body_check_contract) at 0x13ae4 with
   its own two arguments, and calls nothing else but the `jal abort` at 0x13b0c.
   Arguments: a0 is the address body of the bytes bb, a1 their length. The caller is
   LLVMFuzzerTestOneInput (0x13680); it gives the body it decoded and its length.
   Preconditions:
   - body is not 0;
   - the bytes bb at body are readable (bytes_at), and there are fewer than 2^63 of them: the found
     branch (0x13afc: slti a2, a2, 0; addi a2, a2, -1; andi s0, a2, -10) is the signed test
     spec_system_at (b, len) >= 0 of fuzz_decode.c:267 on the long index i, which takes a hit at
     i >= 2^63 for no hit (the caller has len < 2^26);
   - the stack from lo to sp is writable (stk), and lo + 160 <= sp (16 bytes of its own frame and
     the 144 of diginet_body_check's);
   - the bytes at body are not in the 160 bytes below sp;
   - mem_inv holds.
   No premise names DgnDecHarness.check_refusal_ok: the inlined loop is DgnSpec.system_at bb, and
   diginet_body_check returns DgnLib.body_check bb, which is -10 exactly when system_at bb and 0
   otherwise (DgnLib.body_check_spec), so the abort is unreachable for every such body.
   Result: the function returns to ra. It writes only the 160 bytes below sp. It keeps ra, sp, gp,
   tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_REFUSAL : Z := 0x13a90.
Definition CHECK_REFUSAL_FRAME : Z := 16.
(* its own frame and diginet_body_check's 144 bytes *)
Definition CHECK_REFUSAL_STACK : Z := 160.

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 ->
    bytes_at rsegs m body bb -> Z.of_nat (length bb) < 2^63 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_REFUSAL_STACK <= bv_unsigned sp ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - CHECK_REFUSAL_STACK \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_REFUSAL_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL) fc None m (seg_rom rsegs)).
