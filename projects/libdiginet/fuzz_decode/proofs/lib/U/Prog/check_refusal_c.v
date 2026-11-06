(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_refusal (fuzz/fuzz_decode.c:265-276) in fuzz_decode.ubsan.
   The UBSan twin of lib/Prog/check_refusal_c.v: the same premises at this image's values, and one more for the
   UBSan checks of its callee (below).
   Address 0x13b08, size 180 bytes. Stack frame: 16 bytes (ra, s0). It inlines spec_system_at (fuzz/spec.h:264-270:
   the loop at 0x13b3c-0x13b80 tests b[i] = F0, b[i + 1] = 13, b[i + 3] = 70 for i + 3 < len), calls
   diginet_body_check (0x13e04, frame 144 bytes; its UBSan contract, fuzz_frame's relocated to this image) at 0x13b88
   with its own two arguments, and calls nothing else but the `jal abort` at 0x13bb4.
   Arguments: a0 is the address body of the bytes bb, a1 their length. The caller is LLVMFuzzerTestOneInput
   (0x1338c); it gives the body it decoded and its length.
   Preconditions:
   - body is not 0;
   - the bytes bb at body are readable (bytes_at), and there are fewer than 2^63 of them: the found branch
     (0x13ba0: slti a2, a2, 0; addi a2, a2, -1; andi s0, a2, -10) is the signed test spec_system_at (b, len) >= 0 of
     fuzz_decode.c:267 on the long index i, which takes a hit at i >= 2^63 for no hit (the caller has len < 2^26);
   - the stack from lo to sp is writable (stk), 0 < lo and lo + 160 <= sp (16 bytes of its own frame and the 144
     of diginet_body_check's), and sp is 16-aligned (the ABI's stack alignment);
   - the bytes at body are not in the 160 bytes below sp;
   - mem_inv holds.
   No premise names DgnDecHarness.check_refusal_ok: the inlined loop is DgnSpec.system_at bb, and diginet_body_check
   returns DgnLib.body_check bb, which is -10 exactly when system_at bb and 0 otherwise (DgnLib.body_check_spec), so
   the abort is unreachable for every body.
   UBSan checks of the inlined loop (each branches to the unimp at 0x13bb0), all unreachable from the premises
   above: 0x13b40 `bltu t2, a0` (body + i wraps), 0x13b44-0x13b4c `seqz` / `xor` / `beqz` (body is NULL exactly
   when body + i is not), 0x13b50 `beqz a0` (body is NULL), 0x13b60 `bgeu a2, a3` with a3 = ~body (body + i + 1
   wraps), 0x13b6c-0x13b70 `bltu a3, t3` with t3 = i + 3 (body + i + 3 wraps): body is not 0, and
   i + 3 < length bb with body + length bb <= 2^64 (bytes_at).
   UBSan checks of the callee: diginet_body_check (entry sp - 16) keeps its cursor at its sp + 0x28 and its message
   at its sp (sp - 160) and passes them to diginet_cursor_init (0x13bc0 `andi a3, a0, 7` / 0x13bc4 `bnez`, unimp at
   0x13be8) and diginet_msg_next (0x13bf8 / 0x13bfc on the cursor, 0x13c2c / 0x13c30 on the message, unimp at
   0x13dc8): both 8-aligned when sp mod 16 = 0. The message is not NULL because lo > 0: with lo = 0 and sp = 160
   it is at 0, diginet_msg_next returns -1 at its NULL test (0x13bf4 `beqz a1`, then 0x13dc0) without moving
   the cursor, and diginet_body_check's loop (0x13e6c `bnez a0` back to 0x13e5c) never ends. Its other checks
   (0x13e88, 0x13e94 and its prefix loop) are unreachable from body <> 0 and bytes_at, as the loop's above.
   Result: the function returns to ra. It writes only the 160 bytes below sp. It keeps ra, sp, gp, tp, s0..s11, the
   floating-point registers and fcsr, and the stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_REFUSAL : Z := 0x13b08.
Definition CHECK_REFUSAL_FRAME : Z := 16.
(* its own frame and diginet_body_check's 144 bytes *)
Definition CHECK_REFUSAL_STACK : Z := 160.

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 ->
    bytes_at rsegs m body bb -> Z.of_nat (length bb) < 2^63 ->
    stk rsegs m lo (bv_unsigned sp) -> 0 < lo -> lo + CHECK_REFUSAL_STACK <= bv_unsigned sp ->
    (* UBSan: the callee's alignment checks of its cursor and message *)
    bv_unsigned sp mod 16 = 0 ->
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
