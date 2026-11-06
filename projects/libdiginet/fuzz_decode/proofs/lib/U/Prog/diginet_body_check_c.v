(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/check_refusal_c.v, with its numbers changed; 10 of its 28 lines of code are new or changed and 11 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/U/Prog into libdiginet/fuzz_decode (module path and addresses only: entry 0x14028 -> 0x13e04, every other pc -0x224, the two call targets and the caller of this image) *)
(* Contract of diginet_body_check in fuzz_decode.ubsan, relocated from fuzz_frame.ubsan's
   lib/U/Prog/diginet_body_check_c.v (frozen text; module path and addresses changed, nothing
   else). The function lies 0x224 lower here, so every pc of the frozen text is moved by
   -0x224 and checked against this image's bytes; its code differs from fuzz_frame's only in
   its two call offsets, which point at the relocated callees.
   Source: src/diginet_codec.c:47-64 at 835f336c. It calls diginet_cursor_init (0x13bbc, the
   `jal` at 0x13e40) one time and diginet_msg_next (0x13bec, the `jal` at 0x13e64) in a loop;
   both use no stack. Its walk takes their contracts (U/Prog/diginet_cursor_init_c.v,
   diginet_msg_next_c.v) as hypotheses.
   Address 0x13e04, size 328 bytes. Stack frame: 144 bytes (addi sp, sp, -0x90 at 0x13e04; the
   cursor at sp - 104 = sp' + 0x28, the message at sp - 144 = sp').
   Arguments: a0 is the address body, a1 the length of the bytes bb at body. The caller is
   check_refusal (0x13b88); it gives the harness's body.
   Preconditions:
   - body is not 0;
   - the bytes bb at body are readable (bytes_at);
   - sp is 8-aligned; the stack from lo to sp is writable (stk), 0 < lo and lo + 144 <= sp (so
     the message struct at the bottom of the frame, sp - 144, is not at address 0);
   - the bytes at body are not in the 144 bytes below sp;
   - mem_inv holds.
   Result: a0 is body_check bb: -10 (REFUSED) when the cursor finds a sysex F0 13 xx 70 .. F7
   or the prefix scan finds F0 13 xx 70, else 0. By DgnLib.body_check_spec this is -10
   exactly when system_at bb.
   The function writes only the 144 bytes below sp. It keeps ra, sp, gp, tp, s0..s11, the
   floating-point registers and fcsr, and the stack from lo to sp stays writable.
   UBSan checks: seven branches to the trap at 0x13f48 (unimp):
   - 0x13e88: m.sysex is 0 when the loop reads m.sysex[0] (r = 1, status F0, sysex_len >= 3);
     0x13e94: m.sysex + 2 wraps past 2^64. m.sysex is body + start + 1 there, with
     start + 1 + sysex_len < length bb (DgnLib.msg_step_sysex), so it is not 0 and does
     not wrap;
   - 0x13ed0, 0x13edc, 0x13ee0: body + i wraps past 2^64, or body is 0, in the prefix scan
     (only when length bb >= 4); 0x13ef0: body + i + 1 wraps; 0x13efc: body + i + 3 wraps.
     The scan reads only i + 3 < length bb, so with body <> 0 and body + length bb <= 2^64
     no branch is taken.
   The callees' own checks need the cursor and the message 8-aligned: they are at sp - 104
   and sp - 144, so the premise sp mod 8 = 0 gives it.
   Difference from the plain statement: the premise sp mod 8 = 0.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_BODY_CHECK : Z := 0x13e04.

Definition diginet_body_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 ->
    bytes_at rsegs m body bb ->
    bv_unsigned sp mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> 0 < lo -> lo + 144 <= bv_unsigned sp ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_BODY_CHECK) fc None m (seg_rom rsegs)).
