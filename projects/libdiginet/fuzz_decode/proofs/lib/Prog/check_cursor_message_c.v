(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_cursor_message (fuzz/fuzz_decode.c:93-115) in fuzz_decode.plain.
   Address 0x1374c, size 132 bytes. Stack frame: 16 bytes (ra at sp - 8). Its only call is the
   `jal abort` at 0x137cc.
   Arguments: a0 is the address b of the body, a1 the address p of the harness's struct spec_msg sm,
   a2 the address q of the struct diginet_msg. The caller is LLVMFuzzerTestOneInput (0x12f38); p
   and q are in its frame, and the message is the one diginet_msg_next filled from the body at b.
   Preconditions:
   - DgnDecHarness.check_cursor_message_ok sm msg holds;
   - sm's status is a byte, in [0, 256), and when it is F0 its payload offset is not 0: the C test
     msg->sysex != b + m->sysex_at (fuzz_decode.c:113) is the offset test of msg_agrees only when
     the payload pointer is body + offset, and dmsg_cells stores NULL for offset 0 (DgnLayout.v
     sysex_ptr). In the harness's loop the running status is 0 or in [0x80, 0xF0) (it starts at 0,
     and status_out is 0, the status in, or a lead byte in [0x80, 0xF0)), so spec_msg_step gives
     status F0 only to a sysex, whose payload offset is at + 1 >= 1;
   - the 56 bytes at p are spec_msg_cells sm and the 40 bytes at q are dmsg_cells b pad msg
     (ro_cells);
   - the stack from lo to sp is writable (stk), lo + 16 <= sp, and neither struct is in the 16 bytes
     below sp;
   - mem_inv holds.
   Result: the function returns to ra, which is the statement that none of the tests of
   fuzz_decode.c:99-114 branches to the abort. It writes only the 16 bytes below sp. It keeps ra,
   sp, gp, tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_CURSOR_MESSAGE : Z := 0x1374c.
Definition CHECK_CURSOR_MESSAGE_FRAME : Z := 16.

Definition check_cursor_message_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b p q lo : Z) (sm : spec_msg) (msg : dgn_msg) (pad : list byte),
    check_cursor_message_ok sm msg = true ->
    0 <= sm_status sm < 256 ->
    (sm_status sm = 240 -> sm_sysex_at sm <> 0) ->
    ro_cells rsegs m p (spec_msg_cells sm) ->
    ro_cells rsegs m q (dmsg_cells b pad msg) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CURSOR_MESSAGE_FRAME <= bv_unsigned sp ->
    p + SM_SIZE <= bv_unsigned sp - CHECK_CURSOR_MESSAGE_FRAME \/ bv_unsigned sp <= p ->
    q + DM_SIZE <= bv_unsigned sp - CHECK_CURSOR_MESSAGE_FRAME \/ bv_unsigned sp <= q ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CURSOR_MESSAGE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 p) (Z_to_bv 64 q)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CURSOR_MESSAGE) fc None m (seg_rom rsegs)).
