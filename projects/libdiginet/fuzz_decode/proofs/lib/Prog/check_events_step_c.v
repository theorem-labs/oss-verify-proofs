(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_events_step (fuzz/fuzz_decode.c:152-185) in fuzz_decode.plain.
   Address 0x137d0, size 160 bytes. Stack frame: 16 bytes (ra at sp - 8). Its only call is the
   `jal abort` at 0x1386c.
   Arguments: a0 is the address b of the body, a1 the address o of the harness's struct owed ow, a2
   the int rd (sign-extended to 64 bits), a3 the address e of the struct diginet_event ev. The caller
   is LLVMFuzzerTestOneInput (0x131ac); o and e are in its frame, rd is diginet_decoder_next's result
   and the event is the one it filled from the body at b.
   Preconditions:
   - DgnDecHarness.check_events_step_ok ow rd ev holds;
   - the code of ow's message is a C int, in [-2^31, 2^31);
   - the status of ow's message is a byte, in [0, 256), and when it is F0 its payload offset is not
     0 (as check_cursor_message_c.v: fuzz_decode.c:173 compares ev->msg.sysex with b + sysex_at,
     and event_cells stores NULL for offset 0; the harness's running status keeps that offset at
     least 1, as check_cursor_message_c.v says);
   - the 120 bytes at o are owed_cells p1 p2 ow and the 80 bytes at e are event_cells b mpad ev
     (ro_cells);
   - the stack from lo to sp is writable (stk), lo + 16 <= sp, and neither struct is in the 16 bytes
     below sp;
   - mem_inv holds.
   Result: the function returns to ra, which is the statement that none of the tests of
   fuzz_decode.c:161-184 branches to the abort. It writes only the 16 bytes below sp. It keeps ra,
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

Definition CHECK_EVENTS_STEP : Z := 0x137d0.
Definition CHECK_EVENTS_STEP_FRAME : Z := 16.

Definition check_events_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b o e rd lo : Z) (ow : owed) (ev : dgn_event) (p1 p2 mpad : list byte),
    check_events_step_ok ow rd ev = true ->
    -2^31 <= sm_code (ow_m ow) < 2^31 ->
    0 <= sm_status (ow_m ow) < 256 ->
    (sm_status (ow_m ow) = 240 -> sm_sysex_at (ow_m ow) <> 0) ->
    ro_cells rsegs m o (owed_cells p1 p2 ow) ->
    ro_cells rsegs m e (event_cells b mpad ev) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_EVENTS_STEP_FRAME <= bv_unsigned sp ->
    o + OW_SIZE <= bv_unsigned sp - CHECK_EVENTS_STEP_FRAME \/ bv_unsigned sp <= o ->
    e + DE_SIZE <= bv_unsigned sp - CHECK_EVENTS_STEP_FRAME \/ bv_unsigned sp <= e ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_EVENTS_STEP_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 o) (Z_to_bv 64 rd) (Z_to_bv 64 e)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_EVENTS_STEP) fc None m (seg_rom rsegs)).
