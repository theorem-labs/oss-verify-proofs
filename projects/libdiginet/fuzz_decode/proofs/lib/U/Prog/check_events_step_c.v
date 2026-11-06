(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_events_step (fuzz/fuzz_decode.c:152-185) in fuzz_decode.ubsan.
   The UBSan twin of lib/Prog/check_events_step_c.v: the same models and premises at this image's values, and the
   premises that keep its UBSan checks from trapping (below).
   Address 0x137a8, size 192 bytes. Stack frame: 16 bytes (ra at sp - 8), set up only on the way to the `jal abort`
   at 0x13860. It calls nothing else.
   Arguments: a0 is the address b of the body, a1 the address o of the harness's struct owed ow, a2 the int rd
   (sign-extended to 64 bits), a3 the address e of the struct diginet_event ev. The caller is
   LLVMFuzzerTestOneInput (0x131f8); o and e are in its frame, rd is diginet_decoder_next's result and the event is
   the one it filled from the body at b.
   Preconditions:
   - DgnDecHarness.check_events_step_ok ow rd ev holds;
   - the code of ow's message is a C int, in [-2^31, 2^31);
   - the status of ow's message is a byte, in [0, 256), and when it is F0 its payload offset is not 0 (as
     check_cursor_message_c.v: fuzz_decode.c:173 compares ev->msg.sysex with b + sysex_at, and event_cells stores
     NULL for offset 0);
   - the 120 bytes at o are owed_cells p1 p2 ow and the 80 bytes at e are event_cells b mpad ev (ro_cells);
   - the stack from lo to sp is writable (stk), lo + 16 <= sp, and neither struct is in the 16 bytes below sp;
   - mem_inv holds.
   UBSan checks (each branches to the unimp at 0x13864) and the premise that keeps each from trapping:
   - 0x137a8 `andi a4, a1, 7`, 0x137ac `bnez a4`: o not 8-aligned (the alignment check of o->m): o mod 8 = 0;
   - 0x137c0 `andi a2, a3, 7`, 0x137c4 `bnez a2` (reached when rd = 1): e not 8-aligned: e mod 8 = 0;
   - for an F0 message, the pointer b + m->sysex_at (fuzz_decode.c:173): 0x13820 `bltu a2, a0` (the sum wraps) and
     0x13824-0x13830 `snez` / `seqz` / `xor` / `beqz` (b is NULL exactly when the sum is not): 0 < b, 0 <= the
     offset and b + offset < 2^64.
   Result: the function returns to ra, which is the statement that none of the tests of fuzz_decode.c:161-184
   branches to the abort and no UBSan check traps. It writes only the 16 bytes below sp. It keeps ra, sp, gp, tp,
   s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_EVENTS_STEP : Z := 0x137a8.
Definition CHECK_EVENTS_STEP_FRAME : Z := 16.

Definition check_events_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b o e rd lo : Z) (ow : owed) (ev : dgn_event) (p1 p2 mpad : list byte),
    check_events_step_ok ow rd ev = true ->
    -2^31 <= sm_code (ow_m ow) < 2^31 ->
    0 <= sm_status (ow_m ow) < 256 ->
    (sm_status (ow_m ow) = 240 -> sm_sysex_at (ow_m ow) <> 0) ->
    (* UBSan: 0x137ac, 0x137c4 *)
    o mod 8 = 0 -> e mod 8 = 0 ->
    (* UBSan: 0x13820, 0x13830 *)
    (sm_status (ow_m ow) = 240 ->
       0 < b /\ 0 <= sm_sysex_at (ow_m ow) /\ b + sm_sysex_at (ow_m ow) < 2^64) ->
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
