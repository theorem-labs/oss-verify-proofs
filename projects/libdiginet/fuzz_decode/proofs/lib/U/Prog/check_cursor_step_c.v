(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Contract of check_cursor_step (fuzz/fuzz_decode.c:41-91) in fuzz_decode.ubsan.
   The UBSan twin of lib/Prog/check_cursor_step_c.v: the same models and premises at this image's values, and the
   premises that keep its UBSan checks from trapping (below).
   Address 0x1368c, size 124 bytes. Stack frame: 16 bytes (ra at sp - 8), set up only on the way to the `jal abort`
   at 0x13700. It calls nothing else.
   Arguments: a0 is the address p of the harness's struct spec_msg sm, a1 the int r (sign-extended to 64 bits), a2
   the address c of the struct diginet_cursor. The caller is LLVMFuzzerTestOneInput (0x12e58); p and c are in its
   frame, r is diginet_msg_next's result.
   Preconditions:
   - DgnDecHarness.check_cursor_step_ok sm r cur holds;
   - sm's code and r are C ints, in [-2^31, 2^31);
   - the 56 bytes at p are spec_msg_cells sm and the 25 bytes at c are cursor_cells of cur over body, with
     0 <= dc_pos cur (ro_cells);
   - the stack from lo to sp is writable (stk), lo + 16 <= sp, and neither struct is in the 16 bytes below sp;
   - mem_inv holds.
   UBSan checks (each branches to the unimp at 0x13704) and the premise that keeps each from trapping:
   - 0x1368c `andi a3, a0, 7`, 0x13690 `bnez a3`: p not 8-aligned (the alignment check of m): p mod 8 = 0;
   - 0x136d4 `andi a1, a2, 7`, 0x136d8 `bnez a1`: c not 8-aligned (the alignment check of c): c mod 8 = 0.
   Result: the function returns to ra, which is the statement that none of the seven tests of
   fuzz_decode.c:47-90 branches to the abort and no UBSan check traps. It writes only the 16 bytes below sp. It
   keeps ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr, and the stack from lo to sp stays
   writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c DgnLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_CURSOR_STEP : Z := 0x1368c.
Definition CHECK_CURSOR_STEP_FRAME : Z := 16.

Definition check_cursor_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (p c body r lo : Z) (sm : spec_msg) (cur : dgn_cursor),
    check_cursor_step_ok sm r cur = true ->
    -2^31 <= sm_code sm < 2^31 ->
    -2^31 <= r < 2^31 ->
    0 <= dc_pos cur ->
    (* UBSan: 0x13690, 0x136d8 *)
    p mod 8 = 0 -> c mod 8 = 0 ->
    ro_cells rsegs m p (spec_msg_cells sm) ->
    ro_cells rsegs m c (cursor_cells body (dc_len cur) (Z.to_nat (dc_pos cur)) (dc_status cur)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CURSOR_STEP_FRAME <= bv_unsigned sp ->
    p + SM_SIZE <= bv_unsigned sp - CHECK_CURSOR_STEP_FRAME \/ bv_unsigned sp <= p ->
    c + 25 <= bv_unsigned sp - CHECK_CURSOR_STEP_FRAME \/ bv_unsigned sp <= c ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CURSOR_STEP_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 r) (Z_to_bv 64 c)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CURSOR_STEP) fc None m (seg_rom rsegs)).
