(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_top.v, with its module paths changed; 465 of its 529 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/Prog/LLVMFuzzerTestOneInput.v, with its module names and addresses changed; 23 of its 51 lines of code are new or changed and 501 lines of the source are left out. *)
(* walk of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.ubsan from the return of the second memset to the call of check_round_trip or of free, on Exec.evt. *)
(* LLVMFuzzerTestOneInput in fuzz_frame.ubsan from the return of the second memset (0x12dc8) to the call of
   check_round_trip (0x131e4) or of free (0x14dec), fuzz_frame.c:275-283. It is the inlined spec_read_frame
   (fuzz/spec.h:199-223) of the frame bytes b at buf into the struct spec_frame w at sp, then
   check_parse_refusal (r, w), and when w.code is SPEC_OK check_parse_fields (buf, f, w); check_round_trip (w)
   is the next call:
   - fewer than 30 bytes (0x12dcc), an EtherType other than 0x885F (0x12e04), numbytes under 16 (0x12e30) or
     past the buffer (0x12e38): the code -2, -3 or -4 is stored at w (0x12f98), then check_parse_refusal
     (0x12fa4), then lw a0, 0(sp); bnez a0 (0x12fac) to mv a0, s0 and jal free (0x12fd4);
   - else the fields are stored, the body sum is computed by the loop 0x12f74-0x12f8c (or is 0 when the body
     is empty, 0x12ff8), then the code 0 is stored (0x12f98), check_parse_refusal (0x12fa4),
     check_parse_fields (0x12fbc), and mv a0, sp; jal check_round_trip (0x12fc0).
   w is then spec_cells buf b (U/Prog/check_parse_fields_c.v). check_parse_refusal and check_parse_fields are
   taken through their contracts (Section hypotheses).
   UBSan checks: the branches to the trap at 0x1300c test that buf + 12 .. buf + 31 and buf + 30 + i (the loop)
   do not wrap past 2 ^ 64. buf + length b <= lo < sp < 2 ^ 63, so none is taken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c lt_seg_b2_walk.
Import ListNotations.
Open Scope Z_scope.

Section B2.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.

Lemma lt_b2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv rsegs m ->
    s0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 (fr_code b) -> s2 = Z_to_bv 64 (Z.of_nat (length b)) ->
    Z.of_nat (length b) < 2 ^ 26 -> 4096 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 (repeat (b8 0) 80)] ->
    rw_cells rsegs m (bv_unsigned sp + 80)
      (if fr_code b =? 0 then parse_cells buf b (repeat (b8 0) 64) else [CB 64 (repeat (b8 0) 64)]) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    evt rsegs
      (fun ms' =>
         (fr_code b = 0 /\
          exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12fc8) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' sp a1' a2' a3' a4' a5' a6'
                          a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x131e4) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            bytes_at rsegs m' buf b /\
            ro_cells rsegs m' (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) /\
            ro_cells rsegs m' (bv_unsigned sp) (spec_cells buf b) /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]) \/
         (exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12fdc) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' (Z_to_bv 64 buf) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x14dec) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12dc8) fc None m (seg_rom rsegs)).
Proof.
  exact (b2_main CPR CPF).
Qed.

End B2.
