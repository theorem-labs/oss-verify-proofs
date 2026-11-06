(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the contract of spec_msg_step (fuzz/spec.h:298-363) on the UBSan image, where
   it is out of line at 0x13464 (552 bytes: 138 words, the last the unimp at 0x13688), over lib/Spec/DgnSpec.v's
   spec_msg_step. (The plain image inlines it into LLVMFuzzerTestOneInput.)
   Arguments: a0 = b (the body), a1 = len, a2 = at (pos), a3 = status_in (a uint8_t, zero-extended by every caller:
   LLVMFuzzerTestOneInput 0x12e1c and 0x12f10 `andi a3, a0, 0xff`, 0x12f9c `mv a3, s6` of an `lbu`), a4 = m, the
   address of a struct spec_msg (56 bytes, DgnLayout.v spec_msg_cells). The callers are LLVMFuzzerTestOneInput
   0x12e2c (the cursor loop, m = sp + 0x18), 0x12f20 (owed_at, m = sp + 0x18) and 0x12fa0 (owed_at's LSB peek,
   m = sp + 0x150).
   The function saves ra and s0..s4 in a 48-byte frame below sp (0x13464-0x1347c), calls memset (m, 0, 56)
   (0x13494-0x134a0, lib/U/Prog/memset_c.v), then writes the fields as the model gives them and returns void. It
   reads the bytes b[i] only for i < len: len <= the length of bs, and the result is the model over the bytes of bs
   (map bv_unsigned bs; a caller's bytes past len are not read).
   The UBSan check sites, each a branch to the unimp at 0x13688, and the premise that makes each unreachable:
   - 0x134a4 `andi a0, s0, 7` / 0x134a8 `bnez`: m misaligned for m->at (size_t): mp mod 8 = 0;
   - 0x134b8 `add a0, s2, s1` / 0x134bc `bltu a0, s2`: b + at wraps; at < len <= length bs here and bytes_at gives
     b + length bs <= 2^64: no premise of its own;
   - 0x134c0-0x134cc (`snez`, `seqz`, `xor`, `beqz`): b + at with exactly one of b, b + at NULL: b <> 0 (and
     b + at < 2^64 as above);
   - 0x134d0 `beqz s2`: b == NULL at the load b[at]: b <> 0;
   - 0x134ec `not a2, s2` / 0x134f8 `bltu a2, a1`: b + i wraps in the F7 scan (i < len), 0x135f0 / 0x135f8 the same
     for b + data + k, 0x13630 for b + data, 0x13664 for b + data + 1 (all below len): no premise of their own.
   Result: memory changes only in the 56 bytes at m (which hold spec_msg_cells of the model's step) and in the
   48-byte frame; s0..s11, ra, sp, gp, tp are kept; a0..a7 and t0..t6 are written. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout.
Open Scope Z_scope.

Definition SPEC_MSG_STEP : Z := 0x13464.
Definition SPEC_MSG_STEP_FRAME : Z := 48.

Definition spec_msg_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b len pos st mp lo : Z) (bs junk : list byte),
    (* UBSan only: 0x134d0 `beqz s2` (b == NULL at the load b[at]) and 0x134cc (b + at with b NULL) *)
    b <> 0 ->
    0 <= len <= Z.of_nat (length bs) ->
    0 <= pos < 2 ^ 64 ->
    0 <= st < 256 ->
    bytes_at rsegs m b bs ->
    (* UBSan only: 0x134a4 / 0x134a8, the alignment check of m->at *)
    mp mod 8 = 0 ->
    rw_cells rsegs m mp [CB 56 junk] ->
    mp + 56 <= b \/ b + Z.of_nat (length bs) <= mp ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + SPEC_MSG_STEP_FRAME <= bv_unsigned sp ->
    mp + 56 <= bv_unsigned sp - SPEC_MSG_STEP_FRAME \/ bv_unsigned sp <= mp ->
    b + Z.of_nat (length bs) <= bv_unsigned sp - SPEC_MSG_STEP_FRAME \/ bv_unsigned sp <= b ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(mp, mp + 56); (bv_unsigned sp - SPEC_MSG_STEP_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' mp (spec_msg_cells (spec_msg_step (map bv_unsigned bs) len pos st)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 len) (Z_to_bv 64 pos) (Z_to_bv 64 st)
               (Z_to_bv 64 mp) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SPEC_MSG_STEP) fc None m (seg_rom rsegs)).
