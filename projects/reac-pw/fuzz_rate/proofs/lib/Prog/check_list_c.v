From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** check_list(hz, bit, closed, mask, best) (fuzz_rate.c:202-215, bit_of :43-49 inlined twice; 200 bytes, 50
    instructions at 0x1466c in the plain image; frame 16 bytes, saves ra at sp - 8):
      0x1466c addi sp,sp,-16; sd ra,8(sp); mv a5,zero; addi a6,zero,3;
              auipc a7,0xffffc; addi a7,a7,-0x34 (a7 = 0x1467c - 0x4000 - 0x34 = 0x10648 = closed_list);
      0x14684 lw t0,0(a7); beq a0,t0,0x146a4; addi a5,a5,1; addi a6,a6,-1; addi a7,a7,4; bnez a6,0x14684;
              mv a5,zero; j 0x146ac (hz not in the list: a5 = 0, the sllw is skipped);
      0x146a4 addi a6,zero,1;  0x146a8 sllw a5,a6,a5 (1 << index: bit_of(hz));  0x146ac bne a1,a5,0x14730;
              addi a5,zero,2; auipc a1,0xffffc; addi a1,a1,-0x6c (a1 = 0x10648);
      0x146bc lw a6,0(a1); beq a0,a6,0x146d4; mv a7,a5; addi a5,a5,-1; addi a1,a1,4; bnez a7,0x146bc;
      0x146d4 xor a0,a0,a6; seqz a0,a0 (bit_of(hz) != 0); bne a2,a0,0x14730;
              andi a0,a3,4; bnez a0,0x1470c; andi a0,a3,2; bnez a0,0x14724;
              slli a3,a3,0x3f; lui a0,0xb; srai a3,a3,0x3f; addiw a0,a0,-0x3bc; and a0,a3,a0; beq a4,a0,0x14718;
              j 0x14730;
      0x1470c lui a0,0x17; addiw a0,a0,0x700 (96000); bne a4,a0,0x14730;
      0x14718 ld ra,8(sp); addi sp,sp,16; ret;
      0x14724 lui a0,0xc; addiw a0,a0,-0x480 (48000); beq a4,a0,0x14718;
      0x14730 jal abort (0x160bc).
    closed_list (0x10648, .rodata) holds 44100, 48000, 96000; the hz compares read the whole 64-bit a0 against the
    sign-extended words (lw), as reac_rate_bit's do. So when a1 = rate_bit hz, a2 = rate_closed hz and
    a4 = rate_best mask (Pod/RateCfg.v; hz = bv_unsigned a0, mask = bv_unsigned a3; RateCfg's bit_of_rate_bit and
    best_of_rate_best are the same rules as the harness's) no `bne` / `beq` to 0x14730 is taken and it returns. On that
    path it writes a0, a1, a3, a5, a6, a7 and t0, stores ra in its frame [sp - 16, sp) and loads it back, and reads
    closed_list twice (in the read-only segment at 0x10000: mem_inv makes those reads come from the image; the stack
    premise keeps the frame store off them).

    Call site (LLVMFuzzerTestOneInput, plain): 0x144e0 `jal check_list` in the two-pass decide loop, with
    sp = S - 544 (the harness frame) and
      a0 = s5 = asked[i] (0x144d0 `mv a0,s5`);
      a1 = s6 = reac_rate_bit(asked[i]) (0x144d4; the call at 0x144b0 with a0 = s5, result 0x144b4 `mv s6,a0`);
      a2 = s7 = reac_rate_is_closed(asked[i]) (0x144d8; the call at 0x144bc, result 0x144c0 `mv s7,a0`);
      a3 = s9 = mask (0x144dc);
      a4 = reac_rate_best_drivable(mask) (0x144cc `mv a4,a0` after the call at 0x144c8 with a0 = s9).
    Why each premise holds there: the three library contracts return exactly these words, and s5, s6, s7, s9 are
    callee-saved across the calls. The stack region [lo, sp) with lo = S - 65536 is the frame's stack, writable and
    outside the image, lo + 16 <= S - 544; mem_inv holds of the memory the cut runs on and every callee since keeps
    it. *)
Definition CHECK_LIST : Z := 0x1466c.
Definition CHECK_LIST_FRAME : Z := 16.

Definition check_list_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a1 = Z_to_bv 64 (rate_bit (bv_unsigned a0)) ->
    a2 = Z_to_bv 64 (rate_closed (bv_unsigned a0)) ->
    a4 = Z_to_bv 64 (rate_best (bv_unsigned a3)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_LIST_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a3' a5' a6' a7' t0' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2 a3' a4 a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LIST_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LIST) fc None m (seg_rom rsegs)).
