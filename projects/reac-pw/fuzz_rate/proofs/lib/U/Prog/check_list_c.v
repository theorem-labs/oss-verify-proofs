From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** check_list(hz, bit, closed, mask, best) (fuzz_rate.c:202-215, bit_of :43-49 inlined twice; 204 bytes, 51
    instructions at 0x14798 in the UBSan image; frame 16 bytes, saves ra at sp - 8): the plain code
    (Prog/check_list_c.v, 0x1466c) at another address plus one `unimp` after `jal abort` (0x1485c -> 0x164a4,
    0x14860); no trap branch. The first loop's miss path is `mv a5,zero; j 0x147d8` (0x147c8 / 0x147cc: a5 = 0, the
    sllw at 0x147d4 is skipped). closed_list is at 0x10628 (0x147a8 `auipc a7,0xffffc; addi a7,a7,-0x180`; 0x147e0
    `auipc a1,0xffffc; addi a1,a1,-0x1b8`), .rodata: 44100, 48000, 96000. The abort branches: 0x147d8 `bne a1,a5`
    (bit), 0x14808 `bne a2,a0` (closed), 0x14834 / 0x14840 / 0x14858 (best). So when a1 = rate_bit hz,
    a2 = rate_closed hz and a4 = rate_best mask (Pod/RateCfg.v; hz = bv_unsigned a0, mask = bv_unsigned a3) it
    returns. On that path it writes a0, a1, a3, a5, a6, a7 and t0, stores ra in its frame [sp - 16, sp) and loads it
    back, and reads closed_list twice (in the read-only segment at 0x10000: mem_inv makes those reads come from the
    image).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x145f8 `jal check_list` in the two-pass decide loop, with
    sp = S - 592 (the harness frame) and
      a0 = s5 = asked[i] (0x145e8 `mv a0,s5`; 0x145c0 `lw s5,0(s7)`);
      a1 = s6 = reac_rate_bit(asked[i]) (0x145ec; the call at 0x145c8, result 0x145cc `mv s6,a0`);
      a2 = s7 = reac_rate_is_closed(asked[i]) (0x145f0; the call at 0x145d4, result 0x145d8 `mv s7,a0`);
      a3 = s10 = mask (0x145f4);
      a4 = reac_rate_best_drivable(mask) (0x145e4 `mv a4,a0` after the call at 0x145e0 with a0 = s10).
    Why each premise holds there: the three library contracts return exactly these words, and s5, s6, s7, s10 are
    callee-saved across the calls. The stack region [lo, sp) with lo = S - 65536 is the frame's stack, writable and
    outside the image, lo + 16 <= S - 592; mem_inv holds of the memory the cut runs on and every callee since keeps
    it. *)
Definition CHECK_LIST : Z := 0x14798.
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
