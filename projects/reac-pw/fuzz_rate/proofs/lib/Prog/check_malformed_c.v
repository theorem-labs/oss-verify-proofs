From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_malformed(rc, hz) (fuzz_rate.c:158-173; 36 bytes, 9 instructions at 0x145e4 in the plain image):
      0x145e4 addi a2,zero,-1; bne a0,a2,0x145fc; lui a0,0x5a5a6; addiw a0,a0,-0x5a6 (a0 = 0x5a5a5a5a);
              bne a1,a0,0x145fc; ret;
      0x145fc addi sp,sp,-16; sd ra,8(sp); jal abort (0x160bc).
    When a0 = 2^64 - 1 (rc = -1 as a 64-bit word) and a1 = 0x5a5a5a5a, neither branch is taken and it returns at
    once. On that path it writes a2 := -1 (all ones) and a0 := 0x5a5a5a5a, stores nothing, reads no memory and uses
    no stack (only the abort path, 0x145fc, has a frame; the premises make it dead). Both compares read the whole
    64-bit registers, hence premises on bv_unsigned of each.

    Call site (LLVMFuzzerTestOneInput, plain): 0x143d8 `jal check_malformed`, reached when pp->corrupt = 0 (0x14234
    `bnez a1` not taken) and the inlined expect_rate answers -1 (flags bit 0, 0x1423c `bnez s1`; is_props = 0,
    0x14244 `beqz a0`; or the first rate pair's value is neither an Int nor a Float with a nearest integer in
    [INT32_MIN, INT32_MAX]), with sp = S - 544 (the harness frame) and
      a0 = s4 = rc (0x143d4 `mv a0,s4`): the value reac_rate_prop_parse returned (0x14230 `mv s4,a0` after the call
           at 0x14224);
      a1 = hz (0x143d0 `lw a1,0x158(sp)`): the 4-byte cell at sp + 0x158, sign-extended (lw), set to 0x5a5a5a5a at
           0x14214 before the parse.
    Why the premises hold there: expect_rate's -1 is expect_model null r = (None, -1) with null = flags bit 0. With
    null the parse's argument is NULL (0x14218 `addi a0,s1,-1`, 0x1421c `and a0,a0,s3` give 0) and
    harness_parse true bs = (None, -1); without it the pod is uncorrupted and harness_parse false (buf r) =
    expect_model false r (Pod/Rate.v harness_parse_build). Either way reac_rate_prop_parse_contract returns
    a0 = Z_to_bv 64 (-1), whose bv_unsigned is 2^64 - 1, and writes nothing at the cell (rate_mem None): lw of it is
    0x5a5a5a5a. *)
Definition CHECK_MALFORMED : Z := 0x145e4.

Definition check_malformed_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 2^64 - 1 ->
    bv_unsigned a1 = 0x5a5a5a5a ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x5a5a5a5a) a1 (Z_to_bv 64 (-1)) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_MALFORMED) fc None m (seg_rom rsegs)).
