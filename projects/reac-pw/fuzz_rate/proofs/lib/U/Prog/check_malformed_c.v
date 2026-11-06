From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_malformed(rc, hz) (fuzz_rate.c:158-173; 40 bytes, 10 instructions at 0x14704 in the UBSan image):
      0x14704 addi a2,zero,-1; bne a0,a2,0x1471c; lui a0,0x5a5a6; addiw a0,a0,-0x5a6 (a0 = 0x5a5a5a5a);
              bne a1,a0,0x1471c; ret;
      0x1471c addi sp,sp,-16; sd ra,8(sp); jal abort (0x164a4); 0x14728 unimp (after abort, never reached).
    The plain code at another address, plus the unimp. When a0 = 2^64 - 1 (rc = -1 as a 64-bit word) and
    a1 = 0x5a5a5a5a, neither branch is taken and it returns at once. On that path it writes a2 := -1 (all ones) and
    a0 := 0x5a5a5a5a, stores nothing, reads no memory and uses no stack. No trap branch.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x144b8 `jal check_malformed`, reached when pp->corrupt = 0 (0x14254
    `bnez a1` not taken) and the inlined expect_rate answers -1 (flags bit 0, 0x14258 `bnez s0`; is_props = 0,
    0x14260 `beqz a0`; or the first rate pair's value is neither an Int nor a Float with a nearest integer in
    [INT32_MIN, INT32_MAX]), with sp = S - 592 (the harness frame) and
      a0 = s4 = rc (0x144b4 `mv a0,s4`): the value reac_rate_prop_parse returned (0x14250 `mv s4,a0` after the call
           at 0x14244);
      a1 = hz (0x144b0 `lw a1,0x188(sp)`): the cell at sp + 0x188, set to 0x5a5a5a5a at 0x14234 before the parse.
    Why the premises hold there: as in the plain image (Prog/check_malformed_c.v): with flags bit 0 the parse's
    argument is NULL (0x14238 `addi a0,s0,-1`, 0x1423c `and a0,a0,s3` give 0) and harness_parse true bs = (None, -1);
    without it harness_parse false (buf r) = expect_model false r; either way the parse contract returns
    a0 = Z_to_bv 64 (-1) and writes nothing at the cell. *)
Definition CHECK_MALFORMED : Z := 0x14704.

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
