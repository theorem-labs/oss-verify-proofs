From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_absent(rc, hz) (fuzz_rate.c:130-141; 32 bytes, 8 instructions at 0x145a8 in the plain image):
      0x145a8 bnez a0,0x145bc; lui a0,0x5a5a6; addiw a0,a0,-0x5a6 (a0 = 0x5a5a5a5a); bne a1,a0,0x145bc; ret;
      0x145bc addi sp,sp,-16; sd ra,8(sp); jal abort (0x160bc).
    When a0 = 0 and a1 = 0x5a5a5a5a, both as 64-bit words, neither branch is taken and it returns at once. On that
    path it writes a0 := 0x5a5a5a5a (the lui/addiw: the compiler builds the constant in a0, which rc no longer needs),
    stores nothing, reads no memory and uses no stack (only the abort path, 0x145bc, has a frame; the premises make it
    dead). Both compares read the whole 64-bit registers, hence premises on bv_unsigned of each.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14368 `jal check_absent`, reached when pp->corrupt = 0 (0x14234
    `bnez a1` not taken) and the inlined expect_rate answers 0, with sp = S - 544 (the harness frame) and
      a0 = s4 = rc (0x14364 `mv a0,s4`): the value reac_rate_prop_parse returned (0x14230 `mv s4,a0` after the call
           at 0x14224);
      a1 = hz (0x14360 `lw a1,0x158(sp)`): the 4-byte cell at sp + 0x158, sign-extended (lw), into which 0x14214
           `sw a0,0x158(sp)` stored 0x5a5a5a5a (0x14208 `lui a0,0x5a5a6`, 0x14210 `addi a0,a0,-0x5a6`) before the
           parse.
    Why the premises hold there: expect_rate's 0 is expect_model null r = (None, 0) for the pod_build record r, and
    the pod is uncorrupted, so harness_parse null (buf r) = expect_model null r (Pod/Rate.v harness_parse_build).
    Then reac_rate_prop_parse_contract returns a0 = Z_to_bv 64 0 (so s4 = 0) and, nothing being written
    (rate_mem None), writes only its frame below sp, not the cell at sp + 0x158: the cell still holds
    le4 0x5a5a5a5a, and lw of it is 0x5a5a5a5a (below 2^31, so its sign extension is itself). *)
Definition CHECK_ABSENT : Z := 0x145a8.

Definition check_absent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 0 ->
    bv_unsigned a1 = 0x5a5a5a5a ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x5a5a5a5a) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ABSENT) fc None m (seg_rom rsegs)).
