From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_absent(rc, role) (fuzz_role.c:65-76; 32 bytes, 8 instructions at 0x14224 in the UBSan image):
      0x14224 bnez a0,0x14234; addi a0,zero,0x5a; bne a1,a0,0x14234; ret;
      0x14234 addi sp,sp,-16; sd ra,8(sp); jal abort (0x15b14); unimp.
    The plain text with a trap after the abort call (no UBSan check in it). When a0 = 0 and a1 = 0x5a (ROLE_UNSET),
    both as 64-bit words, neither branch is taken and it returns at once. On that path it writes a0 := 0x5a (the
    addi), stores nothing, reads no memory and uses no stack (only the abort path, 0x14234, has a frame; the premises
    make it dead). Both compares read the full 64-bit registers, hence premises on bv_unsigned of each.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x140f8 `jal check_absent`, reached when pp->corrupt = 0 (0x13f7c
    `bnez a1` not taken, a1 = 0x13f74 `lw a1,4(a2)`) and the inlined expect_role answers 0 (0x13f90 `beqz a0`:
    params_struct = 0; 0x13fdc `bge a5,s0`, 0x1406c `j` or 0x14078 `bltz a5`: no role pair left), with
    sp = S - 544 (the harness frame) and
      a0 = s2 = rc (0x140f4 `mv a0,s2`), the value reac_role_prop_parse returned (0x13f78 `mv s2,a0` after the call
           at 0x13f6c);
      a1 = role (0x140f0 `lw a1,0x158(sp)`): the 4-byte role cell at sp + 0x158, sign-extended (lw, not lwu), into
           which 0x13f5c `sw a0,0x158(sp)` stored 0x5a (a0 = 0x5a from 0x13f54) before the parse.
    Why the premises hold there: expect_role's 0 is expect_model false r = (None, 0) for the pod_build record r
    (flags bit 0 is clear, or expect_role would answer -1). The pod is uncorrupted, so the bytes the parse reads are
    buf r and parse_model (buf r) = expect_model false r (Pod/Role.v's parse_model_encode). Then U's
    reac_role_prop_parse_contract returns a0 = Z_to_bv 64 0 (so s2 = 0) and, the role being None, writes only its
    frame below sp (role_mem), not the cell at sp + 0x158: the cell still holds le4 0x5a = [0x5a; 0; 0; 0], and lw of
    it is 0x5a. *)
Definition CHECK_ABSENT : Z := 0x14224.

Definition check_absent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 0 ->
    bv_unsigned a1 = 0x5a ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x5a) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ABSENT) fc None m (seg_rom rsegs)).
