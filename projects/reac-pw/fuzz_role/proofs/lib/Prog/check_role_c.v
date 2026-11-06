From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_role(rc, role, want) (fuzz_role.c:78-89; 28 bytes, 7 instructions at 0x141dc in the plain image):
      0x141dc addi a3,zero,1; bne a0,a3,0x141ec; bne a1,a2,0x141ec; ret;
      0x141ec addi sp,sp,-16; sd ra,8(sp); jal abort (0x1587c).
    When a0 = 1 and a1 = a2, all three as 64-bit words, neither branch is taken and it returns at once. On that path
    it writes a3 := 1 (the addi), stores nothing, reads no memory and uses no stack (only the abort path, 0x141ec, has
    a frame; the premises make it dead).

    Call site (LLVMFuzzerTestOneInput, plain): 0x141b4 `jal check_role`, reached when pp->corrupt = 0 (0x13f90
    `bnez a1` not taken) and the inlined expect_role answers 1: 0x140e0 `bltu a2,a0` taken (a0 = 2 from 0x140dc),
    with a2 = the role flag, either the Int value (0x1409c `lw a2,8(a0)`, then `j 0x140dc`) or pod_nearest's result
    (0x140d8 `ld a2,0x88(sp)`), so a2 is 0 or 1. Then sp = S - 496 (the harness frame) and
      a0 = s2 = rc (0x141b0 `mv a0,s2`), the value reac_role_prop_parse returned (0x13f8c `mv s2,a0` after the call
           at 0x13f84);
      a1 = role (0x141a8 `lw a1,0x128(sp)`): the 4-byte role cell at sp + 0x128, sign-extended (lw, not lwu);
      a2 = want (0x141ac `sext.w a2,a2`): the flag itself, as the select `flag == MASTER ? MASTER : SLAVE` folds away
           (role_z MASTER = 0, role_z SLAVE = 1); 0 and 1 are their own sign extensions.
    Why the premises hold there: expect_role's 1 is expect_model false r = (Some w, 1) for the pod_build record r,
    with want = role_z w. The pod is uncorrupted and flags bit 0 is clear (else expect_role answers -1), so the bytes
    the parse reads are buf r and parse_model (buf r) = expect_model false r (Pod/Role.v's parse_model_encode).
    Then reac_role_prop_parse_contract returns a0 = Z_to_bv 64 1 (so s2 = 1) and stores le4 (role_z w) at the
    cell (role_mem): lw of it is role_z w, so a1 = a2 = Z_to_bv 64 (role_z w). *)
Definition CHECK_ROLE : Z := 0x141dc.

Definition check_role_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 1 ->
    a1 = a2 ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 1) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROLE) fc None m (seg_rom rsegs)).
