From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_malformed(rc, role) (fuzz_role.c:91-105; 32 bytes, 8 instructions at 0x141f8 in the plain image):
      0x141f8 addi a2,zero,-1; bne a0,a2,0x1420c; addi a0,zero,0x5a; bne a1,a0,0x1420c; ret;
      0x1420c addi sp,sp,-16; sd ra,8(sp); jal abort (0x1587c).
    When a0 = 2^64 - 1 (rc = -1 as a 64-bit word) and a1 = 0x5a (ROLE_UNSET), neither branch is taken and it returns
    at once. On that path it writes a2 := -1 (all ones) and a0 := 0x5a (the two addi), stores nothing, reads no
    memory and uses no stack (only the abort path, 0x1420c, has a frame; the premises make it dead). Both compares
    read the full 64-bit registers, hence premises on bv_unsigned of each.

    Call site (LLVMFuzzerTestOneInput, plain): 0x140ec `jal check_malformed`, reached when pp->corrupt = 0 (0x13f90
    `bnez a1` not taken) and the inlined expect_role answers -1: 0x13f98 `bnez s3` (flags bit 0, s3 = 0x13f70
    `andi s3,s5,1`), 0x13fa0 `beqz a0` (is_props = 0), 0x14090 `bne a1,a2` (the value is neither Float nor Int),
    0x14098 / 0x140c4 `bltu a1,a2` (Int / Float body shorter than 4), 0x140d4 `beqz a0` (pod_nearest found no
    nearest integer in range), or 0x140e0 `bltu a2,a0` not taken (flag >= 2 unsigned); then sp = S - 496 (the harness
    frame) and
      a0 = s2 = rc (0x140e8 `mv a0,s2`), the value reac_role_prop_parse returned (0x13f8c `mv s2,a0` after the call
           at 0x13f84);
      a1 = role (0x140e4 `lw a1,0x128(sp)`): the 4-byte role cell at sp + 0x128, sign-extended (lw, not lwu), into
           which 0x13f74 `sw a0,0x128(sp)` stored 0x5a (a0 = 0x5a from 0x13f6c) before the parse.
    Why the premises hold there: expect_role's -1 is expect_model null r = (None, -1) for the pod_build record r and
    null = flags bit 0. With null, the parse's argument is NULL (0x13f78 `addi a0,s3,-1`, 0x13f7c `and a0,a0,s1`
    give 0) and parse_res true bs = (None, -1); without it, the pod is uncorrupted, the bytes the parse reads are
    buf r, and parse_model (buf r) = expect_model false r (Pod/Role.v's parse_model_encode). Either way
    reac_role_prop_parse_contract returns a0 = Z_to_bv 64 (-1), whose bv_unsigned is 2^64 - 1 (so s2 is all ones),
    and, the role being None, writes only its frame below sp (role_mem), not the cell at sp + 0x128: the cell still
    holds le4 0x5a = [0x5a; 0; 0; 0], and lw of it is 0x5a. *)
Definition CHECK_MALFORMED : Z := 0x141f8.

Definition check_malformed_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 2^64 - 1 ->
    bv_unsigned a1 = 0x5a ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x5a) a1 (Z_to_bv 64 (-1)) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_MALFORMED) fc None m (seg_rom rsegs)).
