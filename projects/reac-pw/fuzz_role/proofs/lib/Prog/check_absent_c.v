From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_absent(rc, role) (fuzz_role.c:65-76; 28 bytes, 7 instructions at 0x141c0 in the plain image):
      0x141c0 bnez a0,0x141d0; addi a0,zero,0x5a; bne a1,a0,0x141d0; ret;
      0x141d0 addi sp,sp,-16; sd ra,8(sp); jal abort (0x1587c).
    When a0 = 0 and a1 = 0x5a (ROLE_UNSET), both as 64-bit words, neither branch is taken and it returns at once. On
    that path it writes a0 := 0x5a (the addi: the compiler loads the constant into a0, which rc no longer needs),
    stores nothing, reads no memory and uses no stack (only the abort path, 0x141d0, has a frame; the premises make it
    dead). Both compares read the full 64-bit registers, hence premises on bv_unsigned of each.

    Call site (LLVMFuzzerTestOneInput, plain): 0x140ac `jal check_absent`, reached when pp->corrupt = 0 (0x13f90
    `bnez a1` not taken) and the inlined expect_role answers 0 (0x13fa8 `beqz a0`: params_struct = 0; 0x13fec
    `bge s6,s5`, 0x14034 `beq a2,s9` or 0x14048 `blt s4,s9`: no role pair left), with sp = S - 496 (the harness
    frame) and
      a0 = s2 = rc (0x140a8 `mv a0,s2`), the value reac_role_prop_parse returned (0x13f8c `mv s2,a0` after the call
           at 0x13f84);
      a1 = role (0x140a4 `lw a1,0x128(sp)`): the 4-byte role cell at sp + 0x128, sign-extended (lw, not lwu), into
           which 0x13f74 `sw a0,0x128(sp)` stored 0x5a (a0 = 0x5a from 0x13f6c) before the parse.
    Why the premises hold there: expect_role's 0 is expect_model false r = (None, 0) for the pod_build record r
    (flags bit 0 is clear, or expect_role would answer -1). The pod is uncorrupted, so the bytes the parse reads are
    buf r and parse_model (buf r) = expect_model false r (Pod/Role.v's parse_model_encode). Then
    reac_role_prop_parse_contract returns a0 = Z_to_bv 64 0 (so s2 = 0) and, the role being None, writes only its
    frame below sp (role_mem), not the cell at sp + 0x128: the cell still holds le4 0x5a = [0x5a; 0; 0; 0], and lw of
    it is 0x5a. *)
Definition CHECK_ABSENT : Z := 0x141c0.

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
