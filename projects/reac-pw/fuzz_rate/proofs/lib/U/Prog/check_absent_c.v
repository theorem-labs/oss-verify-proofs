From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_absent(rc, hz) (fuzz_rate.c:130-141; 36 bytes, 9 instructions at 0x146c0 in the UBSan image):
      0x146c0 bnez a0,0x146d4; lui a0,0x5a5a6; addiw a0,a0,-0x5a6 (a0 = 0x5a5a5a5a); bne a1,a0,0x146d4; ret;
      0x146d4 addi sp,sp,-16; sd ra,8(sp); jal abort (0x164a4); 0x146e0 unimp (after abort, never reached).
    The plain code at another address, plus the unimp. When a0 = 0 and a1 = 0x5a5a5a5a, both as 64-bit words,
    neither branch is taken and it returns at once. On that path it writes a0 := 0x5a5a5a5a, stores nothing, reads no
    memory and uses no stack (only the abort path has a frame; the premises make it dead). Both compares read the
    whole 64-bit registers, hence premises on bv_unsigned of each. No trap branch.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x143c4 `jal check_absent`, reached when pp->corrupt = 0 (0x14254
    `bnez a1` not taken) and the inlined expect_rate answers 0, with sp = S - 592 (the harness frame) and
      a0 = s4 = rc (0x143c0 `mv a0,s4`): the value reac_rate_prop_parse returned (0x14250 `mv s4,a0` after the call
           at 0x14244);
      a1 = hz (0x143bc `lw a1,0x188(sp)`): the 4-byte cell at sp + 0x188, sign-extended (lw), into which 0x14234
           `sw a0,0x188(sp)` stored 0x5a5a5a5a (0x14228 `lui a0,0x5a5a6`, 0x14230 `addi a0,a0,-0x5a6`) before the
           parse.
    Why the premises hold there: as in the plain image (Prog/check_absent_c.v): expect_model null r = (None, 0) =
    harness_parse null (buf r) (Pod/Rate.v harness_parse_build), so U/Prog/reac_rate_prop_parse_c.v's contract
    returns a0 = Z_to_bv 64 0 and writes nothing at the cell (rate_mem None): lw reads 0x5a5a5a5a. *)
Definition CHECK_ABSENT : Z := 0x146c0.

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
