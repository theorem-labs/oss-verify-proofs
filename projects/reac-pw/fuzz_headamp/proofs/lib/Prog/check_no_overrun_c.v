From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_no_overrun(guard) (fuzz_headamp.c:183-192; 48 bytes, 12 instructions at 0x14680 in the plain image):
      0x14680 lbu a2,0(a0); addi a1,zero,0xa5; bne a2,a1,0x146a4; lbu a2,1(a0); bne a2,a1,0x146a4;
              lbu a0,2(a0); addi a1,zero,0xa5; bne a0,a1,0x146a4; ret;
      0x146a4 addi sp,sp,-16; sd ra,8(sp); jal abort (0x15e64).
    It returns exactly when the three bytes at a0 (guard->ch, ->param, ->value: uint8_t, read by lbu) are 0xa5, the
    C condition of :190 false. On that path it writes a0, a1, a2 (each := 0xa5, zero-extended), stores nothing,
    reads only those three bytes, and uses no stack (only the abort path, 0x146a4, has a frame; the premise makes it
    dead).

    Call site (LLVMFuzzerTestOneInput, plain): 0x140c8 `jal check_no_overrun` (the only one), on every run past the
    size test and the first three mallocs, with sp = S - 560 (the harness frame) and
      a0 = s3 + s0 (0x140c4 `add a0,s3,s0`) = &out[cap]: s3 = out (0x14084 `mv s3,a0` after malloc(3cap + 3) at
           0x1407c), s0 = 3cap (0x1406c `slli s0,s2,1`, 0x14070 `add s0,s0,s2`), s2 = cap = the second input byte
           mod 10 (0x14054 `andi s2,s6,0xff`).
    Why the premise holds there: memset(out, 0xa5, 3cap + 3) at 0x14090 wrote 0xa5 to [out, out + 3cap + 3);
    reac_headamp_prop_parse_result at 0x140bc (Prog/reac_headamp_prop_parse_result_c.v) writes only its stack
    below sp, out[0, 3n) with n <= cap, errno and res = sp + 0x150 (above sp), none of which meets
    [out + 3cap, out + 3cap + 3) (the out block lies below the stack region, apart from errno by the parse's
    premises): Prog/HeadSites.v [site_no_overrun]. *)
Definition CHECK_NO_OVERRUN : Z := 0x14680.

Definition check_no_overrun_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m (bv_unsigned a0) (repeat GUARD_BYTE 3) ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xa5) (Z_to_bv 64 0xa5) (Z_to_bv 64 0xa5) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_NO_OVERRUN) fc None m (seg_rom rsegs)).
