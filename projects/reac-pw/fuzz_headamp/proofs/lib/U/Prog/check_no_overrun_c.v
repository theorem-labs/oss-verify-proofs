From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_no_overrun(guard) (fuzz_headamp.c:183-192; 52 bytes, 13 instructions at 0x148ac in the UBSan image):
      0x148ac lbu a2,0(a0); addi a1,zero,0xa5; bne a2,a1,0x148d0; lbu a2,1(a0); bne a2,a1,0x148d0;
              lbu a0,2(a0); addi a1,zero,0xa5; bne a0,a1,0x148d0; ret;
      0x148d0 addi sp,sp,-16; sd ra,8(sp); jal abort (0x16364); unimp.
    The plain text (lib/Prog/check_no_overrun_c.v) with a trap after the abort call (no UBSan check in it). It
    returns exactly when the three bytes at a0 are 0xa5; on that path it writes a0, a1, a2 (each := 0xa5), stores
    nothing, reads only those three bytes, and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x1416c `jal check_no_overrun` (the only one), with sp = S - 608 and
      a0 = s3 + s0 (0x14168 `add a0,s3,s0`) = &out[cap]: s3 = out (0x1411c `mv s3,a0` after malloc(3cap + 3) at
           0x14114), s0 = 3cap (0x14104 `slli s0,s2,1`, 0x14108 `add s0,s0,s2`), s2 = cap (0x140ec `lbu s2,8(sp)`).
           main's own trap test of out + 3cap (0x1415c `not a1,s3`, 0x14160 `bltu a1,s0,0x148a0`) precedes it.
    Why the premise holds there: memset(out, 0xa5, 3cap + 3) at 0x14128 and reac_headamp_prop_parse_result at
    0x14158, whose writes (U/Prog/reac_headamp_prop_parse_result_c.v) miss [out + 3cap, out + 3cap + 3):
    U/Prog/HeadSites.v [site_no_overrun]. *)
Definition CHECK_NO_OVERRUN : Z := 0x148ac.

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
