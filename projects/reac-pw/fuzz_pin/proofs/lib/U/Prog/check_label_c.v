From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_label (fuzz_pin.c:55-69; 24 bytes, 6 instructions at 0x12ef0 in the UBSan image):
      0x12ef0 bne a0,a1,0x12ef8; ret; 0x12ef8 addi sp,sp,-16; sd ra,8(sp); jal abort; unimp.
    When a0 = a1 it returns at once, writing no register and no memory, reading no memory, using no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x12e20 `jal check_label`, reached only when rc = 0, after check_row,
    with
      a0 = label, the 8 bytes at sp+8 of the harness frame (0x12e18 `ld a0,8(sp)`), zeroed at 0x12dc0 and written by
           reac_box_pin_parse through its a2 = sp+8;
      a1 = s2 = want_label: spec + tok + 1 (0x12e84 `addi s2,a0,1`) or the row's display pointer (0x12ea4
           `ld s2,8(s1)`, after the alignment test of s1 at 0x12e9c).
    Why the premise holds there: as in the plain build (lib/Prog/check_label_c.v): pin_spec.harness_row_label. *)
Definition CHECK_LABEL : Z := 0x12ef0.

Definition check_label_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = a1 ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LABEL) fc None m (seg_rom rsegs)).
