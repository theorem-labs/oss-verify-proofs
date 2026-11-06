From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_row (fuzz_pin.c:44-53; 24 bytes, 6 instructions at 0x12ed8 in the UBSan image):
      0x12ed8 bne a0,a1,0x12ee0; ret; 0x12ee0 addi sp,sp,-16; sd ra,8(sp); jal abort; unimp.
    When a0 = a1 it returns at once, writing no register and no memory, reading no memory, using no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x12e14 `jal check_row`, reached only when rc = 0 (0x12e08
    `bnez s3,0x12e24` not taken), with
      a0 = model, the 8 bytes at sp+16 of the harness frame (0x12e0c `ld a0,16(sp)`), zeroed at 0x12dbc and written
           by reac_box_pin_parse through its a1 = sp+16;
      a1 = s1 = want (fuzz_catalogue_row's result, 0x12e70).
    Why the premise holds there: as in the plain build (lib/Prog/check_row_c.v): pin_spec.harness_row_label. *)
Definition CHECK_ROW : Z := 0x12ed8.

Definition check_row_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = a1 ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROW) fc None m (seg_rom rsegs)).
