From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_row (fuzz_pin.c:44-53; 20 bytes, 5 instructions at 0x12e68 in the plain image):
      0x12e68 bne a0,a1,0x12e70; ret; 0x12e70 addi sp,sp,-16; sd ra,8(sp); jal abort.
    When a0 = a1 the bne is not taken and it returns at once: it writes no register and no memory, reads no memory
    and uses no stack on that path (the abort path, 0x12e70, is dead under the premise).

    Call site (LLVMFuzzerTestOneInput, plain): 0x12dd4 `jal check_row`, reached only when rc = 0 (0x12dc8
    `bnez s3,0x12de4` not taken), with
      a0 = model, the 8 bytes at sp+8 of the harness frame (0x12dcc `ld a0,8(sp)`), zeroed at 0x12d7c and written by
           reac_box_pin_parse through its a1 = sp+8;
      a1 = s1 = want (fuzz_catalogue_row's result, 0x12e20).
    Why the premise holds there: rc = 0 means parse_out FUZZ_CATALOGUE spec (fl_live fl) s = Some (row, lab) and
    reac_box_pin_parse_contract stored le8 row at sp+8; pin_spec.harness_row_label gives row = want_ptr
    FUZZ_CATALOGUE fl s = want. *)
Definition CHECK_ROW : Z := 0x12e68.

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
