From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_label (fuzz_pin.c:55-69; 20 bytes, 5 instructions at 0x12e7c in the plain image):
      0x12e7c bne a0,a1,0x12e84; ret; 0x12e84 addi sp,sp,-16; sd ra,8(sp); jal abort.
    When a0 = a1 the bne is not taken and it returns at once: it writes no register and no memory, reads no memory
    and uses no stack on that path (the abort path, 0x12e84, is dead under the premise).

    Call site (LLVMFuzzerTestOneInput, plain): 0x12de0 `jal check_label`, reached only when rc = 0, after check_row
    returned (which keeps every register), with
      a0 = label, the 8 bytes at sp+0 of the harness frame (0x12dd8 `ld a0,0(sp)`), zeroed at 0x12d80 and written by
           reac_box_pin_parse through its a2 = sp;
      a1 = s2 = want_label: spec + tok + 1 (0x12e38) or the row's display pointer (0x12e40 `ld s2,8(s1)`).
    Why the premise holds there: rc = 0 means parse_out FUZZ_CATALOGUE spec (fl_live fl) s = Some (row, lab) and
    reac_box_pin_parse_contract stored le8 lab at sp; pin_spec.harness_row_label gives lab = want_label spec fl s,
    which is what the harness computed into s2 (pin_spec.harness_label_off is its test `tok < len && spec[tok + 1]`;
    the display pointer is read from the table, which the caller has as the image's bytes). *)
Definition CHECK_LABEL : Z := 0x12e7c.

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
