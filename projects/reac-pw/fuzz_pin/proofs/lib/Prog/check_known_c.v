From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_known (fuzz_pin.c:30-42; 28 bytes, 7 instructions at 0x12e4c in the plain image):
      0x12e4c seqz a0,a0; seqz a1,a1; beq a0,a1,0x12e5c; ret; 0x12e5c addi sp,sp,-16; sd ra,8(sp); jal abort.
    When (a0 = 0) <-> (a1 <> 0), the beq is not taken and it returns at once. On that path it writes a0 and a1 (seqz),
    stores nothing, reads no memory and uses no stack (only the abort path, 0x12e5c, has a frame; the premise makes it
    dead).

    Call site (LLVMFuzzerTestOneInput, plain): 0x12dc4 `jal check_known` with
      a0 = s3 = rc, the value reac_box_pin_parse returned (0x12dbc `mv s3,a0`): 0 or -1 (2^64 - 1);
      a1 = s1 = want, fuzz_catalogue_row's result (0x12e20 `mv s1,a0`) or 0 (0x12d74 `mv s1,zero`).
    Why the premise holds there: rc = parse_rc (parse_out FUZZ_CATALOGUE spec (fl_live fl) s) by
    reac_box_pin_parse_contract (spec, model and label are NULL exactly by flag bits 0, 1, 2), and want = want_ptr
    FUZZ_CATALOGUE fl s by fuzz_catalogue_row_contract and the harness's scan; pin_spec.harness_known turns the one into
    the other (FUZZ_CATALOGUE > 0, fl a byte, s has no NUL). Both values are below 2^64 as integers (-1 as the word
    2^64 - 1), so the word tests are these. *)
Definition CHECK_KNOWN : Z := 0x12e4c.

Definition check_known_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    (bv_unsigned a0 = 0 <-> bv_unsigned a1 <> 0) ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_KNOWN) fc None m (seg_rom rsegs)).
