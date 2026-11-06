From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_known (fuzz_pin.c:30-42; 32 bytes, 8 instructions at 0x12eb8 in the UBSan image):
      0x12eb8 seqz a0,a0; seqz a1,a1; beq a0,a1,0x12ec8; ret; 0x12ec8 addi sp,sp,-16; sd ra,8(sp); jal abort; unimp.
    The plain text with a trap after the abort call. When (a0 = 0) <-> (a1 <> 0), the beq is not taken and it returns
    at once. On that path it writes a0 and a1 (seqz), stores nothing, reads no memory and uses no stack (only the abort
    path has a frame; the premise makes it dead).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x12e04 `jal check_known` with
      a0 = s3 = rc, the value reac_box_pin_parse returned (0x12dfc `mv s3,a0`): 0 or -1 (2^64 - 1);
      a1 = s1 = want, fuzz_catalogue_row's result (0x12e70 `mv s1,a0`) or 0 (0x12db4 `mv s1,zero`).
    Why the premise holds there: as in the plain build (lib/Prog/check_known_c.v), with U's
    reac_box_pin_parse_contract and fuzz_catalogue_row_contract and pin_spec.harness_known. *)
Definition CHECK_KNOWN : Z := 0x12eb8.

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
