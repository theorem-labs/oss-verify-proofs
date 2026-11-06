From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_rate(rc, hz, want) (fuzz_rate.c:143-157; 28 bytes, 7 instructions at 0x145c8 in the plain image):
      0x145c8 addi a3,zero,1; bne a0,a3,0x145d8; bne a1,a2,0x145d8; ret;
      0x145d8 addi sp,sp,-16; sd ra,8(sp); jal abort (0x160bc).
    The same seven instructions as reac-pw/fuzz_role's check_role (elfdis --diff level 3, both builds), so this is
    role's text with rate's addresses.
    When a0 = 1 and a1 = a2, all three as 64-bit words, neither branch is taken and it returns at once. On that
    path it writes a3 := 1 (the addi), stores nothing, reads no memory and uses no stack (only the abort path,
    0x145d8, has a frame; the premises make it dead).

    Call site (LLVMFuzzerTestOneInput, plain): 0x143c0 `jal check_rate`, on the branch of the inlined expect_rate
    that answers 1 (fuzz_rate.c:258-259), with
      a0 = s4 = rc (0x143bc `mv a0,s4`), the value reac_rate_prop_parse returned;
      a1 = hz (0x143b8 `lw a1,0x158(sp)`): the 4-byte hz cell of the harness frame, sign-extended (lw, not lwu);
      a2 = want, sign-extended (lw, not lwu): on the Float path the 4-byte want cell expect_rate wrote (0x143ac
           `lw a2,0xb8(sp)`); on the Int path the rate entry's Int value, pod_int's i (fuzz_rate.c:76-77), read
           without a store to the cell (0x14358 `lw a2,8(a0)`, then 0x1435c `j 0x143b0` past 0x143ac).
    Why the premises hold there is main's M02 segment (Prog/Seg/M02.v): rate_prop_parse_contract returns
    a0 = Z_to_bv 64 1 and leaves hz = want on that branch, so a0 = 1 and a1 = a2 as 64-bit words. *)
Definition CHECK_RATE : Z := 0x145c8.

Definition check_rate_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 = 1 ->
    a1 = a2 ->
    evt rsegs
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 1) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_RATE) fc None m (seg_rom rsegs)).
