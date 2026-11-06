From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_qdisc.c:89-102 (312 bytes at 0x12ac8 in the plain image;
    frame 80 bytes). The same form as libreac/fuzz_knock's released knock_main_contract (its
    Prog/LLVMFuzzerTestOneInput_c.v), so the slot proof ports. *)
Definition LLVM_QDISC : Z := 0x12ac8.
Definition LLVM_QDISC_STACK : Z := 80.

Definition qdisc_main_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (data : list byte),
    bytes_at rsegs m (bv_unsigned a0) data ->
    bv_unsigned a1 = Z.of_nat (length data) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + LLVM_QDISC_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (bv_unsigned a0 + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    bv_unsigned a0 + Z.of_nat (length data) < 2 ^ 63 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - LLVM_QDISC_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LLVM_QDISC) fc None m (seg_rom rsegs)).
