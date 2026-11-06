From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import FloatExact RcBraid.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BRAID_ENCODE : Z := 0x161d0.
Definition REAC_BRAID_ENCODE_FRAME : Z := 112.

Definition reac_braid_encode_exact_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (a N P ns : Z) (Q : Z -> Z) (V K : Z -> Z -> Z),
    a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 N -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 ns ->
    2 <= N <= 127 -> N mod 2 = 0 -> 1 <= ns <= 12 ->
    frm0 fc -> mem_inv rsegs m ->
    stk rsegs m (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) ->
    0 < a -> a + 3 * N * ns <= 2^64 -> wr_at rsegs m a (3 * N * ns) ->
    0 < P -> P mod 8 = 0 -> P + 8 * N <= 2^64 ->
    (forall ch, 0 <= ch < N -> bytes_at rsegs m (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) ->
    (forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64) ->
    (forall s ch, 0 <= s < ns -> 0 <= ch < N ->
       bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch)) ->
    (a + 3 * N * ns <= P \/ P + 8 * N <= a) ->
    (forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a) ->
    (a + 3 * N * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= a) ->
    (P + 8 * N <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= P) ->
    (forall ch, 0 <= ch < N ->
       Q ch + 4 * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= Q ch) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
         munch [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) /\
         (forall x : word, outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] (bv_unsigned x) ->
            m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BRAID_ENCODE) fc None m (seg_rom rsegs)).
