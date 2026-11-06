From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import ListNotations.
Open Scope Z_scope.

Definition PUT_DEC : Z := 0x1416c.
Definition PUT_DEC_FRAME : Z := 16.

Definition put_dec_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b p v mn : Z) (N : word),
    a0 = Z_to_bv 64 b ->
    0 <= b ->
    a1 = Z_to_bv 64 p ->
    bv_unsigned a2 mod 2^32 = v ->
    (bv_unsigned a2 < 2^32 \/ 10 <= v) ->
    a3 = Z_to_bv 64 mn ->
    0 <= mn <= 10 ->
    bytes_at rsegs m p (le8 N) ->
    wr_at rsegs m p 8 ->
    p mod 8 = 0 ->
    wr_at rsegs m (b + bv_unsigned N) (dec_len v mn) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + PUT_DEC_FRAME <= bv_unsigned sp ->
    (p + 8 <= b + bv_unsigned N \/ b + bv_unsigned N + dec_len v mn <= p) ->
    (p + 8 <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= p) ->
    (b + bv_unsigned N + dec_len v mn <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= b + bv_unsigned N) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - PUT_DEC_FRAME, bv_unsigned sp); (p, p + 8);
                (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (b + bv_unsigned N) (DEC v mn) /\
         bytes_at rsegs m' p (le8 (Z_to_bv 64 (bv_unsigned N + dec_len v mn))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PUT_DEC) fc None m (seg_rom rsegs)).
