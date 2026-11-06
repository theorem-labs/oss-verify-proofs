From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.write_uint_c(write_uint_D, write_uint_n).
Import ListNotations.
Open Scope Z_scope.

Definition WRITE_UINT : Z := 0x14e5c.

Definition write_uint_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v lo : Z),
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 v -> 0 <= v < 65536 ->
    wr_at rsegs m o (write_uint_n v) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    (o + write_uint_n v <= bv_unsigned sp - 16 \/ bv_unsigned sp <= o) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (write_uint_n v)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp); (o, o + write_uint_n v)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' o (write_uint_D v))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WRITE_UINT) fc None m (seg_rom rsegs)).
