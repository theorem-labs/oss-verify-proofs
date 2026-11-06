From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition DT1_HEAD : Z := 0x15144.

Definition dt1_head_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 + 20 <= 2^64 ->
    wr_at rsegs m (bv_unsigned a0) 20 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_bytes (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3))
         /\ munch [(bv_unsigned a0, bv_unsigned a0 + 20)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DT1_HEAD) fc None m (seg_rom rsegs)).
