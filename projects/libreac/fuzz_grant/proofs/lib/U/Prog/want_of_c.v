From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel.
Open Scope Z_scope.

Definition WANT_OF : Z := 0x13e34.

Definition want (WS VS : list byte) (ch p : Z) : Z :=
  if tb WS (3 * ch + p) =? 0 then dflt p else tb VS (3 * ch + p).

Definition want_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w v ch p : Z) (WS VS : list byte),
    a0 = Z_to_bv 64 w -> a1 = Z_to_bv 64 v -> a2 = Z_to_bv 64 ch -> a3 = Z_to_bv 64 p ->
    0 <= ch < 48 -> 0 <= p < 3 ->
    length WS = 144%nat -> bytes_at rsegs m w WS ->
    length VS = 144%nat -> bytes_at rsegs m v VS ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want WS VS ch p)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WANT_OF) fc None m (seg_rom rsegs)).
