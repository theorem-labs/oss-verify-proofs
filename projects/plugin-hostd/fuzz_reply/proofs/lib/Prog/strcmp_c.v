From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition STRCMP : Z := 0x1d474.

Definition strcmp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sx sy : list byte),
    bytes_at rsegs m (bv_unsigned a0) (sx ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sx ->
    bytes_at rsegs m (bv_unsigned a1) (sy ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sy ->
    evt rsegs
      (fun ms' => exists r x11 x12 x13 : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs)
         /\ (r = Z_to_bv 64 0 <-> sx = sy))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRCMP) fc None m (seg_rom rsegs)).
