From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Open Scope Z_scope.

Definition CHECK_SHAPE_DONE : Z := 0x145e0.
Definition G_NOUT : Z := 0x31000.

Definition check_shape_done_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m G_NOUT (le8 a0) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m (seg_rom rsegs)).
