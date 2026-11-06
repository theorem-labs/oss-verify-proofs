From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition FUZZ_ALLOC_FAIL : Z := 0x14268.
Definition G_COUNT : Z := 0x33460.
Definition G_FAIL_AT : Z := 0x231e0.

Definition fail_at_of (count k : word) : word :=
  if bv_unsigned count + bv_unsigned k <? 2^64 then Z_to_bv 64 (bv_unsigned count + bv_unsigned k)
  else Z_to_bv 64 (2^64 - 1).

Definition fuzz_alloc_fail_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (count : word),
    bytes_at rsegs m G_COUNT (le8 count) ->
    wr_at rsegs m G_FAIL_AT 8 ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (fail_at_of count a0) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' G_FAIL_AT (le8 (fail_at_of count a0)) /\
         munch [(G_FAIL_AT, G_FAIL_AT + 8)] m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ALLOC_FAIL) fc None m (seg_rom rsegs)).
