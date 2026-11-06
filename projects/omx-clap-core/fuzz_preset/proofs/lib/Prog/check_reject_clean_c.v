From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_live_c.
Open Scope Z_scope.

Definition CHECK_REJECT_CLEAN : Z := 0x13bbc.
Definition CHECK_REJECT_CLEAN_FRAME : Z := 16.
Definition CHECK_REJECT_CLEAN_EMPTY : Z := 0x10468.

Definition check_reject_clean_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc lo : Z),
    a0 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 -> rc <> 0 ->
    bytes_at rsegs m (bv_unsigned a1) (repeat (Z_to_bv 8 0) 56) ->
    bytes_at rsegs m G_LIVE (le8 a2) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_REJECT_CLEAN_FRAME <= bv_unsigned sp ->
    (bv_unsigned a1 + 56 <= bv_unsigned sp - CHECK_REJECT_CLEAN_FRAME \/ bv_unsigned sp <= bv_unsigned a1) ->
    (G_LIVE + 8 <= bv_unsigned sp - CHECK_REJECT_CLEAN_FRAME \/ bv_unsigned sp <= G_LIVE) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_REJECT_CLEAN_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REJECT_CLEAN) fc None m (seg_rom rsegs)).
