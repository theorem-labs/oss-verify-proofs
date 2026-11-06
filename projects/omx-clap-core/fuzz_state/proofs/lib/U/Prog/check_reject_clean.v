From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import fuzz_alloc_live_c check_reject_clean_c.
Open Scope Z_scope.

Theorem check_reject_clean_holds : fuzz_alloc_live_contract -> check_reject_clean_contract.
Proof.
  intros FAL.
  unfold check_reject_clean_contract, CHECK_REJECT_CLEAN, CHECK_REJECT_CLEAN_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo live
    ST LO HL DL -> -> ->.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 16%nat ST.
  step. step. step.
  step. if_false.
  step. step. if_false.
  step. step.
  eapply evt_cut; [ eapply FAL; exact HL | intros ms' E; cbv beta in E; subst ms' ].
  replace (ret_pc (Z_to_bv 64 80272)) with (Z_to_bv 64 80272) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. if_false.
  step. step. step. step.
  pose proof (stk_release rsegs m1 lo _ _ ST FR ltac:(lia)) as STR.
  change (cells_size [C8 s0; C8 ra]) with 16%nat in STR.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in STR by lia.
  apply evt_done. do 15 eexists. exists m1.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|exact STR].
Qed.
