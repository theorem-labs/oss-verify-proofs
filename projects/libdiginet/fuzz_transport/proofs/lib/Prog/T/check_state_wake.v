(* check_state_wake (fuzz/fuzz_transport.c:507-515), entry 0x15138:
     0x15138 auipc a0, 0x1d           a0 = 0x32138
     0x1513c lw    a0, 1648(a0)       a0 = M.foreign (0x327a8 = W_BASE_PLAIN + A_M_foreign), sign-extended
     0x15140 bnez  a0, 0x15148        M.foreign <> 0: the abort path
     0x15144 ret
     0x15148 addi sp, sp, -16; sd ra, 8(sp); jal abort
   The model premise check_state_wake_m B = Some (B', tt) gives M_foreign B = 0 and B' = B, so the branch falls
   through to the ret and the abort path is never reached: no callee contract is needed. The load is the world
   hook's (WMem.v): it reads s32_at B 24 = M_foreign B. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem check_state_wake_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_state_wake_holds : check_state_wake_contract.
Proof.
  unfold check_state_wake_contract, check_state_wake_ENTRY, check_state_wake_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' WM HM SPA ST LO WOS MI.
  unfold check_state_wake_m, truth in HM.
  destruct (Z.eqb_spec (M_foreign B) 0) as [HF|HF]; cbn [negb] in HM; [|discriminate HM].
  injection HM as HB. subst B'.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  step.                                   (* auipc a0, 0x1d *)
  step.                                   (* lw a0, 1648(a0): a0 = Z_to_bv 64 (s32_at B 24) *)
  change (s32_at B 24) with (M_foreign B). rewrite HF.
  step.                                   (* bnez a0: M.foreign = 0, falls through *)
  if_false.
  step.                                   (* ret *)
  apply evt_done. do 16 eexists. split; [reflexivity|].
  exact (conj MU (conj WMO (conj MI (conj ST (conj eq_refl WM))))).
Qed.
