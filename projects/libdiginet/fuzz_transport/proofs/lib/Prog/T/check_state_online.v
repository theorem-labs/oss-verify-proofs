(* check_state_online, entry 0x1598c: auipc a0,0x1d; addi a0,a0,-508 (a0 = &M = W_BASE_PLAIN); lw a1,16(a0)
   (M.e2_acked); beqz a1,0x159a8; lw a0,20(a0) (M.e1_us); beqz a0,0x159a8; ret; then the abort path at 0x159a8
   (addi sp,sp,-16; sd ra,8(sp); jal abort). The two lw are world loads: the WMem hook rewrites them to
   s32_at B 16 = M_e2_acked B and s32_at B 20 = M_e1_us B. The model premise gives both nonzero, so each beqz falls
   through and the abort path is closed by exfalso. No store, no call: the memory is unchanged, so munch, wmono,
   mem_inv, stk and wmem hold of m. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem check_state_online_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_state_online_holds : check_state_online_contract.
Proof.
  unfold check_state_online_contract, check_state_online_ENTRY, check_state_online_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' WM HM Hsp ST LO WS MI.
  (* the model: M.e2_acked <> 0, M.e1_us <> 0, B' = B (fuzz_transport.c:503-504) *)
  unfold check_state_online_m, truth in HM.
  destruct (M_e2_acked B =? 0) eqn:E2; cbn [negb orb] in HM; [discriminate HM|].
  destruct (M_e1_us B =? 0) eqn:E1; cbn [negb orb] in HM; [discriminate HM|].
  injection HM as <-. apply Z.eqb_neq in E2. apply Z.eqb_neq in E1.
  change (M_e2_acked B) with (s32_at B 16) in E2. change (M_e1_us B) with (s32_at B 20) in E1.
  pose proof (s32_range B 16) as R2. pose proof (s32_range B 20) as R1.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  step.                                   (* 0x1598c auipc a0, 0x1d *)
  step.                                   (* 0x15990 addi a0, a0, -508: a0 = 0x32790 *)
  step.                                   (* 0x15994 lw a1, 16(a0): a1 = s32_at B 16 *)
  step.                                   (* 0x15998 beqz a1, 0x159a8 *)
  (* the taken branch (to the abort path) needs M.e2_acked = 0: closed by exfalso *)
  if_cases K; zify_cond K; try (exfalso; first [ lia | (Z.div_mod_to_equations; lia) ]).
  step.                                   (* 0x1599c lw a0, 20(a0): a0 = s32_at B 20 *)
  step.                                   (* 0x159a0 beqz a0, 0x159a8 *)
  (* the taken branch needs M.e1_us = 0: closed by exfalso *)
  if_cases K'; zify_cond K'; try (exfalso; first [ lia | (Z.div_mod_to_equations; lia) ]).
  step.                                   (* 0x159a4 ret *)
  apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|]. split; [reflexivity|exact WM].
Qed.

Print Assumptions check_state_online_holds.
