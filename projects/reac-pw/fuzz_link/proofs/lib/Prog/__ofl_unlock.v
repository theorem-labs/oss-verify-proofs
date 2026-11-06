From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel __unlock_c __ofl_unlock_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __ofl_unlock_holds : __unlock_contract -> __ofl_unlock_contract.
Proof.
  intros HUNLOCK. unfold __ofl_unlock_contract, OFL_UNLOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [_ [_ HL]].
  unfold A_OFL_LOCK, wz in HL.
  step. step. step.
  eapply evt_cut.
  { eapply HUNLOCK with (w := 0); [ | lia].
    rewrite unsigned_lit by lia. exact HL. }
  intros ms' [a1' ->]. apply evt_done. eexists _, _. reflexivity.
Qed.
