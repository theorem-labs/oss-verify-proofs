From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c memset_c reac_disco_gate_init_c.
Import ListNotations.
Open Scope Z_scope.

Lemma gate0_ok : gate_ok (repeat (zb 0) 264).
Proof.
  assert (G : gn (repeat (zb 0) 264) = 0) by (vm_compute; reflexivity).
  split; [reflexivity |]. rewrite G. split; [lia |]. intros i j _ Hj. lia.
Qed.

Theorem reac_disco_gate_init_holds : memset_contract -> reac_disco_gate_init_contract.
Proof.
  intros MEMS. unfold reac_disco_gate_init_contract, REAC_DISCO_GATE_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g junk
         E HK HMI.
  pose proof (rw_cells_bound rsegs m g [CB 264 junk] HK) as HB. cbn [cells_size csize] in HB.
  assert (U0 : bv_unsigned a0 = g) by (subst a0; apply unsigned_lit; lia).
  assert (U264 : bv_unsigned (Z_to_bv 64 264) = 264) by reflexivity.
  assert (U0b : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  step. step. step.
  eapply evt_cut.
  { eapply MEMS; [ rewrite U0, U264; exact HK | exact HMI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & MU & WM & MI & RC).
  subst ms'. apply evt_done. cbv beta.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity |].
  rewrite U0, U264 in MU. rewrite U0, U264, U0b in RC.
  split; [exact MU |]. split; [exact WM |]. split; [exact MI |]. split; [| exact gate0_ok].
  exact RC.
Qed.
