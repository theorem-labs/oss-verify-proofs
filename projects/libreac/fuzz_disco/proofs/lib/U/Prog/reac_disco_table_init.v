From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c memset_c reac_disco_table_init_c.
Import ListNotations.
Open Scope Z_scope.

Lemma zero_table_ok : table_ok zero_table.
Proof.
  assert (N0 : n_of zero_table = 0) by (vm_compute; reflexivity).
  unfold table_ok, tbl_T1, tbl_T2, tbl_T3, tbl_T4. rewrite N0.
  split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. intros; lia.
Qed.

Theorem reac_disco_table_init_holds : memset_contract -> reac_disco_table_init_contract.
Proof.
  intros MSC. unfold reac_disco_table_init_contract, REAC_DISCO_TABLE_INIT. unfold MEMSET in MSC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    t junk -> Ht0 Ht8 RW MI.
  pose proof (rw_cells_bound rsegs m t _ RW) as TB. cbn in TB.
  do 3 step.
  eapply evt_mono.
  { eapply MSC with (junk := junk).
    - rewrite (unsigned_lit t) by lia. exact RW.
    - exact MI. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & RW').
  subst ms'. rewrite (unsigned_lit t) in MU, RW' by lia.
  exists t0', t1', t2', (Z_to_bv 64 t), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split; [exact RW'|exact zero_table_ok].
Qed.
