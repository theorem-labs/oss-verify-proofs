From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step Cells.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import memset_c reac_headamp_tx_init_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_headamp_tx_init_holds : memset_contract -> reac_headamp_tx_init_contract.
Proof.
  intros MEMSET_OK.
  unfold reac_headamp_tx_init_contract, REAC_HEADAMP_TX_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t junk -> Ht HR HI.
  zstep. zstep. zstep.
  assert (E1 : bv_unsigned (Z_to_bv 64 t) = t) by (apply unsigned_lit; exact Ht).
  assert (E2 : bv_unsigned (Z_to_bv 64 460) = 460) by reflexivity.
  assert (E3 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  eapply evt_mono.
  - eapply (MEMSET_OK ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 0) (Z_to_bv 64 460) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk).
    + rewrite E1, E2. exact HR.
    + exact HI.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI & RW).
    rewrite E1, E2, E3 in *.
    do 15 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    exact RW.
Qed.
