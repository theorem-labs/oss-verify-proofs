From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import memset_c reac_identity_init_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_identity_init_holds : memset_contract -> reac_identity_init_contract.
Proof.
  intros MS_OK. unfold reac_identity_init_contract, REAC_IDENTITY_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m id idb
    -> Hid HS1 MI.
  step.
  if_cases E; cbv iota; zify_cond E.
  - step.
    apply evt_done. unfold reac_identity_init_post.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m.
    split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    split; [reflexivity|]. intros H. exfalso. exact (H E).
  - destruct (HS1 E) as [_ RW].
    step. step. step.
    eapply evt_mono.
    { apply (MS_OK ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 0) (Z_to_bv 64 38) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m idb); [|exact MI].
      rewrite (unsigned_lit id) by lia. exact RW. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & RW').
    rewrite (unsigned_lit id) in MU, RW' by lia.
    change (bv_unsigned (Z_to_bv 64 38)) with 38 in MU, RW'.
    change (Z.to_nat 38) with 38%nat in RW'.
    change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW'.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [intros H; exfalso; exact (E H)|]. intros _. exact RW'.
Qed.
