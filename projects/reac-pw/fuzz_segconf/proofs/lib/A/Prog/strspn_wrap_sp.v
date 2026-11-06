From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import asan_memcpy_bz.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strspn_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strspn.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strspnw.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_memcpy_bz.
Module SPc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strspn_c.
Module SPp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strspn.
Module BzSp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strspnw.

Lemma sp_proof : BzSp.strspn_stmt.
Proof.
  unfold BzSp.strspn_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str set lo can
    STR SNZ SET CNZ GOT CAN ST LOS SEPS SEPC SEPG SEPK MI.
  pose proof ST as (L0 & HH & SA).
  destruct (SA (bv_unsigned sp - 1) ltac:(lia)) as (W & _).
  assert (SPT : bv_unsigned (BzM.wa (bv_unsigned sp - 1)) < BzM.UTOP) by exact (BzM.wview_below BzI.asegs m _ MI W).
  rewrite BzM.wa_unsigned in SPT by lia.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (SPc.strspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str set lo m)).
  - exact (SPp.strspn_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str set lo can STR SNZ SET CNZ GOT CAN ST LOS SEPS SEPC SEPG SEPK (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [exact MU|]. split; [exact WM|]. split; [|exact ST'].
    apply BzM.mem_inv_intro; [intros x; exact (BzM.mem_inv_seg_below _ _ _ MI)|].
    intros x b Hx. split; [exact (MI' x b Hx)|].
    destruct (Z_lt_le_dec (bv_unsigned x) BzM.UTOP) as [L|L]; [exact L|].
    rewrite (MU x) in Hx by (cbn [outside]; repeat split; lia).
    exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
Qed.
