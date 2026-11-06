From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import asan_memcpy_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.stpcpy.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcpyw.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.asan_memcpy_bz.
Module SCc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy_c.
Module SCp := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy.
Module STp := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.stpcpy.
Module BzC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcpyw.

Lemma sc_proof : BzC.strcpy_stmt.
Proof.
  unfold BzC.strcpy_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack junk lo
    MI SRC NZ PAD DST ST LO0 LO OV SEPS SEPD SPT DT.
  apply AMC.evt_to_bz.
  rewrite Nat.add_1_r in DST.
  pose proof (AMC.rw_cb_of_bz _ _ _ _ DST) as DST'.
  apply (evt_mono rsegs (SCc.strcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)).
  - exact (SCp.strcpy_holds STp.stpcpy_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m str slack junk lo SRC NZ PAD DST' ltac:(lia) ST ltac:(lia) ltac:(lia) SEPD (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & RW & _).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [intros x Hx; apply MU; cbn in Hx |- *; tauto|].
    split; [exact WM|].
    split.
    + apply BzM.mem_inv_intro; [intros x; exact (BzM.mem_inv_seg_below _ _ _ MI)|].
      intros x b Hx. split; [exact (MI' x b Hx)|].
      destruct (Z_lt_le_dec (bv_unsigned x) BzM.UTOP) as [L|L]; [exact L|].
      unfold BzM.UTOP in L.
      rewrite (MU x) in Hx by (cbn [outside]; repeat split; lia).
      exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
    + split; [exact ST'|].
      rewrite Nat.add_1_r. exact (AMC.rw_cb_to_bz _ _ _ _ RW).
Qed.
