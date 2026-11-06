(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1, first piece: text_of's return
   (0x13fb8, cut c1_13fb8) to kernel's return (0x13fc4, cut c1b1_13fc4).
   0x13fb8 mv s5, a0 (the alias s); 0x13fbc addi a0, sp, 0x40; 0x13fc0 jal kernel (0x14190, ra 0x13fc4). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib LC1B1KM.
Local Open Scope Z_scope.

Section K.
Hypothesis KERNEL_OK : kernel_contract.

Lemma c1b1_seg_K : forall E i gp own ms, lenv_ok E -> c1_13fb8 E i gp own ms ->
  evt rsegs (eqv_cl (c1b1_13fc4 E i gp own (ms_mem ms))) ms.
Proof.
  intros E i gp own ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m &
    P & N & kbs & mbs & gbs & nb & s & t & sl & -> & FRM & Hi & Hnb & HN & HL & HC & HO & HOS & HA & MI & TM & ST).
  cbn [ms_mem].
  destruct (c1b1_lenv E HE) as (S1 & S2 & _).
  unfold wz, C1_TEXT_OF_RA, SLOT_FRAME.
  step. step. step.
  eapply (leaf_call_eqv KERNEL 4416 c1b1_kP c1b1_kW c1b1_kQ) with (lo := e_S E - SLOT_STACK_Z).
  - exact (c1b1_kok KERNEL_OK).
  - eapply c1b1_kpre; [exact HE | exact HL | exact HC | exact MI | |].
    + rewrite c1b1_spZ. rewrite unsigned_lit by lia. unfold SLOT_FRAME. lia.
    + rewrite c1b1_arg0. rewrite unsigned_lit by lia. unfold SLOT_FRAME, FO_P. lia.
  - exact MI.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. unfold SLOT_STACK_Z. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (regs' & _ & PO) MU WM MI' ST'.
    lazymatch type of PO with c1b1_kQ ?R _ _ _ => set (RR := R) in * end.
    assert (HA0 : arg RR 0 = e_S E - SLOT_FRAME + FO_P)
      by (unfold RR; rewrite c1b1_arg0; rewrite unsigned_lit by lia; unfold SLOT_FRAME, FO_P; lia).
    rewrite unsigned_lit in MU, ST' by lia.
    destruct (c1b1_kpost E i P N kbs mbs gbs m m' own s t sl RR regs' m (e_S E - 480) HE HL HC HO HA TM
                (seg_fp_refl _ _ _) eq_refl HA0 PO MU WM)
      as (P' & N' & kbs' & HL' & NX & HN' & HC' & HO' & HA' & TM' & SF').
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end.
    apply evt_eqv_done. unfold c1b1_13fc4.
    exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s3, s4, t3', t4', t5', t6', F, fc, m',
      P', N', kbs', mbs, gbs, nb, s, t, sl.
    split; [reflexivity|].
    refine (conj FRM (conj Hi (conj Hnb (conj HN' (conj HL' (conj NX (conj HC' (conj HO' (conj HOS (conj HA'
      (conj MI' (conj TM' (conj ST' SF'))))))))))))).
Qed.

End K.
