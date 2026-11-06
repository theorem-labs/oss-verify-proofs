(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1, third piece: the entry of
   model_write (0x15c50, cut c1b1_15c50) to its return (0x13ff8, cut c1_13ff8): a0 = the model's answer
   w_rc (c1_wm nb t kbs), the model block holding its requests. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib LC1B1WM.
Local Open Scope Z_scope.

Section W.
Hypothesis MODEL_WRITE_OK : model_write_contract.

Lemma c1b1_seg_W : forall E i gp own m0 ms, lenv_ok E -> c1b1_15c50 E i gp own m0 ms ->
  evt rsegs (eqv_cl (fun c => c1_13ff8 E i gp own c /\ seg_fp (e_S E) (c1_hp E) m0 (ms_mem c))) ms.
Proof.
  intros E i gp own m0 ms HE H.
  destruct H as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s3 & t3 & t4 & t5 & t6 & F & fc & m & P & N & kbs & mbs &
    gbs & nb & s & t & sl & -> & FRM & Hi & Hnb & HN & HL & NS & ER & EK & HC & HO & HOS & HA & MI & TM & ST & HF).
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  pose proof HL as HL0.
  apply c1b1_lh_split in HL0. destruct HL0 as ((_ & _ & _ & GN & OD & _) & _).
  destruct (c1b1_sel m nb Hnb GN OD) as (_ & SB & _).
  pose proof HA as (_ & A2 & _).
  pose proof (bytes_at_bound rsegs _ _ _ A2) as AB.
  assert (USP : bv_unsigned (wz (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (HA0 : forall x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31 : word,
            arg (mkR x1 (wz (e_S E - SLOT_FRAME)) x3 x4 x5 x6 x7 x8 x9 (wz (e_md E)) x11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) 0 = e_md E)
    by (intros; rewrite c1b1_arg0; apply unsigned_lit; lia).
  assert (HA1 : forall x1 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31 : word,
            arg (mkR x1 (wz (e_S E - SLOT_FRAME)) x3 x4 x5 x6 x7 x8 x9 x10 (wz (sel_ptr nb)) x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) 1 = sel_ptr nb)
    by (intros; rewrite c1b1_arg1; apply unsigned_lit; lia).
  assert (HA2 : forall x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31 : word,
            arg (mkR x1 (wz (e_S E - SLOT_FRAME)) x3 x4 x5 x6 x7 x8 x9 x10 x11 (wz s) x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) 2 = s)
    by (intros; rewrite c1b1_arg2; apply unsigned_lit; rewrite length_app in AB; cbn [length] in AB; lia).
  assert (HSP : forall x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31 : word,
            spZ (mkR x1 (wz (e_S E - SLOT_FRAME)) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) = e_S E - SLOT_FRAME)
    by (intros; rewrite c1b1_spZ; exact USP).
  eapply (leaf_call_eqv MODEL_WRITE 704 c1b1_mP c1b1_mW c1b1_mQ) with (lo := e_S E - SLOT_STACK_Z).
  - exact (c1b1_mok MODEL_WRITE_OK).
  - eapply c1b1_mwpre; [exact HE | exact HL | exact Hnb | exact HA | apply HSP | apply HA0 | apply HA1 | apply HA2].
  - exact MI.
  - rewrite USP. exact ST.
  - rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia.
  - rewrite USP. unfold SLOT_FRAME. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (regs' & EQR & PO) MU WM MI' ST'.
    rewrite USP in MU, ST'.
    destruct (c1b1_mwpost E i P N kbs mbs gbs m m' nb s t sl own m0 _ regs' (e_S E - SLOT_FRAME) HE HL Hnb ER EK
                HC HO HA TM HF eq_refl (HA0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (HA1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (HA2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) PO MU WM)
      as (mbs' & R10 & HL' & RQ & NRQ & HC' & HO' & HA' & TM' & SF').
    rewrite (EQR _), c1b1_getr10 in R10. subst a0'.
    replace (ret_pc (wz C1_MW_RA)) with (wz C1_MW_RA)
      by (symmetry; apply ret_pc_even; [unfold C1_MW_RA; lia | reflexivity]).
    apply evt_eqv_done. split.
    + unfold c1_13ff8.
      exists ra', t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', s3, t3', t4', t5', t6', F, fc, m', P, N, kbs, mbs',
        gbs, nb, s, t, sl.
      split; [reflexivity|].
      refine (conj FRM (conj Hi (conj Hnb (conj HN (conj HL' (conj NS (conj RQ (conj NRQ (conj HC' (conj HO'
        (conj HOS (conj HA' (conj MI' (conj TM' ST')))))))))))))).
    + cbn [ms_mem]. exact SF'.
Qed.

End W.
