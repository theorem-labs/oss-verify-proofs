From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel mseek_c fflush_c.
Import ListNotations.
Open Scope Z_scope.

Theorem fflush_holds : mseek_contract -> fflush_contract.
Proof.
  intros HMS. unfold fflush_contract, FFLUSH, FFLUSH_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b Fc
    fl md q rb pv nx HM HN [HGOT [g HGD]] MI ST LO HLO HB HOH.
  destruct HM as (buf & (pad0 & pad1 & pad2 & ung & HC & Lung & Lbuf & Hh0 & Hh16) & Hq & HRB & HFc & Hb0 & Hbh).
  unfold mfile_cells in HC.
  unfold A_GOT_GUARD, A_GUARD, A_OFL_HEAD, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK, wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 1304)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 32%nat ST.
  do 6 step. if_false.
  do 3 step. if_true.
  do 4 step. if_true.
  do 3 step.
  destruct rb as [[i e]|].
  - destruct HRB as (Hie & He & Hr & HFcf).
    cbn [rpos_of rend_of] in HC |- *. unfold wz in HC |- *.
    destruct (Z.eq_dec i e) as [<- | Hne].
    + if_true.
      do 7 step. if_true. do 5 step. release_frame FR ST (bv_unsigned sp). do 2 step.
      apply evt_done. unfold fflush_post, FFLUSH_K. do 16 eexists. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * reflexivity.
      * exact MU.
      * exact WM.
      * exact MI.
      * exact ST.
      * unfold mfile; cbv zeta; exists buf.
        refine (conj _ (conj _ (conj I (conj HFc (conj Hb0 Hbh))))).
        -- unfold mfile_raw, mfile_cells, rpos_of, rend_of, wz. exists pad0, pad1, pad2, ung.
           refine (conj _ (conj Lung (conj Lbuf (conj Hh0 Hh16)))).
           cbn [rlen]. replace (q - (i - i)) with q by lia. exact HC.
        -- cbn [rlen]. lia.
    + assert (C : bv_eqb (Z_to_bv 64 (bv_unsigned a0 + 280 + i)) (Z_to_bv 64 (bv_unsigned a0 + 280 + e)) = false)
        by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
      rewrite C; cbv iota.
      do 5 step.
      assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HRAW : mfile_raw mm (bv_unsigned a0) b (Z.of_nat (length Fc)) fl (Z_to_bv 64 (bv_unsigned a0 + 280 + i))
                         (Z_to_bv 64 (bv_unsigned a0 + 280 + e)) md q pv nx buf)
          by (unfold mfile_raw; exists pad0, pad1, pad2, ung; exact (conj HC (conj Lung (conj Lbuf (conj Hh0 Hh16)))));
        eapply evt_cut;
        [ eapply HMS with (lo := lo) (r := e - i);
          [ exact HRAW | lia | lia | lia
          | unfold wz; rewrite !unsigned_lit by lia; f_equal; lia
          | reflexivity
          | unfold guard_ok, A_GOT_GUARD, A_GUARD, wz; split; [exact HGOT | exists g; exact HGD]
          | exact MI
          | rewrite U; exact ST
          | rewrite U; unfold MSEEK_K; lia
          | lia
          | unfold A_OFL_HEAD; lia ]
        | ]
      end.
      clear HRAW.
      intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & EA0 & MUc & WMc & MIc & STc & HRAW').
      subst ms'.
      unfold MSEEK_K in MUc. rewrite U in MUc, STc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m' MUc WMc end.
      clear MUc WMc MI. rename MIc into MI. rename STc into ST.
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      destruct HRAW' as (pad0' & pad1' & pad2' & ung' & HC' & Lung' & Lbuf' & _ & _).
      unfold mfile_cells, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK, wz in HC'.
      do 7 step. if_true. do 5 step. release_frame FR ST (bv_unsigned sp). do 2 step.
      apply evt_done. unfold fflush_post, FFLUSH_K. do 16 eexists. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * reflexivity.
      * exact MU.
      * exact WM.
      * exact MI.
      * exact ST.
      * unfold mfile; cbv zeta; exists buf.
        refine (conj _ (conj _ (conj I (conj HFc (conj Hb0 Hbh))))).
        -- unfold mfile_raw, mfile_cells, rpos_of, rend_of, wz. exists pad0', pad1', pad2', ung'.
           refine (conj _ (conj Lung' (conj Lbuf' (conj Hh0 Hh16)))).
           cbn [rlen]. exact HC'.
        -- cbn [rlen]. lia.
  - cbn [rpos_of rend_of] in HC |- *. unfold wz in HC |- *.
    if_true.
    do 7 step. if_true. do 5 step. release_frame FR ST (bv_unsigned sp). do 2 step.
    apply evt_done. unfold fflush_post, FFLUSH_K. do 16 eexists. split; [reflexivity|].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    * reflexivity.
    * exact MU.
    * exact WM.
    * exact MI.
    * exact ST.
    * unfold mfile; cbv zeta; exists buf.
      refine (conj _ (conj _ (conj I (conj HFc (conj Hb0 Hbh))))).
      -- unfold mfile_raw, mfile_cells, rpos_of, rend_of, wz. exists pad0, pad1, pad2, ung.
         refine (conj _ (conj Lung (conj Lbuf (conj Hh0 Hh16)))).
         cbn [rlen]. replace (q - 0) with q by lia. exact HC.
      -- cbn [rlen]. lia.
Qed.
