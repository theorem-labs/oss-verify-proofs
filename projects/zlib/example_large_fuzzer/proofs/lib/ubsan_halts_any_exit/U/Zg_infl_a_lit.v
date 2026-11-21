From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateA_LIT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma arm_LIT_spec : forall X w x26 x12 ms,
  ILOOP X w PC_LIT x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LIT ->
  evt usegs (fun ms' => IPOST X (arm_LIT w) ms' /\ PATG X (wof (arm_LIT w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. iarm_open HL. rewrite arm_LIT_eq.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & RHB & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & [POB POW] & PBK). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LIT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. zstep. br_cases K.
  -
    assert (Kl : ir_left r <> 0) by lia. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kl).
    do 2 zs. gT.
    rd_sub GA 108%nat 0%nat 1%nat. zs. clear RD.
    do 3 zs.
    assert (RLEN : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
    pose proof (u8arr_store_ok usegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(rewrite LOB; lia) eq_refl) as SOK.
    zs. rewrite le1_zx8_wz by lia.
    pose proof (u8arr_write usegs _ _ _ (ir_put r) (Z_to_bv 8 (wrap8 (is_length s))) OUT ltac:(rewrite LOB; lia)) as OUT2. clear OUT LOB.
    store_done.
    rewrite iout_bytes_store in OUT2 by lia.
    pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) (ir_put r + 1) ltac:(lia)) as LOB.
    apply (f_equal Z.of_nat) in LOB.
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; try ireg.
      apply IMEM_intro; ired.
      * exists j0, jf. replace (ir_left r + -1) with (wrap32 (ir_left r - 1)) in FRM by (rewrite wrap32_id by lia; lia). exact FRM.
      * exact STK.
      * exact ZS.
      * constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT2.
      * eassumption.
      * exact MU.
      * exact WM.
    + cbn [wof]. destruct POW as (POW & POL & _ & PHW). unfold PATG, OBYT. ired. rewrite arr_len_set.
      destruct Pfl as [Pf|(Pf & [E|E] & _)]; [|rewrite HM in E; discriminate E ..].
      repeat (split; [first [assumption | left; assumption | unfold LEN, FLAGS, HCRC; lia]|]).
      split; [| revert PBK; bk_keep].
      split; [|split; [exact POW|split; [rewrite wrap32_id by lia; lia| split; [reflexivity| exact PHW]]]]. intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
      * rewrite arr_get_set_same by lia. pose proof (wrap8_range (is_length s)) as H8. change (2^8) with 256 in H8. exact H8.
      * rewrite arr_get_set_other by lia. apply POB. lia.
  -
    assert (Kl : ir_left r = 0) by lia. replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 5 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
    apply IMEML_intro; ired.
    + exists (wz (ir_ret r)), j0, jf. unfold iframe_cells. rewrite Kl. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.
Lemma arm_LIT_ok : forall flush, arm_stmtg flush LIT PC_LIT arm_LIT.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (arm_LIT_spec X w _ x12 ms HL XO HW HP HM). Qed.
