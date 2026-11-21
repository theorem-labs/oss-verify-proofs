(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateA_TYPE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_TYPEDO_NB : Z := 0x1f87c.
Definition PC_TYPEDO_J : Z := 0x1f8bc.
Lemma typedo_nb3 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_TYPEDO_NB x26 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> ir_bits r < 8 ->
  evt usegs (NBJ X s c r 3 PC_TYPEDO_J x26) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_TYPEDO_NB. ix_open XO.
  do 2 zs. br_cases K.
  -
    apply evt_done. left. exists r, (wz 2). split; [|split].
    + rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + left. split; [reflexivity| lia].
    + eapply ILOOP_intro; ired; [ireg .. |]. exact HMEM.
  - zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 2 zs. gT.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * right. split; [reflexivity| lia].
      * eapply ILOOP_intro; pullr_rw c r; ired; [ireg .. |].
        eapply IMEM_regs; [exact HMEM| reflexivity..].
    +
      do 4 zs.
      apply evt_done. right. exists r. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.
Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma typedo_core : forall flush X w x26 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPEDO x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> (is_mode (w_s w) = TYPE \/ is_mode (w_s w) = TYPEDO) ->
  evt usegs (fun ms' => IPOST X (arm_TYPEDO ivar_ref flush w) ms' /\ PATG X (wof (arm_TYPEDO ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] x26 x12 ms EF RF HL XO HW HP HM.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  assert (MFB : ir_bits r < 8).
  { destruct HM as [E|E]; rewrite E in HMF; unfold MF in HMF; cbn in HMF; destruct HMF as [_ H]; exact H. }
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0).
  { destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; destruct HM as [E'|E']; rewrite E' in E; discriminate E. }
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  destruct (Z.eq_dec (is_last s) 0) as [L0|L1].
  2:{
      rewrite (arm_TYPEDO_last flush s c r L1).
      assert (L1' : is_last s = 1) by (destruct PL; [contradiction| assumption]).
      clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HM HREGS.
      iarm_open HL. ix_open XO.
      pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
      pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
      open_IST ST. open_isA GA. open_izs ZS. ifineS m.
      unfold PC_TYPEDO. zs. rewrite L1'. zs. br_false.
      do 6 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by (pose proof (land7_range (ir_bits r)); lia).
      rewrite land_m8_u64 by lia. pose proof (land7_le (ir_bits r) ltac:(lia)) as L7.
      itr_groups MUf WMf.
      apply evt_done. split.
      - cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      - cbn [wof]. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold CHECK, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep].
        exact HISR. }
  eapply evt_cut.
  { destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_TYPEDO. zs. rewrite L0. zs. br_true.
    eapply (typedo_nb3 X s c r x26); [eapply ILOOP_intro; ired; [ireg .. | exact HMEM] | exact XO | exact HREGS | exact HP | exact MFB]. }
  intros ms1 [(r1 & x12' & EN & HR1 & HJ)|(r1 & EN & HR1 & HLV)].
  2:{
      rewrite (arm_TYPEDO_leave flush s c r _ L0 EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATG_regs; [exact HP| reflexivity..]]. }
  pose proof (Rin (ir_next r)) as RBy.
  assert (R1 : 3 <= ir_bits r1 < 64 /\ 0 <= ir_hold r1 < 2 ^ ir_bits r1 /\ ir_put r1 = ir_put r /\ ir_out r1 = ir_out r /\ ir_left r1 = ir_left r).
  { destruct HR1 as [[-> H3]|(-> & H1 & H2)]; [split; [lia|]; split; [exact RH|]; repeat split; reflexivity|].
    pullr_rw c r. pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
    split; [lia|]. split; [exact PR|]. repeat split; reflexivity. }
  destruct R1 as (RB1 & RH1 & EP1 & EO1 & EL1).
  rewrite (arm_TYPEDO_run flush s c r s c r1 L0 EN RB1 RH1). unfold typedo_B. cbn [w_s w_c w_r].
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  assert (RH164 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
  assert (Rv : 0 <= ir_hold r1 mod 2 ^ 1 < 2) by (apply Z.mod_pos_bound; lia).
  assert (Rt : 0 <= (ir_hold r1 / 2 ^ 1) mod 2 ^ 2 < 4) by (apply Z.mod_pos_bound; lia).
  remember (ir_hold r1 mod 2 ^ 1) as v eqn:Ev. remember ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2) as t eqn:Et.
  assert (HISR' : forall M, ISR (iset_mode (iset_last s v) M)) by (intros M; destruct HISR as [_ H2]; split; [ired; lia| exact H2]).
  assert (HISRf : ISR (iset_mode (fixedtables (iset_last s v)) LEN_)) by (destruct HISR as [_ H2]; split; [cbn; lia| exact H2]).
  clear HL RH RH1 HCORE HMF HWF HWB Rin Pfl PL PHD HR1 HM HISR EN RBy HREGS.
  iarm_open HJ. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_TYPEDO_J. do 3 zs. rewrite land1_mod, type_bits by lia. rewrite <- Ev, <- Et.
  do 3 zs. br_cases K; rewrite ?signed_wz in K by lia.
  -
    do 2 zs. br_cases K2.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      do 9 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      do 7 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TABLE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
  - zs. br_cases K2.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
      zs. zs. ustep 0x22664. ustep 0x22664. ustep 0x22664. do 9 zs.
      destruct (le8_of_bytes (le4 (wz (is_lenbits s)) ++ le4 (wz (is_distbits s))) ltac:(rewrite length_app, !length_le4; reflexivity)) as (zz & _ & Hzz).
      eapply (rw_cells_recast _ _ _
        [C8 (wz (il_S (ix_L X))); C4 (wz (is_mode s)); C4 (wz v); C4 (wz (is_wrap s)); C4 (wz 5); C4 (wz (is_havedict s)); C4 (wz (is_flags s)); C4 (wz (is_dmax s)); C4 (wz 0);
         C8 (wz (is_check s)); C8 (wz (is_total s)); C8 (wz (is_head s)); C4 (wz 15); C4 (wz (is_wbits s)); C4 (wz (is_wsize s)); C4 (wz (is_whave s)); C4 (wz (is_wnext s)); C4 (wz 0);
         C8 (wz (win_addr (ix_L X) (is_window_blk s))); C8 (wz (is_hold s)); C4 (wz (is_bits s)); C4 (wz (is_length s)); C4 (wz (is_offset s)); C4 (wz (is_extra s));
         C8 (wz 75486); C8 (wz 77534); C8 (wz zz);
         C4 (wz (is_ncode s)); C4 (wz (is_nlen s)); C4 (wz (is_ndist s)); C4 (wz (is_have s)); C8 (wz (il_As (ix_L X) + 1384 + 4 * is_next s))]) in GA.
      2:{ cbn [cells_wf cell_wf]; repeat split. }
      2:{ cbn [cells_bytes cbytes]; rewrite Hzz, <- !app_assoc; reflexivity. }
      zs.
      eapply (rw_cells_recast _ _ _
        [C8 (wz (il_S (ix_L X))); C4 (wz (is_mode s)); C4 (wz v); C4 (wz (is_wrap s)); C4 (wz 5); C4 (wz (is_havedict s)); C4 (wz (is_flags s)); C4 (wz (is_dmax s)); C4 (wz 0);
         C8 (wz (is_check s)); C8 (wz (is_total s)); C8 (wz (is_head s)); C4 (wz 15); C4 (wz (is_wbits s)); C4 (wz (is_wsize s)); C4 (wz (is_whave s)); C4 (wz (is_wnext s)); C4 (wz 0);
         C8 (wz (win_addr (ix_L X) (is_window_blk s))); C8 (wz (is_hold s)); C4 (wz (is_bits s)); C4 (wz (is_length s)); C4 (wz (is_offset s)); C4 (wz (is_extra s));
         C8 (wz 75486); C8 (wz 77534); C4 (wz 9); C4 (wz 5);
         C4 (wz (is_ncode s)); C4 (wz (is_nlen s)); C4 (wz (is_ndist s)); C4 (wz (is_have s)); C8 (wz (il_As (ix_L X) + 1384 + 4 * is_next s))]) in GA.
      2:{ cbn [cells_wf cell_wf]; repeat split. }
      2:{ cbn [cells_bytes cbytes]; rewrite le8_fixed_bits; rewrite <- !app_assoc; reflexivity. }
      do 9 zs. br_true. do 3 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN_, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISRf.
    +
      replace (t =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      do 7 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold STORED, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
Qed.
Lemma arm_TYPEDO_ok : forall flush, 0 <= flush <= 4 -> arm_stmtg flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Proof. intros flush RF X w x12 ms EF HL XO HW _ HP HM. exact (typedo_core flush X w _ x12 ms EF RF HL XO HW HP (or_intror HM)). Qed.
Lemma type_core : forall flush X w x26 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPE x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = TYPE ->
  evt usegs (fun ms' => IPOST X (arm_TYPE ivar_ref flush w) ms' /\ PATG X (wof (arm_TYPE ivar_ref flush w))) ms.
Proof.
  intros flush X w x26 x12 ms EF RF HL XO HW HP HM.
  assert (EA : arm_TYPE ivar_ref flush w = arm_TYPEDO ivar_ref flush w).
  { unfold arm_TYPE. cbn [iv_flush_exits ivar_ref andb].
    replace (flush =? Z_BLOCK) with false by (symmetry; apply Z.eqb_neq; unfold Z_BLOCK; lia).
    replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia). reflexivity. }
  rewrite EA.
  eapply (evt_cut usegs (ILOOP X w PC_TYPEDO x26 (wz 2))); [| intros ms1 H1; exact (typedo_core flush X w _ _ ms1 EF RF H1 XO HW HP (or_introl HM))].
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((j0 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_s w_c w_r] in FRM. ix_open XO.
  unfold PC_TYPE. do 3 zs. rewrite EF. if_cases K; zify_cond K; rewrite land_ones64_neg in K by lia; [clear K| exfalso; lia].
  apply evt_done. eapply ILOOP_intro; try reflexivity; [rewrite EF; reflexivity| exact HMEM].
Qed.
Lemma arm_TYPE_ok : forall flush, 0 <= flush <= 4 -> arm_stmtg flush TYPE PC_TYPE (arm_TYPE ivar_ref flush).
Proof. intros flush RF X w x12 ms EF HL XO HW _ HP HM. exact (type_core flush X w _ x12 ms EF RF HL XO HW HP HM). Qed.
