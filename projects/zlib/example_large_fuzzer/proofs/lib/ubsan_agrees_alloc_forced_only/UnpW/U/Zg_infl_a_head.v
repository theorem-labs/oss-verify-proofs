(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_adler32 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateA_HDR RefInflateA_HEAD. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_HEAD_J : Z := 0x2017c.
Definition HDQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h14 q = wz 5
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r1) /\ h26 q = wz (ir_have r1) /\ h12 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).
Definition PC_HEAD_L : Z := 0x1f438.
Definition HDL (X : ictx) (r0 r : iregs) (q : iscrh) : Prop :=
  h26 q = wz (ir_have r) /\ h11 q = wz (il_NI (ix_L X) + ir_next r) /\ h16 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h12 q = wz (ir_bits r) /\ h15 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h14 q = wz 5
  /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).
Lemma head_loop : forall f X s c r0 r q ms,
  ILOOPh X (mkW s c r) PC_HEAD_L q ms -> HDL X r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 16 -> 16 <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f 16 (mkW s c r)) PC_HEAD_J (HDQ X r0)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold HDL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E26 & E11 & E16 & E12 & E15 & E22 & E14 & E24 & E25 & E18 & E9 & E10). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  pose proof (pulled_eqs r0 r HPL0) as (PE1 & PE2 & PE3 & PE4 & PE5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_HEAD_L. ix_open XO.
  zs. br_cases K.
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 3 zs. gT. zs. zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zs. br_cases K3.
    +
      rewrite (NB_pull f 16 s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold HDL; hred; rewrite E1, E2, E5, E6; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    +
      rewrite (NB_pull f 16 s c r) by lia. rewrite (NB_done f 16 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold HDQ. hred. rewrite E1, E2, E5, E6. repeat split; ireg.
  -
    rewrite (NB_dry f 16 s c r) by lia.
    do 12 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.
Lemma head_nb16 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_HEAD x26 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_wrap s = 5 ->
  evt usegs (NBGq X s c (NEEDBITS 16 (mkW s c r)) PC_HEAD_J (HDQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP Pw.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  open_IST ST. open_isA GA. cbn [w_s] in GA.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (REGS_hold64 c r HREGS) as RH64.
  unfold PC_HEAD. ix_open XO. rewrite NB_top.
  zs. rewrite Pw. zs. br_false.
  do 2 zs. br_cases K.
  -
    rewrite (NB_done 8 16 s c r) by lia.
    do 3 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold HDQ. hred. repeat split; reflexivity.
  - do 5 zs.
    eapply (head_loop 8%nat X s c r r);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold HDL; hred; repeat split; ireg | exact XO
      | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.
Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma head_core : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_HEAD_J q ms -> HDQ X r r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_mode s = HEAD -> 16 <= ir_bits r -> ir_put r = 0 ->
  evt usegs (fun ms' => IPOST X (hd_zres s c r) ms' /\ PATG X (wof (hd_zres s c r))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP HM HB16 HPUT0.
  unfold HDQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  unfold hd_zres. cbv zeta. rewrite Pw. change (Z.land 5 1 =? 0) with false. cbn [orb].
  rewrite (hd_x_spec (ir_hold r) RH64).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_HEAD_J. do 2 zs. br_true. zs. rewrite Phd. zs. br_true. do 4 zs. br_false.
  do 12 zs. br_cases K; rewrite hd_x_clang in K by lia; change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia.
  1:{
      assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = false) by (apply Z.eqb_neq; intros E0; apply (proj2 (mod31_clang _ (hd_x_range _ RH64))) in E0; lia).
      rewrite E31. cbn [negb].
      do 8 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      + cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep]. }
  assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = true) by (apply Z.eqb_eq; apply (proj1 (mod31_clang _ (hd_x_range _ RH64))); lia).
  rewrite E31. cbn [negb]. clear K E31.
  assert (EB4 : forall h, 0 <= h -> BITSv h 4 = Z.land h 15) by (intros h Hh; rewrite BITSv_mod by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
  rewrite (EB4 _ (proj1 RH64)). unfold Z_DEFLATED.
  do 4 zs. br_cases K.
  -
    replace (Z.land (ir_hold r) 15 =? 8) with false by (symmetry; apply Z.eqb_neq; exact K). cbn [negb].
    do 13 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep].
  - replace (Z.land (ir_hold r) 15 =? 8) with true by (symmetry; apply Z.eqb_eq; exact K). cbn [negb].
    rewrite Pwb. do 4 zs.
    assert (RL4 : 0 <= Z.land (Z.shiftr (ir_hold r) 4) (Z.ones 4) <= 15).
    { rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.shiftr (ir_hold r) 4) (2 ^ 4) ltac:(lia)) as Q. change (2 ^ 4) with 16 in Q. lia. }
    change (Z.ones 4) with 15 in RL4.
    assert (RS4 : 0 <= Z.shiftr (ir_hold r) 4) by (apply Z.shiftr_nonneg; lia).
    change (ir_hold (drop4 r)) with (Z.shiftr (ir_hold r) 4). rewrite (EB4 _ RS4).
    set (l4 := Z.land (Z.shiftr (ir_hold r) 4) 15) in *.
    br_cases K2.
    +
      replace (15 <? l4 + 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
      do 14 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. unfold drop4. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep].
    + replace (15 <? l4 + 8) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
      zs. rewrite ?Pwb. zs. zs. br_false. zs. br_true. zs. br_true.
      do 8 zs.
      remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
      assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
      call (adler32_null_spec (ix_lo X)).
      1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
      1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
      lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
      subst spw.
      do 4 zs. zs. br_cases K3.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with true by (symmetry; apply Z.eqb_eq; apply (fdict_clang _ RH64); exact K3). cbn [negb].
        do 11 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists _, _. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply (fdict_clang _ RH64) in E0; lia). cbn [negb].
        do 12 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists _, _. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold DICTID, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR| bk_keep].
           ired. rewrite HPUT0. reflexivity.
Qed.
Lemma arm_HEAD_ok : forall flush, arm_stmtg flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF. destruct HWF as [HOUT HPUT0].
  rewrite (arm_HEAD_eq s c r ltac:(rewrite Pwb; discriminate)). rewrite Pw. change (5 =? 0) with false. cbv iota.
  eapply evt_cut; [exact (head_nb16 X s c r _ x12 ms HL XO HREGS HP Pw)|].
  intros ms1 [(r1 & q1 & EN & HJ & HQ)|(r1 & EN & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 16 s r r1 HREGS ltac:(lia) EN) as (_ & HPL' & _). eapply PATG_pulled; [exact HP| exact HPL']. }
  rewrite EN. unfold hd_res. rewrite Pw. change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].
  destruct (NEEDBITS_spec c 16 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & HB16 & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  assert (HQ1 : HDQ X r1 r1 q1) by (unfold HDQ in *; rewrite EPUT; exact HQ).
  exact (head_core X s c r1 q1 ms1 HJ HQ1 XO HREGS1 HP1 HM HB16 ltac:(rewrite EPUT; exact HPUT0)).
Qed.
