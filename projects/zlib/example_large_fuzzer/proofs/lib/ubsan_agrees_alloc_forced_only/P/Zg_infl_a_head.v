(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_adler32 Zh_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_HDR RefInflateA_HEAD DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_HEAD_NB : Z := 0x1d3ec.
Definition PC_HEAD_J : Z := 0x1dd88.

Definition PC_HEAD_L : Z := 0x1d3f8.

Lemma head_loop : forall f X s c r q v12 ms,
  ILOOPg X (mkW s c r) PC_HEAD_L q ms -> sc13 q = wz (ir_bits r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc12 q = v12 ->
  ix_ok X -> REGS c r -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 16 -> 16 <= ir_bits r + 8 * Z.of_nat f ->
  evt psegs (NBG X s c (NEEDBITS_k f 16 (mkW s c r)) PC_HEAD_J
               (fun r1 q1 => sc12 q1 = v12 /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  induction f as [|f IH]; intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v12 ms HL E13 E26 E12 XO HREGS Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26 v12.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_HEAD_L. ix_open XO.
  zs. br_cases K.
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    do 2 zs.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia. br_cases K3.
    +
      rewrite (NB_pull f 16 s c r) by lia.
      eapply IH; [ eapply ILOOPg_intro; ired; [ireg .. |] | cbn [sc13]; rewrite E6; ireg | cbn [sc26]; rewrite E1; ireg | reflexivity
                 | exact XO | exact HREGS1 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    +
      rewrite (NB_pull f 16 s c r) by lia. rewrite (NB_done f 16 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPg_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * cbn [sc12 sc26 sc27]. rewrite E1. split; [reflexivity| split; ireg].
  -
    rewrite (NB_dry f 16 s c r) by lia.
    do 2 zs.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma head_nb16 : forall X s c r q v12 ms,
  ILOOPg X (mkW s c r) PC_HEAD_NB q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc12 q = v12 ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  evt psegs (NBG X s c (NEEDBITS 16 (mkW s c r)) PC_HEAD_J (fun r1 q1 => sc12 q1 = v12
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v12 ms HL E26 E12 XO HREGS HP.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x26 v12.
  pose proof HMEM as ((jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  unfold PC_HEAD_NB. ix_open XO. rewrite NB_top.
  do 2 zs. br_cases K.
  -
    rewrite (NB_done 8 16 s c r) by lia.
    zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [sc12 sc26 sc27]. repeat split; reflexivity.
  - zs.
    eapply (head_loop 8%nat X s c r (mkSC x5 x6 x7 x8 x12 (wz (ir_bits r)) x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
      [ eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | reflexivity | exact XO
      | exact HREGS | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma head_core : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_HEAD_J q ms -> sc12 q = wz 5 -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_mode s = HEAD -> 16 <= ir_bits r -> ir_put r = 0 ->
  evt psegs (fun ms' => IPOST X (hd_zres s c r) ms' /\ PATG X (wof (hd_zres s c r))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E26 E27 XO HREGS HP HM HB16 HPUT0.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  unfold hd_zres. cbv zeta. rewrite Pw. change (Z.land 5 1 =? 0) with false. cbn [orb].
  rewrite (hd_x_spec (ir_hold r) RH64).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x12 x26 x27. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_HEAD_J. do 2 zs. br_true. zs. rewrite Phd. zs. br_true. do 2 zs. br_false.
  do 12 zs. br_cases K; rewrite hd_x_clang in K by lia; change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia.
  2:{
      assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = false) by (apply Z.eqb_neq; intros E0; apply (proj2 (mod31_clang _ (hd_x_range _ RH64))) in E0; lia).
      rewrite E31. cbn [negb].
      do 8 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      + cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR]. }
  assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = true) by (apply Z.eqb_eq; apply (proj1 (mod31_clang _ (hd_x_range _ RH64))); exact K).
  rewrite E31. cbn [negb]. clear K E31.
  assert (EB4 : forall h, 0 <= h -> BITSv h 4 = Z.land h 15) by (intros h Hh; rewrite BITSv_mod by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
  rewrite (EB4 _ (proj1 RH64)). unfold Z_DEFLATED.
  do 4 zs. br_cases K.
  -
    replace (Z.land (ir_hold r) 15 =? 8) with false by (symmetry; apply Z.eqb_neq; exact K). cbn [negb].
    do 14 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR].
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
      do 16 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. unfold drop4. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATG_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR].
    + replace (15 <? l4 + 8) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
      zs. rewrite ?Pwb. do 2 zs. br_false. zs. br_true. zs. br_true.
      do 8 zs.
      call (adler32_null_spec).
      1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
      do 5 zs. zs. br_cases K3.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with true by (symmetry; apply Z.eqb_eq; apply (fdict_clang _ RH64); exact K3). cbn [negb].
        do 14 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply (fdict_clang _ RH64) in E0; lia). cbn [negb].
        do 15 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold DICTID, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR].
           ired. rewrite HPUT0. reflexivity.
Qed.

Lemma arm_HEAD_ok : forall flush, arm_stmtg flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF. destruct HWF as [HOUT HPUT0].
  rewrite (arm_HEAD_eq s c r ltac:(rewrite Pwb; discriminate)). rewrite Pw. change (5 =? 0) with false. cbv iota.

  eapply (evt_cut psegs (NBG X s c (NEEDBITS 16 (mkW s c r)) PC_HEAD_J (fun r1 q1 => sc12 q1 = wz 5
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1)))).
  { destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_HEAD. zs. rewrite Pw. zs. br_false.
    eapply (head_nb16 X s c r (mkSC x5 x6 x7 (wz (-3)) (wz 5) x13 x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
      [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | exact XO | exact HREGS | exact HP]. }
  intros ms1 [(r1 & q1 & EN & HJ & E12 & E26 & E27)|(r1 & EN & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 16 s r r1 HREGS ltac:(lia) EN) as (_ & HPL & _). eapply PATG_pulled; [exact HP| exact HPL]. }
  rewrite EN. unfold hd_res. rewrite Pw. change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].
  destruct (NEEDBITS_spec c 16 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & HB16 & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  exact (head_core X s c r1 q1 ms1 HJ E12 E26 E27 XO HREGS1 HP1 HM HB16 ltac:(rewrite EPUT; exact HPUT0)).
Qed.
