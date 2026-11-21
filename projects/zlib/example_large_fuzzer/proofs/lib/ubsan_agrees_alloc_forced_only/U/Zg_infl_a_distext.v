(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_a_distext Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_MATCH1 RefInflateA_DISTEXT RefInflateSafeOK2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_DISTEXT_L : Z := 0x21308.
Definition DXL (X : ictx) (s : inflate_state) (r0 r : iregs) (q : iscrh) : Prop :=
  h24 q = wz (ir_have r) /\ h17 q = wz (il_NI (ix_L X) + ir_next r) /\ h5 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h15 q = wz (ir_bits r) /\ h11 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h16 q = wz (is_extra s) /\ h14 q = wz (is_extra s)
  /\ h12 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).
Lemma distext_loop : forall f X s c r0 r q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_L q ms -> DXL X s r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> 1 <= is_extra s <= 15 -> ir_bits r < is_extra s -> is_extra s <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f (is_extra s) (mkW s c r)) PC_DISTEXT_J (DXQ X s r0)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 REX HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold DXL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E24 & E17 & E5 & E15 & E11 & E22 & E16 & E14 & E12 & E25 & E18 & E9 & E10). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  pose proof (pulled_eqs r0 r HPL0) as (PE1 & PE2 & PE3 & PE4 & PE5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_DISTEXT_L. ix_open XO.
  zstep. br_cases K.
  -
    rewrite (NB_dry f (is_extra s) s c r) by lia.
    do 9 zs. rewrite ?land_ones32, ?shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6 & E3 & E4 & E7 & E8 & E9' & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    do 2 zs. gF. zs. gF.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zstep. br_cases K3.
    +
      rewrite (NB_pull f (is_extra s) s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold DXL; hred; rewrite ?E1, ?E2, ?E5', ?E6; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | exact REX | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    +
      rewrite (NB_pull f (is_extra s) s c r) by lia. rewrite (NB_done f (is_extra s) s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold DXQ. hred. rewrite ?E1, ?E2, ?E5', ?E6. repeat split; ireg.
Qed.
Lemma distext_nb : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_E q ms -> DXE X s r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt usegs (NBGq X s c (NEEDBITS (is_extra s) (mkW s c r)) PC_DISTEXT_J (DXQ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E11 & E13 & E18 & E22 & E25 & E14 & E12) XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (REGS_hold64 c r HREGS) as RH64.
  unfold PC_DISTEXT_E. ix_open XO. rewrite NB_top.
  zs. br_false. zs. br_cases K.
  -
    rewrite (NB_done 8 (is_extra s) s c r) by lia.
    do 3 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold DXQ. hred. repeat split; reflexivity.
  - do 8 zs. rewrite !land_u32_small by lia.
    eapply (distext_loop 8%nat X s c r r);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold DXL; hred; repeat split; ireg | exact XO
      | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | exact REX | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.
Lemma distext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_J q ms -> DXQ X s r r1 q ->
  ix_ok X -> PATG X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_offset s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists x26 x12, ILOOP X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s))) PC_MATCH x26 x12 ms') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E14 & E13 & E11 & E24 & E22 & E9 & E10) XO HP EI EO ER EP EL REX ROFF RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_DISTEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  zs. gF. do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 10 zs. rewrite (land63_small (is_extra s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold dx_s, dx_r; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_offset s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.
Section DistExt.
Hypothesis MATCH_CORE : match_core_stmt.
Lemma distext_core : forall X w q ms,
  ILOOPh X w PC_DISTEXT_E q ms -> DXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DISTEXT ->
  evt usegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATG X (wof (arm_DISTEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & REX & ROFF).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  destruct (Z.eq_dec (is_extra s) 0) as [E0|NE0].
  -
    rewrite (arm_DISTEXT_off s c r E0).
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode s MATCH) c r)).
    { unfold distext_next. cbn [w_s w_c w_r]. rewrite E0. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    assert (HP2 : PATG X (mkW (iset_mode s MATCH) c r)).
    { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    eapply (evt_cut usegs (fun ms1 => exists x26 x12, ILOOP X (mkW (iset_mode s MATCH) c r) PC_MATCH x26 x12 ms1)).
    2:{ intros ms1 (x26' & x12' & H1). exact (MATCH_CORE X _ x26' x12' ms1 H1 XO HW2 HP2 HM2). }
    destruct q as [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31].
    destruct HE as (E9 & E10 & E11 & E13 & E18 & E22 & E25 & E14 & E12).
    destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
    clear HW HW2 HP2 HCORE HWF HWB Pfl Pgz Pisr POBY RH Rin HP.
    iarm_openh HL. subst. ix_open XO. unfold PC_DISTEXT_E.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    zs. rewrite E0. br_true. do 4 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - rewrite (arm_DISTEXT_on s c r NE0).
    eapply evt_cut; [exact (distext_nb X s c r q ms HL HE XO HREGS HP ltac:(lia))|].
    intros ms1 [(r1 & q1 & EN & HJ & HQ)|(r1 & EN & HLV)].
    2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct (NBG_leave_facts c (is_extra s) s r r1 HREGS ltac:(lia) EN) as (_ & HPL' & _). eapply PATG_pulled; [exact HP| exact HPL']. }
    rewrite EN.
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { unfold distext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    destruct (NBG_run_facts c (is_extra s) s r r1 HREGS ltac:(lia) EN) as (HREGS1 & HPL & HBX & _).
    destruct (nbG_r1_facts c r r1 (is_extra s) HREGS1 HPL HBX) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
    pose proof (ILOOPh_regs X s c r1 r _ q1 ms1 HJ (eq_sym EI) (eq_sym EO) (eq_sym ER) (eq_sym EP) (eq_sym EL)) as HJr.
    assert (HP2 : PATG X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
      unfold bk_ok, dx_s. rewrite HM. cbn -[Z.add Z.mul Z.opp Z.sub Z.le Z.lt Z.eqb swrap32]. unfold bkmax. cbn -[swrap32 Z.le Z.add]. intros [B1 B2].
      rewrite swrap32_id by lia. lia. }
    eapply evt_cut.
    { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
      exact (distext_fin X s c r r1 q1 ms1 HJr HQ XO HP EI EO ER EP EL ltac:(lia) ROFF RB1 RH1 RHV1 RN1 ltac:(lia)). }
    intros ms2 (x26' & x12' & H2). exact (MATCH_CORE X _ x26' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.
Lemma arm_DISTEXT_of : forall flush, arm_stmtg flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_DISTEXT_E q ms1 /\ DXE X s r q)).
  2:{ intros ms1 (q & H1 & HE). exact (distext_core X _ q ms1 H1 HE XO HW HP HM). }
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & _ & REX & _).
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
  unfold PC_DISTEXT. do 3 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold DXE. cbn [h9 h10 h11 h12 h13 h14 h18 h22 h25]. repeat split; reflexivity.
Qed.
Lemma distext_core_ok : distext_core_stmt.
Proof. exact distext_core. Qed.
End DistExt.
