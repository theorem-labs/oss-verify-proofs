(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs Z_infl_c_pure Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_MATCH1 RefInflateA_DISTEXT RefInflateSafeOK2. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_DISTEXT_J : Z := 0x1eb2c.

Definition PC_DISTEXT_L : Z := 0x1eae0.

Lemma distext_loop : forall f X s c r0 r n q ms,
  ILOOPh X (mkW s c r0) PC_DISTEXT_L q ms ->
  h9 q = wz (ir_have r0) -> h23 q = wz (ir_bits r0) -> h26 q = wz (il_NI (ix_L X) + ir_next r0) ->
  h12 q = wz (ir_have r) -> h13 q = wz n -> h14 q = wz (ir_bits r) -> h16 q = wz (il_NI (ix_L X) + ir_next r) -> h22 q = wz (ir_hold r) ->
  h29 q = wz 30 -> h31 q = wz (-16180) ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_bits r0 -> 0 <= ir_have r0 < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  1 <= n <= 15 -> ir_bits r < n -> n <= ir_bits r + 8 * Z.of_nat f ->
  evt psegs (NBGh X s c r0 (NEEDBITS_k f n (mkW s c r)) n PC_DISTEXT_J) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r n [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms
    HL E9 E23 E26 E12 E13 E14 E16 E22 E29 E31 XO HREGS HPL HB0 HH0 Pin Pin1 Hn HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
  subst x9 x23 x26 x12 x13 x14 x16 x22 x29 x31.
  pose proof HMEM as ((jf0 & jf1 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r0 r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_DISTEXT_L. ix_open XO.
  zs. br_cases K.
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (NB_dry f n s c r) by lia.
    do 8 zs. rewrite (zx32_small (ir_have r0)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |].
    eapply IMEML_of_IMEM; [exact HMEM| first [assumption | symmetry; assumption | reflexivity]..].
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r0 r HREGS HB0 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9' & RH1).
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia. br_cases K3.
    +
      rewrite (NB_pull f n s c r) by lia.
      eapply (IH X s c r0 (RefInflateArmLib.pullr c r) n);
        [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h9 h12 h13 h14 h15 h16 h22 h23 h26 h29 h31] .. | exact XO | exact HREGS1 | exact HPL1
        | exact HB0 | exact HH0 | exact Pin | exact Pin1 | exact Hn | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ];
        first [ reflexivity | rewrite ?E1, ?E2, ?E5, ?E6; ireg ].
    +
      rewrite (NB_pull f n s c r) by lia. rewrite (NB_done f n s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
      cbn [h12 h13 h14 h15 h22 h29 h31]. rewrite E1, E2, E5, E6. repeat split; ireg.
Qed.

Lemma distext_nb : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_DISTEXT_E q ms -> sc13 q = wz (is_extra s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt psegs (NBGh X s c r (NEEDBITS (is_extra s) (mkW s c r)) (is_extra s) PC_DISTEXT_J) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E26 XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26.
  pose proof HMEM as ((jf0 & jf1 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_DISTEXT_E. ix_open XO. rewrite NB_top.
  zs. br_false. zs. br_cases K.
  -
    rewrite (NB_done 8 (is_extra s) s c r) by lia.
    do 3 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    cbn [h12 h13 h14 h15 h22 h29 h31]. repeat split; reflexivity.
  - do 3 zs.
    eapply (distext_loop 8%nat X s c r r (is_extra s));
      [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h9 h12 h13 h14 h15 h16 h22 h23 h26 h29 h31] .. | exact XO | exact HREGS
      | apply pulled_refl; [exact Rh| exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1 | exact REX | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ];
      reflexivity.
Qed.

Lemma distext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_J q ms ->
  h12 q = wz (ir_have r1) -> h13 q = wz (is_extra s) -> h14 q = wz (ir_bits r1) -> h15 q = wz (il_NI (ix_L X) + ir_next r1) ->
  h22 q = wz (ir_hold r1) -> h29 q = wz 30 -> h31 q = wz (-16180) ->
  ix_ok X -> PATG X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_offset s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x8 x12, ILOOP X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s))) PC_MATCH x8 x12 ms') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL E12 E13 E14 E15 E22 E29 E31 XO HP
         EI EO ER EP EL REX ROFF RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst x12 x13 x14 x15 x22 x29 x31.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_DISTEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 9 zs. rewrite (land63_small (is_extra s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold dx_s, dx_r; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists jf0, jf1, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_offset s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Section DistExt.
Hypothesis MATCH_CORE : match_core_stmt.

Lemma distext_core : forall X w q ms,
  ILOOPg X w PC_DISTEXT_E q ms -> sc13 q = wz (is_extra (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DISTEXT ->
  evt psegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATG X (wof (arm_DISTEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL E13 E26 XO HW HP HM. cbn [w_s w_c w_r] in *.
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
    { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr. }
    eapply (evt_cut psegs (fun ms1 => exists x8 x12, ILOOP X (mkW (iset_mode s MATCH) c r) PC_MATCH x8 x12 ms1)).
    2:{ intros ms1 (x8' & x12' & H1). exact (MATCH_CORE X _ x8' x12' ms1 H1 XO HW2 HP2 HM2). }
    destruct q as [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30].
    destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
    clear HW HW2 HP2 HCORE HWF HWB Pfl Pgz Pisr POBY RH Rin HP.
    iarm_openg HL. subst x13 x26. ix_open XO. unfold PC_DISTEXT_E.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    zs. rewrite E0. br_true. do 2 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists jf0, jf1, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - rewrite (arm_DISTEXT_on s c r NE0).
    eapply evt_cut; [exact (distext_nb X s c r q ms HL E13 E26 XO HREGS HP ltac:(lia))|].
    intros ms1 [(r1 & q1 & EN & HJ & E12 & E13' & E14 & E15 & E22 & E29 & E31)|(r1 & EN & HLV)].
    2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct (NBG_leave_facts c (is_extra s) s r r1 HREGS ltac:(lia) EN) as (_ & HPL & _). eapply PATG_pulled; [exact HP| exact HPL]. }
    rewrite EN.
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { unfold distext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    destruct (NBG_run_facts c (is_extra s) s r r1 HREGS ltac:(lia) EN) as (HREGS1 & HPL & HBX & _).
    destruct (nbG_r1_facts c r r1 (is_extra s) HREGS1 HPL HBX) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
    assert (HP2 : PATG X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
    eapply evt_cut.
    { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
      exact (distext_fin X s c r r1 q1 ms1 HJ E12 E13' E14 E15 E22 E29 E31 XO HP EI EO ER EP EL ltac:(lia) ROFF RB1 RH1 RHV1 RN1 ltac:(lia)). }
    intros ms2 (x8' & x12' & H2). exact (MATCH_CORE X _ x8' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.

Lemma arm_DISTEXT_of : forall flush, arm_stmtg flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  eapply (evt_cut psegs (fun ms1 => exists q, ILOOPg X (mkW s c r) PC_DISTEXT_E q ms1 /\ sc13 q = wz (is_extra s) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r))).
  2:{ intros ms1 (q & H1 & E13 & E26). exact (distext_core X _ q ms1 H1 E13 E26 XO HW HP HM). }
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & _ & REX & _).
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
  unfold PC_DISTEXT. do 2 zs.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc13 sc26]. split; reflexivity.
Qed.
End DistExt.
