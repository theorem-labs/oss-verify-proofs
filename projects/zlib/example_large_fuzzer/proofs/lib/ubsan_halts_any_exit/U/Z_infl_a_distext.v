(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_a_match.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_MATCH1 RefInflateA_DISTEXT RefInflateSafeOK2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_DISTEXT_E : Z := 0x212e0.
Definition PC_DISTEXT_J : Z := 0x2135c.
Definition DXE (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h14 q = wz (is_extra s) /\ h12 q = wz (ir_have r).
Definition DXQ (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  h14 q = wz (is_extra s) /\ h13 q = wz (il_NI (ix_L X) + ir_next r1) /\ h11 q = wz (ir_bits r1) /\ h24 q = wz (ir_have r1)
  /\ h22 q = wz (ir_hold r1) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).
Lemma distext_nb : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_E q ms -> DXE X s r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt usegs (NBJq X s c r (is_extra s) PC_DISTEXT_J (DXQ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E11 & E13 & E18 & E22 & E25 & E14 & E12) XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_DISTEXT_E. ix_open XO.
  zs. br_false. zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold DXQ. cbn [h9 h10 h11 h13 h14 h22 h24]. repeat split; reflexivity.
  - do 8 zs. rewrite !land_u32_small by lia. zstep. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zstep. br_cases K3.
      *
        zstep. br_true. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
        -- unfold hide in RH. unfold DXQ. cbn [h9 h10 h11 h13 h14 h22 h24]. pullr_rw c r. repeat split; ireg.
Qed.
Lemma distext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_J q ms -> DXQ X s r r1 q ->
  ix_ok X -> PATI X (mkW s c r) ->
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
Lemma distext_core : forall X w q ms,
  ILOOPh X w PC_DISTEXT_E q ms -> DXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DISTEXT ->
  evt usegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATI X (wof (arm_DISTEXT ivar_ref w))) ms.
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
    assert (HP2 : PATI X (mkW (iset_mode s MATCH) c r)).
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    eapply (evt_cut usegs (fun ms1 => exists x26 x12, ILOOP X (mkW (iset_mode s MATCH) c r) PC_MATCH x26 x12 ms1)).
    2:{ intros ms1 (x26' & x12' & H1). exact (match_core X _ x26' x12' ms1 H1 XO HW2 HP2 HM2). }
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
    intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
    2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
    rewrite EN.
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { unfold distext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    destruct (nb_r1_facts c r r1 (is_extra s) HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
    assert (HP2 : PATI X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
      unfold bk_ok, dx_s. rewrite HM. cbn -[Z.add Z.mul Z.opp Z.sub Z.le Z.lt Z.eqb swrap32]. unfold bkmax. cbn -[swrap32 Z.le Z.add]. intros [B1 B2].
      rewrite swrap32_id by lia. lia. }
    eapply evt_cut.
    { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
      exact (distext_fin X s c r r1 q1 ms1 HJ HQ XO HP EI EO ER EP EL ltac:(lia) ROFF RB1 RH1 RHV1 RN1 ltac:(lia)). }
    intros ms2 (x26' & x12' & H2). exact (match_core X _ x26' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.
