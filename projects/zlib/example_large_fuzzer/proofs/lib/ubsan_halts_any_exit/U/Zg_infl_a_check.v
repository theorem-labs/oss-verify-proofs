(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Z_ukit Zg_infl_pure Zg_infl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_LENGTH RefInflateA_CHECK DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_CHECK_J : Z := 0x20218.
Definition PC_CHECK_T : Z := 0x2081c.

Definition CHKQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h13 q = wz (il_S (ix_L X)) /\ h14 q = wz 5
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r1) /\ h26 q = wz (ir_have r1) /\ h20 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).

Definition PC_CHECK_L : Z := 0x1f768.

Definition CKL (X : ictx) (r0 r : iregs) (q : iscrh) : Prop :=
  h26 q = wz (ir_have r) /\ h11 q = wz (il_NI (ix_L X) + ir_next r) /\ h16 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h20 q = wz (ir_bits r) /\ h15 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h14 q = wz 5
  /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2) /\ h13 q = wz (il_S (ix_L X)).

Lemma check_loop : forall f X s c r0 r q ms,
  ILOOPh X (mkW s c r) PC_CHECK_L q ms -> CKL X r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 32 -> 32 <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f 32 (mkW s c r)) PC_CHECK_J (CHKQ X r0)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold CKL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E26 & E11 & E16 & E20 & E15 & E22 & E14 & E24 & E25 & E18 & E9 & E10 & E13). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  pose proof (pulled_eqs r0 r HPL0) as (PE1 & PE2 & PE3 & PE4 & PE5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_CHECK_L. ix_open XO.
  zs. br_cases K.
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 2 zs. gT. do 2 zs. zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zs. br_cases K3.
    +
      rewrite (NB_pull f 32 s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold CKL; hred; rewrite ?E1, ?E2, ?E5, ?E6; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    +
      rewrite (NB_pull f 32 s c r) by lia. rewrite (NB_done f 32 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold CHKQ. hred. rewrite ?E1, ?E2, ?E5, ?E6. repeat split; ireg.
  -
    rewrite (NB_dry f 32 s c r) by lia.
    do 10 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma check_nb32 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_CHECK x26 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_wrap s = 5 ->
  evt usegs (NBGq X s c (NEEDBITS 32 (mkW s c r)) PC_CHECK_J (CHKQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP Pw.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  open_IST ST. open_isA GA. cbn [w_s] in GA.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (REGS_hold64 c r HREGS) as RH64.
  unfold PC_CHECK. ix_open XO. rewrite NB_top.
  zs. rewrite Pw. zs. br_false.
  do 2 zs. br_cases K.
  -
    rewrite (NB_done 8 32 s c r) by lia.
    do 3 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold CHKQ. hred. repeat split; reflexivity.
  - do 5 zs.
    eapply (check_loop 8%nat X s c r r);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold CKL; hred; repeat split; ireg | exact XO
      | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.


Definition CHKT (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r) /\ h26 q = wz (ir_have r) /\ h20 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).

Definition chk_ov (s : inflate_state) (c : icall) (r : iregs) : option Z :=
  if chk_out r =? 0 then None
  else Some (UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r - chk_out r) (chk_out r))).

Section Check.
Hypothesis ADLER32 : adler32_stmt.

Lemma adler32_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B len lo : Z) (d : list byte),
  0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
  bytes_at usegs m B d -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 -> (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
  len = Z.of_nat (length d) ->
  evt usegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof. intros. subst. apply ADLER32; assumption. Qed.

Lemma check_mid : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CHECK_J q ms -> CHKQ X r r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) -> ir_out r = arr_len (ic_outbuf c) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (chk_s3 s r (chk_ov s c r)) (chk_c3 c r (chk_ov s c r)) r) PC_CHECK_T q' ms' /\ CHKT X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP Pf0 HCK HOUT.
  unfold CHKQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & [POB POW] & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  destruct HCK as (CK1 & CK2 & CK3).
  assert (ECO : chk_out r = ir_put r).
  { unfold chk_out. rewrite HOUT, <- Rpl. replace (ir_put r + ir_left r - ir_left r) with (ir_put r) by lia. rewrite wrap32_id by lia. reflexivity. }
  assert (RPUT : 0 <= ir_put r < 2^31) by lia.
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_J. do 3 zs. replace (ir_out r - ir_left r) with (ir_put r) by lia.
  do 4 zs. rewrite !land_u32_small by lia.
  do 5 zs. change (Z.land 5 4) with 4. zs. br_false. zs. br_cases K.
  -
    assert (EP : ir_put r = 0) by lia.
    assert (EOV : chk_ov s c r = None) by (unfold chk_ov; rewrite ECO, EP; reflexivity).
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO.
    zs. zs. br_true.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPh_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists j0, jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    unfold CHKT. hred. repeat split; first [reflexivity | ireg].
  -
    assert (EP : 0 < ir_put r) by lia.
    pose proof (iout_prefix_bytes _ (ix_L X) (ix_rest0 X) c (ir_put r) OUT ltac:(lia)) as BY.
    pose proof (av8_zlength (ic_outbuf c) (ir_put r) ltac:(lia)) as LAV.
    assert (EOV : chk_ov s c r = Some (adler32_z_spec (is_check s) (il_NO (ix_L X)) (av8 (ic_outbuf c) (ir_put r)))).
    { unfold chk_ov. rewrite ECO. replace (ir_put r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal.
      unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb]. unfold iadler32_upd.
      rewrite (adler32_z_spec_any (is_check s) (il_NO (ix_L X)) _ (conj CK1 (conj CK2 CK3))) by lia.
      rewrite bZ_av8 by (first [lia | intros i Hi; apply POB; lia]). rewrite Z.sub_diag. reflexivity. }
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO.
    zs. rewrite Pf0. do 7 zs.
    replace (il_NO (ix_L X) + ir_put r <? ir_put r) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite xor_guard_sub by lia. cbn [Z.b2z]. change (Z.land (Z.lxor 0 18446744073709551615) 1) with 1.
    gT. gT.
    do 2 zs. replace (il_NO (ix_L X) + ir_put r + - ir_put r) with (il_NO (ix_L X)) by lia. zs.
    assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply adler32_call; [lia| lia| rewrite LAV; lia| rewrite LAV; lia| exact BY| eassumption| rewrite E256; exact STK| rewrite E256; lia| rewrite E256; lia
                            | rewrite LAV; lia| rewrite LAV; reflexivity]
      | cbv beta; unfold adler32_postS; rewrite ?E256; post_call usegs mm ] end.
    try clear STK. match goal with H : stk usegs _ (ix_lo X) _ |- _ => rename H into STK end.
    do 2 zs. rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw. zs. change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4.
    do 4 zs. zs. br_false.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPh_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists j0, jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    unfold CHKT. hred. repeat split; first [reflexivity | ireg].
Qed.


Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma check_tail : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CHECK_T q ms -> CHKT X r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) ->
  evt usegs (fun ms' => IPOST X (chk_tail s c r 5 (ZSWAP32 (ir_hold r))) ms' /\ PATG X (wof (chk_tail s c r 5 (ZSWAP32 (ir_hold r))))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP Pf0 HCK.
  unfold CHKT in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  destruct HCK as (CK1 & _).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_T. zs. rewrite Pf0. zs. zs. br_false.
  do 14 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  zs. br_cases K.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with false by (symmetry; apply Z.eqb_neq; exact K).
    cbn [negb andb]. unfold chk_r3.
    do 10 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATG_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity| | bk_keep]. exact HISR.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with true by (symmetry; apply Z.eqb_eq; exact K).
    cbn [negb andb]. rewrite (arm_LENGTH_skip (iset_mode s LENGTH) c _ (or_intror Pf0)). unfold done_w, chk_r3.
    do 8 zs. zs. rewrite Pw. zs. br_false. zs. rewrite Pf0. zs. br_true. do 9 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
      apply IMEML_intro; inorm.
      * eexists _, j0, jf. exact FRM.
      * exact STK.
      * eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS.
      * constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT.
      * eassumption.
      * exact MU.
      * exact WM.
    + cbn [wof]. eapply PATG_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity| | bk_keep]. exact HISR.
Qed.


Lemma arm_CHECK_run : forall s c r r1,
  is_wrap s = 5 -> is_flags s = 0 -> NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c r1) ->
  arm_CHECK (mkW s c r) = chk_tail (chk_s3 s r1 (chk_ov s c r1)) (chk_c3 c r1 (chk_ov s c r1)) r1 5 (ZSWAP32 (ir_hold r1)).
Proof.
  intros s c r r1 Hw Hf HN. unfold chk_ov.
  assert (EV : chk_v s r1 = ZSWAP32 (ir_hold r1)) by (unfold chk_v; rewrite Hf; reflexivity).
  destruct (Z.eqb_spec (chk_out r1) 0) as [E0|NE0].
  - rewrite (arm_CHECK_run_noupd s c r r1 ltac:(lia) HN (or_intror E0)). rewrite Hw, EV. reflexivity.
  - rewrite (arm_CHECK_run_upd s c r r1 ltac:(lia) HN ltac:(rewrite Hw; discriminate) NE0). rewrite Hw, EV. reflexivity.
Qed.

Lemma arm_CHECK_of : forall flush, arm_stmtg flush CHECK PC_CHECK arm_CHECK.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [_ HCK]. specialize (HCK Pf0).
  eapply evt_cut; [exact (check_nb32 X s c r _ x12 ms HL XO HREGS HP Pw)|].
  intros ms1 [(r1 & q1 & EN & HJ & HQ)|(r1 & EN & HLV)].
  2:{
      rewrite (arm_CHECK_dry s c r _ ltac:(lia) EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 32 s r r1 HREGS ltac:(lia) EN) as (_ & HPL' & _). eapply PATG_pulled; [exact HP| exact HPL']. }
  rewrite (arm_CHECK_run s c r r1 Pw Pf0 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  assert (HOUT1 : ir_out r1 = arr_len (ic_outbuf c)) by (rewrite EOUT; exact HWF).
  assert (HQ1 : CHKQ X r1 r1 q1) by (unfold CHKQ in *; rewrite EPUT; exact HQ).
  eapply evt_cut; [exact (check_mid X s c r1 q1 ms1 HJ HQ1 XO HREGS1 HP1 Pf0 HCK HOUT1)|].
  intros ms2 (q2 & HJ2 & HQ2).
  destruct (chk_c3_facts c r1 (chk_ov s c r1)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  destruct (chk_s3_eq s r1 (chk_ov s c r1)) as (t & ck & ES3 & Rt & Eck).
  apply (check_tail X _ _ r1 q2 ms2 HJ2 HQ2 XO).
  - unfold REGS in *. rewrite F5, F6. exact HREGS1.
  - rewrite ES3. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold CHECK, FLAGS, HCRC; lia| reflexivity| exact F5| exact F6| reflexivity| reflexivity| reflexivity| reflexivity| cbn [is_mode iset_check iset_total]; rewrite HM; reflexivity| | bk_keep]. exact HISR.
  - rewrite ES3. exact Pf0.
  - rewrite ES3. cbn [is_check iset_check]. rewrite Eck. unfold chk_ov. destruct (chk_out r1 =? 0); [exact HCK|].
    unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb]. apply adler32_model_canon.
Qed.

End Check.

Lemma arm_LENGTH_ok : forall flush, arm_stmtg flush LENGTH PC_LENGTH arm_LENGTH.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENGTH_skip s c r (or_intror Pf0)). unfold done_w.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (HISR : ISR s) by (split; assumption).
  clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  unfold PC_LENGTH. zs. rewrite Pw. zs. br_false. zs. rewrite Pf0. zs. br_true.
  do 9 zs.
  itr_groups MUf WMf.
  apply evt_done. split; [| cbn [wof]; eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]; exact HISR].
  cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
  apply IMEML_intro; inorm.
  + exists (wz (ir_ret r)), j0, jf. exact FRM.
  + exact STK.
  + exact ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.
