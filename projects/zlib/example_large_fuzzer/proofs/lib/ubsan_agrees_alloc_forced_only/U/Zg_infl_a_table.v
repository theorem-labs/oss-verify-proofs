(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Zh_kit Z_ukit Z_infl_c_pure Z_infl_t_iface Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_TABLE RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.
Lemma shl3 : forall x, x ≪ 3 = 8 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Definition PC_TABLE_J : Z := 0x1fa5c.
Definition PC_TABLE_DRY : Z := 0x216a8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TBQ (X : ictx) (x26 : word) (r1 : iregs) (q : iscrh) : Prop :=
  h11 q = wz (ir_bits r1) /\ h14 q = wz (il_NI (ix_L X) + ir_next r1) /\ h12 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1)
  /\ h13 q = wz (il_S (ix_L X)) /\ h9 q = wz (il_NO (ix_L X) + ir_put r1) /\ h10 q = wz (-2) /\ h26 q = x26.

Definition PC_TABLE_L : Z := 0x1f6f8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TBL (X : ictx) (x26 : word) (r0 r : iregs) (q : iscrh) : Prop :=
  h12 q = wz (ir_have r) /\ h15 q = wz (il_NI (ix_L X) + ir_next r) /\ h5 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h11 q = wz (ir_bits r) /\ h17 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h13 q = wz (il_S (ix_L X)) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h26 q = x26.

(* [comment removed for export] *)
Lemma table_loop : forall f X s c r0 r q x26 ms,
  ILOOPh X (mkW s c r) PC_TABLE_L q ms -> TBL X x26 r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 14 -> 14 <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f 14 (mkW s c r)) PC_TABLE_J (TBQ X x26)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26' x28 x29 x30 x31] x26 ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold TBL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E12 & E15 & E5 & E11 & E17 & E22 & E24 & E25 & E18 & E13 & E9 & E10 & E26). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_TABLE_L. ix_open XO.
  zs. br_cases K.
  - (* [comment removed for export] *)
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. zs. zs. br_cases KG; [| exfalso; lia].
    zs. zs. zs. clear RD. zs. zs. zs. zs. rewrite <- Pin. rewrite !pull_shift by lia. zs. zs. zs. zs. zs. br_cases K3.
    + (* [comment removed for export] *)
      rewrite (NB_pull f 14 s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold TBL; hred; rewrite E1, E2, E5, E6, E3; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    + (* [comment removed for export] *)
      rewrite (NB_pull f 14 s c r) by lia. rewrite (NB_done f 14 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold TBQ. hred. rewrite E1, E2, E5, E6, E3. repeat split; ireg.
  - (* [comment removed for export] *)
    rewrite (NB_dry f 14 s c r) by lia.
    do 10 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

(* [comment removed for export] *)
Lemma table_nb14 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_TABLE x26 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> ir_bits r < 14 ->
  evt usegs (NBGq X s c (NEEDBITS 14 (mkW s c r)) PC_TABLE_J (TBQ X x26)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_TABLE. ix_open XO.
  zs. zs. br_cases K0; [exfalso; lia|]. do 5 zs.
  rewrite NB_top.
  eapply (table_loop 8%nat X s c r r);
    [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold TBL; hred; repeat split; ireg | exact XO
    | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | exact MFB | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

(* [comment removed for export] *)
Lemma tb_f1 : forall h, Z.land h 31 = h mod 2^5.
Proof. intros h. change 31 with (Z.ones 5). apply Z.land_ones. lia. Qed.
Lemma tb_f2 : forall h, 0 <= h < 2^64 -> Z.land (h ≪ 54) 18446744073709551615 ≫ 59 = h mod 2^10 / 2^5.
Proof.
  intros h H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616 in *. change (2^54) with 18014398509481984. change (2^59) with 576460752303423488.
  change (2^10) with 1024. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
Lemma tb_f3 : forall h, 0 <= h < 2^64 -> Z.land (h ≪ 50) 18446744073709551615 ≫ 60 = h mod 2^14 / 2^10.
Proof.
  intros h H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616 in *. change (2^50) with 1125899906842624. change (2^60) with 1152921504606846976.
  change (2^14) with 16384. change (2^10) with 1024. Z.div_mod_to_equations. lia.
Qed.
Lemma tb_ranges : forall h, 0 <= h mod 2^5 < 32 /\ 0 <= h mod 2^10 / 2^5 < 32 /\ 0 <= h mod 2^14 / 2^10 < 16.
Proof. intros h. change (2^5) with 32. change (2^10) with 1024. change (2^14) with 16384. Z.div_mod_to_equations. lia. Qed.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

(* [comment removed for export] *)
Lemma table_fin : forall flush X s c r q x26 ms,
  ix_flush X = flush ->
  ILOOPh X (mkW s c r) PC_TABLE_J q ms -> TBQ X x26 r q ->
  ix_ok X -> PATG X (mkW s c r) -> 14 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_have r ->
  evt usegs (fun ms' =>
     if (286 <? is_nlen (tb_s s (ir_hold r))) || (30 <? is_ndist (tb_s s (ir_hold r)))
     then exists x26' x12', ILOOP X (mkW (iset_mode (tb_s s (ir_hold r)) BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) (tb_r r)) PC_DISPATCH x26' x12' ms'
     else exists q', ILOOPh X (mkW (tb_s2 s (ir_hold r)) c (tb_r r)) PC_LENLENS_E q' ms' /\ h17 q' = wz 0 /\ h14 q' = wz (il_NI (ix_L X) + ir_next r)
                     /\ h12 q' = wz (ir_have r) /\ h9 q' = wz (il_NO (ix_L X) + ir_put r) /\ h11 q' = wz (ix_flush X) /\ h13 q' = wz (il_S (ix_L X))
                     /\ h18 q' = wz (ir_bits r - 14) /\ h22 q' = wz (Z.shiftr (ir_hold r) 14)) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26' x28 x29 x30 x31] x26 ms EF HL HQ XO HP RB RH RPUT RHV.
  unfold TBQ in HQ. iarm_openh HL. destruct HQ as (E11 & E14 & E12 & E22 & E13 & E9 & E10 & E26). subst x11 x14 x12 x22 x13 x9 x10 x26'.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_TABLE_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  do 7 zs. rewrite tb_f1, (tb_f2 (ir_hold r) RH), (tb_f3 (ir_hold r) RH).
  destruct (tb_ranges (ir_hold r)) as (Ra & Rb & Rc).
  unfold tb_s2, tb_s, tb_r. cbn [is_nlen is_ndist is_ncode iset_ncode iset_ndist iset_nlen iset_have iset_mode].
  set (fa := ir_hold r mod 2^5) in *. set (fb := ir_hold r mod 2^10 / 2^5) in *. set (fc := ir_hold r mod 2^14 / 2^10) in *.
  do 8 zs. zs. br_cases K1.
  { (* [comment removed for export] *)
    replace (286 <? fa + 257) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
    do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (286 <? fa + 257) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  zs. zs. br_cases K2.
  { (* [comment removed for export] *)
    replace (30 <? fb + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (30 <? fb + 1) with false by (symmetry; apply Z.ltb_ge; lia).
  do 4 zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity| hred; repeat split; try reflexivity; ireg].
  close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section Table.
Variable flush : Z.
Hypothesis LENLENS_CORE : lenlens_core_stmt flush.

Lemma table_core : forall X w x26 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_TABLE x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = TABLE ->
  evt usegs (fun ms' => IPOST X (arm_TABLE ivar_ref flush w) ms' /\ PATG X (wof (arm_TABLE ivar_ref flush w))) ms.
Proof.
  intros X [s c r] x26 x12 ms EF HL XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & MFB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (table_nb14 X s c r x26 x12 ms HL XO HREGS HP MFB)|].
  intros ms1 [(r1 & q1 & EN & HJ & HQ1)|(r1 & EN & HLV)].
  2:{ rewrite (arm_TABLE_leave flush _ _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 14 s r r1 HREGS ltac:(lia) EN) as (_ & HPL & _). eapply PATG_pulled; [exact HP| exact HPL]. }
  destruct (NBG_run_facts c 14 s r r1 HREGS ltac:(lia) EN) as (HREGS1 & HPL & HB14 & _).
  destruct (nbG_r1_facts c r r1 14 HREGS1 HPL HB14) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  rewrite (arm_TABLE_eq flush s c r s c r1 EN ltac:(lia) ltac:(lia)).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (table_fin flush X s c r1 q1 x26 ms1 EF HJ HQ1 XO HP1 ltac:(lia) RH1 ltac:(rewrite EP; lia) ltac:(lia)). }
  intros ms2 H2. unfold tb_res. cbv zeta.
  assert (HN : table_next (mkW s c r) = if (286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1))) then None
                                        else Some (mkW (tb_s2 s (ir_hold r1)) c (tb_r r1))).
  { unfold table_next. rewrite EN. reflexivity. }
  destruct ((286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1)))).
  - destruct H2 as (x26' & x12' & H2). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H2|]. cbn [wof].
    eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep].
  - destruct H2 as (q2 & H2 & E17 & E14 & E12 & E9 & E11 & E13 & E18 & E22).
    destruct (table_next_WINV _ _ HW HM HN) as [HW2 HM2].
    pose proof (table_next_ATY (mkW s c r) _ HA HN) as HA2.
    refine (LENLENS_CORE X _ q2 ms2 EF H2 E17 E14 E12 E9 E11 E13 E18 E22 XO HW2 HA2 _ HM2).
    eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold tb_s2; cbn [is_mode iset_mode]; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| exact Pisr| bk_keep].
Qed.

Lemma arm_TABLE_of : arm_stmtg flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Proof. intros X w x12 ms EF HL XO HW HA HP HM. exact (table_core X w _ x12 ms EF HL XO HW HA HP HM). Qed.
End Table.
