(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs Z_infl_c_pure Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_TABLE RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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

Definition PC_TABLE_J : Z := 0x1d890.

Definition PC_TABLE_L : Z := 0x1d558.

(* [comment removed for export] *)
Lemma table_loop : forall f X s c r q v8 ms,
  ILOOPg X (mkW s c r) PC_TABLE_L q ms -> sc12 q = wz (ir_bits r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc8 q = v8 ->
  ix_ok X -> REGS c r -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 14 -> 14 <= ir_bits r + 8 * Z.of_nat f ->
  evt psegs (NBG X s c (NEEDBITS_k f 14 (mkW s c r)) PC_TABLE_J
               (fun r1 q1 => sc27 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc8 q1 = v8)) ms.
Proof.
  induction f as [|f IH]; intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v8 ms HL E12 E26 E8 XO HREGS Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x26 v8.
  pose proof HMEM as ((jf0 & jf1 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_TABLE_L. ix_open XO.
  zs. br_cases K.
  - (* [comment removed for export] *)
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    do 2 zs.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia. br_cases K3.
    + (* [comment removed for export] *)
      rewrite (NB_pull f 14 s c r) by lia.
      eapply IH; [ eapply ILOOPg_intro; ired; [ireg .. |] | cbn [sc12]; rewrite E6; ireg | cbn [sc26]; rewrite E1; ireg | reflexivity
                 | exact XO | exact HREGS1 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    + (* [comment removed for export] *)
      rewrite (NB_pull f 14 s c r) by lia. rewrite (NB_done f 14 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPg_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * cbn [sc27 sc8]. rewrite E1. split; [ireg| reflexivity].
  - (* [comment removed for export] *)
    rewrite (NB_dry f 14 s c r) by lia.
    do 2 zs.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

(* [comment removed for export] *)
Lemma table_nb14 : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_TABLE x8 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> ir_bits r < 14 ->
  evt psegs (NBG X s c (NEEDBITS 14 (mkW s c r)) PC_TABLE_J (fun r1 q1 => sc27 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc8 q1 = x8)) ms.
Proof.
  intros X s c r x8 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf0 & jf1 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  unfold PC_TABLE. ix_open XO.
  do 2 zs. br_false. zs.
  rewrite NB_top.
  eapply (table_loop 8%nat X s c r (mkSC x5 x6 x7 x8 (wz (ir_bits r)) x13 x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 (wz (ir_out r))));
    [ eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | reflexivity | exact XO
    | exact HREGS | exact Pin | exact Pin1 | exact MFB | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

Local Ltac close_mem jf0 jf1 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf0, jf1, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma table_fin : forall flush X s c r q ms,
  ix_flush X = flush ->
  ILOOPg X (mkW s c r) PC_TABLE_J q ms -> sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> PATG X (mkW s c r) -> 14 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
     if (286 <? is_nlen (tb_s s (ir_hold r))) || (30 <? is_ndist (tb_s s (ir_hold r)))
     then exists x8, ILOOP X (mkW (iset_mode (tb_s s (ir_hold r)) BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) (tb_r r)) PC_DISPATCH x8 (wz BAD) ms'
     else exists q', ILOOPg X (mkW (tb_s2 s (ir_hold r)) c (tb_r r)) PC_LENLENS_E q' ms' /\ sc12 q' = wz (is_ncode (tb_s2 s (ir_hold r)))
                     /\ sc15 q' = wz 0 /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms EF HL E27 XO HP RB RH RPUT.
  iarm_openg HL. subst x27.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_TABLE_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  do 7 zs. rewrite tb_f1, (tb_f2 (ir_hold r) RH), (tb_f3 (ir_hold r) RH).
  destruct (tb_ranges (ir_hold r)) as (Ra & Rb & Rc).
  unfold tb_s2, tb_s, tb_r. cbn [is_nlen is_ndist is_ncode iset_ncode iset_ndist iset_nlen iset_have iset_mode].
  set (fa := ir_hold r mod 2^5) in *. set (fb := ir_hold r mod 2^10 / 2^5) in *. set (fc := ir_hold r mod 2^14 / 2^10) in *.
  do 8 zs. br_cases K1.
  { (* [comment removed for export] *)
    replace (286 <? fa + 257) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem jf0 jf1 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (286 <? fa + 257) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  do 2 zs. br_cases K2.
  { (* [comment removed for export] *)
    replace (30 <? fb + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem jf0 jf1 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (30 <? fb + 1) with false by (symmetry; apply Z.ltb_ge; lia).
  do 5 zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc15 sc26]; repeat split; reflexivity].
  close_mem jf0 jf1 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section Table.
Variable flush : Z.
Hypothesis LENLENS_CORE : lenlens_core_stmt flush.

Lemma table_core : forall X w x8 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_TABLE x8 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = TABLE ->
  evt psegs (fun ms' => IPOST X (arm_TABLE ivar_ref flush w) ms' /\ PATG X (wof (arm_TABLE ivar_ref flush w))) ms.
Proof.
  intros X [s c r] x8 x12 ms EF HL XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & MFB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (table_nb14 X s c r x8 x12 ms HL XO HREGS HP MFB)|].
  intros ms1 [(r1 & q1 & EN & HJ & E27 & _)|(r1 & EN & HLV)].
  2:{ rewrite (arm_TABLE_leave flush _ _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 14 s r r1 HREGS ltac:(lia) EN) as (_ & HPL & _). eapply PATG_pulled; [exact HP| exact HPL]. }
  destruct (NBG_run_facts c 14 s r r1 HREGS ltac:(lia) EN) as (HREGS1 & HPL & HB14 & _).
  destruct (nbG_r1_facts c r r1 14 HREGS1 HPL HB14) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  rewrite (arm_TABLE_eq flush s c r s c r1 EN ltac:(lia) ltac:(lia)).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (table_fin flush X s c r1 q1 ms1 EF HJ E27 XO HP1 ltac:(lia) RH1 ltac:(rewrite EP; lia)). }
  intros ms2 H2. unfold tb_res. cbv zeta.
  assert (HN : table_next (mkW s c r) = if (286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1))) then None
                                        else Some (mkW (tb_s2 s (ir_hold r1)) c (tb_r r1))).
  { unfold table_next. rewrite EN. reflexivity. }
  destruct ((286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1)))).
  - destruct H2 as (x8' & H2). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H2|]. cbn [wof].
    eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr.
  - destruct H2 as (q2 & H2 & E12 & E15 & E26).
    destruct (table_next_WINV _ _ HW HM HN) as [HW2 HM2].
    pose proof (table_next_ATY (mkW s c r) _ HA HN) as HA2.
    refine (LENLENS_CORE X _ q2 ms2 EF H2 E12 E15 E26 XO HW2 HA2 _ HM2).
    eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold tb_s2; cbn [is_mode iset_mode]; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..|]. exact Pisr.
Qed.

Lemma arm_TABLE_of : arm_stmtg flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Proof. intros X w x12 ms EF HL XO HW HA HP HM. exact (table_core X w _ x12 ms EF HL XO HW HA HP HM). Qed.
End Table.
