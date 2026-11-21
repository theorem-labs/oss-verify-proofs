(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Zg_infl_a_type Zg_infl_a_dict.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_DICT DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ILOOP11 (X : ictx) (w : iw) (pc : Z) (x8 x11 x12 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x30 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 x8 (wz (il_S (ix_L X))) x11 x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 75072)
                 x27 (wz (il_NI (ix_L X) + ir_next (w_r w))) x28 (wz 30) x30 (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOP11_intro : forall X w pc x8 x11 x12 x1 x2 x3 x4 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 75072 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOP11 X w pc x8 x11 x12 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                          F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOP11. do 12 eexists. split; [reflexivity| assumption]. Qed.

Lemma dict_core11 : forall flush X w x8 x11 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 -> ILOOP11 X w PC_DICT x8 x11 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DICT ->
  evt psegs (fun ms' => IPOST X (arm_DICT ivar_ref flush w) ms' /\ PATG X (wof (arm_DICT ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] x8 x11 x12 ms EF RF HL XO HW HP HM. rewrite arm_DICT_eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HAV : ir_have r < 2^31 /\ ir_left r < 2^31) by (rewrite Pin in Rnh; lia).
  assert (HISR : ISR s) by (split; assumption).
  destruct (Z.eq_dec (is_havedict s) 0) as [D0|D1].
  -
    replace (is_havedict s =? 0) with true by (symmetry; apply Z.eqb_eq; exact D0). cbv zeta. rewrite RESTORE_eq. cbn [w_s w_c w_r].
    assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATG_noput _ _ _ _ HP)); right; left; exact HM).
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D0. zs. br_false.
    (* 1.4: j to the need-dict block; RESTORE's six stores plus total_in += in - avail_in (ld, ld, subw, zext, add, sd);
       li s5,2; j (as Zg_infl_a_dict's DICT walk) *)
    do 16 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| exact Pgz| first [reflexivity | exact (PATG_noput _ _ _ _ HP)]..|]; exact HISR].
    cbn [IPOST]. eapply IRET_intro; inorm; [ireg .. | | intros _; unfold RST; cbn [w_c w_r]; ired; repeat split; exact HPUT0].
    apply IMEML_intro; inorm.
    + exists (wz (ir_ret r)), jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. close_cells ZS.
      all: apply dict_total_in_eq.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    replace (is_havedict s =? 0) with false by (symmetry; apply Z.eqb_neq; exact D1).
    assert (D1' : is_havedict s = 1) by (destruct PHD; [contradiction| assumption]).
    set (w1 := mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
    assert (HW1 : WINV w1).
    { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
      rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. destruct HMF as [HMF1 HMF2].
      split; [split; [split; [exact HMF1| intros _; exact adler_canon_1]| exact HMF2]|]. split; [exact HWF| exact HWB]. }
    assert (HP1 : PATG X w1).
    { unfold w1. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
    eapply (evt_cut psegs (fun ms' => exists x8' x12', ILOOP X w1 PC_TYPE x8' x12' ms')).
    2:{ intros ms1 (x8' & x12' & H1). exact (type_core flush X w1 x8' x12' ms1 EF RF H1 XO HW1 HP1 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D1'. zs. br_true.
    do 5 zs.
    call (adler32_null_spec).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    do 10 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE, iadler32_init. cbn [app]. inorm. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells, iadler32_init; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.

Definition PC_DICTID_J : Z := 0x1d684.

Definition PC_DICTID_L : Z := 0x1d4b0.

Lemma dictid_loop : forall f X s c r q v8 ms,
  ILOOPg X (mkW s c r) PC_DICTID_L q ms -> sc13 q = wz (ir_bits r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc8 q = v8 ->
  ix_ok X -> REGS c r -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 32 -> 32 <= ir_bits r + 8 * Z.of_nat f ->
  evt psegs (NBG X s c (NEEDBITS_k f 32 (mkW s c r)) PC_DICTID_J
               (fun r1 q1 => sc8 q1 = v8 /\ sc12 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  induction f as [|f IH]; intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v8 ms HL E13 E26 E8 XO HREGS Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26 v8.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_DICTID_L. ix_open XO.
  zs. br_cases K.
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    do 2 zs.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia. br_cases K3.
    +
      rewrite (NB_pull f 32 s c r) by lia.
      eapply IH; [ eapply ILOOPg_intro; ired; [ireg .. |] | cbn [sc13]; rewrite E6; ireg | cbn [sc26]; rewrite E1; ireg | reflexivity
                 | exact XO | exact HREGS1 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    +
      rewrite (NB_pull f 32 s c r) by lia. rewrite (NB_done f 32 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPg_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * cbn [sc8 sc12]. rewrite E1. split; [reflexivity| ireg].
  -
    rewrite (NB_dry f 32 s c r) by lia.
    do 2 zs.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma dictid_nb32 : forall X s c r x12 ms,
  ILOOP X (mkW s c r) PC_DICTID (wz (-3)) x12 ms ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  evt psegs (NBG X s c (NEEDBITS 32 (mkW s c r)) PC_DICTID_J (fun r1 q1 => sc8 q1 = wz (-3) /\ sc12 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r x12 ms HL XO HREGS HP.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  unfold PC_DICTID. ix_open XO. rewrite NB_top.
  do 2 zs. br_cases K.
  -
    rewrite (NB_done 8 32 s c r) by lia.
    zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [sc8 sc12]. split; reflexivity.
  - zs.
    eapply (dictid_loop 8%nat X s c r (mkSC x5 x6 x7 (wz (-3)) (wz 31) (wz (ir_bits r)) x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
      [ eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | reflexivity | exact XO
      | exact HREGS | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma dictid_core : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_DICTID_J q ms -> sc8 q = wz (-3) -> sc12 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  evt psegs (fun ms' => exists x11' x12', ILOOP11 X (mkW (iset_mode (iset_check s (ZSWAP32 (ir_hold r))) DICT) (icset_adler c (ZSWAP32 (ir_hold r))) (irset_bits (irset_hold r 0) 0))
                                              PC_DICT (wz (-3)) x11' x12' ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E8 E12 XO HREGS HP.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x8 x12. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_DICTID_J. do 15 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  do 5 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP11_intro; ired; [ireg .. |].
  close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma arm_DICTID_ok : forall flush, 0 <= flush <= 4 -> arm_stmtg flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATG_noput _ _ _ _ HP)); left; exact HM).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [HWB0 HCK].

  eapply evt_cut; [exact (dictid_nb32 X s c r x12 ms HL XO HREGS HP)|].
  intros ms1 [(r1 & q1 & EN & HJ & E8 & E12)|(r1 & EN & HLV)].
  2:{ rewrite (arm_DICTID_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 32 s r r1 HREGS ltac:(lia) EN) as (_ & HPL & _). eapply PATG_pulled; [exact HP| exact HPL]. }
  rewrite (arm_DICTID_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  eapply evt_cut; [exact (dictid_core X s c r1 q1 ms1 HJ E8 E12 XO HREGS1 HP1)|].
  intros ms2 (x11' & x12' & H2).
  apply (dict_core11 flush X _ _ x11' x12' ms2 EF RF H2 XO).
  -
    unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split.
    { destruct HREGS1 as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & Rli & Rlo). unfold REGS, HB. ired. change (2 ^ 0) with 1.
      split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|]. split; [lia|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
    ired. unfold MF, WF. cbn. split; [split; [exact HWB0| lia]|]. split; [rewrite EOUT; exact HWF| intros E; rewrite EPUT; exact HPUT0].
  - eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DICT, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR].
    ired. rewrite EPUT, HPUT0. reflexivity.
  - reflexivity.
Qed.
