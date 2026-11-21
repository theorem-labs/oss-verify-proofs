From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_adler32 Zg_infl_a_type Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma arm_DICT_eq : forall flush s c r,
  arm_DICT ivar_ref flush (mkW s c r)
  = if is_havedict s =? 0 then
      ARet Z_NEED_DICT (let w := RESTORE (mkW s c r) in
                        mkW (w_s w) (icset_total_in (w_c w) (wrap64 (ic_total_in (w_c w) + wrap32 (ir_in r - ic_avail_in (w_c w))))) (w_r w))
    else arm_TYPE ivar_ref flush (mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
Proof.
  intros flush s c r. unfold arm_DICT, abind, gs. cbn [w_s]. destruct (is_havedict s =? 0); reflexivity.
Qed.

Lemma dict_total_in_eq : forall t X h,
  wz (t + Z.land (Z.land (bv_swrap 32 (Z.land X 18446744073709551615 - h)) 18446744073709551615) 4294967295)
  = wz (wrap64 (t + wrap32 (X - h))).
Proof.
  intros t X h. apply Z_to_bv_eqm. rewrite wrap64_mod, wrap32_mod.
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  rewrite !Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div]. change (4294967296 / 2) with 2147483648.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
(* the UBSan build zero-extends with sll 32 / srl 32 *)

Lemma dict_total_in_eq_u : forall t X h,
  wz (t + Z.land (Z.land (bv_swrap 32 (Z.land X 18446744073709551615 - h)) 18446744073709551615 ≪ 32) 18446744073709551615 ≫ 32)
  = wz (wrap64 (t + wrap32 (X - h))).
Proof.
  intros t X h. rewrite <- dict_total_in_eq. f_equal. f_equal.
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  set (y := Z.land (bv_swrap 32 (Z.land X (Z.ones 64) - h)) (Z.ones 64)).
  assert (Ry : 0 <= y < 2 ^ 64) by (subst y; rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.land_ones by lia.
  change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. nia.
Qed.
Definition DQ (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h13 q = wz (il_S (ix_L X)) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).
Lemma dict_core11 : forall flush X w q ms,
  ix_flush X = flush -> 0 <= flush <= 4 -> ILOOPh X w PC_DICT q ms -> DQ X (w_r w) q ->
  ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DICT ->
  evt usegs (fun ms' => IPOST X (arm_DICT ivar_ref flush w) ms' /\ PATG X (wof (arm_DICT ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms EF RF HL HQ XO HW HP HM.
  unfold DQ in HQ. hred_in HQ. cbn [w_r] in HQ. destruct HQ as (-> & -> & -> & -> & -> & ->).
  rewrite arm_DICT_eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D0. zs. br_false.
    do 17 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| exact Pgz| first [reflexivity | exact (PATG_noput _ _ _ _ HP)]..| | bk_keep]; exact HISR].
    cbn [IPOST]. eapply IRET_intro; inorm; [ireg .. | | intros _; unfold RST; cbn [w_c w_r]; ired; repeat split; exact HPUT0].
    apply IMEML_intro; inorm.
    + exists (wz (ir_ret r)), j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. close_cells ZS.
      all: first [apply dict_total_in_eq_u | apply dict_total_in_eq].
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
    { unfold w1. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR. }
    eapply (evt_cut usegs (fun ms' => exists x26' x12', ILOOP X w1 PC_TYPE x26' x12' ms')).
    2:{ intros ms1 (x26' & x12' & H1). exact (type_core flush X w1 x26' x12' ms1 EF RF H1 XO HW1 HP1 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D1'. zs. br_true.
    do 4 zs.
    remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_null_spec (ix_lo X)).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
    subst spw.
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE, iadler32_init. cbn [app]. inorm. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells, iadler32_init; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.
Lemma arm_DICT_ok : forall flush, 0 <= flush <= 4 -> arm_stmtg flush DICT PC_DICT (arm_DICT ivar_ref flush).
Proof.
  intros flush RF X w x12 ms EF HL XO HW _ HP HM.
  destruct (ILOOPh_of_ILOOP _ _ _ _ _ _ HL) as (q & HL' & _ & _ & HH).
  apply (dict_core11 flush X w q ms EF RF HL'); [|assumption ..].
  unfold hhome in HH. unfold DQ. destruct HH as (E9 & _ & _ & E13 & E18 & E22 & E24 & E25). repeat split; assumption.
Qed.
