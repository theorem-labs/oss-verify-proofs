(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zg_infl_pure Z_adler32 Zh_kit Zg_infl_iface Z_infl_leave.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface ZChkAdl AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma iout_slice_bytes : forall m L rest0 c put a k, iout m L rest0 c put -> 0 <= a -> 0 <= k -> a + k <= put -> put <= Z.of_nat (length rest0) ->
  bytes_at psegs m (il_NO L + a) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) a k)).
Proof.
  intros m L rest0 c put a k H Ha Hk Hak Hp.
  pose proof (iout_prefix_bytes m L rest0 c put H ltac:(lia)) as HB.
  rewrite <- (av8_sub (ic_outbuf c) put a k) by lia.
  rewrite <- (firstn_skipn (Z.to_nat a) (av8 (ic_outbuf c) put)) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, av8_length, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn _ _)) in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  replace (il_NO L + a) with (il_NO L + Z.of_nat (Z.to_nat a)) by lia. exact HB.
Qed.

Lemma bZ_map8 : forall l, (forall k, (k < length l)%nat -> 0 <= nth k l 0 < 256) -> bZ (map (Z_to_bv 8) l) = l.
Proof.
  intros l. induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [map bZ]. unfold bZ in IH |- *. cbn [map]. f_equal.
  - apply bv8_small. apply (H 0%nat). cbn. lia.
  - apply IH. intros k Hk. apply (H (S k)). cbn. lia.
Qed.

Lemma bZ_slice : forall a so n, 0 <= so -> 0 <= n -> (forall i, so <= i < so + n -> 0 <= arr_get a i < 256) ->
  bZ (map (Z_to_bv 8) (arr_slice a so n)) = arr_slice a so n.
Proof.
  intros a so n Hso Hn Hb. apply bZ_map8. intros k Hk. unfold arr_slice in *. rewrite arr_slice_nat_length in Hk.
  rewrite arr_slice_nat_nth by exact Hk. apply Hb. lia.
Qed.

Section Leave.
Hypothesis ADLER32 : adler32_stmt.

Lemma adler32_callG : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B len lo : Z) (d : list byte),
  0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
  bytes_at psegs m B d -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
  len = Z.of_nat (length d) ->
  evt psegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom psegs)).
Proof. intros. subst. apply ADLER32; assumption. Qed.

Lemma leave_preG : forall X w ms,
  ILEAVE X w ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  ir_in (w_r w) = arr_len (ic_input (w_c w)) ->
  evt psegs (ILVT (ix_W X) X (lv_w w) PC_LV_WIN (wz (il_S (ix_L X))) (wz (is_mode (w_s w))) (wz (is_wsize (w_s w)))
                  (wz (ir_out (w_r w) - ir_left (w_r w))) (wz (il_As (ix_L X)))) ms.
Proof.
  intros X [s c r] ms HL XO HW HA HP EIN. unfold lv_w. cbn [w_s w_c w_r] in *.
  pose proof (okL_WINV 0 _ HW HA) as HOK.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW)). cbn [w_s w_c w_r] in *.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (RM : HEAD <= is_mode s <= MEM) by exact (MF_mode_range _ _ _ _ HMF). unfold HEAD, MEM in RM.
  assert (RL : 0 <= is_last s <= 1) by lia.
  assert (RWS : 0 <= is_wsize s <= 32768).
  { destruct HCORE as (_ & _ & C3 & _ & _ & _ & C7 & _). destruct (Z.eq_dec (is_wsize s) 0) as [E|NE]; [lia|].
    rewrite (C3 NE), Pwb. change (shl32 1 15) with 32768. lia. }
  assert (RIN : 0 <= ir_in r < 2^31 /\ ir_in r - ir_have r = ir_next r) by (rewrite Pin in *; lia).
  destruct RIN as [RIN EIH].
  set (o := ir_out r - ir_left r) in *.
  assert (RPUT : ir_put r < 2^31) by (rewrite Pout in Rpl; lia).
  assert (RO : 0 <= o <= ir_put r) by exact POL.
  rewrite lv_pre_shape. cbv zeta.
  assert (EW : is_wrap (s_rest s r) = 5) by exact Pw.
  assert (EO : wrap32 (ir_out r - ic_avail_out (c_rest c r)) = o) by (cbn [c_rest ic_avail_out icset_avail_in icset_next_in icset_avail_out]; fold o; apply wrap32_id; lia).
  assert (EI : wrap32 (ir_in r - ic_avail_in (c_rest c r)) = ir_next r) by (cbn [c_rest ic_avail_in icset_avail_in]; rewrite EIN, <- Rnh; replace (ir_next r + ir_have r - ir_have r) with (ir_next r) by lia; apply wrap32_id; lia).
  rewrite EO, EI, EW. change (Z.land 5 4 =? 0) with false. cbn [negb andb].
  clear RH Rin HCORE HMF HWB PL PHD HREGS.
  destruct HL as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x24 & x27 & x28 & x29 & x30 & x31 & m & -> & (retw & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_LEAVE. do 2 zs. rewrite EIH. do 2 zs. fold o. do 6 zs. rewrite !land_u32_small by lia. do 3 zs. rewrite !land_u32_small by lia.
  do 6 zs. rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw. do 5 zs.
  change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4. zs. br_false. zs. br_cases K.
  -
    assert (EO0 : o = 0) by lia. rewrite EO0 in *. change (0 =? 0) with true. cbn [negb].
    do 3 zs. do 19 zs.
    itr_groups MUf WMf.
    apply evt_done. unfold s_rest, c_rest. cbn [fst snd]. eapply ILVT_intro; ired; [ireg .. |].
    apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
    + eexists _, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite !wz_wrap64. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite !wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    assert (EO1 : 0 < o) by lia.
    assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(_ & _ & _ & Pf)]; [exact Pf| exfalso; lia]).
    assert (HCK : adler_canon (is_check s)).
    { apply leave_okb_ok; [| rewrite Pw; discriminate| exact Pf0].
      unfold okL in HOK. cbn [w_s] in HOK.
      destruct ((is_mode s =? DICT) || (is_mode s =? MEM) || (is_mode s =? SYNC)) eqn:EM; [|apply andb_prop in HOK; exact (proj1 HOK)].
      exfalso. apply orb_prop in EM. destruct EM as [EM|EM]; [apply orb_prop in EM; destruct EM as [EM|EM]|]; apply Z.eqb_eq in EM.
      - pose proof (NOPUTb_false _ _ PNP (or_intror (or_introl EM))). lia.
      - pose proof (NOPUTb_false _ _ PNP (or_intror (or_intror EM))). lia.
      - rewrite EM in RM. unfold SYNC in RM. lia. }
    destruct HCK as (CK1 & CK2 & CK3).
    pose proof (iout_slice_bytes _ _ _ _ _ (ir_put r - o) o OUT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BY.
    assert (LSL : Z.of_nat (length (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))) = o).
    { rewrite length_map. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
    replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    assert (EV : UPDATE_CHECK_bytes (s_rest s r) (is_check (s_rest s r)) (arr_slice (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r) - o) o)
                 = adler32_z_spec (is_check s) (il_NO (ix_L X) + (ir_put r - o)) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
    { unfold UPDATE_CHECK_bytes, s_rest, c_rest. ired. rewrite Pf0. cbn [Z.eqb negb]. unfold iadler32_upd.
      rewrite (adler32_z_spec_any (is_check s) _ _ (conj CK1 (conj CK2 CK3))) by lia.
      rewrite bZ_slice by (first [lia | intros i Hi; apply POB; lia]). reflexivity. }
    rewrite EV.
    do 2 zs. rewrite Pf0. do 4 zs. br_true. replace (il_NO (ix_L X) + ir_put r + - o) with (il_NO (ix_L X) + (ir_put r - o)) by lia. zs.
    assert (E224 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -224)) = bv_unsigned (ix_sp X) + -224) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply adler32_callG; [lia| lia| rewrite LSL; lia| rewrite LSL; lia| exact BY| eassumption| rewrite E224; exact STK| rewrite E224; lia| rewrite E224; lia
                            | rewrite LSL; lia| rewrite LSL; reflexivity]
      | cbv beta; unfold adler32_postS; rewrite ?E224; post_call psegs mm ] end.
    try clear STK. match goal with H : stk psegs _ (ix_lo X) _ |- _ => rename H into STK end.
    do 7 zs. do 3 zs. do 19 zs.
    itr_groups MUf WMf.
    apply evt_done. unfold s_rest, c_rest. cbn [fst snd]. eapply ILVT_intro; ired; [ireg .. |].
    apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
    + eexists _, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite !wz_wrap64. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite !wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.
End Leave.
