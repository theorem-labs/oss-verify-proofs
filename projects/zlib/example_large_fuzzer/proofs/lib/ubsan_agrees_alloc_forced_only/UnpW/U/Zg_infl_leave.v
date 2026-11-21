(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Zg_infl_leave.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Zg_infl_pure Z_adler32 Zh_kit Z_ukit Zg_infl_iface Z_infl_leave.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface ZChkAdl AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma iout_slice_bytes : forall m L rest0 c put a k, iout m L rest0 c put -> 0 <= a -> 0 <= k -> a + k <= put -> put <= Z.of_nat (length rest0) ->
  bytes_at usegs m (il_NO L + a) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) a k)).
Proof.
  intros m L rest0 c put a k H Ha Hk Hak Hp.
  pose proof (iout_prefix_bytes m L rest0 c put H ltac:(lia)) as HB.
  rewrite <- (av8_sub (ic_outbuf c) put a k) by lia.
  rewrite <- (firstn_skipn (Z.to_nat a) (av8 (ic_outbuf c) put)) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, av8_length, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn _ _)) in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  replace (il_NO L + a) with (il_NO L + Z.of_nat (Z.to_nat a)) by lia. exact HB.
Qed.

(* [comment removed for export] *)
Definition bZ_map8 := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_leave.bZ_map8.
Definition bZ_slice := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_leave.bZ_slice.

Section Leave.
Hypothesis ADLER32 : adler32_stmt.

Lemma adler32_callG : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B len lo : Z) (d : list byte),
  0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
  bytes_at usegs m B d -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 -> (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
  len = Z.of_nat (length d) ->
  evt usegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof. intros. subst. apply ADLER32; assumption. Qed.

Lemma leave_preG : forall X w ms,
  ILEAVE X w ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  ir_in (w_r w) = arr_len (ic_input (w_c w)) ->
  evt usegs (fun ms' => exists x12, ILVT (ix_W X) X (lv_r w) PC_LV_WIN (wz (is_wsize (w_s w))) x12 (wz (ir_left (w_r w))) (wz (ir_bits (w_r w))) ms') ms.
Proof.
  intros X [s c r] ms HL XO HW HA HP EIN. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (RM : HEAD <= is_mode s <= MEM) by exact (MF_mode_range _ _ _ _ HMF). unfold HEAD, MEM in RM.
  assert (RWS : 0 <= is_wsize s <= 32768).
  { destruct HCORE as (_ & _ & C3 & _ & _ & _ & C7 & _). destruct (Z.eq_dec (is_wsize s) 0) as [E|NE]; [lia|].
    rewrite (C3 NE), Pwb. change (shl32 1 15) with 32768. lia. }
  destruct HL as (x1 & x5 & x6 & x7 & x10 & x12 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_LEAVE. do 9 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. unfold lv_r, s_rest, c_rest. eapply ILVT_intro; ired; [ireg .. |].
  apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
  + eexists _, j0, jf. exact FRM.
  + exact STK.
  + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite ?wz_wrap64. close_cells ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.
Local Ltac lv_dtU :=
  do 3 zs;
  lazymatch goal with |- context [Z.b2z ?b] => pose proof (zb_b2z_range b) end;
  zs; rewrite (b2z_shl _ 6) by lia; change (2^6) with 64;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 6 zs;
  lazymatch goal with |- context [Z.b2z (Z.lxor ?m ?k <? 1)] => pose proof (zb_b2z_range (Z.lxor m k <? 1)) end;
  zs; rewrite (b2z_shl _ 7) by lia; change (2^7) with 128;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 8 zs; rewrite lor_b2z;
  lazymatch goal with |- context [Z.b2z (?a || ?b)] => pose proof (zb_b2z_range (a || b)) end;
  zs; rewrite (b2z_shl _ 8) by lia; change (2^8) with 256;
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF.
Lemma leave_totG : forall W X w x10 x12 x18 ms,
  ILVT W X w PC_LV_TOT x10 x12 (wz (ir_left (w_r w))) x18 ms -> sub_fp (ix_W X) W -> ix_ok X ->
  WINV w -> ATY (w_s w) -> PATG X w ->
  ic_avail_in (w_c w) = ir_have (w_r w) -> ic_avail_out (w_c w) = ir_left (w_r w) -> ic_next_out (w_c w) = ir_put (w_r w) ->
  ir_in (w_r w) = arr_len (ic_input (w_c w)) -> is_bits (w_s w) = ir_bits (w_r w) ->
  evt usegs (fun ms' => exists dtz x12' x14', 0 <= dtz < 2^31 /\
       ILVT W X (mkW (fst (lv_pre (w_s w) (w_c w) (w_r w))) (snd (lv_pre (w_s w) (w_c w) (w_r w))) (w_r w)) PC_LV_TAIL (wz dtz) x12' x14' (wz (ir_left (w_r w))) ms') ms.
Proof.
  intros W X [s c r] x10 x12 x18 ms HL HSUB XO HW HA HP HAI HAO ENO EIN Eb. cbn [w_s w_c w_r] in *.
  pose proof (okL_WINV 0 _ HW HA) as HOK.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (RM : HEAD <= is_mode s <= MEM) by exact (MF_mode_range _ _ _ _ HMF). unfold HEAD, MEM in RM.
  assert (RL : 0 <= is_last s <= 1) by lia.
  assert (RIN : 0 <= ir_in r < 2^31 /\ ir_in r - ir_have r = ir_next r) by (rewrite Pin in *; lia).
  destruct RIN as [RIN EIH].
  set (o := ir_out r - ir_left r) in *.
  assert (RPUT : ir_put r < 2^31) by (rewrite Pout in Rpl; lia).
  assert (RO : 0 <= o <= ir_put r) by exact POL.
  rewrite lv_pre_shape. cbv zeta.
  assert (EW : is_wrap s = 5) by exact Pw.
  assert (EO : wrap32 (ir_out r - ic_avail_out c) = o) by (rewrite HAO; fold o; apply wrap32_id; lia).
  assert (EI : wrap32 (ir_in r - ic_avail_in c) = ir_next r) by (rewrite HAI; rewrite EIH; apply wrap32_id; lia).
  rewrite EO, EI, EW, ENO. change (Z.land 5 4 =? 0) with false. cbn [negb andb].
  clear RH Rin HCORE HMF HWB PL PHD HREGS.
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x21 & x22 & x23 & x25 & x26 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU0 & WM).
  pose proof (conj MU0 I) as MUbox. clear MU0.
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; cbn [w_s w_c w_r] in *.
  pose proof (munch_refl (ix_W X) m) as MU. unfold ix_W in MU.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_LV_TOT. do 2 zs. fold o. do 2 zs. rewrite EIH.
  do 4 zs. rewrite !land_u32_small by lia. do 3 zs. rewrite !land_u32_small by lia. zs.
  do 2 zs.
  zs. rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw. do 2 zs.
  change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4. zs. zs. br_false. zs. br_cases K.
  -
    assert (EO0 : o = 0) by lia. rewrite EO0 in *. change (0 =? 0) with true. cbn [negb].
    lv_dtU.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _, _. split.
    2:{ eapply ILVT_intro; ired; [ireg .. |].
        unfold IMEMLW; cbn [w_s w_c w_r].
        split; [eexists _, _, _; unfold iframe_cells; exact FRM|]. split; [exact STK|].
        split; [ split;
           [ eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; rewrite ?wz_wrap64; close_cells ZS
           | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY] ] |].
        split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|]. split; [eassumption|].
        split; [destruct MUbox as [MUW _]; exact (munch_trans W _ _ _ MUW (munch_weaken (ix_W X) W _ _ HSUB MU))| exact WM]. }
    lia.
  - assert (EO1 : 0 < o) by lia.
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
    assert (EV : UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r - o) o)
                 = adler32_z_spec (is_check s) (il_NO (ix_L X) + (ir_put r - o)) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
    { unfold UPDATE_CHECK_bytes. ired. rewrite Pf0. cbn [Z.eqb negb]. unfold iadler32_upd.
      rewrite (adler32_z_spec_any (is_check s) _ _ (conj CK1 (conj CK2 CK3))) by lia.
      rewrite bZ_slice by (first [lia | intros i Hi; apply POB; lia]). reflexivity. }
    rewrite EV.
    do 2 zs. rewrite Pf0, ENO. do 7 zs.
    replace (il_NO (ix_L X) + ir_put r <? o) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite xor_guard_sub by lia. cbn [Z.b2z]. change (Z.land (Z.lxor 0 18446744073709551615) 1) with 1.
    gT. gF.
    do 2 zs. replace (il_NO (ix_L X) + ir_put r + - o) with (il_NO (ix_L X) + (ir_put r - o)) by lia. zs.
    assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply adler32_callG; [lia| lia| rewrite LSL; lia| rewrite LSL; lia| exact BY| eassumption| rewrite E256; exact STK| rewrite E256; lia| rewrite E256; lia
                            | rewrite LSL; lia| rewrite LSL; reflexivity]
      | cbv beta; unfold adler32_postS; rewrite ?E256; post_call usegs mm ] end.
    try clear STK. match goal with H : stk usegs _ (ix_lo X) _ |- _ => rename H into STK end.
    do 4 zs.
    lv_dtU.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _, _. split.
    2:{ eapply ILVT_intro; ired; [ireg .. |].
        unfold IMEMLW; cbn [w_s w_c w_r].
        split; [eexists _, _, _; unfold iframe_cells; exact FRM|]. split; [exact STK|].
        split; [ split;
           [ eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; rewrite ?wz_wrap64; close_cells ZS
           | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY] ] |].
        split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|]. split; [eassumption|].
        split; [destruct MUbox as [MUW _]; exact (munch_trans W _ _ _ MUW (munch_weaken (ix_W X) W _ _ HSUB MU))| exact WM]. }
    lia.
Qed.
End Leave.
