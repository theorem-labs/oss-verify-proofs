(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_updwin_pure Z_updwin.

Module Z_infl_leave.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LV_WIN : Z := 0x21590.
Definition PC_LV_TAIL : Z := 0x215ec.

Definition lv_w (w : iw) : iw :=
  mkW (fst (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w)))
      (snd (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w))) (w_r w).

Definition IMEMLW (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  iframeL X (w_r w) m
  /\ stk usegs m (ix_lo X) (bv_unsigned (ix_sp X) + -256)
  /\ IREP m (ix_L X) (w_s w) (w_c w)
  /\ iin m X
  /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m.
Lemma IMEMLW_of_IMEML : forall X w m, IMEML X w m -> IMEMLW (ix_W X) X w m.
Proof. intros X w m H. exact H. Qed.
Definition ix_WF (X : ictx) : list ivl := ix_W X ++ [(il_Aw (ix_L X), il_Aw (ix_L X) + 32768)].

Definition ILVT (W : list ivl) (X : ictx) (w : iw) (pc : Z) (x10 x12 x13 x14 x19 : word) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x15 x16 x17 x18 x20 x21 x22 x23 x25 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X))) (wz (il_NO (ix_L X) + ir_put (w_r w))) x10 (wz (ix_flush X)) x12 x13 x14 x15 x16 x17 (wz (il_S (ix_L X))) x18 x19 x20 x21 (wz (ir_have (w_r w))) x23 x22 x25 (wz (ir_ret (w_r w))) x28 x29 x30 x31)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMLW W X w m.

Lemma ILVT_intro : forall W X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  (* 1.4 inflate registers: strm s2, put s1, have s7, ret s11, state s0; the 5th parameter (1.3.1 s3) is s4 *)
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X -> x18 = wz (il_S (ix_L X)) ->
  x9 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x11 = wz (ix_flush X) -> x23 = wz (ir_have (w_r w)) ->
  x27 = wz (ir_ret (w_r w)) -> x8 = wz (il_As (ix_L X)) -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  ILVT W X w pc x10 x12 x13 x14 x20 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ILVT. do 18 eexists. split; [reflexivity| assumption]. Qed.

Lemma b2z_shl : forall b n, 0 <= n -> Z.shiftl (Z.b2z b) n = Z.b2z b * 2^n.
Proof. intros b n Hn. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma lor_b2z : forall a b, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [|] [|]; reflexivity. Qed.
Ltac lv_dt :=
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
  do 2 zs; rewrite ?land_ones64, ?bv_swrap32_id by lia; gF;
  do 2 zs.

Lemma leave_pre : forall X w ms,
  ILEAVE X w ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  ir_in (w_r w) = arr_len (ic_input (w_c w)) ->
  evt usegs (fun ms' => exists x12, ILVT (ix_W X) X (lv_w w) PC_LV_WIN (wz (is_mode (w_s w))) x12 (wz (il_S (ix_L X))) (wz (is_wsize (w_s w)))
                  (wz (ir_out (w_r w) - ir_left (w_r w))) ms') ms.
Proof.
  intros X [s c r] ms HL XO HW HA HP EIN. unfold lv_w. cbn [w_s w_c w_r] in *.
  pose proof (okL_WINV 0 _ HW HA) as HOK.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (RM : HEAD <= is_mode s <= MEM) by exact (MF_mode_range _ _ _ _ HMF). unfold HEAD, MEM in RM.
  assert (RL : 0 <= is_last s <= 1) by lia.
  assert (RWS : 0 <= is_wsize s <= 32768).
  { destruct HCORE as (_ & _ & C3 & _ & _ & _ & C7 & _). destruct (Z.eq_dec (is_wsize s) 0) as [E|NE]; [lia|].
    rewrite (C3 NE), Pwb. change (shl32 1 15) with 32768. lia. }
  assert (RIN : 0 <= ir_in r <= 1 /\ ir_in r - ir_have r = ir_next r) by (rewrite Pin in *; lia).
  destruct RIN as [RIN EIH].
  set (o := ir_out r - ir_left r) in *.
  assert (RO : 0 <= o <= 1) by lia.
  rewrite lv_pre_shape. cbv zeta.
  assert (EW : is_wrap (s_rest s r) = 5) by exact Pw.
  assert (EO : wrap32 (ir_out r - ic_avail_out (c_rest c r)) = o) by (cbn [c_rest ic_avail_out icset_avail_in icset_next_in icset_avail_out]; fold o; apply wrap32_id; lia).
  assert (EI : wrap32 (ir_in r - ic_avail_in (c_rest c r)) = ir_next r) by (cbn [c_rest ic_avail_in icset_avail_in]; rewrite EIN, <- Rnh; replace (ir_next r + ir_have r - ir_have r) with (ir_next r) by lia; apply wrap32_id; lia).
  rewrite EO, EI, EW. change (Z.land 5 4 =? 0) with false. cbn [negb andb].
  clear RH Rin HCORE HMF HWB PL PHD HREGS.
  destruct HL as (x1 & x5 & x6 & x7 & x10 & x12 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_LEAVE. do 3 zs. fold o. do 2 zs. rewrite EIH.
  do 4 zs. rewrite !land_u32_small by lia. do 3 zs. rewrite !land_u32_small by lia. zs.
  do 6 zs.
  zs. rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw. do 2 zs.
  change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4. do 3 zs. zs. br_false. zs. br_cases K.
  -
    assert (EO0 : o = 0) by lia. rewrite EO0 in *. change (0 =? 0) with true. cbn [negb].
    do 3 zs.
    lazymatch goal with |- context [Z.b2z ?b] => pose proof (zb_b2z_range b) end.
    zs. rewrite (b2z_shl _ 6) by lia. change (2^6) with 64.
    do 2 zs. rewrite ?land_ones64, ?bv_swrap32_id by lia. gF.
    do 6 zs.
    lazymatch goal with |- context [Z.b2z (Z.lxor ?m ?k <? 1)] => pose proof (zb_b2z_range (Z.lxor m k <? 1)) end.
    zs. rewrite (b2z_shl _ 7) by lia. change (2^7) with 128.
    do 2 zs. rewrite ?land_ones64, ?bv_swrap32_id by lia. gF.
    do 8 zs. rewrite lor_b2z.
    lazymatch goal with |- context [Z.b2z (?a || ?b)] => pose proof (zb_b2z_range (a || b)) end.
    zs. rewrite (b2z_shl _ 8) by lia. change (2^8) with 256.
    do 2 zs. rewrite ?land_ones64, ?bv_swrap32_id by lia. gF.
    do 2 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. unfold s_rest, c_rest. cbn [fst snd]. eapply ILVT_intro; ired; [ireg .. |].
    apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
    + eexists _, j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite !wz_wrap64. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite !wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    assert (EO1 : o = 1) by lia. assert (EP : ir_put r = 1) by lia.
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
    pose proof (POB 0 ltac:(lia)) as RBY.
    pose proof (iout_byte_at _ _ _ _ _ 0 OUT ltac:(lia) ltac:(lia)) as BY. rewrite Z.add_0_r in BY.
    rewrite EO1 in *. change (1 =? 0) with false. cbn [negb].
    assert (EV : UPDATE_CHECK_bytes (s_rest s r) (is_check (s_rest s r)) (arr_slice (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r) - 1) 1)
                 = adler32_len1 (is_check s) (arr_get (ic_outbuf c) 0)).
    { unfold UPDATE_CHECK_bytes, s_rest, c_rest. ired. rewrite Pf0, EP. cbn [Z.eqb negb].
      change (arr_slice (ic_outbuf c) (1 - 1) 1) with [arr_get (ic_outbuf c) 0]. unfold iadler32_upd.
      apply adler32_model_len1; [exact (conj CK1 (conj CK2 CK3))| exact RBY]. }
    rewrite EV. rewrite EP in *.
    zs. rewrite Pf0. do 7 zs.
    replace (il_NO (ix_L X) + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite xor_guard_sub by lia. cbn [Z.b2z]. change (Z.land (Z.lxor 0 18446744073709551615) 1) with 1.
    gT. gF.
    do 3 zs. replace (il_NO (ix_L X) + 1 + - (1)) with (il_NO (ix_L X)) by lia. zs.
    remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_len1_spec (ix_lo X)).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RBY. } 1:{ exact BY. } 1:{ eassumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
    subst spw.
    do 4 zs.
    lv_dt.
    itr_groups MUf WMf.
    apply evt_done. eexists. unfold s_rest, c_rest. cbn [fst snd]. eapply ILVT_intro; ired; [ireg .. |].
    apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
    + eexists _, j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite !wz_wrap64. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite !wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. rewrite EP. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.


Definition IMEMF (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  stk usegs m (ix_lo X) (bv_unsigned (ix_sp X))
  /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m.

Definition IFIN (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
    ms = MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz rc) a1 a2 a3 a4 a5 a6 a7
                 (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
            (ix_F X) (ret_pc (ix_ra X)) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMF W X w m.

Definition IRETW (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 x8 x9 (wz rc) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (ix_F X) (wz PC_EPILOGUE) (ix_fc X) None m (seg_rom usegs)
    /\ IMEMLW W X w m.
Lemma IRETW_of_IRET : forall X rc w ms, IRET X rc w ms -> IRETW (ix_W X) X rc w ms.
Proof.
  intros X rc w ms (x1 & x5 & x6 & x7 & x8 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & E & HM & _).
  unfold IRETW. do 28 eexists. split; [exact E| exact HM].
Qed.
Lemma IRETW_intro : forall W X rc w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X -> x10 = wz rc -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  IRETW W X rc w (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz PC_EPILOGUE) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold IRETW. do 28 eexists. split; [reflexivity| assumption]. Qed.

Lemma epilogue_gen : forall W X rc w ms, IRETW W X rc w ms -> ix_ok X -> evt usegs (IFIN W X rc w) ms.
Proof.
  intros W X rc [s c r] ms HL XO.
  destruct HL as (x1 & x5 & x6 & x7 & x8 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m
                  & -> & (retw & j0 & jf & FRM) & STK & HREP & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM. cbn [w_s w_c w_r] in *. ix_open XO.
  unfold PC_EPILOGUE. do 14 zs.
  release_frame FRM STK (bv_unsigned (ix_sp X)).
  zs.
  apply evt_done. unfold IFIN. do 15 eexists. split; [reflexivity|].
  unfold IMEMF. cbn [w_s w_c w_r]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma epilogue_spec : forall X rc w ms, IRET X rc w ms -> ix_ok X -> evt usegs (IFIN (ix_W X) X rc w) ms.
Proof. intros X rc w ms H XO. exact (epilogue_gen _ X rc w ms (IRETW_of_IRET _ _ _ _ H) XO). Qed.

Lemma leave_tail : forall W X w x10 x12 x13 x14 x19 ms,
  ILVT W X w PC_LV_TAIL x10 x12 x13 x14 x19 ms -> ix_ok X ->
  0 <= ix_flush X <= 4 -> 0 <= ir_in (w_r w) < 2^32 -> 0 <= ir_have (w_r w) < 2^32 -> 0 <= ir_out (w_r w) < 2^32 -> 0 <= ir_left (w_r w) < 2^32 ->
  - 2^31 <= ir_ret (w_r w) < 2^31 ->
  evt usegs (IFIN W X (ret_model (ix_flush X) (wrap32 (ir_in (w_r w) - ir_have (w_r w))) (wrap32 (ir_out (w_r w) - ir_left (w_r w))) (w_r w)) w) ms.
Proof.
  intros W X [s c r] x10 x12 x13 x14 x19 ms HL XO RF RI RH RO RL RR. cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen W X _ _ ms1 H1 XO)].
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((retw & j0 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_r] in *. ix_open XO.
  unfold PC_LV_TAIL. do 12 zs. rewrite bufrule_clang by lia.
  unfold ret_model. change Z_FINISH with 4. change Z_OK with 0.
  destruct ((((wrap32 (ir_in r - ir_have r) =? 0) && (wrap32 (ir_out r - ir_left r) =? 0)) || (ix_flush X =? 4)) && (ir_ret r =? 0))%bool; cbn [Z.b2z].
  - zs. br_false. do 2 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
  - zs. br_true. do 1 zs. apply evt_done. eapply IRETW_intro; try reflexivity. exact HMEM.
Qed.
End Z_infl_leave.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_updwin_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_updwin OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_leave2.Z_infl_leave OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefUpdWin1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.

Module Z_infl_pro.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma inflate_prologue : forall (X : ictx) (s : inflate_state) (zc : ZCall)
         (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
  ix_m0 X = m -> ix_ok X ->
  izs m (ix_L X) (icall_of_zcall zc) -> IST m (ix_L X) s -> iin m X -> iout m (ix_L X) (ix_rest0 X) (icall_of_zcall zc) 0 ->
  stk usegs m (ix_lo X) (bv_unsigned (ix_sp X)) -> mem_inv usegs m ->
  (is_window_blk s <> None -> ix_hasw X = true) ->
  HEAD <= is_mode s <= SYNC -> 0 <= is_bits s < 64 -> 0 <= is_hold s < 2^64 ->
  0 <= zlength (zc_input zc) <= 1 -> 0 <= zc_avail_out zc <= 1 -> 0 <= ix_flush X <= 4 ->
  0 < il_NI (ix_L X) < 2^63 -> 0 < il_NO (ix_L X) < 2^63 ->
  evt usegs (fun ms' => exists x26 x12, ILOOP X (W0 s zc) PC_DISPATCH x26 x12 ms')
      (MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz (il_S (ix_L X))) (wz (ix_flush X)) a2 a3 a4 a5 a6 a7
               (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
          (ix_F X) (wz Z_INFLATE) (ix_fc X) None m (seg_rom usegs)).
Proof.
  intros X s zc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m EM0 XO ZS ST IN OUT STK MI HWIN RM RB RH RAI RAO RF RNI RNO.
  unfold Z_INFLATE, HEAD, SYNC in *. ix_open XO.
  pose proof (munch_refl (ix_W X) m) as MU. unfold ix_W in MU. pose proof (wmono_refl usegs m) as WM.
  unfold iin in IN. unfold iout in OUT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) (icall_of_zcall zc) 0 ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_izs ZS. cbn [icall_of_zcall ic_next_in ic_avail_in ic_total_in ic_next_out ic_avail_out ic_total_out ic_msg ic_adler] in ZS.
  open_IST ST. open_isA GA.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  carve_frame 256%nat STK.
  do 17 zs. br_true.
  zs. al8 (il_S (ix_L X)). gT.
  do 2 zs. br_true. do 2 zs. br_true. do 2 zs. br_true.
  zs. al8 (il_As (ix_L X)). gT.
  do 2 zs. br_true.
  do 6 zs. rewrite (swrap32_sub _ 16180) by (try reflexivity; lia).
  br_true. do 2 zs. br_true. do 2 zs. br_true.
  do 6 zs.
  br_cases KT.
  -
    do 35 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _.
    assert (ES : s_entry s = s) by (unfold s_entry; replace (is_mode s =? TYPE) with false by (symmetry; apply Z.eqb_neq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists _, _. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; [unfold isA, isA_cells; exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
  -
    do 2 zs. do 35 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _.
    assert (ES : s_entry s = iset_mode s TYPEDO) by (unfold s_entry; replace (is_mode s =? TYPE) with true by (symmetry; apply Z.eqb_eq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists _, _. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
Qed.
End Z_infl_pro.

Module Z_inflate_mem.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Stdio ZHarness.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import F_fwritex Z_ikit Z_updwin Zlib_iface Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma izs_of_pub : forall m L c z (p1 p2 : list byte),
  rw_cells usegs m (il_S L) (zs_pub (il_NI L + ic_next_in c) (ic_avail_in c) (ic_total_in c) (il_NO L + ic_next_out c) (ic_avail_out c) (ic_total_out c) p1 p2) ->
  izq m L z -> zs_msg z = ic_msg c -> zs_adler z = ic_adler c -> izs m L c.
Proof.
  intros m L c z p1 p2 PUB (dt & p3 & resv & PRIV) E1 E2. exists p1, p2, dt, p3, resv.
  unfold izs_call_cells. apply (proj2 (rw_cells_app usegs m _ _ _)). split.
  - exact PUB.
  - rewrite <- E1, <- E2. exact PRIV.
Qed.

Lemma izs_to_pub : forall m L c, izs m L c ->
  (exists p1 p2, rw_cells usegs m (il_S L) (zs_pub (il_NI L + ic_next_in c) (ic_avail_in c) (ic_total_in c) (il_NO L + ic_next_out c) (ic_avail_out c) (ic_total_out c) p1 p2))
  /\ izq m L (zstrm_of_icall c).
Proof.
  intros m L c (p1 & p2 & dt & p3 & resv & H). unfold izs_call_cells in H. apply (proj1 (rw_cells_app usegs m _ _ _)) in H. destruct H as [H1 H2].
  split; [exists p1, p2; exact H1|]. exists dt, p3, resv. exact H2.
Qed.

Lemma iin_of_compr : forall m C (comprc : list Z) ti,
  u8arr usegs m C (to_bytes comprc) -> 0 <= ti < zlength comprc ->
  u8ro usegs m (C + ti) (av8 (arr_of_list (zfirstn 1 (zskipn ti comprc))) (arr_len (arr_of_list (zfirstn 1 (zskipn ti comprc)))))
  /\ zlength (zfirstn 1 (zskipn ti comprc)) = 1.
Proof.
  intros m C comprc ti H Hti. unfold zlength in Hti.
  pose proof (u8arr_sub_bytes m C _ (Z.to_nat ti) 1%nat H ltac:(unfold to_bytes; rewrite length_map; lia)) as HB.
  replace (Z.of_nat (Z.to_nat ti)) with ti in HB by lia.
  unfold zfirstn, zskipn. change (Z.to_nat 1) with 1%nat.
  destruct (skipn (Z.to_nat ti) comprc) as [|c0 rest] eqn:ES.
  { exfalso. apply (f_equal (@length Z)) in ES. rewrite length_skipn in ES. cbn in ES. lia. }
  unfold to_bytes in HB. rewrite skipn_map, ES in HB. cbn [map firstn] in HB.
  split; [|reflexivity]. cbn [firstn]. rewrite arr_len_of_list. change (zlength [c0]) with 1.
  unfold u8ro. replace (av8 (arr_of_list [c0]) 1) with [Z_to_bv 8 c0]; [exact HB|].
  symmetry. apply list_ext_nth; [rewrite av8_length; reflexivity|]. intros k Hk. rewrite av8_length in Hk.
  assert (k = 0%nat) as -> by lia. change 0%nat with (Z.to_nat 0) at 1. rewrite (av8_nth _ 1 0) by lia. reflexivity.
Qed.

Lemma uncompr_split : forall m U (uc : list Z) to,
  u8arr usegs m U (to_bytes uc) -> 0 <= to < zlength uc ->
  let bs := to_bytes uc in
  let rest0 := firstn 1 (skipn (Z.to_nat to) bs) in
  length rest0 = 1%nat
  /\ u8arr usegs m U (firstn (Z.to_nat to) bs)
  /\ u8arr usegs m (U + to) rest0
  /\ u8arr usegs m (U + to + 1) (skipn (Z.to_nat to + 1) bs).
Proof.
  intros m U uc to H Hto. cbv zeta. unfold zlength in Hto.
  assert (LB : length (to_bytes uc) = length uc) by (unfold to_bytes; apply length_map).
  destruct (u8arr_split3 m U _ (Z.to_nat to) 1%nat H ltac:(lia)) as (H1 & H2 & H3).
  replace (Z.of_nat (Z.to_nat to)) with to in H2, H3 by lia. change (Z.of_nat 1) with 1 in H3.
  split; [rewrite length_firstn, length_skipn; lia|]. split; [exact H1|]. split; [|exact H3].
  apply (u8arr_of_rw_cells usegs m _ 1%nat). exact H2.
Qed.

Lemma map_upd_nat : forall (f : Z -> byte) (l : list Z) k v, (k < length l)%nat ->
  firstn k (map f l) ++ [f v] ++ skipn (k + 1) (map f l) = map f (upd_nat l k v).
Proof.
  intros f l. induction l as [|x l IH]; intros k v Hk; [cbn in Hk; lia|].
  destruct k as [|k]; cbn [upd_nat map firstn skipn Nat.add app].
  - reflexivity.
  - f_equal. apply IH. cbn in Hk. lia.
Qed.

Lemma to_bytes_zupd : forall (uc : list Z) to v, 0 <= to < zlength uc ->
  firstn (Z.to_nat to) (to_bytes uc) ++ [Z_to_bv 8 v] ++ skipn (Z.to_nat to + 1) (to_bytes uc) = to_bytes (zupd uc to v).
Proof.
  intros uc to v Hto. unfold zlength in Hto. unfold to_bytes, zupd.
  replace (to <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  apply map_upd_nat. lia.
Qed.

Lemma uncompr_join : forall m U (uc : list Z) to c put,
  0 <= to < zlength uc -> 0 <= put <= 1 ->
  let bs := to_bytes uc in
  let rest0 := firstn 1 (skipn (Z.to_nat to) bs) in
  u8arr usegs m U (firstn (Z.to_nat to) bs) ->
  u8arr usegs m (U + to) (iout_bytes rest0 c put) ->
  u8arr usegs m (U + to + 1) (skipn (Z.to_nat to + 1) bs) ->
  u8arr usegs m U (to_bytes (zstore uc to (arr_slice (ic_outbuf c) 0 put))).
Proof.
  intros m U uc to c put Hto Hput. cbv zeta. intros H1 H2 H3. unfold zlength in Hto.
  assert (LB : length (to_bytes uc) = length uc) by (unfold to_bytes; apply length_map).
  assert (L1 : length (firstn (Z.to_nat to) (to_bytes uc)) = Z.to_nat to) by (rewrite length_firstn; lia).
  assert (LR : length (firstn 1 (skipn (Z.to_nat to) (to_bytes uc))) = 1%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (iout_bytes_length _ c put ltac:(rewrite LR; lia)) as LO. rewrite LR in LO.
  apply rw_cells_of_u8arr in H2. rewrite LO in H2.
  pose proof (u8arr_join3k m U _ _ _ (Z.to_nat to) 1%nat L1 H1 ltac:(replace (Z.of_nat (Z.to_nat to)) with to by lia; exact H2)
                ltac:(replace (Z.of_nat (Z.to_nat to)) with to by lia; exact H3)) as HJ.
  assert (C01 : put = 0 \/ put = 1) by lia. destruct C01 as [-> | ->].
  - rewrite iout_bytes_0 in HJ. change (arr_slice (ic_outbuf c) 0 0) with (@nil Z). cbn [zstore].
    replace (firstn (Z.to_nat to) (to_bytes uc) ++ firstn 1 (skipn (Z.to_nat to) (to_bytes uc)) ++ skipn (Z.to_nat to + 1) (to_bytes uc)) with (to_bytes uc) in HJ; [exact HJ|].
    rewrite <- (firstn_skipn (Z.to_nat to) (to_bytes uc)) at 1. f_equal.
    rewrite <- (firstn_skipn 1 (skipn (Z.to_nat to) (to_bytes uc))) at 1. f_equal. rewrite skipn_skipn. f_equal. lia.
  - change (arr_slice (ic_outbuf c) 0 1) with [arr_get (ic_outbuf c) 0]. cbn [zstore].
    rewrite <- to_bytes_zupd by (unfold zlength; lia).
    replace (iout_bytes (firstn 1 (skipn (Z.to_nat to) (to_bytes uc))) c 1) with [Z_to_bv 8 (arr_get (ic_outbuf c) 0)] in HJ; [exact HJ|].
    pose proof (iout_bytes_nth (firstn 1 (skipn (Z.to_nat to) (to_bytes uc))) c 1 0 ltac:(lia)) as HN. change (Z.to_nat 0) with 0%nat in HN.
    destruct (iout_bytes (firstn 1 (skipn (Z.to_nat to) (to_bytes uc))) c 1) as [|b0 [|b1 l]]; cbn in LO; try lia. cbn in HN. congruence.
Qed.

Lemma IST_setw : forall m L s A, is_window_blk s = None -> IST m L s -> IST m (il_setw L A) s.
Proof.
  intros m L s A HB [GA GT Gl Gw Gc Gwin ARRS LAY]. constructor; try assumption.
  - unfold isA, isA_cells in *. rewrite HB in *. exact GA.
  - unfold iwin. rewrite HB. exact I.
  - unfold ilay_ok in *. destruct LAY as [L1 _]. split; [exact L1|]. intros NE. exfalso. apply NE. exact HB.
Qed.
Lemma izs_setw : forall m L c A, izs m L c -> izs m (il_setw L A) c.
Proof. intros m L c A H. exact H. Qed.


Lemma agree_iv : forall LBx SP m1 m2 lo hi, rheap_pres LBx SP m1 m2 -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> rclient_addr LBx SP a) -> Z_dview.agree_on lo hi m1 m2.
Proof. intros LBx SP m1 m2 lo hi H Hlo Hhi HC a Ha. apply H; [lia| apply HC; exact Ha]. Qed.

Lemma in_block_iv : forall LBx (b : block) a, In b LBx -> blk_addr b <= a < blk_addr b + blk_size b -> in_block LBx a.
Proof. intros LBx b a Hb Ha. exists b. split; assumption. Qed.

Lemma imem_heap_pres : forall (X : ictx) s c r put LBx SPx m1 m2 (bs bc bu : block),
  rheap_pres LBx SPx m1 m2 ->
  SPx <= bv_unsigned (ix_sp X) + -256 -> bv_unsigned (ix_sp X) <= il_S (ix_L X) -> il_S (ix_L X) + 112 < 2^63 -> 0 <= SPx ->
  In bs LBx -> blk_addr bs = il_As (ix_L X) -> blk_size bs = 7176 -> 0 < il_As (ix_L X) -> il_As (ix_L X) + 7176 < 2^63 ->
  In bc LBx -> blk_addr bc <= il_NI (ix_L X) -> il_NI (ix_L X) + arr_len (ix_input X) <= blk_addr bc + blk_size bc -> 0 < il_NI (ix_L X) -> blk_addr bc + blk_size bc < 2^63 ->
  In bu LBx -> blk_addr bu <= il_NO (ix_L X) -> il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)) <= blk_addr bu + blk_size bu -> 0 < il_NO (ix_L X) -> blk_addr bu + blk_size bu < 2^63 ->
  0 <= arr_len (ix_input X) -> 0 <= put <= Z.of_nat (length (ix_rest0 X)) ->
  is_window_blk s = None ->
  iframeL X r m1 -> IREP m1 (ix_L X) s c -> iin m1 X -> iout m1 (ix_L X) (ix_rest0 X) c put ->
  iframeL X r m2 /\ IREP m2 (ix_L X) s c /\ iin m2 X /\ iout m2 (ix_L X) (ix_rest0 X) c put.
Proof.
  intros X s c r put LBx SPx m1 m2 bs bc bu HP SP1 SP2 S63 SP0 Hbs Ebs1 Ebs2 As0 As63 Hbc Ebc1 Ebc2 NI0 Bc63 Hbu Ebu1 Ebu2 NO0 Bu63 RIN RPUT HB (retw & j0 & jf & FRM) [ZS ST] IN OUT.
  assert (STKC : forall lo hi, SPx <= lo -> hi < 2^63 -> Z_dview.agree_on lo hi m1 m2).
  { intros lo hi H1 H2. apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. left. lia. }
  split; [|split; [|split]].
  - exists retw, j0, jf. eapply Z_dview.rw_cells_agree; [exact FRM|]. apply STKC; [lia|].
    unfold iframe_cells. cbn [cells_size csize Nat.add]. lia.
  - split.
    + eapply izs_agree; [exact ZS|]. apply STKC; lia.
    + eapply IST_agree; [exact ST|]. split.
      * apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bs); [exact Hbs| lia].
      * intros NE. exfalso. apply NE. exact HB.
  - unfold iin in *. unfold u8ro in *. eapply Z_dview.bytes_at_agree; [exact IN|]. rewrite av8_length.
    apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bc); [exact Hbc| lia].
  - unfold iout in *. eapply Z_dview.u8arr_agree; [exact OUT|]. rewrite iout_bytes_length by lia.
    apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bu); [exact Hbu| lia].
Qed.

Lemma IREPq_relay : forall m L0 s z NI NO, IREPq m L0 s z -> IREPq m (Z_irep.mkIL (il_S L0) (il_As L0) (il_Aw L0) NI NO) s z.
Proof.
  intros m [S0 As0 Aw0 NI0 NO0] s z NI NO [(dt & p3 & resv & HZ) [GA GT Gl Gw Gc Gwin ARRS LAY]].
  split; [exists dt, p3, resv; exact HZ|]. constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
Qed.
End Z_inflate_mem.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LV_CALL : Z := 0x21594.
Definition PC_LV_BACK : Z := 0x215a4.

Definition lv_condv (flush mode wsize o : Z) : bool :=
  negb (wsize =? 0) || (negb (o =? 0) && (mode <? BAD) && ((mode <? CHECK) || negb (flush =? Z_FINISH))).

Lemma leave_decide : forall W X w mode x12 wsize o ms,
  ILVT W X w PC_LV_WIN (wz mode) x12 (wz (il_S (ix_L X))) (wz wsize) (wz o) ms ->
  16180 <= mode <= 16211 -> 0 <= wsize <= 32768 -> o = ir_out (w_r w) - ir_left (w_r w) -> 0 <= o <= 1 ->
  0 <= ir_left (w_r w) <= 1 -> 0 <= ix_flush X <= 4 ->
  evt usegs (fun ms' => exists x12' x14', ILVT W X w (if lv_condv (ix_flush X) mode wsize o then PC_LV_CALL else PC_LV_TAIL)
                                              (wz mode) x12' (wz (il_S (ix_L X))) x14' (wz o) ms') ms.
Proof.
  intros W X [s c r] mode x12 wsize o ms HL RM RW EO RO RL RF. cbn [w_r] in *.
  assert (ROUT : 0 <= ir_out r <= 2) by lia.
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((retw & j0 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_s w_c w_r] in FRM.
  cbn [w_r]. unfold lv_condv, BAD, CHECK, Z_FINISH.
  unfold PC_LV_WIN. zs. br_cases K.
  -
    replace (wsize =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb orb].
    do 2 zs. zs. br_cases K1.
    +
      replace (o =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
      apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
    + replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
      do 2 zs. zs. br_cases K2.
      *
        replace (mode <? 16209) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
        apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
      * replace (mode <? 16209) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
        zs. zs. br_cases K3.
        --
           replace (ix_flush X =? 4) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rewrite orb_true_r.
           apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
        -- replace (ix_flush X =? 4) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rewrite orb_false_r.
           do 2 zs. zs. br_cases K4.
           ++ replace (mode <? 16206) with true by (symmetry; apply Z.ltb_lt; lia).
              apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
           ++ replace (mode <? 16206) with false by (symmetry; apply Z.ltb_ge; lia).
              apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
  - replace (wsize =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb].
    apply evt_done. eexists _, _. eapply ILVT_intro; try reflexivity. exact HMEM.
Qed.


Definition WFACTS (s : inflate_state) : Prop :=
  is_wbits s = 15 /\ (is_wsize s <> 0 -> is_wsize s = 32768) /\ 0 <= uw_wnext0 s < 32768 /\ 0 <= uw_whave0 s <= 32768
  /\ (is_window_blk s <> None -> arr_len (is_window s) = 32768).

Lemma leave_call_have : forall X w b x10 x12 x14 o ms,
  ILVT (ix_W X) X w PC_LV_CALL x10 x12 (wz (il_S (ix_L X))) x14 (wz o) ms ->
  ix_ok X -> ix_hasw X = true -> is_window_blk (w_s w) = Some b -> WFACTS (w_s w) ->
  0 <= o <= 1 -> o <= ir_put (w_r w) -> ic_next_out (w_c w) = ir_put (w_r w) ->
  0 <= ir_put (w_r w) -> ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists x10' x12' x13' x14' x19',
               ILVT (ix_WF X) X (mkW (updw_core (w_s w) (ic_outbuf (w_c w)) (ir_put (w_r w)) o) (w_c w) (w_r w)) PC_LV_TAIL x10' x12' x13' x14' x19' ms') ms.
Proof.
  intros X [s c r] b x10 x12 x14 o ms HL XO HASW HB (Hwb & Hws & Hwn & Hwh & Hwl) RO ROP ENO RP RPL. cbn [w_s w_c w_r] in *.
  specialize (Hwl ltac:(rewrite HB; discriminate)).
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. pose proof (xo_win _ XO HASW) as XW. pose proof (xo_sw _ XO HASW) as XSW. pose proof (xo_ow _ XO HASW) as XOW. pose proof (xo_os _ XO) as XOS.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (SRC : bytes_at usegs m (il_NO (ix_L X) + ir_put r - o) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
  { assert (C01 : o = 0 \/ o = 1) by lia. destruct C01 as [-> | ->].
    - apply bytes_at_nil. lia.
    - replace (il_NO (ix_L X) + ir_put r - 1) with (il_NO (ix_L X) + (ir_put r - 1)) by lia.
      exact (iout_byte_at _ _ _ _ _ (ir_put r - 1) OUT ltac:(lia) ltac:(lia)). }
  unfold iout in OUT.
  open_IST ST. pose proof ZS as ZS0. open_izs ZS.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  apply (munch_weaken _ [(ix_lo X, bv_unsigned (ix_sp X)); (il_S (ix_L X), il_S (ix_L X) + 112); (il_As (ix_L X), il_As (ix_L X) + 7176);
                          (il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X))); (il_Aw (ix_L X), il_Aw (ix_L X) + 32768)]) in MU.
  2:{ unfold sub_fp. cbn [outside]. intros. tauto. }
  unfold PC_LV_CALL. do 4 zs. rewrite ENO.
  pose proof (updw_small s (ic_outbuf c) (ir_put r) o Hwb RO Hws Hwn Hwh) as EUW.
  eapply evt_cut.
  { eapply (updwin_have_spec (ix_L X) s c (ic_outbuf c) (ir_put r) o (il_NO (ix_L X) + ir_put r) (ix_lo X) b); rewrite ?E256;
      [ exact STK | exact ZS0 | exact GA | exact HB | exact Gwin | exact Hwl | exact SRC | exact Hwb | exact RO | exact Hws | exact Hwn | exact Hwh
      | lia | lia | lia | lia | lia | lia | lia | lia | exact XSW | lia | lia | unfold apart in XOW; lia | unfold apart in XOS; lia | exact MI | lia | exact XAl ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E256 in *. rewrite EUW in GA', GW' |- *.
  clear GA Gwin STK ZS.
  itr_groups MUc WMc.
  clear SRC. transport_after_call usegs m m' MUc WMc.
  replace (ret_pc (wz 136612)) with (wz 136612) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 2 zs. zs. br_true.
  apply evt_done. do 5 eexists. eapply ILVT_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS0|]. constructor; [exact GA'| exact GT| exact Gl| exact Gw| exact Gc| exact GW'| | ].
           - destruct ARRS as (A1 & A2 & A3 & A4). unfold iarrs, uw_set. ired. repeat (split; [assumption|]). intros _. rewrite arr_len_blit. exact Hwl.
           - unfold ilay_ok, uw_set in *. ired. exact LAY. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_WF, ix_W; exact MU| exact WM].
Qed.


Definition ILVM (W : list ivl) (X : ictx) (w : iw) (pc : Z) (a0v : word) (Pm : mem -> Prop) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18c x20 x21 x22 x23 x25 t3 t4 t5 t6 fj m,
    ms = MS (mkR (wz PC_UW_RET) (wz (bv_unsigned (ix_sp X) + -320)) (ix_gp X) (ix_tp X) t0 t1 t2
                 (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz (ir_out (w_r w) - ir_left (w_r w))) a0v a1 a2 a3 a4 a5 a6 a7
                 (wz 1) (wz (il_As (ix_L X))) (wz (ir_out (w_r w) - ir_left (w_r w))) x20 x21 (wz (ir_have (w_r w))) x23 x22 x25 (wz (ir_ret (w_r w))) t3 t4 t5 t6)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    (* 1.4: updatewindow saves inflate's s0..s5 = state, put, strm, (1.3.1 s2), out - left, (1.3.1 s4); inflate's s6..s11
       stay in registers *)
    /\ rw_cells usegs m (bv_unsigned (ix_sp X) + -320)
          [CB 8 fj; C8 x20; C8 (wz (ir_out (w_r w) - ir_left (w_r w))); C8 x18c; C8 (wz (il_S (ix_L X)));
           C8 (wz (il_NO (ix_L X) + ir_put (w_r w))); C8 (wz (il_As (ix_L X))); C8 (wz PC_LV_BACK)]
    /\ iframeL X (w_r w) m
    /\ stk usegs m (ix_lo X) (bv_unsigned (ix_sp X) + -320)
    /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
    /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m /\ Pm m.

Lemma leave_call_to_malloc : forall X w x10 x12 x14 ms,
  ILVT (ix_W X) X w PC_LV_CALL x10 x12 (wz (il_S (ix_L X))) x14 (wz (ir_out (w_r w) - ir_left (w_r w))) ms ->
  ix_ok X -> is_window_blk (w_s w) = None -> is_wbits (w_s w) = 15 -> ic_next_out (w_c w) = ir_put (w_r w) ->
  0 <= ir_put (w_r w) -> ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (ILVM (ix_W X) X w PC_MALLOC (wz 32768) (fun _ => True)) ms.
Proof.
  intros X [s c r] x10 x12 x14 ms HL XO HB Hwb ENO RP RPL. cbn [w_s w_c w_r] in *.
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold iout in OUT.
  open_IST ST. pose proof ZS as ZS0. open_izs ZS.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  unfold PC_LV_CALL. do 4 zs. rewrite ENO.
  eapply evt_cut.
  { eapply (updwin_to_malloc (ix_L X) s c (ir_out r - ir_left r) (il_NO (ix_L X) + ir_put r) (ix_lo X)); rewrite ?E256;
      [ exact STK | exact ZS0 | exact GA | exact HB | exact Hwb | lia | lia | lia | lia | lia | lia | exact MI | lia | exact XAl ]. }
  intros ms' PO. unfold uw_at_malloc in PO.
  destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & fj & -> & FRU & STK' & MUc & WMc & MIc).
  rewrite E256 in *. replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) in * by lia.
  clear STK ZS Gwin.
  itr_groups MUc WMc.
  transport_after_call usegs m m' MUc WMc.
  apply evt_done. unfold ILVM. cbn [w_s w_c w_r]. do 22 eexists. split; [reflexivity|].
  split; [exact FRU|]. split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split; [split; [exact ZS0| constructor; try assumption; unfold iwin; rewrite HB; exact I]|].
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_W; exact MU|]. split; [exact WM| exact I].
Qed.

Lemma leave_from_malloc_null : forall X w Pm ms,
  ILVM (ix_W X) X w PC_UW_RET (wz 0) Pm ms ->
  ix_ok X -> is_window_blk (w_s w) = None -> 0 <= ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (IFIN (ix_W X) X Z_MEM_ERROR (mkW (iset_mode (w_s w) MEM) (w_c w) (w_r w))) ms.
Proof.
  intros X [s c r] Pm ms HL XO HB RP. cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen _ X _ _ ms1 H1 XO)].
  destruct HL as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18c & x20 & x21 & x22 & x23 & x25 & t3 & t4 & t5 & t6 & fj & m & -> & FRU & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM & _).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold iout in OUT.
  open_IST ST.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  replace (wz (bv_unsigned (ix_sp X) + -320)) with (wz (bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) + -64)) by (rewrite E256; f_equal; lia).
  eapply evt_cut.
  { eapply (updwin_ret_null fj (ix_L X) s (ir_out r - ir_left r) (il_NO (ix_L X) + ir_put r) (ix_lo X) (wz PC_LV_BACK) (wz (bv_unsigned (ix_sp X) + -256))); rewrite ?E256;
      [ replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact FRU
      | replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact STK
      | exact GA | exact HB | lia | lia | lia | lia | lia | exact MI ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E256 in *.
  clear GA Gwin STK FRU.
  itr_groups MUc WMc.
  transport_after_call usegs m m' MUc WMc.
  replace (ret_pc (wz PC_LV_BACK)) with (wz PC_LV_BACK) by (symmetry; apply ret_pc_even; [unfold PC_LV_BACK; lia| reflexivity]).
  open_isA GA'. unfold PC_LV_BACK.
  pose proof (munch_refl [(il_As (ix_L X), il_As (ix_L X) + 168)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  do 2 zs. zs. br_false. do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eapply IRETW_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS|]. constructor; ired; [unfold isA, isA_cells; ired; close_cells GA'| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite HB; exact I| exact ARRS| exact LAY]. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [eassumption|]. split; [unfold ix_W; exact MU| exact WM].
Qed.

Lemma il_setw_id : forall L, il_setw L (il_Aw L) = L.
Proof. intros [a b c d e]. reflexivity. Qed.

Lemma leave_from_malloc_block : forall X w A wb junk ms,
  ILVM (ix_WF X) X w PC_UW_RET (wz A) (fun m => rw_cells usegs m A [CB (Z.to_nat 32768) junk]) ms ->
  ix_ok X -> ix_hasw X = true -> il_Aw (ix_L X) = A -> blk_ok A 32768 ->
  is_window_blk (w_s w) = None -> WFACTS (w_s w) ->
  0 <= ir_out (w_r w) - ir_left (w_r w) <= 1 -> ir_out (w_r w) - ir_left (w_r w) <= ir_put (w_r w) ->
  0 <= ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists x10' x12' x13' x14' x19',
               ILVT (ix_WF X) X (mkW (updw_core (s_fresh (w_s w) wb junk) (ic_outbuf (w_c w)) (ir_put (w_r w)) (ir_out (w_r w) - ir_left (w_r w))) (w_c w) (w_r w))
                    PC_LV_TAIL x10' x12' x13' x14' x19' ms') ms.
Proof.
  intros X [s c r] A wb junk ms HL XO HASW EA BOK HB (Hwb & Hws & Hwn & Hwh & _) RO ROP RP. cbn [w_s w_c w_r] in *.
  set (o := ir_out r - ir_left r) in *.
  destruct HL as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18c & x20 & x21 & x22 & x23 & x25 & t3 & t4 & t5 & t6 & fj & m & -> & FRU & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM & WJ).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_WF, ix_W in MU; cbn [w_s w_c w_r app] in *.
  ix_open XO. pose proof (xo_win _ XO HASW) as XW. pose proof (xo_sw _ XO HASW) as XSW. pose proof (xo_ow _ XO HASW) as XOW. pose proof (xo_os _ XO) as XOS.
  pose proof (xo_iw _ XO HASW) as XIW. pose proof (xo_is _ XO) as XIS. pose proof XSW as XSW0.
  rewrite EA in *. unfold apart in XSW, XOW, XOS, XIW, XIS.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (SRC : bytes_at usegs m (il_NO (ix_L X) + ir_put r - o) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
  { assert (C01 : o = 0 \/ o = 1) by lia. destruct C01 as [E0 | E1]; rewrite ?E0, ?E1.
    - apply bytes_at_nil. lia.
    - replace (il_NO (ix_L X) + ir_put r - 1) with (il_NO (ix_L X) + (ir_put r - 1)) by lia.
      exact (iout_byte_at _ _ _ _ _ (ir_put r - 1) OUT ltac:(lia) ltac:(lia)). }
  unfold iout in OUT.
  open_IST ST.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  assert (HWF : is_wbits (s_fresh s wb junk) = 15 /\ (is_wsize (s_fresh s wb junk) <> 0 -> is_wsize (s_fresh s wb junk) = 32768)
                /\ 0 <= uw_wnext0 (s_fresh s wb junk) < 32768 /\ 0 <= uw_whave0 (s_fresh s wb junk) <= 32768) by exact (conj Hwb (conj Hws (conj Hwn Hwh))).
  destruct HWF as (Hwb' & Hws' & Hwn' & Hwh').
  pose proof (updw_small (s_fresh s wb junk) (ic_outbuf c) (ir_put r) o Hwb' ltac:(lia) Hws' Hwn' Hwh') as EUW.
  replace (wz (bv_unsigned (ix_sp X) + -320)) with (wz (bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) + -64)) by (rewrite E256; f_equal; lia).
  eapply evt_cut.
  { eapply (updwin_ret_block fj (ix_L X) s (ic_outbuf c) (ir_put r) o (il_NO (ix_L X) + ir_put r) (ix_lo X) A wb junk (wz PC_LV_BACK) (wz (bv_unsigned (ix_sp X) + -256))); rewrite ?E256;
      [ replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact FRU
      | replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact STK
      | exact GA | exact HB | exact WJ | exact SRC | exact Hwb | lia | exact Hws | exact Hwn | exact Hwh
      | lia | lia | lia | lia | lia | lia | lia | exact XSW0 | lia | lia | lia | lia | exact MI ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E256 in *. rewrite <- EA in GA', GW'. rewrite il_setw_id in GA', GW'.
  rewrite EUW in GA', GW' |- *.
  clear GA Gwin STK FRU WJ SRC.
  itr_groups MUc WMc.
  transport_after_call usegs m m' MUc WMc.
  replace (ret_pc (wz PC_LV_BACK)) with (wz PC_LV_BACK) by (symmetry; apply ret_pc_even; [unfold PC_LV_BACK; lia| reflexivity]).
  unfold PC_LV_BACK. do 2 zs. zs. br_true.
  apply evt_done. do 5 eexists. eapply ILVT_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS|]. constructor; [exact GA'| exact GT| exact Gl| exact Gw| exact Gc| exact GW'| | ].
           - destruct ARRS as (A1 & A2 & A3 & A4). unfold iarrs, uw_set, s_fresh. ired. repeat (split; [assumption|]). intros _. rewrite arr_len_blit. unfold iarr_u8_of. apply arr_len_init.
           - destruct LAY as [LAY1 _]. unfold ilay_ok, uw_set, s_fresh. ired. split; [exact LAY1|]. intros _. rewrite EA. split; [exact BOK| exact XSW0]. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_WF, ix_W; cbn [app]; rewrite EA; exact MU| exact WM].
Qed.
