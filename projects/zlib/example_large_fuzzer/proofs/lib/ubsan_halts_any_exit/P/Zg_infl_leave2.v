(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zg_infl_pure Zh_kit Z_updwin_pure Z_updwin Zg_updwin_pure Zg_updwin_iface Z_infl_leave Zg_infl_leave Z_infl_leave2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefUpdWin1 RefInflate_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma updw_core_wlen : forall s src e copy, arr_len (is_window s) = 32768 -> arr_len (is_window (updw_core s src e copy)) = 32768.
Proof.
  intros s src e copy H. unfold updw_core, sA. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] =>
           lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end end;
  destruct s; cbn in *; rewrite ?arr_len_blit; cbn; rewrite ?arr_len_blit; exact H.
Qed.

Lemma leave_decideG : forall W X w mode wsize o ms,
  ILVT W X w PC_LV_WIN (wz (il_S (ix_L X))) (wz mode) (wz wsize) (wz o) (wz (il_As (ix_L X))) ms ->
  16180 <= mode <= 16211 -> 0 <= wsize <= 32768 -> o = ir_out (w_r w) - ir_left (w_r w) -> 0 <= o < 2^31 ->
  0 <= ir_left (w_r w) < 2^31 -> 0 <= ix_flush X <= 4 ->
  evt psegs (fun ms' => exists x12, ILVT W X w (if lv_condv (ix_flush X) mode wsize o then PC_LV_CALL else PC_LV_TAIL)
                                         (wz (il_S (ix_L X))) x12 (wz wsize) (wz o) (wz (il_As (ix_L X))) ms') ms.
Proof.
  intros W X [s c r] mode wsize o ms HL RM RW EO RO RL RF. cbn [w_r] in *.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x16 & x17 & x18 & x21 & x22 & x23 & x26 & x27 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  cbn [w_r]. unfold lv_condv, BAD, CHECK, Z_FINISH.
  unfold PC_LV_WIN. zs. br_cases K.
  -
    replace (wsize =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb orb].
    zs. br_cases K1.
    +
      replace (o =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
      apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
    + replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
      do 3 zs. br_cases K2.
      *
        replace (mode <? 16209) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
        apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
      * replace (mode <? 16209) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
        do 2 zs. br_cases K3.
        --
           replace (ix_flush X =? 4) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rewrite orb_true_r.
           apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
        -- replace (ix_flush X =? 4) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rewrite orb_false_r.
           do 3 zs. br_cases K4.
           ++ replace (mode <? 16206) with true by (symmetry; apply Z.ltb_lt; lia).
              apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
           ++ replace (mode <? 16206) with false by (symmetry; apply Z.ltb_ge; lia).
              apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
  - replace (wsize =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb].
    apply evt_done. eexists. eapply ILVT_intro; try reflexivity. exact HMEM.
Qed.



Section LeaveW.
Hypothesis UPDW_HAVE : updwin_have_stmt.
Hypothesis UPDW_BLOCK : updwin_ret_block_stmt.

Lemma leave_call_haveG : forall X w b x12 x15 o ms,
  ILVT (ix_W X) X w PC_LV_CALL (wz (il_S (ix_L X))) x12 x15 (wz o) (wz (il_As (ix_L X))) ms ->
  ix_ok X -> ix_hasw X = true -> is_window_blk (w_s w) = Some b -> WFACTS (w_s w) ->
  0 <= o < 2^32 -> o <= ir_put (w_r w) -> ic_next_out (w_c w) = ir_put (w_r w) ->
  0 <= ir_put (w_r w) -> ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x10' x12' x15' x19' x25',
               ILVT (ix_WF X) X (mkW (updw_core (w_s w) (ic_outbuf (w_c w)) (ir_put (w_r w)) o) (w_c w) (w_r w)) PC_LV_TAIL x10' x12' x15' x19' x25' ms') ms.
Proof.
  intros X [s c r] b x12 x15 o ms HL XO HASW HB (Hwb & Hws & Hwn & Hwh & Hwl) RO ROP ENO RP RPL. cbn [w_s w_c w_r] in *.
  specialize (Hwl ltac:(rewrite HB; discriminate)).
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x16 & x17 & x18 & x21 & x22 & x23 & x26 & x27 & x28 & x29 & x30 & x31 & m & -> & (retw & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. pose proof (xo_win _ XO HASW) as XW. pose proof (xo_sw _ XO HASW) as XSW. pose proof (xo_ow _ XO HASW) as XOW. pose proof (xo_os _ XO) as XOS.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (SRC : bytes_at psegs m (il_NO (ix_L X) + ir_put r - o) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
  { replace (il_NO (ix_L X) + ir_put r - o) with (il_NO (ix_L X) + (ir_put r - o)) by lia.
    exact (iout_slice_bytes _ _ _ _ _ (ir_put r - o) o OUT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  unfold iout in OUT.
  open_IST ST. pose proof ZS as ZS0. open_izs ZS.
  assert (E224 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -224)) = bv_unsigned (ix_sp X) + -224) by (apply unsigned_lit; lia).
  apply (munch_weaken _ [(ix_lo X, bv_unsigned (ix_sp X)); (il_S (ix_L X), il_S (ix_L X) + 112); (il_As (ix_L X), il_As (ix_L X) + 7176);
                          (il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X))); (il_Aw (ix_L X), il_Aw (ix_L X) + 32768)]) in MU.
  2:{ unfold sub_fp. cbn [outside]. intros. tauto. }
  unfold PC_LV_CALL. do 4 zs. rewrite ENO.
  eapply evt_cut.
  { eapply (UPDW_HAVE (ix_L X) s c (ic_outbuf c) (ir_put r) o (il_NO (ix_L X) + ir_put r) (ix_lo X) b); rewrite ?E224;
      [ exact STK | exact ZS0 | exact GA | exact HB | exact Gwin | exact Hwl | exact SRC | exact Hwb | lia | exact Hws | exact Hwn | exact Hwh
      | lia | lia | lia | lia | lia | lia | lia | lia | exact XSW | lia | lia | unfold apart in XOW; lia | unfold apart in XOS; lia | exact MI ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E224 in *.
  pose proof (updw_core_wlen s (ic_outbuf c) (ir_put r) o Hwl) as LW'.
  pose proof (updw_core_shape s (ic_outbuf c) (ir_put r) o) as SH. cbv zeta in SH.
  set (s' := updw_core s (ic_outbuf c) (ir_put r) o) in *.
  set (W' := is_window s') in *. set (ws' := is_wsize s') in *. set (wn' := is_wnext s') in *. set (wh' := is_whave s') in *.
  clearbody W' ws' wn' wh'. clearbody s'. subst s'.
  clear GA Gwin STK ZS.
  itr_groups MUc WMc.
  clear SRC. transport_after_call psegs m m' MUc WMc.
  replace (ret_pc (wz 126676)) with (wz 126676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 2 zs. zs. br_true.
  apply evt_done. do 5 eexists. eapply ILVT_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS0|]. constructor; [exact GA'| exact GT| exact Gl| exact Gw| exact Gc| exact GW'| | ].
           - destruct ARRS as (A1 & A2 & A3 & A4). unfold iarrs, uw_set. ired. repeat (split; [assumption|]). intros _. exact LW'.
           - unfold ilay_ok, uw_set in *. ired. exact LAY. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_WF, ix_W; exact MU| exact WM].
Qed.



Lemma leave_from_malloc_blockG : forall X w A wb junk ms,
  ILVM (ix_WF X) X w PC_UW_RET (wz A) (fun m => rw_cells psegs m A [CB (Z.to_nat 32768) junk]) ms ->
  ix_ok X -> ix_hasw X = true -> il_Aw (ix_L X) = A -> blk_ok A 32768 ->
  is_window_blk (w_s w) = None -> WFACTS (w_s w) ->
  0 <= ir_out (w_r w) - ir_left (w_r w) < 2^32 -> ir_out (w_r w) - ir_left (w_r w) <= ir_put (w_r w) ->
  0 <= ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x10' x12' x15' x19' x25',
               ILVT (ix_WF X) X (mkW (updw_core (s_fresh (w_s w) wb junk) (ic_outbuf (w_c w)) (ir_put (w_r w)) (ir_out (w_r w) - ir_left (w_r w))) (w_c w) (w_r w))
                    PC_LV_TAIL x10' x12' x15' x19' x25' ms') ms.
Proof.
  intros X [s c r] A wb junk ms HL XO HASW EA BOK HB (Hwb & Hws & Hwn & Hwh & _) RO ROP RP. cbn [w_s w_c w_r] in *.
  set (o := ir_out r - ir_left r) in *.
  destruct HL as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x21 & x22 & x23 & x26 & x27 & t3 & t4 & t5 & t6 & m & -> & FRU & (retw & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM & WJ).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_WF, ix_W in MU; cbn [w_s w_c w_r app] in *.
  ix_open XO. pose proof (xo_win _ XO HASW) as XW. pose proof (xo_sw _ XO HASW) as XSW. pose proof (xo_ow _ XO HASW) as XOW. pose proof (xo_os _ XO) as XOS.
  pose proof (xo_iw _ XO HASW) as XIW. pose proof (xo_is _ XO) as XIS. pose proof XSW as XSW0.
  rewrite EA in *. unfold apart in XSW, XOW, XOS, XIW, XIS.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (SRC : bytes_at psegs m (il_NO (ix_L X) + ir_put r - o) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - o) o))).
  { replace (il_NO (ix_L X) + ir_put r - o) with (il_NO (ix_L X) + (ir_put r - o)) by lia.
    exact (iout_slice_bytes _ _ _ _ _ (ir_put r - o) o OUT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  unfold iout in OUT.
  open_IST ST.
  assert (E224 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -224)) = bv_unsigned (ix_sp X) + -224) by (apply unsigned_lit; lia).
  assert (HWF : is_wbits (s_fresh s wb junk) = 15 /\ (is_wsize (s_fresh s wb junk) <> 0 -> is_wsize (s_fresh s wb junk) = 32768)
                /\ 0 <= uw_wnext0 (s_fresh s wb junk) < 32768 /\ 0 <= uw_whave0 (s_fresh s wb junk) <= 32768) by exact (conj Hwb (conj Hws (conj Hwn Hwh))).
  destruct HWF as (Hwb' & Hws' & Hwn' & Hwh').
  replace (wz (bv_unsigned (ix_sp X) + -272)) with (wz (bv_unsigned (wz (bv_unsigned (ix_sp X) + -224)) + -48)) by (rewrite E224; f_equal; lia).
  eapply evt_cut.
  { eapply (UPDW_BLOCK (ix_L X) s (ic_outbuf c) (ir_put r) o (il_NO (ix_L X) + ir_put r) (ix_lo X) A wb junk (wz PC_LV_BACK) (wz (bv_unsigned (ix_sp X) + -224))); rewrite ?E224;
      [ replace (bv_unsigned (ix_sp X) + -224 + -48) with (bv_unsigned (ix_sp X) + -272) by lia; exact FRU
      | replace (bv_unsigned (ix_sp X) + -224 + -48) with (bv_unsigned (ix_sp X) + -272) by lia; exact STK
      | exact GA | exact HB | exact WJ | exact SRC | exact Hwb | lia | exact Hws | exact Hwn | exact Hwh
      | lia | lia | lia | lia | lia | lia | lia | exact XSW0 | lia | lia | lia | lia | exact MI ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E224 in *. rewrite <- EA in GA', GW'. rewrite il_setw_id in GA', GW'.
  pose proof (updw_core_wlen (s_fresh s wb junk) (ic_outbuf c) (ir_put r) o ltac:(unfold s_fresh; ired; unfold iarr_u8_of; apply arr_len_init)) as LW'.
  pose proof (updw_core_shape (s_fresh s wb junk) (ic_outbuf c) (ir_put r) o) as SH. cbv zeta in SH.
  set (s' := updw_core (s_fresh s wb junk) (ic_outbuf c) (ir_put r) o) in *.
  set (W' := is_window s') in *. set (ws' := is_wsize s') in *. set (wn' := is_wnext s') in *. set (wh' := is_whave s') in *.
  clearbody W' ws' wn' wh'. clearbody s'. subst s'.
  clear GA Gwin STK FRU WJ SRC.
  itr_groups MUc WMc.
  transport_after_call psegs m m' MUc WMc.
  replace (ret_pc (wz PC_LV_BACK)) with (wz PC_LV_BACK) by (symmetry; apply ret_pc_even; [unfold PC_LV_BACK; lia| reflexivity]).
  unfold PC_LV_BACK. do 2 zs. zs. br_true.
  apply evt_done. do 5 eexists. eapply ILVT_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS|]. constructor; [exact GA'| exact GT| exact Gl| exact Gw| exact Gc| exact GW'| | ].
           - destruct ARRS as (A1 & A2 & A3 & A4). unfold iarrs, uw_set, s_fresh. ired. repeat (split; [assumption|]). intros _. exact LW'.
           - destruct LAY as [LAY1 _]. unfold ilay_ok, uw_set, s_fresh. ired. split; [exact LAY1|]. intros _. rewrite EA. split; [exact BOK| exact XSW0]. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_WF, ix_W; cbn [app]; rewrite EA; exact MU| exact WM].
Qed.
End LeaveW.
