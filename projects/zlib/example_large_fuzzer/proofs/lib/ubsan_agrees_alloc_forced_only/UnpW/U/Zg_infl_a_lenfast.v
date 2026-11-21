(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit Z_infl_iface Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Zg_infl_iface Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastSafe RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_LEN1 RefInflateA_LEN2 RefInflateA_LENF RefInflateSafeF3 RefInflateSafeOK RefInflateSafeOK2. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma ff_typed_LEN : forall X s c r, WINV (mkW s c r) -> PATG X (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
  ir_bits r < 8 ->
  ff_typed X (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r.
Proof.
  intros X s c r HW HP HM GH GL GB.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [HTL HTD]).
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF.
  pose proof (WINV_len_okb _ HW HM) as OKB.
  destruct HCORE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  assert (RWS : is_wsize s = 0 \/ is_wsize s = 32768).
  { destruct (Z.eq_dec (is_wsize s) 0) as [E|NE]; [left; exact E| right]. rewrite (C3 NE), Pwb. reflexivity. }
  assert (RWH : is_whave s <= 32768 /\ is_wnext s <= 32768).
  { destruct RWS as [E|E]; [destruct (C6 E); lia| pose proof (C7 ltac:(rewrite E; lia)); lia]. }
  destruct (len_okb_fast s c r OKB GH GL GB) as (RN1 & RN2 & _).
  unfold ff_typed, RESTORE. cbv zeta. ired.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: clear HW HP HWB PL PHD POB POW PNP PHW Pwin C1 C2 C3 C6 C7 C8 C9.
  all: first [ clear RH; lia | exact (proj1 RH) | exact (proj2 RH) | rewrite Pin; exact Pin1 | rewrite Pout; exact Pout1
             | rewrite wrap32_id by (clear RH; lia); clear RH; lia | exact (cpok_ofs_ok _ _ _ _ HTL) | exact (cpok_ofs_ok _ _ _ _ HTD) | rewrite C13; lia ].
Qed.
Lemma PATG_call_out : forall X s c r s' c' hd bt,
  PATG X (mkW s c r) -> is_mode s = LEN -> ir_out r = arr_len (ic_outbuf c) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_window_blk s' = is_window_blk s -> is_window s' = is_window s -> is_last s' = is_last s -> is_havedict s' = is_havedict s ->
  (is_mode s' = LEN \/ is_mode s' = TYPE \/ is_mode s' = BAD) ->
  ic_input c' = ic_input c -> arr_len (ic_outbuf c') = arr_len (ic_outbuf c) ->
  (forall i, 0 <= i < ic_next_out c' -> 0 <= arr_get (ic_outbuf c') i < 256) ->
  0 <= ic_next_out c' -> ic_next_out c' + ic_avail_out c' = arr_len (ic_outbuf c) ->
  (is_back s' = is_back s \/ is_back s' = -1) ->
  PATG X (mkW s' c' (mkIR (ic_next_in c') (ic_avail_in c') (ic_next_out c') (ic_avail_out c') hd bt (ir_in r) (ir_out r) (ir_ret r))).
Proof.
  intros X s c r s' c' hd bt HP HM HOUT Ew Ewb Ehd Efl Ewk Ewn Ela Ehv Hmd Ein Eob OB Hp Hpl HBK.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  unfold PATG, OBYT, ISR. ired. rewrite Ew, Ewb, Ehd, Efl, Ewk, Ewn, Ela, Ehv, Ein, Eob.
  split; [exact Pw|]. split; [exact Pwb|]. split; [exact Phd|]. split; [left; exact Pf0|].
  split; [unfold LEN, TYPE, BAD, FLAGS, HCRC in *; lia|].
  split; [exact Pwin|]. split; [exact Pin|]. split; [exact Pin1|]. split; [exact Pout|]. split; [exact Pout1|].
  split; [split; assumption|].
  split.
  { split; [exact OB|]. split; [exact POW|]. split; [lia|].
    split; [| exact PHW].
    unfold NOPUTb. destruct Hmd as [E|[E|E]]; rewrite E; reflexivity. }
  unfold bk_ok in *. rewrite HM in PBK. pose proof (bkmax_range LEN) as BML. pose proof (bkmax_range (is_mode s')) as BM'.
  assert (BMX : bkmax (is_mode s') = 1050) by (unfold bkmax; destruct Hmd as [E|[E|E]]; rewrite E; reflexivity).
  rewrite BMX. destruct HBK as [E|E]; rewrite E; [| lia]. unfold bkmax in PBK. cbn in PBK. lia.
Qed.
Section LenFast.
Hypothesis INFFAST : inflate_fast_stmt.
Local Ltac close_T j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma len_fast : len_fast_stmt.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL (E9 & E10 & E18 & E22 & E24 & E25) E13 XO HW HP HM GH GL GB.
  cbn [h9 h10 h13 h18 h22 h24 h25] in E9, E10, E13, E18, E22, E24, E25. subst x9 x10 x13 x18 x22 x24 x25.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF.
  pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31 /\ ir_left r < 2^31) by (rewrite Pin in Rnh; rewrite Pout in Rpl; lia).
  pose proof (ff_typed_LEN X s c r HW HP HM GH GL GB) as FT.
  pose proof (WINV_lenfast_okb s c r HW HM GH GL) as LFO.
  pose proof (lenfast_okb_sound s c r LFO) as [FOK CUR]. clear LFO.
  pose proof (arm_LEN_safe (mkW s c r) s c r HW HM (Z.le_refl _)) as PST. rewrite (arm_LEN_fast s c r GH GL GB) in PST.
  unfold lf_res, lf_w in PST. cbv zeta in PST. unfold lf_res, lf_w. cbv zeta.
  change (inflate_fast (RESTORE (mkW s c r))) with (inflate_fast (mkW (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r)) in CUR.
  change (inflate_fast (RESTORE (mkW s c r))) with (inflate_fast (mkW (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r)) in PST.
  change (inflate_fast (RESTORE (mkW s c r))) with (inflate_fast (mkW (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r)).
  destruct (lf_shape' (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r) as (fh & fb & md & ob & fi & fo & ai & ao & omsg & Hmd & Es & Er & Ec).
  clear RH HCORE HMF HWB Pfl PL PHD.
  destruct HL as (m & -> & HMEM). hred.
  pose proof HMEM as ((j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LEN.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (il_As (ix_L X), il_As (ix_L X) + 168)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 3 zs. br_false. do 2 zs. br_false. do 2 zs. br_false.
  do 7 zs. do 2 zs.
  itr_groups MUf WMf.
  assert (HM1 : IMEM X (RESTORE (mkW s c r)) m1).
  { unfold RESTORE. apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ]. }
  clear FRM STK ZS GA GT Gl Gw Gc Gwin IN OUT MU WM MUf WMf LOB.
  eapply evt_cut.
  { eapply (INFFAST X (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r); [exact HM1 | exact XO | repeat split; reflexivity | exact FT | exact FOK]. }
  cbv beta. intros ms' (x5' & x6' & x7' & x10' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & -> & HM' & (EIN & ELEN & PUTM & OB')).
  replace (ret_pc (wz 134560)) with (wz 134560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  clear HM1 FT FOK.
  set (w1 := inflate_fast (mkW (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) r)) in *.
  clearbody w1. destruct w1 as [s1 c1 r1]. cbn [w_s w_c w_r] in Es, Er, Ec, CUR, PUTM, EIN, ELEN, OB', HM', PST. cbn [w_s w_c w_r].
  subst s1 r1. clear Ec ob fi fo ai ao omsg.
  unfold LOAD, RESTORE, InflateState.wset_r in HM', PST. cbv zeta in HM'. cbv zeta in PST. unfold LOAD, RESTORE, InflateState.wset_r. cbv zeta.
  unfold RESTORE in Hmd, CUR, PUTM, EIN, ELEN. cbv zeta in Hmd. cbv zeta in CUR. cbv zeta in PUTM. cbv zeta in EIN. cbv zeta in ELEN.
  ired_in HM'. ired_in PST. ired_in Hmd. ired_in CUR. ired_in PUTM. ired_in EIN. ired_in ELEN. ired.
  rewrite HM in Hmd.
  destruct CUR as (Cn1 & Ca1 & Cna & Cp1 & Cl1 & Cpl).
  assert (RMD : 0 <= md < 2^31) by (destruct Hmd as [E|[E|E]]; rewrite E; unfold LEN, TYPE, BAD; lia).
  assert (RA1 : ic_avail_in c1 < 2^31 /\ ic_avail_out c1 < 2^31) by (rewrite Pin in Cna; rewrite Pout in Cpl; lia).
  assert (RFB : 0 <= fb <= 63).
  { destruct (md =? TYPE); cbn [RefInflateSafeD.POST] in PST; destruct PST as [(_ & HR1 & _) _]; cbn [w_s w_c w_r] in HR1;
      destruct HR1 as (_ & _ & _ & _ & _ & _ & [RB1 _] & _); cbn [ir_bits] in RB1; exact RB1. }
  clear PST.
  pose proof HM' as ((j0' & jf' & FRM') & STK' & [ZS' ST'] & IN' & OUT' & MI' & MU' & WM').
  unfold iframe_cells in FRM'; unfold iin in IN'; unfold iout in OUT'; unfold ix_W in MU'.
  cbn [ir_in ir_out ir_ret ir_put w_s w_c w_r] in FRM', STK', ZS', ST', IN', OUT', MU'.
  pose proof (iout_bytes_length (ix_rest0 X) c1 (ic_next_out c1) ltac:(lia)) as LOB'. apply (f_equal Z.of_nat) in LOB'.
  open_IST ST'. open_isA GA. open_izs ZS'. open_isT GT. ired_in GA. ired_in GT.
  lazymatch type of Gwin with iwin _ _ ?sx => assert (PwinL : is_window_blk sx <> None -> ix_hasw X = true) by exact Pwin end.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m') as MUf'. pose proof (wmono_refl usegs m') as WMf'.
   do 7 zs. zs. do 3 zs. do 2 zs. zs.
  destruct Hmd as [Emd|[Emd|Emd]]; subst md.
  2:{
      zs. br_true. do 3 zs. zs.
      itr_groups MUf' WMf'.
      change (TYPE =? TYPE) with true. cbv beta iota delta [IPOST wof].
      apply evt_done. split.
      + eexists _, _. eapply ILOOP_intro; ired; [ireg .. |]. close_T j0' jf' FRM' STK' ZS' GA GT padT Gl Gw Gc Gwin ARRS LAY IN' OUT' MU' WM'.
      + eapply (PATG_call_out X s c r _ c1 fh fb HP HM HWF); try reflexivity; [right; left; reflexivity | exact EIN | exact ELEN | exact OB' | lia | exact Cpl | right; reflexivity]. }
  all: zs; if_cases K; br_norm K; [exfalso; unfold LEN, BAD, TYPE in K; lia | clear K]; zs.
  all: first [change (LEN =? TYPE) with false | change (BAD =? TYPE) with false]; cbv beta iota delta [IPOST wof].
  all: itr_groups MUf' WMf'.
  all: apply evt_done; split; [eexists _, _; eapply ILOOP_intro; ired; [ireg .. | close_T j0' jf' FRM' STK' ZS' GA GT padT Gl Gw Gc Gwin ARRS LAY IN' OUT' MU' WM'] |].
  all: eapply (PATG_call_out X s c r _ c1 fh fb HP HM HWF); try reflexivity;
       [first [left; reflexivity | right; right; reflexivity] | exact EIN | exact ELEN | exact OB' | lia | exact Cpl | left; reflexivity].
Qed.
End LenFast.
