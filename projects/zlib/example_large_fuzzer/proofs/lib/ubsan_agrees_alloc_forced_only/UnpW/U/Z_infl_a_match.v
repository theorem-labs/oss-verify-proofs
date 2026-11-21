(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_MATCH1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_MATCH_J : Z := 0x21478.   (* [comment removed for export] *)
Definition PC_MATCH_T : Z := 0x214a0.   (* [comment removed for export] *)

Definition mt_s1 (s : inflate_state) : inflate_state := iset_length s (is_length s - 1).
Definition mt_c1 (s : inflate_state) (c : icall) : icall := icset_outbuf c (arr_set (ic_outbuf c) 0 (arr_get (is_window s) (mt_idx s))).
Definition mt_r1 (r : iregs) : iregs := irset_put (irset_left r 0) 1.

(* [comment removed for export] *)
Lemma match_tail : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_MATCH_T q ms ->
  h9 q = wz (il_NO (ix_L X) + ir_put r) -> h10 q = wz (-2) -> h18 q = wz (ir_bits r) -> h22 q = wz (ir_hold r) ->
  h24 q = wz (ir_have r) -> h25 q = wz (il_NI (ix_L X) + ir_next r) ->
  h11 q = wz (il_Aw (ix_L X) + mt_idx s) -> h12 q = wz 1 -> h13 q = wz (bv_swrap 32 (is_length s)) -> h14 q = wz 1 ->
  ix_ok X -> ix_hasw X = true -> is_window_blk s <> None -> 0 <= mt_idx s < 32768 -> 0 <= arr_get (is_window s) (mt_idx s) < 256 ->
  ir_left r = 1 -> ir_put r = 0 -> arr_len (ic_outbuf c) = 1 -> length (ix_rest0 X) = 1%nat -> 1 <= is_length s < 2^32 -> 0 <= is_mode s < 2^31 ->
  evt usegs (IPOST X (if is_length s - 1 =? 0 then ARun tt (mkW (iset_mode (mt_s1 s) LEN) (mt_c1 s c) (mt_r1 r)) else ARun tt (mkW (mt_s1 s) (mt_c1 s c) (mt_r1 r)))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         E9 E10 E18 E22 E24 E25 E11 E12 E13 E14 XO HASW NWB RIDX RBYTE HL1 HP0 HOB HR0 RLEN RMODE.
  iarm_openh HL. subst. ix_open XO.
  pose proof (xo_win _ XO HASW) as XWin.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  open_IST ST. open_isA GA.
  unfold iwin in Gwin. destruct (is_window_blk s) as [wb|] eqn:EWB; [|contradiction]. clear NWB.
  pose proof (munch_refl (ix_Wf X) m) as MUf; unfold ix_Wf in MUf; pose proof (wmono_refl usegs m) as WMf.
  unfold PC_MATCH_T.
  do 2 zs.
  zs. rewrite bv_swrap32_sub_land. set (l1 := bv_swrap 32 (is_length s - 1)). pose proof (bv_swrap32_range (is_length s - 1)) as Rl1. fold l1 in Rl1.
  do 3 zs.
  (* [comment removed for export] *)
  do 2 zs. gF. zs. gF.
  ld8 Gwin (is_window s) 32768 (il_Aw (ix_L X)) (mt_idx s) ltac:(exact RBYTE).
  do 3 zs.
  pose proof (u8arr_store_ok usegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(lia) eq_refl) as SOK.
  zs. rewrite le1_wz_byte by exact RBYTE.
  pose proof (u8arr_write usegs _ _ _ (ir_put r) (Z_to_bv 8 (arr_get (is_window s) (mt_idx s))) OUT ltac:(lia)) as OUT2. clear OUT LOB.
  store_done.
  rewrite iout_bytes_store in OUT2 by lia.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (arr_get (is_window s) (mt_idx s)))) (ir_put r + 1) ltac:(lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  zs. gF. do 4 zs. zstep. br_cases K.
  - apply (proj1 (land64_zero_iff l1 ltac:(lia))) in K. unfold l1 in K. apply (proj1 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))) in K.
    replace (is_length s - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact K).
    do 4 zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; try ireg.
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; ired.
    + exists j0, jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; ired; exact LAY].
    + exact IN.
    + unfold iout; exact OUT2.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (K' : is_length s - 1 <> 0).
    { intros E. apply K. apply (proj2 (land64_zero_iff l1 ltac:(lia))). unfold l1. apply (proj2 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))). exact E. }
    replace (is_length s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact K').
    zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; try ireg.
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; ired.
    + exists j0, jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; ired; exact LAY].
    + exact IN.
    + unfold iout; exact OUT2.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.

Local Ltac fin_cut HMEM EIDX :=
  apply evt_done; eexists; split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
  cbn [h9 h10 h11 h12 h13 h14 h18 h22 h24 h25]; rewrite EIDX; rewrite ?land_u32_small by lia; repeat split; ireg.
(* [comment removed for export] *)
Local Ltac clamps HMEM EIDX ESL sl s :=
  let K5 := fresh "K5" in
  do 3 zs; gX; zs; zs; rewrite ESL; zstep; br_cases K5;
  [   gF; zs; fin_cut HMEM EIDX
  |
    let Esl := fresh "Esl" in let B1 := fresh "B" in let B2 := fresh "B" in
    let K6 := fresh "K6" in
    assert (B1 : 0 <= is_length s < 2^32) by lia; pose proof K5 as K6; unfold sl in K6;
    lazymatch type of K6 with _ <= ?y => assert (B2 : 0 <= y < 2^31) by lia end;
    apply (proj1 (sx32u_le_small (is_length s) _ B1 B2)) in K6;
    assert (Esl : sl = is_length s) by (unfold sl; apply bv_swrap32_id; lia);
    zs; rewrite Esl; gF; zs; rewrite <- Esl; fin_cut HMEM EIDX ].

Lemma match_core : forall X w x26 x12 ms,
  ILOOP X w PC_MATCH x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = MATCH ->
  evt usegs (fun ms' => IPOST X (arm_MATCH ivar_ref w) ms' /\ PATI X (wof (arm_MATCH ivar_ref w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & Hoff).
  destruct (match_win_facts s HCORE Pwb) as (Hws & Hwh & Hwn & HWIN). apply (id : _ -> hide _) in HWIN.
  assert (Csane : is_sane s = 1) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Clen : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RMODE : 0 <= is_mode s < 2^31) by (rewrite HM; unfold MATCH; lia).
  apply (id : _ -> hide _) in Pisr. apply (id : _ -> hide _) in Pwin. apply (id : _ -> hide _) in POW.
  clear HCORE HWF HWB Pfl Pgz PNP RH Rin PHW.
  pose proof HMEM as ((j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_MATCH.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zs. zstep. br_cases K.
  - (* [comment removed for export] *)
    assert (Kl : ir_left r = 0) by lia.
    rewrite (arm_MATCH_eq s c r Csane). replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 3 zs. unfold hide in Pwin.
    itr_groups MUf WMf.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
    apply IMEML_intro; ired.
    + exists (wz (ir_ret r)), j0, jf. unfold iframe_cells. rewrite Kl. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; ired; close_cells ZS.
    + constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (HL1 : ir_left r = 1) by lia. assert (HP0 : ir_put r = 0) by lia. assert (HO1 : ir_out r = 1) by lia.
    rewrite (arm_MATCH_pat s c r Csane HL1 HO1 HP0) by lia.
    do 4 zs. rewrite Z.add_0_r. zs. br_cases K2.
    { exfalso. rewrite HO1, HL1 in K2. change (1 - 1) with 0 in K2. apply (proj2 (Z.nlt_ge _ _)) in K2. apply K2. apply sx32u_lt_small; lia. }
    clear K2. replace (ir_out r - ir_left r) with 0 by lia.
    do 3 zs. rewrite Z.sub_0_r in *. br_cases K3.
    2:{ (* [comment removed for export] *)
        assert (Kf : is_whave s < is_offset s) by (apply Z.nle_gt; intros C; apply (proj2 (Z.nle_gt _ _) K3); apply sx32u_le_small; lia).
        replace (is_whave s <? is_offset s) with true by (symmetry; apply Z.ltb_lt; exact Kf).
        open_isT GT. do 2 zs. rewrite Csane. zs. br_false.
        do 5 zs. unfold hide in Pwin.
        itr_groups MUf WMf.
        apply evt_done. split.
        - cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; try ireg.
          apply IMEM_intro; ired.
          + exists j0, jf. exact FRM.
          + exact STK.
          + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; ired; close_cells ZS.
          + constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| unfold isT, isT_cells; exists padT; ired; close_cells GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
          + exact IN.
          + unfold iout; exact OUT.
          + eassumption.
          + exact MU.
          + exact WM.
        - cbn [wof]. unfold hide in Pisr. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    (* [comment removed for export] *)
    assert (Kok : is_offset s <= is_whave s) by (apply (proj1 (sx32u_le_small (is_offset s) (is_whave s) ltac:(lia) ltac:(lia))); exact K3).
    replace (is_whave s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; exact Kok).
    destruct (HWIN ltac:(lia)) as (EWS & NWB & RIDX & WN).
    assert (HASW : ix_hasw X = true) by (apply Pwin; exact NWB).
    assert (RBYTE : 0 <= arr_get (is_window s) (mt_idx s) < 256).
    { apply POW. destruct ARRS as (_ & _ & _ & AW). rewrite (AW NWB). exact RIDX. }
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| contradiction]).
    rewrite EWA in GA. pose proof (xo_win _ XO HASW) as XWin.
    pose proof (bv_swrap32_range (is_length s)) as RSL. pose proof (sx32_wz_u (is_length s)) as ESL.
    set (sl := bv_swrap 32 (is_length s)) in *. rewrite HL1 in FRM.
    eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_MATCH_T q ms1
         /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
         /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r)
         /\ h11 q = wz (il_Aw (ix_L X) + mt_idx s) /\ h12 q = wz 1 /\ h13 q = wz sl /\ h14 q = wz 1)).
    { rewrite (bv_swrap32_id (is_offset s)) by lia. do 2 zs. br_cases K4.
      - (* [comment removed for export] *)
        assert (EIDX : mt_idx s = is_wnext s - is_offset s) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        do 5 zs. rewrite land_u32_small by lia. gF. clamps HMEM EIDX ESL sl s.
      - (* [comment removed for export] *)
        assert (EIDX : mt_idx s = is_wsize s - (is_offset s - is_wnext s)) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
        do 7 zs. rewrite land_u32_small by lia. gT. clamps HMEM EIDX ESL sl s. }
    intros ms1 (q & HJ & E9 & E10 & E18 & E22 & E24 & E25 & E11 & E12 & E13 & E14).
    eapply evt_mono; [exact (match_tail X s c r q ms1 HJ E9 E10 E18 E22 E24 E25 E11 E12 E13 E14 XO HASW NWB RIDX RBYTE HL1 HP0 ltac:(lia) ltac:(lia) ltac:(lia) RMODE)|].
    intros ms' HPO. split; [exact HPO|]. unfold hide in Pisr.
    destruct (is_length s - 1 =? 0); cbn [wof];
      (eapply (PATI_step_put X s c r _ _ _ (arr_get (is_window s) (mt_idx s)));
       [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| ired; rewrite ?HM; unfold LEN, MATCH, FLAGS, HCRC; lia| reflexivity| reflexivity
       | ired; rewrite HP0; reflexivity| exact RBYTE| lia| ired; lia| reflexivity| ired; lia| ired; rewrite ?HM; reflexivity| exact Pisr| bk_keep]).
Qed.

