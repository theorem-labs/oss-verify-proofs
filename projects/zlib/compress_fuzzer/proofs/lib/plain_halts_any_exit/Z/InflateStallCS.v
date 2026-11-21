(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage ModelRel AdlerModel RefZApi RefInflateRel RefUpdWin1 RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeS1 RefInflateSafeS2 RefInflateSafeS3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqD RefInflateEqA2 RefInflateEqF RefInflateEqS RefInflateEqB InflateFrameIn InflateCall HarnessSmall.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1 RefInflateSafeA3 RefInflateSafeA4 RefInflateSafeA5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC InflateStallCA1 InflateStallCA2 InflateStallCA3 InflateStallCA4 InflateStallCA5 InflateStallCA6 InflateStallR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma noflush : (Z_NO_FLUSH =? Z_BLOCK) = false /\ (Z_NO_FLUSH =? Z_TREES) = false.
Proof. split; reflexivity. Qed.

Lemma UW_UWL : forall s c r, UW s c r -> UWL s.
Proof.
  intros s c r (W & _ & F). split; [exact W|]. destruct F as [F|(_ & [M|M] & _)]; [left; exact F|right; left; exact M|right; right; left; exact M].
Qed.

Lemma lv_fin_zr : forall flush s c r,
  zr_consumed (snd (lv_fin flush s c r)) = ic_next_in c
  /\ zr_output (snd (lv_fin flush s c r)) = arr_slice (ic_outbuf c) 0 (ic_next_out c)
  /\ zr_rc (snd (lv_fin flush s c r)) = ret_model flush (wrap32 (ir_in r - ic_avail_in c)) (wrap32 (ir_out r - ic_avail_out c)) r.
Proof.
  intros flush s c r. unfold lv_fin. cbv zeta.
  lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end;
    cbn [fst snd zret_of_icall zr_consumed zr_output zr_rc]; sacc; repeat split; reflexivity.
Qed.

Theorem dispatch_sq : forall s c r, WINV (mkW s c r) -> UW s c r -> SQ (dispatch ivar_ref Z_NO_FLUSH (mkW s c r)).
Proof.
  intros s c r HW HU. pose proof (UW_UWL _ _ _ HU) as HUL. destruct HU as (_ & Hgz & _).
  unfold dispatch. arun3 gs_eq. cbv zeta.
  Ltac try_arm3 lem HUL Hgz := lazymatch goal with |- SQ ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) =>
    destruct (Z.eqb_spec (is_mode s) M) as [E|?NE];
    [first [ exact (lem s c r ltac:(assumption) HUL E)
           | exfalso; rewrite E in Hgz; discriminate Hgz ] |] end.
  try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz.
  try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_HEAD_sq) HUL Hgz.
  try_arm3 (arm_HEAD_sq) HUL Hgz. try_arm3 (arm_DICTID_sq ivar_ref Z_NO_FLUSH noflush) HUL Hgz. try_arm3 (arm_DICT_sq ivar_ref Z_NO_FLUSH noflush) HUL Hgz.
  try_arm3 (arm_TYPE_sq ivar_ref Z_NO_FLUSH noflush) HUL Hgz. try_arm3 (arm_TYPEDO_sq ivar_ref Z_NO_FLUSH noflush) HUL Hgz.
  try_arm3 (arm_STORED_sq ivar_ref Z_NO_FLUSH noflush) HUL Hgz.
  try_arm3 (arm_COPY__sq) HUL Hgz. try_arm3 (arm_COPY_sq) HUL Hgz. try_arm3 (arm_TABLE_sq Z_NO_FLUSH noflush) HUL Hgz.
  try_arm3 (arm_LENLENS_sq Z_NO_FLUSH noflush) HUL Hgz. try_arm3 (arm_CODELENS_sq Z_NO_FLUSH noflush) HUL Hgz.
  try_arm3 (arm_LEN__sq) HUL Hgz. try_arm3 (arm_LEN_sq) HUL Hgz. try_arm3 (arm_LENEXT_sq) HUL Hgz.
  try_arm3 (arm_DIST_sq) HUL Hgz. try_arm3 (arm_DISTEXT_sq) HUL Hgz. try_arm3 (arm_MATCH_sq ivar_ref) HUL Hgz. try_arm3 (arm_LIT_sq) HUL Hgz.
  try_arm3 (arm_CHECK_sq) HUL Hgz. try_arm3 (arm_LENGTH_sq) HUL Hgz. try_arm3 (arm_DONE_sq) HUL Hgz. try_arm3 (arm_BAD_sq) HUL Hgz. try_arm3 (arm_MEM_sq) HUL Hgz.

  unfold arm_SYNC. rewrite areturn_eq. cbn [SQ]. intros X; discriminate X.
Qed.

Lemma inf_loop_sq_nat : forall m w, WINV w -> WMID w w -> PHI w < Z.of_nat m ->
  let '(stop, w') := iterZ (Z.of_nat m) (lstep Z_NO_FLUSH) (fun w0 => (SLeave, w0)) w in
  match stop with SLeave => LV w' | SRet rc => rc <> Z_OK end.
Proof.
  induction m as [|m IH]; intros w HW HM HP.
  { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
  rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
  unfold lstep at 1. destruct w as [s c r]. destruct HM as (_ & _ & HQ & HU). cbn [w_s w_c w_r] in HQ, HU.
  pose proof (dispatch_safe Z_NO_FLUSH (mkW s c r) s c r HW ltac:(lia)) as D.
  pose proof (dispatch_sq s c r HW HU) as Q.
  pose proof (dispatch_cong Z_NO_FLUSH fastc_proof s s c r HW HQ HU) as C.
  destruct (dispatch ivar_ref Z_NO_FLUSH (mkW s c r)) as [u w'|w'|rc w'].
  - destruct D as [HW' HP']. destruct C as [_ HM']. exact (IH w' HW' HM' ltac:(lia)).
  - exact Q.
  - exact Q.
Qed.

Theorem inf_loop_sq : forall w, WINV w -> WMID w w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  let '(stop, w') := inf_loop ivar_ref Z_NO_FLUSH w in
  match stop with SLeave => LV w' | SRet rc => rc <> Z_OK end.
Proof.
  intros w HW HM HP. unfold inf_loop. change (fun w0 : iw => _) with (lstep Z_NO_FLUSH) at 1.
  pose proof (PHI_nonneg w HW).
  rewrite <- (Z2Nat.id (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64))) by lia.
  apply inf_loop_sq_nat; [exact HW|exact HM|]. rewrite Z2Nat.id by lia. exact HP.
Qed.

Lemma SC_updw_core : forall s src e copy h b, SC s h b -> SC (updw_core s src e copy) h b.
Proof.
  intros s src e copy h b H. pose proof (updw_core_fields s src e copy) as F. cbv zeta in F.
  destruct F as (F1 & _ & _ & _ & _ & F6 & _ & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & _ & _ & _ & _ & F23).
  exact (SC_keep s _ h b F1 F23 F6 F8 F16 F13 F14 F15 F9 F10 F11 F12 F17 F18 H).
Qed.

Lemma SC_uw_pure : forall s src e copy ch s2 h b, uw_pure s src e copy ch = Some s2 -> SC s h b -> SC s2 h b.
Proof.
  intros s src e copy ch s2 h b H HS. unfold uw_pure in H. destruct (is_window_blk s) as [bk|].
  - injection H as <-. apply SC_updw_core. exact HS.
  - destruct ch as [[bk g]|]; [|discriminate H]. injection H as <-. apply SC_updw_core.
    apply (SC_keep s); try reflexivity. exact HS.
Qed.

Lemma SC_lv_fin : forall flush s c r h b, SC s h b -> SC (fst (lv_fin flush s c r)) h b.
Proof.
  intros flush s c r h b HS. unfold lv_fin. cbv zeta.
  lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst]; apply (SC_keep s); try reflexivity; exact HS.
Qed.

Lemma lv_fin_holdbits : forall flush s c r, is_hold (fst (lv_fin flush s c r)) = is_hold s /\ is_bits (fst (lv_fin flush s c r)) = is_bits s.
Proof.
  intros flush s c r. unfold lv_fin. cbv zeta.
  lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst]; sacc; split; reflexivity.
Qed.

Lemma uw_pure_holdbits : forall s src e copy ch s2, uw_pure s src e copy ch = Some s2 -> is_hold s2 = is_hold s /\ is_bits s2 = is_bits s.
Proof.
  intros s src e copy ch s2 H.
  assert (K : forall t, is_hold (updw_core t src e copy) = is_hold t /\ is_bits (updw_core t src e copy) = is_bits t).
  { intros t. pose proof (updw_core_fields t src e copy) as F. cbv zeta in F.
    destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F19 & F20 & _). exact (conj F19 F20). }
  unfold uw_pure in H. destruct (is_window_blk s) as [bk|].
  - injection H as <-. apply K.
  - destruct ch as [[bk g]|]; [|discriminate H]. injection H as <-. destruct (K (iset_window (iset_window_blk s (Some bk)) (iarr_u8_of g 0 (shl32 1 (is_wbits s))))) as [A B].
    rewrite A, B. sacc. split; reflexivity.
Qed.

Lemma SC_s_entry : forall s h b, SC s h b -> SC (s_entry s) h b.
Proof.
  intros s h b HS. unfold s_entry. destruct (Z.eqb_spec (is_mode s) TYPE) as [E|E]; [|exact HS].
  unfold SC in HS |- *. rewrite E in HS. sacc. sc_red_in HS. sc_red. exact HS.
Qed.

Lemma OC_updw_core : forall s src e copy, OC s -> OC (updw_core s src e copy).
Proof.
  intros s src e copy H. pose proof (updw_core_fields s src e copy) as F. cbv zeta in F.
  destruct F as (F1 & _ & _ & _ & _ & F6 & _).
  exact (OC_keep s _ F1 F6 H).
Qed.

Lemma OC_uw_pure : forall s src e copy ch s2, uw_pure s src e copy ch = Some s2 -> OC s -> OC s2.
Proof.
  intros s src e copy ch s2 H HS. unfold uw_pure in H. destruct (is_window_blk s) as [bk|].
  - injection H as <-. apply OC_updw_core. exact HS.
  - destruct ch as [[bk g]|]; [|discriminate H]. injection H as <-. apply OC_updw_core.
    apply (OC_keep s); try reflexivity. exact HS.
Qed.

Lemma OC_lv_fin : forall flush s c r, OC s -> OC (fst (lv_fin flush s c r)).
Proof.
  intros flush s c r HS. unfold lv_fin. cbv zeta.
  lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst]; apply (OC_keep s); try reflexivity; exact HS.
Qed.

Lemma OC_s_entry_id : forall s, OC s -> s_entry s = s.
Proof.
  intros s HS. unfold s_entry. destruct (Z.eqb_spec (is_mode s) TYPE) as [E|E]; [|reflexivity].
  exfalso. exact (OC_not_TYPE s HS E).
Qed.

Section Call1.

  Theorem inflate_m_sq2 : forall s zc ch p,
    INV s -> UWS s -> IEQ s s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc Z_NO_FLUSH) ch = Some p ->
    zr_rc (snd p) = Z_OK ->
    (zlength (zr_output (snd p)) = zc_avail_out zc /\ OSTALLED (fst p)) \/ (zr_consumed (snd p) = zlength (zc_input zc) /\ STALLED (fst p)).
  Proof.
    intros s zc ch p HI HUS HQ Hz E Hrc. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
    destruct (Z.eq_dec (is_mode s) MEM) as [EM|NM].
    - rewrite (inf_loop_MEM Z_NO_FLUSH (W0 s zc)) in E; cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      exfalso. unfold sret in E. cbn [fst] in E. injection E; intros <-. cbn [snd zret_of_icall zr_rc] in Hrc. discriminate Hrc.
    - destruct (WINV_entry' s zc HI Hz) as [HW HP].
      pose proof (W0_WMID s s zc HQ HUS NM ltac:(lia)) as HM.
      assert (HB : BK (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc)).
      { unfold BK, caseA. cbn [W0 w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out]. unfold arr_make. rewrite arr_len_init.
        split; [reflexivity|]. unfold s_entry.
        assert (NS : is_mode s <> SYNC) by (intros ES; destruct HI as (_ & _ & HMF); rewrite ES in HMF; exact HMF).
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; sacc; [split; [discriminate|]; split; [discriminate|] | split; [exact NM|]; split; [exact NS|]]; left; split; reflexivity. }
      pose proof (inf_loop_bk Z_NO_FLUSH (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc) HW HB HP) as L.
      pose proof (inf_loop_fi _ _ _ Z_NO_FLUSH (W0 s zc) (FI_W0 s zc)) as LF.
      pose proof (inf_loop_sq (W0 s zc) HW HM HP) as Q.
      destruct (inf_loop ivar_ref Z_NO_FLUSH (W0 s zc)) as [stop [s' c' r']]. destruct L as (HW' & HB' & HR'). cbn [fst snd] in LF.
      pose proof HW' as HW''. unfold WINV in HW'. cbn [w_s w_c w_r] in HW'. destruct HW' as (_ & HREG & _).
      pose proof HREG as (RN & RH & RNH & RP & RL & RPL & _ & _ & RNI & RNO).
      destruct HB' as (B1 & B2 & B3 & HAB). cbn [w_s w_c w_r] in B1, B2, B3, HAB.
      destruct stop as [|rc].
      +
        destruct LF as (LF1 & LF2 & LF3 & LF4). cbn [w_c w_r] in LF1, LF2, LF3, LF4.
        unfold LV in Q. cbn [w_r w_s] in Q.
        rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
        assert (TAIL : forall s2 ch',
                  is_hold s2 = ir_hold r' -> is_bits s2 = ir_bits r' -> (SC s' (ir_hold r') (ir_bits r') -> SC s2 (ir_hold r') (ir_bits r')) ->
                  (OC s' -> OC s2) ->
                  match @sret CH _ (lv_fin Z_NO_FLUSH s2 (c_rest c' r') r') ch' with MRet q => Some (fst q) | _ => None end = Some p ->
                  (zlength (zr_output (snd p)) = zc_avail_out zc /\ OSTALLED (fst p)) \/ (zr_consumed (snd p) = zlength (zc_input zc) /\ STALLED (fst p))).
        { intros s2 ch' Hh2 Hb2 HS2 HO2 X. unfold sret in X. cbn [fst] in X. injection X; intros <-.
          destruct (lv_fin_zr Z_NO_FLUSH s2 (c_rest c' r') r') as (Z1 & Z2 & Z3).
          rewrite Z3 in Hrc. rewrite Z1, Z2. unfold c_rest in Hrc |- *. sacc_in Hrc. sacc. rewrite arr_slice_length. rewrite Z.max_r by exact RP.

          assert (RET : ir_ret r' = Z_OK).
          { unfold ret_model in Hrc. destruct (Z.eqb_spec (ir_ret r') Z_OK) as [ER|ER]; [exact ER|].
            rewrite Bool.andb_false_r in Hrc. exfalso. exact (ER Hrc). }
          destruct Q as [[Q QO]|[Q|[Qh QS]]].
          - left. split; [clear - Q RPL B1; lia|]. unfold OSTALLED. apply OC_lv_fin. apply HO2. exact QO.
          - exfalso. exact (Q RET).
          - right. split.
            + clear - Qh RNH LF3. lia.
            + unfold STALLED. destruct (lv_fin_holdbits Z_NO_FLUSH s2
                 (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c' (ir_put r')) (ir_left r')) (ir_next r')) (ir_have r')) r') as [E1 E2].
              rewrite E1, E2, Hh2, Hb2. apply SC_lv_fin. apply HS2. exact QS. }
        destruct (lv_cond Z_NO_FLUSH (s_rest s' r') (c_rest c' r') r').
        * rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
          destruct (uw_pure (s_rest s' r') _ _ _ ch) as [s2|] eqn:EU.
          -- destruct (uw_pure_holdbits _ _ _ _ _ _ EU) as [U1 U2].
             apply (TAIL s2 ch); [rewrite U1; reflexivity|rewrite U2; reflexivity| | |exact E].
             ++ intros HS. apply (SC_uw_pure _ _ _ _ _ _ _ _ EU). unfold s_rest. apply (SC_keep s'); try reflexivity. exact HS.
             ++ intros HO. apply (OC_uw_pure _ _ _ _ _ _ EU). unfold s_rest. apply (OC_keep s'); try reflexivity. exact HO.
          -- exfalso. unfold sret in E. injection E; intros <-. unfold lv_mem in Hrc. cbn [fst snd zret_of_icall zr_rc] in Hrc. discriminate Hrc.
        * unfold sret at 1 in E. cbn [mbind fst snd] in E. apply (TAIL (s_rest s' r') ch); [reflexivity|reflexivity| | |exact E].
          -- intros HS. unfold s_rest. apply (SC_keep s'); try reflexivity. exact HS.
          -- intros HO. unfold s_rest. apply (OC_keep s'); try reflexivity. exact HO.
      +
        exfalso. unfold sret in E. cbn [fst] in E. injection E; intros <-. cbn [fst snd zret_of_icall zr_rc] in Hrc. exact (Q Hrc).
  Qed.

  Theorem sq_call2 : forall (s : inflate_state) (zc : ZCall) (ans : option (blk * (Z -> Z))),
    INV s -> UWS s -> IEQ s s -> ZC zc ->
    let p := fst (inflate_p ans s zc Z_NO_FLUSH) in
    zr_rc (snd p) = Z_OK ->
    (zlength (zr_output (snd p)) = zc_avail_out zc /\ OSTALLED (fst p)) \/ (zr_consumed (snd p) = zlength (zc_input zc) /\ STALLED (fst p)).
  Proof.
    intros s zc ans HI HUS HQ Hz. cbv zeta.
    pose proof (inflate_p_pure ans s zc Z_NO_FLUSH (INV_check _ HI)) as EP.
    set (p := fst (inflate_p ans s zc Z_NO_FLUSH)) in *. clearbody p.
    intros Hrc. exact (inflate_m_sq2 s zc ans p HI HUS HQ Hz EP Hrc).
  Qed.
End Call1.

Section Call2.

  Theorem stalled_call : forall (s : inflate_state) (zc : ZCall) (ans : option (blk * (Z -> Z))),
    INV s -> UWS s -> ZC zc -> zc_input zc = [] -> STALLED s ->
    zr_rc (snd (fst (inflate_p ans s zc Z_NO_FLUSH))) <> Z_OK.
  Proof.
    intros s zc ans HI HUS Hz Hnil HST. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    pose proof (INV_check _ HI) as Hc.
    assert (NM : is_mode s <> MEM) by (intros EM; unfold STALLED, SC in HST; rewrite EM in HST; sc_red_in HST; exact HST).
    destruct (WINV_entry' s zc HI Hz) as [HW HP].
    destruct HUS as (HWR5 & _ & _).
    unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.

    set (r0 := mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold s) (is_bits s) (zlength (zc_input zc)) (zc_avail_out zc) Z_OK).
    assert (EW0 : W0 s zc = mkW (s_entry s) (icall_of_zcall zc) r0) by reflexivity.
    assert (L : exists s' r', inf_loop ivar_ref Z_NO_FLUSH (W0 s zc) = (SLeave, mkW s' (icall_of_zcall zc) r') /\ RS r0 r').
    { unfold inf_loop. rewrite iterZ_step by (cbn [W0 w_c icall_of_zcall ic_avail_in ic_avail_out]; lia).
      rewrite EW0 in HW |- *.
      destruct (dispatch_restall Z_NO_FLUSH noflush (s_entry s) (icall_of_zcall zc) r0) as (s' & r' & EQ & HRS).
      - exact HW.
      - unfold s_entry. destruct (is_mode s =? TYPE); sacc; rewrite HWR5; discriminate.
      - subst r0. cbn [ir_have]. rewrite Hnil. reflexivity.
      - subst r0. cbn [ir_hold ir_bits]. apply SC_s_entry. exact HST.
      - exists s', r'. rewrite EQ. split; [reflexivity|exact HRS]. }
    destruct L as (s' & r' & EL & HRS). rewrite EL.
    destruct HRS as (R1 & R2 & R3 & R4 & R5 & R6). subst r0. cbn [ir_left ir_out ir_in ir_have ir_ret ir_put] in R1, R2, R3, R4, R5, R6.
    rewrite Hnil in R3. cbn [zlength length Z.of_nat] in R3.
    assert (RC : ret_model Z_NO_FLUSH (wrap32 (ir_in r' - ic_avail_in (c_rest (icall_of_zcall zc) r'))) (wrap32 (ir_out r' - ic_avail_out (c_rest (icall_of_zcall zc) r'))) r' <> Z_OK).
    { unfold c_rest. sacc. rewrite R1, R2, R3, R4. replace (0 - 0) with 0 by lia. replace (zc_avail_out zc - zc_avail_out zc) with 0 by lia.
      change (wrap32 0) with 0. unfold ret_model. cbn [Z.eqb andb orb].
      destruct (Z.eqb_spec (ir_ret r') Z_OK) as [ER|ER]; [intros X; discriminate X|exact ER]. }
    rewrite inf_leave_eq. unfold sbind. destruct (lv_cond Z_NO_FLUSH (s_rest s' r') (c_rest (icall_of_zcall zc) r') r').
    - rewrite updatewindow_dh. cbn [mbind fst snd].
      destruct (uw_pure (s_rest s' r') _ _ _ ans) as [s2|]; unfold sret; cbn [fst snd].
      + destruct (lv_fin_zr Z_NO_FLUSH s2 (c_rest (icall_of_zcall zc) r') r') as (_ & _ & Z3). rewrite Z3. exact RC.
      + unfold lv_mem. cbn [fst snd zret_of_icall zr_rc]. intros X; discriminate X.
    - unfold sret. cbn [mbind fst snd]. destruct (lv_fin_zr Z_NO_FLUSH (s_rest s' r') (c_rest (icall_of_zcall zc) r') r') as (_ & _ & Z3). rewrite Z3. exact RC.
  Qed.
End Call2.

Definition orestall (M : Z) (arm : AM unit) : Prop :=
  forall s c r, is_mode s = M -> ir_left r = 0 -> 0 <= ir_have r -> OC s -> exists s', arm (mkW s c r) = ALeave (mkW s' c r).

Lemma orestall_LIT : orestall LIT arm_LIT.
Proof.
  intros s c r E L0 _ _. unfold arm_LIT. rewrite ?abind_assoc. unfold abind at 1. rewrite gr_eq. cbv beta iota.
  rewrite L0. change (0 =? 0) with true. cbv iota. exists s. apply aleave_eq.
Qed.

Lemma orestall_MATCH : forall iv, orestall MATCH (arm_MATCH iv).
Proof.
  intros iv s c r E L0 _ _. unfold arm_MATCH. rewrite ?abind_assoc. unfold abind at 1. rewrite gr_eq. cbv beta iota.
  rewrite L0. change (0 =? 0) with true. cbv iota. exists s. apply aleave_eq.
Qed.

Lemma orestall_COPY : orestall COPY arm_COPY.
Proof.
  intros s c r E L0 Hh HO. unfold OC in HO. rewrite E in HO. oc_red_in HO.
  unfold arm_COPY. rewrite ?abind_assoc. unfold abind at 1. rewrite gs_eq. cbv beta iota zeta.
  replace (negb (is_length s =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  rewrite ?abind_assoc. unfold abind at 1. rewrite gr_eq. cbv beta iota zeta. rewrite L0.
  match goal with |- context [if (if ?cnd then 0 else ?cp) =? 0 then _ else _] =>
    replace ((if cnd then 0 else cp) =? 0) with true end.
  - exists s. apply aleave_eq.
  - symmetry. apply Z.eqb_eq. destruct (Z.ltb_spec (ir_have r) (is_length s)) as [A|A].
    + destruct (Z.ltb_spec 0 (ir_have r)) as [B|B]; [reflexivity| lia].
    + destruct (Z.ltb_spec 0 (is_length s)) as [B|B]; [reflexivity| exfalso; lia].
Qed.

Lemma orestall_COPY_ : orestall COPY_ arm_COPY_.
Proof.
  intros s c r E L0 Hh HO. unfold OC in HO. rewrite E in HO. oc_red_in HO.
  unfold arm_COPY_. rewrite ?abind_assoc. unfold abind at 1. rewrite set_mode_eq. cbv beta iota.
  destruct (orestall_COPY (iset_mode s COPY) c r) as [s' EQ]; [sacc; reflexivity | exact L0 | exact Hh | unfold OC; sacc; oc_red; exact HO |].
  exists s'. exact EQ.
Qed.

Theorem dispatch_orestall : forall flush s c r,
  ir_left r = 0 -> 0 <= ir_have r -> OC s ->
  exists s', dispatch ivar_ref flush (mkW s c r) = ALeave (mkW s' c r).
Proof.
  intros flush s c r L0 Hh HO. unfold dispatch. unfold abind. rewrite gs_eq. cbv beta zeta.
  Ltac try_omode lem L0 Hh HO :=
    lazymatch goal with |- exists s', ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) = _ =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE];
      [first [ exact (lem s c r E L0 Hh HO)
             | exfalso; unfold OC in HO; rewrite E in HO; oc_red_in HO; exact HO ] |] end.
  do 14 (try_omode orestall_LIT L0 Hh HO).
  try_omode orestall_COPY_ L0 Hh HO. try_omode orestall_COPY L0 Hh HO.
  do 8 (try_omode orestall_LIT L0 Hh HO).
  try_omode (orestall_MATCH ivar_ref) L0 Hh HO. try_omode orestall_LIT L0 Hh HO.
  do 5 (try_omode orestall_LIT L0 Hh HO).

  exfalso. unfold OC in HO.
  repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HO; clear N end.
  cbn [orb] in HO. exact HO.
Qed.

Section Call3.

  Theorem ostalled_call : forall (s : inflate_state) (zc : ZCall) (ans : option (blk * (Z -> Z))),
    INV s -> ZC zc -> zc_avail_out zc = 0 -> OSTALLED s ->
    zr_rc (snd (fst (inflate_p ans s zc Z_NO_FLUSH))) <> Z_OK.
  Proof.
    intros s zc ans HI Hz Hao0 HST. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    pose proof (INV_check _ HI) as Hc.
    unfold OSTALLED in HST.
    unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.

    set (r0 := mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold s) (is_bits s) (zlength (zc_input zc)) (zc_avail_out zc) Z_OK).
    assert (EW0 : W0 s zc = mkW (s_entry s) (icall_of_zcall zc) r0) by reflexivity.
    assert (L : exists s', inf_loop ivar_ref Z_NO_FLUSH (W0 s zc) = (SLeave, mkW s' (icall_of_zcall zc) r0)).
    { unfold inf_loop. rewrite iterZ_step by (cbn [W0 w_c icall_of_zcall ic_avail_in ic_avail_out]; lia).
      rewrite EW0. rewrite (OC_s_entry_id s HST).
      destruct (dispatch_orestall Z_NO_FLUSH s (icall_of_zcall zc) r0) as [s' EQ].
      - subst r0. cbn [ir_left]. exact Hao0.
      - subst r0. cbn [ir_have]. exact LN.
      - exact HST.
      - exists s'. rewrite EQ. reflexivity. }
    destruct L as [s' EL]. rewrite EL.
    assert (RC : ret_model Z_NO_FLUSH (wrap32 (ir_in r0 - ic_avail_in (c_rest (icall_of_zcall zc) r0))) (wrap32 (ir_out r0 - ic_avail_out (c_rest (icall_of_zcall zc) r0))) r0 <> Z_OK).
    { unfold c_rest. subst r0. sacc. replace (zlength (zc_input zc) - zlength (zc_input zc)) with 0 by lia. replace (zc_avail_out zc - zc_avail_out zc) with 0 by lia.
      change (wrap32 0) with 0. unfold ret_model. cbn [ir_ret Z.eqb andb orb]. intros X; discriminate X. }
    rewrite inf_leave_eq. unfold sbind. destruct (lv_cond Z_NO_FLUSH (s_rest s' r0) (c_rest (icall_of_zcall zc) r0) r0).
    - rewrite updatewindow_dh. cbn [mbind fst snd].
      destruct (uw_pure (s_rest s' r0) _ _ _ ans) as [s2|]; unfold sret; cbn [fst snd].
      + destruct (lv_fin_zr Z_NO_FLUSH s2 (c_rest (icall_of_zcall zc) r0) r0) as (_ & _ & Z3). rewrite Z3. exact RC.
      + unfold lv_mem. cbn [fst snd zret_of_icall zr_rc]. intros X; discriminate X.
    - unfold sret. cbn [mbind fst snd]. destruct (lv_fin_zr Z_NO_FLUSH (s_rest s' r0) (c_rest (icall_of_zcall zc) r0) r0) as (_ & _ & Z3). rewrite Z3. exact RC.
  Qed.
End Call3.
