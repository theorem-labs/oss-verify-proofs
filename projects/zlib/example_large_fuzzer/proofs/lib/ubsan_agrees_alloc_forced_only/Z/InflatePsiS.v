(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require ZApiL ZHarnessL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage AdlerModel RefZApi RefInflateRel RefUpdWin1 RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeS1 RefInflateSafeS2 RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqS RefInflateEqB InflateFrameIn InflateCall HarnessSmall ZApiInst ZApiOk ZApiInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1 RefInflateSafeA3 RefInflateSafeA4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflatePsi InflatePsi1 InflatePsiA1 InflatePsiA2 InflatePsiA3 InflatePsiA4 InflatePsiF3 InflatePsiA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Dispatch.
  Variable flush : Z.

  Theorem dispatch_psi : forall s c r, WINV (mkW s c r) -> PP (mkW s c r) (dispatch ivar_ref flush (mkW s c r)).
  Proof.
    intros s c r HW. unfold dispatch. arun2 gs_eq. cbv zeta.
    Ltac try_arm2 lem := lazymatch goal with |- PP ?w0 ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [exact (lem w0 s c r ltac:(assumption) E (PPw_refl _))|] end.
    try_arm2 (arm_HEAD_psi). try_arm2 (arm_FLAGS_psi). try_arm2 (arm_TIME_psi). try_arm2 (arm_OS_psi).
    try_arm2 (arm_EXLEN_psi). try_arm2 (arm_EXTRA_psi). try_arm2 (arm_NAME_psi). try_arm2 (arm_COMMENT_psi).
    try_arm2 (arm_HCRC_psi). try_arm2 (arm_DICTID_psi ivar_ref flush). try_arm2 (arm_DICT_psi ivar_ref flush).
    try_arm2 (arm_TYPE_psi ivar_ref flush). try_arm2 (arm_TYPEDO_psi ivar_ref flush). try_arm2 (arm_STORED_psi ivar_ref flush).
    try_arm2 (arm_COPY__psi). try_arm2 (arm_COPY_psi). try_arm2 (arm_TABLE_psi flush). try_arm2 (arm_LENLENS_psi flush).
    try_arm2 (arm_CODELENS_psi flush). try_arm2 (arm_LEN__psi). try_arm2 (arm_LEN_psi). try_arm2 (arm_LENEXT_psi).
    try_arm2 (arm_DIST_psi). try_arm2 (arm_DISTEXT_psi). try_arm2 (arm_MATCH_psi ivar_ref). try_arm2 (arm_LIT_psi).
    try_arm2 (arm_CHECK_psi). try_arm2 (arm_LENGTH_psi). try_arm2 (arm_DONE_psi). try_arm2 (arm_BAD_psi). try_arm2 (arm_MEM_psi).
    (* [comment removed for export] *)
    exfalso. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & _ & HMF & _). unfold MF in HMF.
    repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
    cbn [orb] in HMF. exact HMF.
  Qed.

End Dispatch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loops.
  Variable flush : Z.

  Lemma inf_loop_psi_nat : forall m w, WINV w -> PHI w < Z.of_nat m ->
    let '(stop, w') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w in
    match stop with SLeave => PPw w w' | SRet _ => True end.
  Proof.
    induction m as [|m IH]; intros w HW HP.
    { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    unfold lstep at 1. destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW ltac:(lia)) as D.
    pose proof (dispatch_psi flush s c r HW) as Q.
    destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w'].
    - destruct D as [HW' HP']. specialize (IH w' HW' ltac:(lia)).
      destruct (iterZ (Z.of_nat m) (lstep flush) _ w') as [stop w'']. destruct stop; [exact (PPw_trans _ _ _ Q IH)|exact I].
    - exact Q.
    - exact I.
  Qed.

  Theorem inf_loop_psi : forall w, WINV w ->
    PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
    let '(stop, w') := inf_loop ivar_ref flush w in
    match stop with SLeave => PPw w w' | SRet _ => True end.
  Proof.
    intros w HW HP. unfold inf_loop. change (fun w0 : iw => _) with (lstep flush) at 1.
    pose proof (PHI_nonneg w HW).
    rewrite <- (Z2Nat.id (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64))) by lia.
    apply inf_loop_psi_nat; [exact HW|]. rewrite Z2Nat.id by lia. exact HP.
  Qed.
End Loops.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma updw_core_pend : forall s src e copy,
  pend (updw_core s src e copy) = pend s /\ is_bits (updw_core s src e copy) = is_bits s.
Proof.
  intros s src e copy.
  assert (F : is_mode (updw_core s src e copy) = is_mode s /\ is_length (updw_core s src e copy) = is_length s
              /\ is_extra (updw_core s src e copy) = is_extra s /\ is_bits (updw_core s src e copy) = is_bits s).
  { unfold updw_core, RefUpdWin1.sA. sacc.
    repeat lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; sacc; repeat split; reflexivity. }
  destruct F as (F1 & F2 & F3 & F4). split; [exact (pend_keep _ _ F1 F2 F3)|exact F4].
Qed.

Lemma uw_pure_pend : forall s src e copy ch s2,
  uw_pure s src e copy ch = Some s2 -> pend s2 = pend s /\ is_bits s2 = is_bits s.
Proof.
  intros s src e copy ch s2 H. unfold uw_pure in H. destruct (is_window_blk s) as [b|].
  - injection H as <-. apply updw_core_pend.
  - destruct ch as [[b g]|]; [|discriminate H]. injection H as <-.
    destruct (updw_core_pend (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s)))) src e copy) as [A B].
    rewrite A, B. split; reflexivity.
Qed.

Lemma lv_fin_pend : forall flush s c r,
  pend (fst (lv_fin flush s c r)) = pend s /\ is_bits (fst (lv_fin flush s c r)) = is_bits s.
Proof.
  intros flush s c r. unfold lv_fin. cbv zeta.
  lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst snd]; unfold pend; sacc; split; reflexivity.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Call.

  Theorem inflate_m_psi : forall s zc ch p,
    INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc Z_NO_FLUSH) ch = Some p ->
    zr_rc (snd p) = Z_OK ->
    PSIq (zlength (zc_input zc) - zr_consumed (snd p)) (fst p) + zlength (zr_output (snd p)) <= PSIq (zlength (zc_input zc)) s.
  Proof.
    intros s zc ch p HI Hz E Hrc. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
    destruct (Z.eq_dec (is_mode s) MEM) as [EM|NM].
    - rewrite (inf_loop_MEM Z_NO_FLUSH (W0 s zc)) in E; cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      exfalso. unfold sret in E. cbn [fst] in E. injection E; intros <-. cbn [snd zret_of_icall zr_rc] in Hrc. discriminate Hrc.
    - destruct (WINV_entry' s zc HI Hz) as [HW HP].
      assert (HB : BK (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc)).
      { unfold BK, caseA. cbn [W0 w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out]. unfold arr_make. rewrite arr_len_init.
        split; [reflexivity|]. unfold s_entry.
        assert (NS : is_mode s <> SYNC) by (intros ES; destruct HI as (_ & _ & HM); rewrite ES in HM; exact HM).
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; sacc; [split; [discriminate|]; split; [discriminate|] | split; [exact NM|]; split; [exact NS|]]; left; split; reflexivity. }
      pose proof (inf_loop_bk Z_NO_FLUSH (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc) HW HB HP) as L.
      pose proof (inf_loop_fi _ _ _ Z_NO_FLUSH (W0 s zc) (FI_W0 s zc)) as LF. (* zl14infl-r2: inf_loop_fi splits on the stop *)
      pose proof (inf_loop_psi Z_NO_FLUSH (W0 s zc) HW HP) as Q.
      destruct (inf_loop ivar_ref Z_NO_FLUSH (W0 s zc)) as [stop [s' c' r']]. destruct L as (HW' & HB' & HR'). cbn [fst snd] in LF.
      pose proof HW' as HW''. unfold WINV in HW'. cbn [w_s w_c w_r] in HW'. destruct HW' as (_ & HREG & _).
      pose proof HREG as (RN & RH & RNH & RP & RL & RPL & _ & _ & RNI & RNO).
      destruct stop as [|rc].
      + (* [comment removed for export] *)
        destruct LF as (LF1 & LF2 & LF3 & LF4). cbn [w_c w_r] in LF1, LF2, LF3, LF4.
        unfold PPw, PSI, PSIr in Q. cbn [W0 w_s w_c w_r ir_put ir_have ir_bits] in Q. destruct Q as [Q1 Q2].
        assert (Epe : pend (s_entry s) = pend s).
        { unfold s_entry. destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; [|reflexivity]. unfold pend. sacc. rewrite ET. reflexivity. }
        rewrite Epe in Q2.
        rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
        assert (TAIL : forall s2 ch',
                  pend s2 = pend s' -> is_bits s2 = ir_bits r' ->
                  match @sret CH _ (lv_fin Z_NO_FLUSH s2 (c_rest c' r') r') ch' with MRet q => Some (fst q) | _ => None end = Some p ->
                  PSIq (zlength (zc_input zc) - zr_consumed (snd p)) (fst p) + zlength (zr_output (snd p)) <= PSIq (zlength (zc_input zc)) s).
        { intros s2 ch' Hp2 Hb2 X. unfold sret in X. cbn [fst] in X. injection X; intros <-.
          destruct (lv_fin_pend Z_NO_FLUSH s2 (c_rest c' r') r') as [P1 P2].
          destruct (lv_fin_zr Z_NO_FLUSH s2 (c_rest c' r') r') as (Z1 & Z2 & _).
          unfold PSIq. rewrite P1, P2, Z1, Z2, Hp2, Hb2. unfold c_rest. sacc. rewrite arr_slice_length.
          replace (zlength (zc_input zc) - ir_next r') with (ir_have r') by (clear - RNH LF3; lia).
          rewrite Z.max_r by exact RP.
          unfold PSI, PSIr in Q2. cbn [w_r w_s] in Q2. clear - Q2 RNH LF3 RN RH RP. lia. }
        destruct (lv_cond Z_NO_FLUSH (s_rest s' r') (c_rest c' r') r').
        * rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
          destruct (uw_pure (s_rest s' r') _ _ _ ch) as [s2|] eqn:EU.
          -- destruct (uw_pure_pend _ _ _ _ _ _ EU) as [U1 U2]. apply (TAIL s2 ch); [exact U1|exact U2|exact E].
          -- exfalso. unfold sret in E. injection E; intros <-. unfold lv_mem in Hrc. cbn [fst snd zret_of_icall zr_rc] in Hrc. discriminate Hrc.
        * unfold sret at 1 in E. cbn [mbind fst snd] in E. apply (TAIL (s_rest s' r') ch); [reflexivity|reflexivity|exact E].
      + (* [comment removed for export] *)
        exfalso. unfold sret in E. cbn [fst] in E. injection E; intros <-. destruct HR' as [-> Hno].
        cbn [fst snd zret_of_icall zr_rc] in Hrc. discriminate Hrc.
  Qed.

  Theorem psi_call : psi_call_stmt.
  Proof.
    unfold psi_call_stmt. intros s zc ok HI Hz. cbv zeta.
    pose proof (inflate_p_pure (wans ok) s zc Z_NO_FLUSH (INV_check _ HI)) as EP.
    set (p := fst (inflate_p (wans ok) s zc Z_NO_FLUSH)) in *. clearbody p.
    pose proof (inflate_m_post2 Z_NO_FLUSH s zc (wans ok) p HI Hz EP) as [Q1 _].
    intros Hrc. destruct (Q1 Hrc) as (C1 & C2 & C3).
    split; [exact C1|]. split; [lia|]. exact (inflate_m_psi s zc (wans ok) p HI Hz EP Hrc).
  Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Harness.

  Lemma Forall_skipn' : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
  Proof.
    intros P n l H. revert n. induction H as [|x l Hx H IH]; intros [|n]; cbn; [constructor|constructor|constructor; assumption|apply IH].
  Qed.

  Lemma is0_bits_pend : is_bits is0 = 0 /\ pend is0 = 0.
  Proof. split; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ILI (N : Z) (x : istream) : Prop := INV (iz_s x) /\ 0 <= zs_total_in (iz_z x) <= N.
  Definition IM (N : Z) (x : istream) : Z := PSIq (N - zs_total_in (iz_z x)) (iz_s x) + (N - zs_total_in (iz_z x)).

  Lemma IM_nonneg : forall N x, ILI N x -> 0 <= IM N x.
  Proof. intros N x [HI HT]. unfold IM. pose proof (PSIq_nonneg_INV (N - zs_total_in (iz_z x)) _ HI ltac:(lia)). lia. Qed.

  Lemma il_step : forall N comprc x,
    0 <= N < 2 ^ 32 -> zlength comprc = N -> Forall (fun b => 0 <= b < 256) comprc -> ILI N x ->
    match ZHarnessL.il_stepP zinstL N comprc x with
    | inl x' => ILI N x' /\ IM N x' < IM N x
    | inr r => r <> ZHarnessL.IRLstuck
    end.
  Proof.
    intros N comprc x HN Hlen Hby [HI HT].
    unfold ZHarnessL.il_stepP, ZHarnessL.i_callL. cbn [ZApiL.il_inflate ZApiL.il_total_in zinstL]. unfold zil_inflate.
    set (inp := Prelim.zdrop (zs_total_in (iz_z x)) comprc).
    assert (Hinp : zlength inp = N - zs_total_in (iz_z x)).
    { subst inp. unfold Prelim.zdrop.
      unfold zlength. rewrite length_skipn. unfold zlength in Hlen. lia. }
    set (zc := mkZCall inp N (iz_z x)).
    assert (Hz : ZC zc).
    { unfold ZC. subst zc. cbn [zc_avail_out zc_input]. split; [lia|]. split; [lia|].
      subst inp. unfold bytes_ok, Prelim.zdrop. apply Forall_skipn'. exact Hby. }
    pose proof (psi_call (iz_s x) zc true HI Hz) as PC. cbv zeta in PC.
    pose proof (inflate_p_pure (wans true) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
    pose proof (inflate_m_post2 Z_NO_FLUSH (iz_s x) zc (wans true) _ HI Hz EP) as [Q1 _].
    destruct (inflate_p (wans true) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked]. cbn [fst snd] in PC, Q1, EP.
    pose proof (inflate_INV' (iz_s x) zc Z_NO_FLUSH (wans true) s' zr HI Hz EP) as HI'.
    assert (Ezi : zs_total_in (zc_strm zc) = zs_total_in (iz_z x)) by reflexivity.
    assert (Ein : zlength (zc_input zc) = N - zs_total_in (iz_z x)) by (subst zc; cbn [zc_input]; exact Hinp).
    rewrite Ezi, Ein in Q1. rewrite Ein in PC.
    destruct (Z.eqb_spec (zr_rc zr) ZApi.Z_STREAM_END) as [E1|N1]; [discriminate|].
    destruct (Z.eqb_spec (zr_rc zr) ZApi.Z_OK) as [E0|N0]; [|discriminate].
    destruct (Q1 E0) as (K1 & K2 & K3). destruct (PC E0) as (P1 & P2 & P3).
    assert (ET : zs_total_in (zr_strm zr) = zs_total_in (iz_z x) + zr_consumed zr) by (rewrite K2; apply wrap64_id; lia).
    split.
    - unfold ILI. cbn [iz_s iz_z]. split; [exact HI'|]. rewrite ET. lia.
    - unfold IM. cbn [iz_s iz_z]. rewrite ET.
      replace (N - (zs_total_in (iz_z x) + zr_consumed zr)) with (N - zs_total_in (iz_z x) - zr_consumed zr) by lia.
      pose proof (zlength_nonneg (zr_output zr)). lia.
  Qed.

End Harness.
