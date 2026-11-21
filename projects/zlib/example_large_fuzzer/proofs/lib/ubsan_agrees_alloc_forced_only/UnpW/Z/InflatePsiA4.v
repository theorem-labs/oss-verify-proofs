(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import InflatePsi InflatePsi1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section HeaderArms.
  Variable iv : ivariant.
  Variable flush : Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma arm_HCRC_psi : arm_psi HCRC arm_HCRC.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_HCRC. arun2 gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    acase2 Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply PP_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
        aflat. arun2 HOLD_eq. aflat. arun2 gs_eq. acase2 Cbad.
        * aflat. arun2 go_bad_eq. arun2 aret_eq. rewrite aret_eq. apply PP_ARun. ppw E HQ.
        * aflat. arun2 INITBITS_eq. arun2 aret_eq. aflat. arun2 set_adler_check_eq. rewrite set_mode_eq. apply PP_ARun. ppw E HQ.
      + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
    - arun2 aret_eq. aflat. arun2 set_adler_check_eq. rewrite set_mode_eq. apply PP_ARun. ppw E HQ.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma PP_name_like : forall w0 flag s c r M (K : bool -> AM unit),
    WINV (mkW s c r) -> is_mode s = M -> (M = NAME \/ M = COMMENT) -> PPw w0 (mkW s c r) ->
    (forall w', WINV w' -> PPw w0 w' -> PP w0 (K false w')) ->
    (forall s' r', CORE s' -> REGS c r' -> common s' -> is_mode s' = M -> is_wbits s' = is_wbits s ->
                   is_length s' = is_length s ->
                   ir_bits r' = ir_bits r -> ir_hold r' = ir_hold r -> ir_out r' = ir_out r -> ir_put r' = ir_put r ->
                   ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
                   PPw w0 (mkW s' c r') ->
                   PP w0 (K true (mkW s' c r'))) ->
    PP w0 (abind (name_like flag) K (mkW s c r)).
  Proof.
    intros w0 flag s c r M K HW E HM HQ KF KT.
    assert (HW' : CORE s /\ REGS c r /\ (common s /\ ir_bits r < 8) /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0)).
    { pose proof HW as HW1. destruct HM as [-> | ->]; [winv_open2 HW1 E HC HR | winv_open2 HW1 E HC HR]; repeat (split; [assumption|]); assumption. }
    destruct HW' as (HC & HR & [HCm Hb8] & HWF & HWB). regs_open HR.
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; destruct HM as [-> | ->]; reflexivity).
    assert (HQ' : forall s' c' r', is_mode s' = M -> ir_put r' = ir_put r -> ir_bits r' = ir_bits r -> 0 <= ir_have r' <= ir_have r -> PPw w0 (mkW s' c' r')).
    { intros s' c' r' A1 A2 A3 A4. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd.
      assert (Hpd' : pend s' = 0) by (unfold pend; rewrite A1; destruct HM as [-> | ->]; reflexivity). rewrite Hpd'. unfold PSIW. lia. }
    unfold name_like. aflat. arun2 gs_eq. acase2 Cf.
    - aflat. arun2 gr_eq. acase2 Ch0.
      + arun2 aret_eq. apply KF; [exact HW|exact HQ].
      + apply Z.eqb_neq in Ch0. aflat. arun2 aget_eq. cbn [w_s w_c w_r].
        pose proof (scan_zero_spec (ic_input c) (ir_next r) (ir_have r) ltac:(lia)) as SZ.
        destruct (scan_zero (ic_input c) (ir_next r) (ir_have r)) as [copy len]. ired.
        assert (STEP : exists ck, (if hcrc_on s then crc_input copy else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)
                       /\ (hcrc_on s = false -> ck = is_check s)).
        { destruct (hcrc_on s).
          - eexists. split; [reflexivity|]. intros X; discriminate X.
          - exists (is_check s). split; [|reflexivity]. unfold aret. f_equal. destruct s; reflexivity. }
        destruct STEP as (ck & STEP & Hck).
        aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 ur_eq.
        assert (HCm' : common (iset_check s ck)).
        { destruct (hcrc_on s) eqn:Hh.
          - eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
          - rewrite (Hck eq_refl). common_keep HCm. }
        rewrite (wrap32_id (ir_have r - copy)) by lia.
        acase2 Clen.
        * arun2 aret_eq. apply KF.
          -- unfold WINV. cbn [w_s w_c w_r]. sacc. rewrite E. split; [core_keep HC; apply CORE_length; exact HC|].
             split; [regs_solve RIN|].
             split; [destruct HM as [-> | ->]; mred; (split; [exact HCm'|exact Hb8])|].
             split; [destruct HM as [-> | ->]; mred; exact HWF|]. exact HWB.
          -- apply HQ'; sacc; [exact E|reflexivity|reflexivity|lia].
        * arun2 aret_eq. apply KT; try reflexivity.
          -- core_keep HC. apply CORE_length; exact HC.
          -- regs_solve RIN.
          -- exact HCm'.
          -- sacc. exact E.
          -- sacc. lia.
          -- apply HQ'; sacc; [exact E|reflexivity|reflexivity|lia].
    - arun2 aret_eq. apply KT; try reflexivity; try assumption. lia.
  Qed.

  Lemma arm_COMMENT_psi : arm_psi COMMENT arm_COMMENT.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_COMMENT.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (PP_name_like w0 4096 s c r COMMENT _ HW0 E (or_intror eq_refl) HQ).
    - intros w' HW' HQ'. cbv beta. aleave2. exact HQ'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh HQ'. cbv beta iota. arun2 set_mode_eq.
      apply (PP_arm HCRC arm_HCRC _ _ _ _ arm_HCRC_psi).
      + winv_split.
        * core_keep HC'. apply CORE_length; exact HC'.
        * exact HR'.
        * split; [common_keep HCm'|]. intros _. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + ppw E' HQ'.
  Qed.

  Lemma arm_NAME_psi : arm_psi NAME arm_NAME.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_NAME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (PP_name_like w0 2048 s c r NAME _ HW0 E (or_introl eq_refl) HQ).
    - intros w' HW' HQ'. cbv beta. aleave2. exact HQ'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh HQ'. cbv beta iota. aflat. arun2 us_eq. arun2 set_mode_eq.
      apply (PP_arm COMMENT arm_COMMENT _ _ _ _ arm_COMMENT_psi).
      + winv_split.
        * core_keep HC'. lia.
        * exact HR'.
        * split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + ppw E' HQ'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma arm_EXTRA_psi : arm_psi EXTRA arm_EXTRA.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_EXTRA. arun2 gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; reflexivity).
    assert (HQ' : forall s' c' r', pend s' = 0 -> ir_put r' = ir_put r -> ir_bits r' = ir_bits r -> 0 <= ir_have r' <= ir_have r -> PPw w0 (mkW s' c' r')).
    { intros s' c' r' A1 A2 A3 A4. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd, A1. unfold PSIW. lia. }
    (* [comment removed for export] *)
    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' = ir_bits r -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
              PP w0 ((us (fun s0 => iset_length s0 0) ;; set_mode NAME ;; arm_NAME)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Eb Eo Ep El Hh. aflat. arun2 us_eq. arun2 set_mode_eq.
      apply (PP_arm NAME arm_NAME _ _ _ _ arm_NAME_psi).
      - winv_split.
        + core_keep HC'. lia.
        + exact HR'.
        + split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - apply HQ'; sacc; [pend_lit; reflexivity|exact Ep|exact Eb|exact Hh]. }
    acase2 Cf.
    - aflat. arun2 gr_eq. cbv zeta.
      set (cp := if ir_have r <? is_length s then ir_have r else is_length s).
      assert (Hcp : 0 <= cp <= ir_have r /\ cp <= is_length s) by (subst cp; destruct (Z.ltb_spec (ir_have r) (is_length s)); lia).
      match goal with |- PP _ (abind (abind ?m _) _ ?w) =>
        assert (STEP : exists ck, m w = ARun tt (mkW (iset_length (iset_check s ck) (is_length s - cp)) c
                                                  (irset_next (irset_have r (ir_have r - cp)) (ir_next r + cp)))
                       /\ common (iset_check s ck))
      end.
      { destruct (negb (cp =? 0)) eqn:Ccp.
        - assert (CRC : exists ck, (if hcrc_on s then crc_input cp else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)
                         /\ common (iset_check s ck)).
          { destruct (hcrc_on s) eqn:Hh.
            - eexists. split; [reflexivity|]. eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
            - exists (is_check s). split; [unfold aret; f_equal; destruct s; reflexivity|]. common_keep HCm. }
          destruct CRC as (ck & CRC & HCk). exists ck. split; [|exact HCk].
          unfold abind. rewrite CRC. rewrite ur_eq. cbn [w_s w_c w_r]. unfold us. cbn [w_s w_c w_r wset_s]. sacc.
          rewrite !wrap32_id by lia. destruct s; reflexivity.
        - exists (is_check s). destruct (Z.eqb_spec cp 0) as [C0|C0]; [|discriminate Ccp]. rewrite C0, !Z.sub_0_r, !Z.add_0_r.
          split; [|common_keep HCm]. unfold aret. f_equal. destruct s, r; reflexivity. }
      destruct STEP as (ck & STEP & HCk).
      aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 gs_eq. acase2 Clen.
      + arun2 aret_eq. aleave2. apply HQ'; sacc; [pend_lit; rewrite E; pend_red; reflexivity|reflexivity|reflexivity|lia].
      + arun2 aret_eq. apply TAIL; first [ core_keep HC; lia | regs_solve RIN | common_keep HCk | sacc; first [reflexivity | lia] ].
    - arun2 aret_eq. apply TAIL; first [assumption | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma arm_EXLEN_psi : arm_psi EXLEN arm_EXLEN.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_EXLEN. arun2 gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; reflexivity).
    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' < 8 -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r ->
              8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r ->
              PP w0 ((set_mode EXTRA ;; arm_EXTRA)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Hb Eo Ep El Hm. arun2 set_mode_eq.
      apply (PP_arm EXTRA arm_EXTRA _ _ _ _ arm_EXTRA_psi).
      - winv_split.
        + core_keep HC'. apply CORE_length; exact HC'.
        + exact HR'.
        + split; [common_keep HCm'|exact Hb].
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd. pend_lit. unfold PSIW. lia. }
    acase2 Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply PP_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
        aflat. arun2 HOLD_eq. aflat. arun2 us_eq.
        destruct (hcrc_step (iset_length s (wrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 ltac:(common_keep HCm) ltac:(eexists; reflexivity))
          as (ck & STEP & HCk).
        aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 INITBITS_eq.
        apply TAIL; first [ core_keep HC; apply wrap32_range | apply REGS_init; exact HR1 | exact HCk | sacc; first [reflexivity | lia] ].
      + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
    - arun2 aret_eq.
      assert (F0 : Z.land (is_flags s) 1024 = 0) by (destruct (Z.eqb_spec (Z.land (is_flags s) 1024) 0); [assumption|discriminate Cf]).
      apply TAIL; first [assumption | reflexivity | exact (Hb8 F0) | lia].
  Qed.

  Lemma arm_OS_psi : arm_psi OS arm_OS.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_OS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply PP_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      aflat. arun2 HOLD_eq. aflat. arun2 gs_eq.
      destruct (hcrc_step s (CRC2 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 INITBITS_eq. arun2 set_mode_eq.
      apply (PP_arm EXLEN arm_EXLEN _ _ _ _ arm_EXLEN_psi).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * split; [common_keep HCk|]. intros _. cbn. lia.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + ppw E HQ.
    - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  Qed.

  Lemma arm_TIME_psi : arm_psi TIME arm_TIME.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_TIME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply PP_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      aflat. arun2 HOLD_eq. aflat. arun2 gs_eq.
      destruct (hcrc_step s (CRC4 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 INITBITS_eq. arun2 set_mode_eq.
      apply (PP_arm OS arm_OS _ _ _ _ arm_OS_psi).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + ppw E HQ.
    - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  Qed.

  Lemma arm_FLAGS_psi : arm_psi FLAGS arm_FLAGS.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_FLAGS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HWb HCk0].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply PP_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      aflat. arun2 HOLD_eq. aflat. arun2 us_eq. aflat. arun2 gs_eq.
      assert (BADc : forall msg, PP w0 (go_bad msg (mkW (iset_flags s (swrap32 (ir_hold r1))) c r1))).
      { intros msg. unfold go_bad. arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. ppw E HQ. }
      acase2 C1; [apply BADc|]. acase2 C2; [apply BADc|].
      assert (HCm1 : common (iset_flags s (swrap32 (ir_hold r1)))).
      { split; [exact HWb|]. intros _. exact HCk0. }
      destruct (hcrc_step (iset_flags s (swrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 HCm1 ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply PP_bind_run; [exact STEP|]. cbv beta iota. aflat. arun2 INITBITS_eq. arun2 set_mode_eq.
      apply (PP_arm TIME arm_TIME _ _ _ _ arm_TIME_psi).
      + winv_split.
        * core_keep HC. exact HL0.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact (proj1 HWF).
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + ppw E HQ.
    - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma arm_HEAD_psi : arm_psi HEAD (arm_HEAD ivar_ref).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_HEAD. arun2 gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [Hwb8 HCk0].
    pose proof (CORE_length s HC) as HL0.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; reflexivity).
    acase2 Cw0.
    - (* [comment removed for export] *)
      rewrite set_mode_eq. apply PP_ARun. ppw E HQ.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply PP_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
        pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
        aflat. arun2 HOLD_eq. acase2 Cgz.
        * (* [comment removed for export] *)
          apply andb_prop in Cgz as [_ Cgz]. apply Z.eqb_eq in Cgz.
          aflat. destruct (wbits_step s c r1 15 HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply PP_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun2 us_eq. unfold CRC2. aflat. arun2 us_eq. aflat. arun2 INITBITS_eq. rewrite set_mode_eq.
          apply PP_ARun. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. sacc. rewrite Hpd. pend_lit. unfold PSIW. lia.
        * (* [comment removed for export] *)
          aflat. arun2 BITS_eq.
          assert (BADc : forall msg s1 r', ir_put r' = ir_put r -> 8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r ->
                    PP w0 (go_bad msg (mkW s1 c r'))).
          { intros msg s1 r' Ep Hm. unfold go_bad. arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun.
            eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd. pend_lit. unfold PSIW. lia. }
          acase2 Chk; [apply BADc; [exact Ep1 | lia]|].
          aflat. arun2 BITS_eq.
          acase2 Ccm; [apply BADc; [exact Ep1 | lia]|].
          aflat. arun2 DROPBITS_eq. aflat. arun2 BITS_eq. cbv zeta. sacc.
          rewrite (wrap32_id (ir_bits r1 - 4)) by lia.
          set (r2 := irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (ir_bits r1 - 4)).
          set (len := BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8).
          assert (Hlen : 8 <= len).
          { subst len. rewrite BITSv_mod; [|apply Z.shiftr_nonneg; lia|lia]. pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 4) 4 ltac:(lia)). lia. }
          (* zlib 1.4 (zl14infl-r2): the window-size check first, then wbits := len only if it is 0 *)
          aflat. arun2 gs_eq.
          acase2 Cws; [apply BADc; [subst r2; sacc; exact Ep1 | subst r2; sacc; lia]|].
          aflat. destruct (wbits_step s c r2 len HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply PP_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun2 aux_ref'. aflat. arun2 us_eq. aflat. arun2 set_adler_check_eq. aflat. arun2 HOLD_eq. aflat. arun2 set_mode_eq.
          rewrite INITBITS_eq.
          apply PP_ARun. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. subst r2. sacc. rewrite Hpd.
          destruct (negb (Z.land (Z.shiftr (ir_hold r1) 4) 512 =? 0)); pend_lit; unfold PSIW; lia.
      + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  Qed.
End HeaderArms.
