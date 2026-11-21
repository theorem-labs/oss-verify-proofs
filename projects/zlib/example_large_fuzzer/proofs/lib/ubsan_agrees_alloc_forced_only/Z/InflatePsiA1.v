(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflatePsi InflatePsi1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arm_BAD_psi : arm_psi BAD arm_BAD.
Proof.
  intros w0 s c r HW E HQ. unfold arm_BAD. arun2 ur_eq. rewrite aleave_eq. cbn [PP]. ppw E HQ.
Qed.

Lemma arm_DONE_psi : arm_psi DONE arm_DONE.
Proof.
  intros w0 s c r HW E HQ. unfold arm_DONE. arun2 ur_eq. rewrite aleave_eq. cbn [PP]. ppw E HQ.
Qed.

Lemma arm_MEM_psi : arm_psi MEM arm_MEM.
Proof. intros w0 s c r HW E HQ. unfold arm_MEM. rewrite areturn_eq. exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arm_LIT_psi : arm_psi LIT arm_LIT.
Proof.
  intros w0 s c r HW E HQ. unfold arm_LIT.
  arun2 gr_eq.
  destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0].
  { rewrite aleave_eq. exact HQ. }
  arun2 gs_eq. arun2 uc_eq. arun2 ur_eq. rewrite set_mode_eq.
  winv_open2 HW E HC HR. regs_open HR.
  apply PP_ARun. ppw E HQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arm_LENGTH_psi : arm_psi LENGTH arm_LENGTH.
Proof.
  intros w0 s c r HW E HQ. unfold arm_LENGTH. arun2 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct (negb (is_wrap s =? 0) && negb (is_flags s =? 0)) eqn:Cwf.
  - aflat.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply PP_bind_run; [exact EQ|]. cbv beta. aflat. arun2 HOLD_eq. aflat. arun2 gs_eq.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      acase2 Cbad.
      * aflat. arun2 go_bad_eq. arun2 aret_eq. ired. rewrite aret_eq. apply PP_ARun. ppw E HQ.
      * aflat. arun2 INITBITS_eq. arun2 aret_eq. ired. aflat. arun2 set_mode_eq.
        apply (PP_arm DONE arm_DONE _ _ _ _ arm_DONE_psi).
        -- winv_split.
           ++ core_keep HC. apply CORE_length; exact HC.
           ++ apply REGS_init. exact HR1.
           ++ exact HMF.
           ++ exact I.
           ++ rewrite Ep1. exact HWB.
        -- reflexivity.
        -- ppw E HQ.
    + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  - arun2 aret_eq. ired. aflat. arun2 set_mode_eq.
    apply (PP_arm DONE arm_DONE _ _ _ _ arm_DONE_psi).
    + winv_split.
      * core_keep HC. apply CORE_length; exact HC.
      * exact HR.
      * exact HMF.
      * exact I.
      * exact HWB.
    + reflexivity.
    + ppw E HQ.
Qed.

(* [comment removed for export] *)
Ltac check_tail2 HC HCK HR1 Ep1 HWB E HQ :=
  aflat; arun2 ur_eq; aflat; arun2 HOLD_eq; aflat; arun2 gs_eq; cbv zeta;
  let Cbad := fresh "Cbad" in
  acase2 Cbad;
  [ aflat; arun2 go_bad_eq; arun2 aret_eq; ired; rewrite aret_eq; apply PP_ARun; ppw E HQ
  | aflat; arun2 INITBITS_eq; arun2 aret_eq; ired; arun2 set_mode_eq;
    apply (PP_arm LENGTH arm_LENGTH _ _ _ _ arm_LENGTH_psi);
    [ winv_split;
      [ core_keep HC; apply CORE_length; exact HC
      | eapply REGS_cview; [| reflexivity | reflexivity]; apply REGS_init; apply REGS_out_reg; apply REGS_out_reg; exact HR1
      | exact HCK
      | exact I
      | rewrite Ep1; exact HWB ]
    | reflexivity
    | ppw E HQ ] ].

Lemma arm_CHECK_psi : arm_psi CHECK arm_CHECK.
Proof.
  intros w0 s c r HW E HQ. unfold arm_CHECK. arun2 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  acase2 Cw.
  - aflat.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply PP_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      aflat. arun2 gr_eq. cbv zeta. aflat. arun2 ur_eq. aflat. arun2 uc_eq. aflat. arun2 us_eq. aflat. arun2 gs_eq.
      acase2 Cupd.
      * aflat. arun02. cbn [w_s w_c w_r]. arun2 set_adler_check_eq.
        match goal with |- PP _ (_ (mkW ?s1 _ _)) => assert (HCK : common s1) end.
        { eapply (common_update_check s); [exact HMF | reflexivity | reflexivity | | sacc; reflexivity]. reflexivity. }
        check_tail2 HC HCK HR1 Ep1 HWB E HQ.
      * arun2 aret_eq.
        match goal with |- PP _ (_ (mkW ?s1 _ _)) => assert (HCK : common s1) end.
        { common_keep HMF. }
        check_tail2 HC HCK HR1 Ep1 HWB E HQ.
    + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  - arun2 aret_eq. ired. arun2 set_mode_eq.
    apply (PP_arm LENGTH arm_LENGTH _ _ _ _ arm_LENGTH_psi).
    + winv_split.
      * core_keep HC. apply CORE_length; exact HC.
      * exact HR.
      * exact HMF.
      * exact I.
      * exact HWB.
    + reflexivity.
    + ppw E HQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TypeArms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_TYPEDO_core_psi : forall M, (M = TYPE \/ M = TYPEDO) -> arm_psi M (arm_TYPEDO iv flush).
  Proof.
    intros M HM w0 s c r HW E HQ.
    assert (HW' : CORE s /\ REGS c r /\ (common s /\ ir_bits r < 8) /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0)).
    { destruct HM as [-> | ->]; [winv_open2 HW E HC HR | winv_open2 HW E HC HR]; repeat (split; [assumption|]); assumption. }
    clear HW. destruct HW' as (HC & HR & [HCm Hb8] & HWF & HWB). regs_open HR.
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; destruct HM as [-> | ->]; reflexivity).
    assert (HQ' : forall s' c' r', ir_put r <= ir_put r' -> PSIW * (8 * ir_have r' + ir_bits r') + pend s' <= PSIW * (8 * ir_have r + ir_bits r) ->
                   ir_put r' = ir_put r -> PPw w0 (mkW s' c' r')).
    { intros s' c' r' A1 A2 A3. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd. lia. }
    unfold arm_TYPEDO. arun2 gs_eq. acase2 Clast.
    - (* [comment removed for export] *)
      arun2 BYTEBITS_eq. rewrite set_mode_eq.
      pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
      assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
      apply PP_ARun. apply HQ'; sacc; [lia| |reflexivity]. pend_lit. rewrite L7. rewrite wrap32_id by lia. unfold PSIW. lia.
    - (* [comment removed for export] *)
      aflat.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply PP_bind_run; [exact EQ|]. cbv beta.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
        pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
        aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq. aflat. arun2 BITS_eq. sacc.
        rewrite (wrap32_id (ir_bits r1 - 1)) by lia.
        assert (Hb8' : ir_bits r1 - 1 - 2 < 8) by lia.
        acase2 Ct0; [|acase2 Ct1; [|acase2 Ct2]].
        * (* [comment removed for export] *)
          aflat. arun2 set_mode_eq. arun2 aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply PP_ARun. apply HQ'; sacc; [lia| |lia]. pend_lit. unfold PSIW. lia.
        * (* [comment removed for export] *)
          aflat. arun2 us_eq. aflat. arun2 set_mode_eq.
          unfold fixedtables.
          acase2 Cz.
          -- aflat. arun2 DROPBITS_eq. aleave2. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
             apply HQ'; sacc; [lia| |lia]. pend_lit. unfold PSIW. lia.
          -- arun2 aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
             apply PP_ARun. apply HQ'; sacc; [lia| |lia]. pend_lit. unfold PSIW. lia.
        * (* [comment removed for export] *)
          aflat. arun2 set_mode_eq. arun2 aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply PP_ARun. apply HQ'; sacc; [lia| |lia]. pend_lit. unfold PSIW. lia.
        * (* [comment removed for export] *)
          aflat. arun2 go_bad_eq. arun2 aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply PP_ARun. apply HQ'; sacc; [lia| |lia]. pend_lit. unfold PSIW. lia.
      + eapply PP_bind_leave; [exact EQ|]. pose proof (pulled_psi r r1 HP1) as PS1. apply HQ'; [lia| |lia]. rewrite Hpd. lia.
  Qed.

  Lemma arm_TYPEDO_psi : arm_psi TYPEDO (arm_TYPEDO iv flush).
  Proof. apply arm_TYPEDO_core_psi. right; reflexivity. Qed.

  Lemma arm_TYPE_psi : arm_psi TYPE (arm_TYPE iv flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_TYPE.
    destruct (iv_flush_exits iv && ((flush =? Z_BLOCK) || (flush =? Z_TREES))).
    - rewrite aleave_eq. exact HQ.
    - exact (arm_TYPEDO_core_psi TYPE (or_introl eq_refl) w0 s c r HW E HQ).
  Qed.
End TypeArms.
