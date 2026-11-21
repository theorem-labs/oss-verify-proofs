(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage ItDefs ItProof ItTable AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA1 RefInflateSafeA3 RefInflateSafeA5 RefInflateSafeA6 RefInflateSafeF3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflatePsi InflatePsi1 InflatePsiA3 InflatePsiF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Leaves.
  Variable c : icall.

  Lemma codelens_body_leave : forall s r w',
    CL s c r -> is_have s < is_nlen s + is_ndist s ->
    codelens_body (mkW s c r) = ALeave w' -> exists r', w' = mkW s c r' /\ pulled r r'.
  Proof.
    intros s r w' HCL Hlt. pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    regs_open HR. pose proof (CORE_length s HC) as HL0.
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & _).
    pose proof (T_root _ _ _ _ HTg) as HR15.
    unfold codelens_body. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    destruct (DECODE1_spec c s (is_lencode s) CODES (is_lenbits s) used HTg r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    2:{ unfold abind at 1. rewrite EQ. intros X. injection X as <-. exists r1. split; [reflexivity|exact HP1]. }
    unfold abind at 1. rewrite EQ.
    pose proof HR1 as (RN1 & RH1 & RNH1 & RP1 & RL1 & RPL1 & [RB1 RHO1] & _).
    destruct (root_cell CODES _ _ used HTg (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HTg _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits.
    cbv beta. destruct (Z.ltb_spec (code_val here) 16) as [V16|V16].
    - unfold abind. rewrite DROPBITS_eq. rewrite gs_eq. cbn [w_s]. unfold set_lens. rewrite us_eq. rewrite us_eq. unfold aret.
      intros X; discriminate X.
    - assert (GEN : forall e base (lenf : inflate_state -> Z) (chk : bool), 1 <= e <= 7 ->
        (abind (NEEDBITS (code_bits here + e) ;; DROPBITS (code_bits here) ;;
                do s0 <- gs (fun s0 => s0) ;
                if chk && (is_have s0 =? 0) then go_bad MSG_invalid_bit_length_repeat ;; aret None
                else do b <- BITS e ; DROPBITS e ;; aret (Some (lenf s0, base + b)))
               (fun lc => match lc with
                          | None => aret false
                          | Some (len, copy) =>
                              do s0 <- gs (fun s0 => s0) ;
                              if is_nlen s0 + is_ndist s0 <? is_have s0 + copy
                              then go_bad MSG_invalid_bit_length_repeat ;; aret false
                              else lens_repeat copy len ;; aret true
                          end) (mkW s c r1))%am = ALeave w' ->
        exists r', w' = mkW s c r' /\ pulled r r').
      { intros e base lenf chk He.
        rewrite abind_assoc. unfold abind at 1.
        destruct (NEEDBITS_spec c (code_bits here + e) s r1 HR1 ltac:(lia)) as [(r2 & EQ2 & HR2 & HP2 & Hn2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hb2 & Hh2)].
        2:{ rewrite EQ2. intros X. injection X as <-. exists r2. split; [reflexivity|exact (pulled_trans r r1 r2 ltac:(lia) HP1 HP2)]. }
        rewrite EQ2. mrun DROPBITS_eq. mrun gs_eq. cbn [w_s].
        destruct (chk && (is_have s =? 0)).
        { mrun go_bad_eq. unfold aret. intros X; discriminate X. }
        mrun BITS_eq. mrun DROPBITS_eq. mrun aret_eq. mrun gs_eq. cbn [w_s].
        match goal with |- context [if ?cnd then _ else _] => destruct cnd end.
        { mrun go_bad_eq. unfold aret. intros X; discriminate X. }
        unfold lens_repeat. mrun us_eq. unfold aret. intros X; discriminate X. }
      destruct (Z.eqb_spec (code_val here) 16) as [E16|E16].
      + exact (GEN 2 3 (fun s0 => arr_get (is_lens s0) (is_have s0 - 1)) true ltac:(lia)).
      + destruct (Z.eqb_spec (code_val here) 17) as [E17|E17].
        * exact (GEN 3 3 (fun _ => 0) false ltac:(lia)).
        * exact (GEN 7 11 (fun _ => 0) false ltac:(lia)).
  Qed.

  Lemma codelens_while_leave : forall k s r w',
    CL s c r -> is_nlen s + is_ndist s - is_have s < Z.of_nat k ->
    codelens_while k (mkW s c r) = ALeave w' ->
    exists s' r', w' = mkW s' c r' /\ is_mode s' = CODELENS /\ 8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r /\ ir_put r' = ir_put r.
  Proof.
    induction k as [|k IH]; intros s r w' HCL Hk.
    { exfalso. pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & Hh & _). cbn in Hk. lia. }
    pose proof HCL as (_ & HR & E & _). pose proof HR as (_ & _ & _ & _ & _ & RPL & _).
    rewrite codelens_while_S. mrun gs_eq. cbn [w_s].
    destruct (Z.ltb_spec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE].
    - unfold abind at 1. pose proof (codelens_body_spec c s r HCL LT) as B.
      destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w1 | rc w1] eqn:EB.
      + cbv beta iota. destruct B as (-> & HCL1 & Hh1 & Hb1 & En1 & Ed1 & P1 & Ep1).
        intros X. destruct (IH s1 r1 w' HCL1 ltac:(lia) X) as (s' & r' & -> & Em' & TB' & Ep').
        pose proof HCL1 as (_ & HR1 & _). pose proof HR1 as (_ & _ & _ & _ & _ & RPL1 & _).
        exists s', r'. split; [reflexivity|]. split; [exact Em'|]. unfold PHIr in P1. lia.
      + cbv beta iota. unfold aret. intros X; discriminate X.
      + intros X. injection X as <-. destruct (codelens_body_leave s r w1 HCL LT EB) as (r' & -> & HP').
        apply pulled_psi in HP'. exists s, r'. split; [reflexivity|]. split; [exact E|]. lia.
      + destruct B.
    - unfold aret. intros X; discriminate X.
  Qed.

  Lemma lenlens_while1_leave : forall k s r w',
    REGS c r -> lenlens_while1 k (mkW s c r) = ALeave w' ->
    exists s' r', w' = mkW s' c r' /\ is_mode s' = is_mode s /\ is_length s' = is_length s /\ is_extra s' = is_extra s
                  /\ 8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r /\ ir_put r' = ir_put r.
  Proof.
    induction k as [|k IH]; intros s r w' HR.
    - cbn [lenlens_while1]. unfold aret. intros X; discriminate X.
    - regs_open HR. rewrite lenlens_while1_S. mrun gs_eq. cbn [w_s].
      destruct (Z.ltb_spec (is_have s) (is_ncode s)) as [LT|GE].
      2:{ unfold aret. intros X; discriminate X. }
      rewrite ?abind_assoc. unfold abind at 1.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      2:{ rewrite EQ. intros X. injection X as <-. apply pulled_psi in HP1. exists s, r1. repeat (split; [reflexivity|]). lia. }
      rewrite EQ. cbv beta iota.
      pose proof (pulled_psi r r1 HP1) as PS1. pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      mrun BITS_eq. mrun gs_eq. cbn [w_s]. unfold set_lens. mrun us_eq. mrun us_eq. mrun DROPBITS_eq. sacc.
      rewrite (wrap32_id (ir_bits r1 - 3)) by lia.
      intros X.
      match type of X with lenlens_while1 k (mkW ?s1 ?c1 ?r1') = _ =>
        destruct (IH s1 r1' w' ltac:(apply REGS_holdbits; [exact HR1|]; apply HB_drop; [split; [exact RB1|exact RHO1]|lia]) X)
          as (s' & r' & -> & Em' & El' & Ex' & TB' & Ep') end.
      revert Em' El' Ex' TB' Ep'. sacc. intros Em' El' Ex' TB' Ep'.
      exists s', r'. repeat (split; [first [reflexivity | assumption] |]). lia.
  Qed.
End Leaves.


Section TableArms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_CODELENS_psi : arm_psi CODELENS (arm_CODELENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_CODELENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & CA2 & CA3 & CS & CL0).
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; reflexivity).
    assert (LEAF : forall s' c' r', pend s' = 0 -> ir_put r' = ir_put r -> 8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r -> PPw w0 (mkW s' c' r')).
    { intros s' c' r' A1 A2 A3. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd, A1. unfold PSIW. lia. }
    assert (HCL : CL s c r).
    { unfold CL. repeat (split; [first [assumption | lia]|]). exact HWB. }
    apply PP_bind.
    pose proof (codelens_while_spec c 321 s r HCL ltac:(cbn; lia)) as W.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1] eqn:EW; [| |destruct W].
    2:{ destruct (codelens_while_leave c 321 s r w1 HCL ltac:(cbn; lia) EW) as (s' & r' & -> & Em' & TB' & Ep').
        apply LEAF; [unfold pend; rewrite Em'; reflexivity|exact Ep'|exact TB']. }
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & P1 & Ep1 & Q1 & _)|(Hm1 & HW1 & P1 & Ep1 & Ei1 & Eo1)].
    2:{
        arun2 gs_eq. rewrite Hm1. change (BAD =? BAD) with true. cbv iota. rewrite aret_eq. apply PP_ARun.
        pose proof HW1 as HW1'. unfold WINV in HW1'. cbn [w_s w_c w_r] in HW1'. destruct HW1' as (_ & HR1 & _).
        pose proof HR1 as (_ & _ & _ & _ & _ & RPL1 & _). rewrite Eo1 in RPL1.
        apply LEAF; [unfold pend; rewrite Hm1; reflexivity|exact Ep1|unfold PHIr in P1; lia]. }
    destruct (Q1 (proj2 Hh)) as [P1' Hb1]. clear Q1 P1.
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & _ & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & RPL1 & [RB1 RHO1] & _).
    assert (TB1 : 8 * ir_have r1 + ir_bits r1 <= 8 * ir_have r + ir_bits r) by (unfold PHIr in P1'; lia).
    arun2 gs_eq. rewrite E1. change (CODELENS =? BAD) with false. cbv iota.
    acase2 C256.
    { arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. apply LEAF; [pend_lit; reflexivity|exact Ep1|exact TB1]. }
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    match goal with |- context [inflate_table LENS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table LENS a1 a2 a3 a4 a5 a6 a7) as [[[[retL tblL] nextL] lenbitsL] workL] end.
    destruct TL as [[TL5 TL6] TL].
    cbv beta iota. aflat. arun2 us_eq. aflat. arun2 ur_eq.
    acase2 CrL.
    { arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. apply LEAF; [pend_lit; reflexivity|sacc; exact Ep1|sacc; exact TB1]. }
    assert (RL0 : retL = 0) by (destruct (Z.eqb_spec retL 0); [assumption|discriminate CrL]).
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    arun2 gs_eq. sacc.
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    match goal with |- context [inflate_table DISTS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table DISTS a1 a2 a3 a4 a5 a6 a7) as [[[[retD tblD] nextD] distbitsD] workD] end.
    destruct TD as [[TD5 TD6] TD].
    cbv beta iota. aflat. arun2 us_eq. aflat. arun2 ur_eq.
    acase2 CrD.
    { arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. apply LEAF; [pend_lit; reflexivity|sacc; exact Ep1|sacc; exact TB1]. }
    assert (RD0 : retD = 0) by (destruct (Z.eqb_spec retD 0); [assumption|discriminate CrD]).
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    aflat. arun2 set_mode_eq.
    match goal with |- PP _ (_ ?w) => assert (HW3 : WINV w) end.
    { winv_split.
      - core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
      - eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
      - split; [common_keep HCm1|]. split; [exact Hb1|]. unfold tables. sacc. split.
        + cbn [cpok]. split; [lia|]. exists (nextL - 0). split; [lia|].
          apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        + cbn [cpok]. split; [lia|]. exists (nextD - nextL). split; [lia|]. exact TD3.
      - exact HWF1.
      - exact HWB1. }
    match goal with |- PP _ (_ ?w) => assert (HQ3 : PPw w0 w) end.
    { apply LEAF; [pend_lit; reflexivity|sacc; exact Ep1|sacc; exact TB1]. }
    acase2 Cz.
    - aleave2. exact HQ3.
    - match goal with |- PP _ (_ (mkW ?s3 ?c3 ?r3)) => apply (PP_arm LEN_ (arm_LEN_ ivar_ref) w0 s3 c3 r3 arm_LEN__psi HW3) end.
      + reflexivity.
      + exact HQ3.
  Qed.


  Lemma arm_LENLENS_psi : arm_psi LENLENS (arm_LENLENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_LENLENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
    assert (Hpd : pend s = 0) by (unfold pend; rewrite E; reflexivity).
    assert (LEAF : forall s' c' r', pend s' = 0 -> ir_put r' = ir_put r -> 8 * ir_have r' + ir_bits r' <= 8 * ir_have r + ir_bits r -> PPw w0 (mkW s' c' r')).
    { intros s' c' r' A1 A2 A3. eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Hpd, A1. unfold PSIW. lia. }
    assert (HLL : LL s c r) by (unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    apply PP_bind.
    pose proof (lenlens_while1_spec c 19 s r HLL ltac:(cbn; lia)) as W1.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1] eqn:EW; [| |destruct W1].
    2:{ destruct (lenlens_while1_leave c 19 s r w1 HR EW) as (s' & r' & -> & Em' & El' & Ex' & TB' & Ep').
        apply LEAF; [rewrite (pend_keep s s' Em' El' Ex'); exact Hpd|exact Ep'|exact TB']. }
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & P1 & Ep1 & Q1 & Ecd & Ewk). specialize (Q1 (proj2 Hh)).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & RPL1 & _).
    assert (TB1 : 8 * ir_have r1 + ir_bits r1 <= 8 * ir_have r + ir_bits r) by (unfold PHIr in P1; lia).
    apply PP_bind.
    destruct (lenlens_while2_spec c 19 s1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    rewrite EQ2.
    assert (HLs' : forall i, 0 <= i < 0 + 19 -> 0 <= arr_get lens19 i <= 7).
    { intros i Hi. destruct (order_a_onto i ltac:(lia)) as [j [Hj <-]]. apply HLs19. exact Hj. }
    arun2 gs_eq. sacc.
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    match goal with |- context [inflate_table CODES ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table CODES a1 a2 a3 a4 a5 a6 a7) as [[[[retC tblC] nextC] lenbitsC] workC] end.
    destruct TC as [[TC5 TC6] TC].
    cbv beta iota. aflat. arun2 us_eq. aflat. arun2 ur_eq.
    acase2 CrC.
    { arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. apply LEAF; [pend_lit; reflexivity|sacc; exact Ep1|sacc; exact TB1]. }
    assert (RC0 : retC = 0) by (destruct (Z.eqb_spec retC 0); [assumption|discriminate CrC]).
    specialize (TC RC0). destruct TC as (TC1 & TC2 & TC3 & TC4). cbn [it_room] in TC2.
    aflat. arun2 us_eq. arun2 set_mode_eq.
    apply (PP_arm CODELENS (arm_CODELENS ivar_ref flush) _ _ _ _ arm_CODELENS_psi).
    - winv_split.
      + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [left; exact Hb1|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros i Hi; exfalso; lia|].
        cbn [cpok]. split; [lia|]. exists (nextC - 0). split; [lia|]. exact TC3.
      + exact HWF1.
      + exact HWB1.
    - reflexivity.
    - apply LEAF; [pend_lit; reflexivity|sacc; exact Ep1|sacc; exact TB1].
  Qed.


  Lemma arm_TABLE_psi : arm_psi TABLE (arm_TABLE ivar_ref flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_TABLE.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb14].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 14 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    2:{ eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1). }
    eapply PP_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq.
    aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq.
    aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq.
    aflat. arun2 gs_eq. sacc.
    rewrite (wrap32_id (ir_bits r1 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5 - 4)) by lia.
    rewrite !BITSv_mod by (repeat (try apply Z.shiftr_nonneg); lia).
    pose proof (mod_pow2_range (ir_hold r1) 5 ltac:(lia)) as M1.
    pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 5) 5 ltac:(lia)) as M2.
    pose proof (mod_pow2_range (Z.shiftr (Z.shiftr (ir_hold r1) 5) 5) 4 ltac:(lia)) as M3.
    match goal with |- PP _ (_ (mkW _ _ ?r4)) => set (r' := r4) in *; assert (HR' : REGS c r') end.
    { subst r'. apply REGS_holdbits; [apply REGS_holdbits; [apply REGS_holdbits; [exact HR1|]|]|].
      all: repeat (apply HB_drop); try (split; [exact RB1|exact RHO1]); lia. }
    acase2 Cbad.
    - arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. subst r'. ppw E HQ.
    - apply Bool.orb_false_iff in Cbad as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
      aflat. arun2 us_eq. arun2 set_mode_eq.
      apply (PP_arm LENLENS (arm_LENLENS ivar_ref flush) _ _ _ _ arm_LENLENS_psi).
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR'.
        * split; [common_keep HCm|]. subst r'. sacc. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          intros k Hk. exfalso. lia.
        * subst r'. sacc. rewrite Eo1. exact HWF.
        * subst r'. sacc. rewrite Ep1. exact HWB.
      + reflexivity.
      + subst r'. ppw E HQ.
  Qed.
End TableArms.
