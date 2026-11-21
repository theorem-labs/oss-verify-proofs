(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition canon_b (a : Z) : bool := (0 <=? a) && (a <? 2 ^ 32) && (lo16 a <? ABASE) && (hi16 a <? ABASE).
Lemma canon_b_ok : forall a, canon_b a = true -> adler_canon a.
Proof.
  intros a H. unfold canon_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. unfold adler_canon. lia.
Qed.
Lemma adler_canon_0 : adler_canon 0.
Proof. apply canon_b_ok. vm_compute. reflexivity. Qed.

Lemma gz_magic_crc_canon : adler_canon (icrc32_upd icrc32_init [31; 139]).
Proof. apply canon_b_ok. vm_compute. reflexivity. Qed.

Lemma hcrc_on_flags : forall s, hcrc_on s = true -> is_flags s <> 0.
Proof.
  intros s H F. unfold hcrc_on in H. rewrite F in H. cbn in H. discriminate H.
Qed.

Lemma common_hcrc : forall s s1 s', common s -> hcrc_on s1 = true -> is_flags s1 = is_flags s ->
  is_wbits s' = is_wbits s -> is_flags s' = is_flags s -> common s'.
Proof.
  intros s s1 s' [W F] Hh E1 E2 E3. unfold common. rewrite E2, E3. split; [exact W|].
  intros F0. exfalso. apply (hcrc_on_flags s1 Hh). rewrite E1. exact F0.
Qed.

Lemma CORE_wbits : forall s v, CORE s -> is_wbits s = 0 -> v <> 0 -> CORE (iset_wbits s v).
Proof.
  intros s v HC W Hv. pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  destruct (C9 W) as [N Wr]. pose proof (C1 N) as Z0.
  unfold CORE. sacc. rewrite N, Z0. repeat (split; [first [assumption | congruence | lia] |]). lia.
Qed.

Lemma scan_zero_spec : forall input next have, 0 < have < 2 ^ 32 ->
  let '(copy, _) := scan_zero input next have in 1 <= copy <= have.
Proof.
  intros input next have Hh.
  assert (GEN : forall m k l, 0 <= k < have -> have - k <= Z.of_nat m ->
    let '(copy, _) := loopZ (Z.of_nat m)
        (fun cl : Z * Z => let '(copy, _) := cl in
           let len := arr_get input (next + copy) in
           let copy := wrap32 (copy + 1) in
           (negb (len =? 0) && (copy <? have), (copy, len))) (k, l) in k + 1 <= copy <= have).
  { induction m as [|m IH]; intros k l Hk Hm; [cbn in Hm; lia|].
    rewrite loopZ_step by lia. cbv beta iota zeta.
    rewrite (wrap32_id (k + 1)) by lia.
    destruct (negb (arr_get input (next + k) =? 0) && (k + 1 <? have)) eqn:C.
    - apply andb_prop in C as [_ C]. apply Z.ltb_lt in C.
      replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      specialize (IH (k + 1) (arr_get input (next + k)) ltac:(lia) ltac:(lia)).
      destruct (loopZ _ _ _) as [cp ln]. lia.
    - lia. }
  unfold scan_zero. specialize (GEN (Z.to_nat have) 0 0 ltac:(lia) ltac:(lia)).
  rewrite Z2Nat.id in GEN by lia. cbv zeta in GEN. exact GEN.
Qed.

Section HeaderArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_HCRC_safe : arm_safe HCRC arm_HCRC.
  Proof.
    intros w0 s c r HW E HP. unfold arm_HCRC. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    acase Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        aflat. arun HOLD_eq. aflat. arun gs_eq. acase Cbad.
        * aflat. arun go_bad_eq. arun aret_eq. rewrite aret_eq. apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. exact HL0.
             ++ eapply REGS_cview; [exact HR1 | reflexivity | reflexivity].
             ++ exact (proj2 HCm).
             ++ exact I.
             ++ rewrite Ep1. exact HWB.
          -- phi_norm E HP. lia.
        * aflat. arun INITBITS_eq. arun aret_eq. aflat. arun set_adler_check_eq. rewrite set_mode_eq. apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. exact HL0.
             ++ eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
             ++ split; [|cbn; lia]. split; [exact (proj1 HCm)|]. intros _. exact adler_canon_0.
             ++ rewrite Eo1. exact HWF.
             ++ rewrite Ep1. exact HWB.
          -- phi_norm E HP. lia.
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|].
        intros F0. rewrite F0 in Cf. discriminate Cf.
    - arun aret_eq. aflat. arun set_adler_check_eq. rewrite set_mode_eq.
      assert (F0 : Z.land (is_flags s) 512 = 0) by (destruct (Z.eqb_spec (Z.land (is_flags s) 512) 0); [assumption|discriminate Cf]).
      apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * split; [|exact (Hb8 F0)]. split; [exact (proj1 HCm)|]. intros _. exact adler_canon_0.
        * exact HWF.
        * exact HWB.
      + phi_norm E HP. lia.
  Qed.

  Lemma POST_name_like : forall w0 flag s c r M (K : bool -> AM unit),
    WINV (mkW s c r) -> is_mode s = M -> (M = NAME \/ M = COMMENT) ->
    (forall w', WINV w' -> POST w0 (K false w')) ->
    (forall s' r', CORE s' -> REGS c r' -> common s' -> is_mode s' = M -> is_wbits s' = is_wbits s ->
                   is_length s' = is_length s ->
                   ir_bits r' = ir_bits r -> ir_hold r' = ir_hold r -> ir_out r' = ir_out r -> ir_put r' = ir_put r ->
                   ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
                   POST w0 (K true (mkW s' c r'))) ->
    POST w0 (abind (name_like flag) K (mkW s c r)).
  Proof.
    intros w0 flag s c r M K HW E HM KF KT.
    assert (HW' : CORE s /\ REGS c r /\ (common s /\ ir_bits r < 8) /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0)).
    { pose proof HW as HW1. destruct HM as [-> | ->]; [winv_open2 HW1 E HC HR | winv_open2 HW1 E HC HR]; repeat (split; [assumption|]); assumption. }
    destruct HW' as (HC & HR & [HCm Hb8] & HWF & HWB). regs_open HR.
    unfold name_like. aflat. arun gs_eq. acase Cf.
    - aflat. arun gr_eq. acase Ch0.
      + arun aret_eq. apply KF. exact HW.
      + apply Z.eqb_neq in Ch0. aflat. arun aget_eq. cbn [w_s w_c w_r].
        pose proof (scan_zero_spec (ic_input c) (ir_next r) (ir_have r) ltac:(lia)) as SZ.
        destruct (scan_zero (ic_input c) (ir_next r) (ir_have r)) as [copy len]. ired.

        assert (STEP : exists ck, (if hcrc_on s then crc_input copy else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)
                       /\ (hcrc_on s = false -> ck = is_check s)).
        { destruct (hcrc_on s).
          - eexists. split; [reflexivity|]. intros X; discriminate X.
          - exists (is_check s). split; [|reflexivity]. unfold aret. f_equal. destruct s; reflexivity. }
        destruct STEP as (ck & STEP & Hck).
        aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun ur_eq.
        assert (HCm' : common (iset_check s ck)).
        { destruct (hcrc_on s) eqn:Hh.
          - eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
          - rewrite (Hck eq_refl). common_keep HCm. }
        rewrite (wrap32_id (ir_have r - copy)) by lia.
        acase Clen.
        * arun aret_eq. apply KF.
          unfold WINV. cbn [w_s w_c w_r]. sacc. rewrite E. split; [core_keep HC; apply CORE_length; exact HC|].
          split; [regs_solve RIN|].
          split; [destruct HM as [-> | ->]; mred; (split; [exact HCm'|exact Hb8])|].
          split; [destruct HM as [-> | ->]; mred; exact HWF|]. exact HWB.
        * arun aret_eq. apply KT; try reflexivity.
          -- core_keep HC. apply CORE_length; exact HC.
          -- regs_solve RIN.
          -- exact HCm'.
          -- sacc. exact E.
          -- sacc. lia.
    - arun aret_eq. apply KT; try reflexivity; try assumption. lia.
  Qed.

  Lemma arm_COMMENT_safe : arm_safe COMMENT arm_COMMENT.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COMMENT.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (POST_name_like w0 4096 s c r COMMENT _ HW0 E (or_intror eq_refl)).
    - intros w' HW'. cbv beta. aleave. exact HW'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh. cbv beta iota. arun set_mode_eq.
      apply (POST_arm HCRC arm_HCRC _ _ _ _ arm_HCRC_safe).
      + winv_split.
        * core_keep HC'. apply CORE_length; exact HC'.
        * exact HR'.
        * split; [common_keep HCm'|]. intros _. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_NAME_safe : arm_safe NAME arm_NAME.
  Proof.
    intros w0 s c r HW E HP. unfold arm_NAME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (POST_name_like w0 2048 s c r NAME _ HW0 E (or_introl eq_refl)).
    - intros w' HW'. cbv beta. aleave. exact HW'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh. cbv beta iota. aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm COMMENT arm_COMMENT _ _ _ _ arm_COMMENT_safe).
      + winv_split.
        * core_keep HC'. lia.
        * exact HR'.
        * split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_EXTRA_safe : arm_safe EXTRA arm_EXTRA.
  Proof.
    intros w0 s c r HW E HP. unfold arm_EXTRA. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.

    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' = ir_bits r -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
              POST w0 ((us (fun s0 => iset_length s0 0) ;; set_mode NAME ;; arm_NAME)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Eb Eo Ep El Hh. aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm NAME arm_NAME _ _ _ _ arm_NAME_safe).
      - winv_split.
        + core_keep HC'. lia.
        + exact HR'.
        + split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - phi_norm E HP. lia. }
    acase Cf.
    - aflat. arun gr_eq. cbv zeta.
      set (cp := if ir_have r <? is_length s then ir_have r else is_length s).
      assert (Hcp : 0 <= cp <= ir_have r /\ cp <= is_length s) by (subst cp; destruct (Z.ltb_spec (ir_have r) (is_length s)); lia).

      match goal with |- POST _ (abind (abind ?m _) _ ?w) =>
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
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun gs_eq. acase Clen.
      + arun aret_eq. aleave.
        unfold WINV. cbn [w_s w_c w_r]. sacc. rewrite E. mred.
        split; [core_keep HC; lia|]. split; [regs_solve RIN|]. split; [split; [common_keep HCk|exact Hb8]|]. split; [exact HWF|exact HWB].
      + arun aret_eq. apply TAIL; first [ core_keep HC; lia | regs_solve RIN | common_keep HCk | sacc; first [reflexivity | lia] ].
    - arun aret_eq. apply TAIL; first [assumption | reflexivity | lia].
  Qed.

  Lemma hcrc_step : forall s (m : AM unit) c r,
    common s -> (exists ck, m (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)) ->
    exists ck, (if hcrc_on s then m else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r) /\ common (iset_check s ck).
  Proof.
    intros s m c r HCm [ck0 Hm]. destruct (hcrc_on s) eqn:Hh.
    - exists ck0. split; [exact Hm|]. eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
    - exists (is_check s). split; [unfold aret; f_equal; destruct s; reflexivity|]. common_keep HCm.
  Qed.

  Lemma arm_EXLEN_safe : arm_safe EXLEN arm_EXLEN.
  Proof.
    intros w0 s c r HW E HP. unfold arm_EXLEN. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' < 8 -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r ->
              64 * ir_have r' + 8 * ir_bits r' <= 64 * ir_have r + 8 * ir_bits r ->
              POST w0 ((set_mode EXTRA ;; arm_EXTRA)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Hb Eo Ep El Hm. arun set_mode_eq.
      apply (POST_arm EXTRA arm_EXTRA _ _ _ _ arm_EXTRA_safe).
      - winv_split.
        + core_keep HC'. apply CORE_length; exact HC'.
        + exact HR'.
        + split; [common_keep HCm'|exact Hb].
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - phi_norm E HP. lia. }
    acase Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        aflat. arun HOLD_eq. aflat. arun us_eq.
        destruct (hcrc_step (iset_length s (wrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 ltac:(common_keep HCm) ltac:(eexists; reflexivity))
          as (ck & STEP & HCk).
        aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq.
        apply TAIL; first [ core_keep HC; apply wrap32_range | apply REGS_init; exact HR1 | exact HCk | sacc; first [reflexivity | lia] ].
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|].
        intros F0. rewrite F0 in Cf. discriminate Cf.
    - arun aret_eq.
      assert (F0 : Z.land (is_flags s) 1024 = 0) by (destruct (Z.eqb_spec (Z.land (is_flags s) 1024) 0); [assumption|discriminate Cf]).
      apply TAIL; first [assumption | reflexivity | exact (Hb8 F0) | lia].
  Qed.

  Lemma arm_OS_safe : arm_safe OS arm_OS.
  Proof.
    intros w0 s c r HW E HP. unfold arm_OS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun gs_eq.
      destruct (hcrc_step s (CRC2 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm EXLEN arm_EXLEN _ _ _ _ arm_EXLEN_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * split; [common_keep HCk|]. intros _. cbn. lia.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.

  Lemma arm_TIME_safe : arm_safe TIME arm_TIME.
  Proof.
    intros w0 s c r HW E HP. unfold arm_TIME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun gs_eq.
      destruct (hcrc_step s (CRC4 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm OS arm_OS _ _ _ _ arm_OS_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.

  Lemma arm_FLAGS_safe : arm_safe FLAGS arm_FLAGS.
  Proof.
    intros w0 s c r HW E HP. unfold arm_FLAGS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HWb HCk0].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun us_eq. aflat. arun gs_eq.
      assert (BADc : forall msg, POST w0 (go_bad msg (mkW (iset_flags s (swrap32 (ir_hold r1))) c r1))).
      { intros msg. unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
        - winv_split.
          + core_keep HC. exact HL0.
          + eapply REGS_cview; [exact HR1|reflexivity|reflexivity].
          + intros _. exact HCk0.
          + exact I.
          + rewrite Ep1. exact HWB.
        - phi_norm E HP. lia. }
      acase C1; [apply BADc|]. acase C2; [apply BADc|].
      assert (HCm1 : common (iset_flags s (swrap32 (ir_hold r1)))).
      { split; [exact HWb|]. intros _. exact HCk0. }
      destruct (hcrc_step (iset_flags s (swrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 HCm1 ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm TIME arm_TIME _ _ _ _ arm_TIME_safe).
      + winv_split.
        * core_keep HC. exact HL0.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact (proj1 HWF).
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.

  Lemma aux_ref' : forall f s c r, aux ivar_ref f (mkW s c r) = ARun tt (mkW (f s) c r).
  Proof. reflexivity. Qed.

  Lemma wbits_step : forall s c r v, CORE s -> v <> 0 ->
    exists s1, (if is_wbits s =? 0 then us (fun s0 => iset_wbits s0 v) else aret tt) (mkW s c r) = ARun tt (mkW s1 c r)
      /\ CORE s1 /\ is_wbits s1 <> 0 /\ is_flags s1 = is_flags s /\ is_check s1 = is_check s.
  Proof.
    intros s c r v HC Hv. destruct (Z.eqb_spec (is_wbits s) 0) as [W|W].
    - exists (iset_wbits s v). split; [reflexivity|]. split; [apply CORE_wbits; assumption|]. sacc. repeat split; try reflexivity. exact Hv.
    - exists s. split; [reflexivity|]. split; [exact HC|]. split; [exact W|]. split; reflexivity.
  Qed.

  Lemma arm_HEAD_safe : arm_safe HEAD (arm_HEAD ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_HEAD. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [Hwb8 HCk0].
    pose proof (CORE_length s HC) as HL0.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
    acase Cw0.
    -
      apply Z.eqb_eq in Cw0.
      assert (HWb : is_wbits s <> 0) by (intros W; exact (proj2 (C9 W) Cw0)).
      rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR.
        * split; [split; [exact HWb | exact HCk0] | exact (Hwb8 Cw0)].
        * exact (proj1 HWF).
        * exact HWB.
      + phi_norm E HP. lia.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
        aflat. arun HOLD_eq. acase Cgz.
        *
          apply andb_prop in Cgz as [_ Cgz]. apply Z.eqb_eq in Cgz.
          aflat. destruct (wbits_step s c r1 15 HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply POST_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun us_eq. unfold CRC2. aflat. arun us_eq. aflat. arun INITBITS_eq. rewrite set_mode_eq.
          apply POST_ARun.
          -- winv_split.
             ++ core_keep HC1. apply CORE_length; exact HC1.
             ++ apply REGS_init. exact HR1.
             ++ split; [exact HWb1|]. rewrite Cgz.
                change (adler_canon (icrc32_upd icrc32_init [31; 139])). exact gz_magic_crc_canon.
             ++ split; [rewrite Eo1; exact (proj1 HWF) | rewrite Ep1; exact (proj2 HWF)].
             ++ intros W. exfalso. exact (HWb1 W).
          -- phi_norm E HP. lia.
        *
          aflat. arun BITS_eq.
          assert (BADc : forall msg s1 r', CORE s1 -> REGS c r' -> is_flags s1 = is_flags s -> is_check s1 = is_check s ->
                    ir_put r' = ir_put r -> (is_wbits s1 = 0 -> is_wbits s = 0) ->
                    64 * ir_have r' + 8 * ir_bits r' + 8 * ir_left r' <= 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r ->
                    POST w0 (go_bad msg (mkW s1 c r'))).
          { intros msg s1 r' HC1 HR' EF ECk Ep Ewb Hm. unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
            - winv_split.
              + core_keep HC1. apply CORE_length; exact HC1.
              + eapply REGS_cview; [exact HR'|reflexivity|reflexivity].
              + rewrite EF, ECk. exact HCk0.
              + exact I.
              + intros W. rewrite Ep. exact (HWB (Ewb W)).
            - phi_norm E HP. lia. }
          acase Chk; [apply BADc; [exact HC | exact HR1 | reflexivity | reflexivity | exact Ep1 | intros W; exact W | lia]|].
          aflat. arun BITS_eq.
          acase Ccm; [apply BADc; [exact HC | exact HR1 | reflexivity | reflexivity | exact Ep1 | intros W; exact W | lia]|].
          aflat. arun DROPBITS_eq. aflat. arun BITS_eq. cbv zeta. sacc.
          rewrite (wrap32_id (ir_bits r1 - 4)) by lia.
          set (r2 := irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (ir_bits r1 - 4)).
          assert (HR2 : REGS c r2).
          { subst r2. rewrite <- (wrap32_id (ir_bits r1 - 4)) by lia. apply REGS_drop; [exact HR1 | lia]. }
          set (len := BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8).
          assert (Hlen : 8 <= len).
          { subst len. rewrite BITSv_mod; [|apply Z.shiftr_nonneg; lia|lia]. pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 4) 4 ltac:(lia)). lia. }
          (* zlib 1.4: the window-size check comes first, the wbits store after it *)
          aflat. arun gs_eq.
          acase Cws; [apply BADc; [exact HC | exact HR2 | reflexivity | reflexivity | subst r2; sacc; exact Ep1 | intros W; exact W | subst r2; sacc; lia]|].
          aflat. destruct (wbits_step s c r2 len HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply POST_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun aux_ref'. aflat. arun us_eq. aflat. arun set_adler_check_eq. aflat. arun HOLD_eq. aflat. arun set_mode_eq.
          rewrite INITBITS_eq.
          apply POST_ARun.
          -- destruct (negb (Z.land (ir_hold r2) 512 =? 0)).
             ++ winv_split.
                ** core_keep HC1. apply CORE_length; exact HC1.
                ** eapply REGS_cview; [apply REGS_holdbits; [exact HR2 | exact HB_0] | reflexivity | reflexivity].
                ** split; [exact HWb1|]. intros _. exact adler_canon_1.
                ** subst r2. sacc. rewrite Eo1. exact (proj1 HWF).
                ** intros W. exfalso. exact (HWb1 W).
             ++ winv_split.
                ** core_keep HC1. apply CORE_length; exact HC1.
                ** eapply REGS_cview; [apply REGS_holdbits; [exact HR2 | exact HB_0] | reflexivity | reflexivity].
                ** split; [|cbn; lia]. split; [exact HWb1|]. intros _. exact adler_canon_1.
                ** subst r2. sacc. rewrite Eo1. exact (proj1 HWF).
                ** intros W. exfalso. exact (HWb1 W).
          -- lazymatch goal with |- _ < PHI ?w => set (PW0 := PHI w) in *; clearbody PW0 end.
             pose proof (rank_le3 (if negb (Z.land (ir_hold r2) 512 =? 0) then DICTID else TYPE)) as R3.
             unfold PHI. cbn [w_s w_c w_r]. subst r2. sacc. revert R3. sacc. intros R3.
             unfold PHI in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. mred_in HP. lia.
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [|exact HCk0].
        intros W. rewrite W in Cw0. discriminate Cw0.
  Qed.
End HeaderArms.
