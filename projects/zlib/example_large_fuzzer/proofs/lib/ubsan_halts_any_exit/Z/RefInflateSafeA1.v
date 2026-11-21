(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
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


Lemma arm_BAD_safe : arm_safe BAD arm_BAD.
Proof.
  intros w0 s c r HW E HP. unfold arm_BAD. arun ur_eq. rewrite aleave_eq. cbn [POST].
  unfold WINV in *; cbn [w_s w_c w_r] in *. revert HW. sacc. intros HW. exact HW.
Qed.

Lemma arm_DONE_safe : arm_safe DONE arm_DONE.
Proof.
  intros w0 s c r HW E HP. unfold arm_DONE. arun ur_eq. rewrite aleave_eq. cbn [POST].
  unfold WINV in *; cbn [w_s w_c w_r] in *. revert HW. sacc. intros HW. exact HW.
Qed.

Lemma arm_MEM_safe : arm_safe MEM arm_MEM.
Proof.
  intros w0 s c r HW E HP. unfold arm_MEM. rewrite areturn_eq. cbn [POST]. split; [exact HW|].
  winv_open2 HW E HC HR. cbn [w_s]. destruct HMF as [Eh Eb].
  unfold INV. rewrite E. mred. rewrite Eh, Eb. split; [exact HC|]. split; [|split; reflexivity].
  destruct HR as (_ & _ & _ & _ & _ & _ & HBr & _). exact HBr.
Qed.



Lemma arm_LIT_safe : arm_safe LIT arm_LIT.
Proof.
  intros w0 s c r HW E HP. unfold arm_LIT.
  arun gr_eq.
  destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0].
  { rewrite aleave_eq. exact HW. }
  arun gs_eq. arun uc_eq. arun ur_eq. rewrite set_mode_eq.
  winv_open2 HW E HC HR. regs_open HR. destruct HMF as (HCm & Hb8 & Htb).
  apply POST_ARun.
  - winv_split.
    + core_keep HC. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HC))))))))))))).
    + apply REGS_out; [exact HR | apply arr_len_set | lia | rewrite wrap32_id by lia; lia | rewrite wrap32_id by lia; lia].
    + split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
    + rewrite arr_len_set. exact HWF.
    + intros W. exfalso. exact (proj1 HCm W).
  - phi_norm E HP. rewrite (wrap32_id (ir_left r - 1)) by lia. lia.
Qed.


Lemma CORE_length : forall s, CORE s -> 0 <= is_length s < 2 ^ 32.
Proof. intros s HC. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HC))))))))))))). Qed.

Lemma WINV_regs : forall s c r r',
  WINV (mkW s c r) -> REGS c r' -> ir_out r' = ir_out r -> ir_put r' = ir_put r ->
  (MF (is_mode s) s (ir_hold r) (ir_bits r) -> MF (is_mode s) s (ir_hold r') (ir_bits r')) ->
  WINV (mkW s c r').
Proof.
  intros s c r r' HW HR' Eo Ep HM. unfold WINV in *. cbn [w_s w_c w_r] in *.
  destruct HW as (HC & HR & HMF & HWF & HWB). split; [exact HC|]. split; [exact HR'|]. split; [exact (HM HMF)|].
  split.
  - unfold WF in *. rewrite Eo, Ep. exact HWF.
  - rewrite Ep. exact HWB.
Qed.

Lemma arm_LENGTH_safe : arm_safe LENGTH arm_LENGTH.
Proof.
  intros w0 s c r HW E HP. unfold arm_LENGTH. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct (negb (is_wrap s =? 0) && negb (is_flags s =? 0)) eqn:Cwf.
  - aflat.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta. aflat. arun HOLD_eq. aflat. arun gs_eq.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      acase Cbad.
      * aflat. arun go_bad_eq. arun aret_eq. ired. rewrite aret_eq. apply POST_ARun.
        -- winv_split.
           ++ core_keep HC. apply CORE_length; exact HC.
           ++ apply (REGS_cview c); [exact HR1 | reflexivity | reflexivity].
           ++ exact (proj2 HMF).
           ++ exact I.
           ++ rewrite Ep1. exact HWB.
        -- phi_norm E HP. lia.
      * aflat. arun INITBITS_eq. arun aret_eq. ired. aflat. arun set_mode_eq.
        apply (POST_arm DONE arm_DONE _ _ _ _ arm_DONE_safe).
        -- winv_split.
           ++ core_keep HC. apply CORE_length; exact HC.
           ++ apply REGS_init. exact HR1.
           ++ exact HMF.
           ++ exact I.
           ++ rewrite Ep1. exact HWB.
        -- reflexivity.
        -- phi_norm E HP. lia.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  - arun aret_eq. ired. aflat. arun set_mode_eq.
    apply (POST_arm DONE arm_DONE _ _ _ _ arm_DONE_safe).
    + winv_split.
      * core_keep HC. apply CORE_length; exact HC.
      * exact HR.
      * exact HMF.
      * exact I.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.

Ltac check_tail HC HCK HR1 Ep1 HWB E HP :=
  aflat; arun ur_eq; aflat; arun HOLD_eq; aflat; arun gs_eq; cbv zeta;
  let Cbad := fresh "Cbad" in
  acase Cbad;
  [ aflat; arun go_bad_eq; arun aret_eq; ired; rewrite aret_eq; apply POST_ARun;
    [ winv_split;
      [ core_keep HC; apply CORE_length; exact HC
      | eapply REGS_cview; [| reflexivity | reflexivity]; apply REGS_out_reg; apply REGS_out_reg; exact HR1
      | exact (proj2 HCK)
      | exact I
      | rewrite Ep1; exact HWB ]
    | phi_norm E HP; lia ]
  | aflat; arun INITBITS_eq; arun aret_eq; ired; arun set_mode_eq;
    apply (POST_arm LENGTH arm_LENGTH _ _ _ _ arm_LENGTH_safe);
    [ winv_split;
      [ core_keep HC; apply CORE_length; exact HC
      | eapply REGS_cview; [| reflexivity | reflexivity]; apply REGS_init; apply REGS_out_reg; apply REGS_out_reg; exact HR1
      | exact HCK
      | exact I
      | rewrite Ep1; exact HWB ]
    | reflexivity
    | phi_norm E HP; lia ] ].

Lemma arm_CHECK_safe : arm_safe CHECK arm_CHECK.
Proof.
  intros w0 s c r HW E HP. unfold arm_CHECK. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  acase Cw.
  - aflat.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun gr_eq. cbv zeta. aflat. arun ur_eq. aflat. arun uc_eq. aflat. arun us_eq. aflat. arun gs_eq.
      acase Cupd.
      * aflat. arun0. cbn [w_s w_c w_r]. arun set_adler_check_eq.
        match goal with |- POST _ (_ (mkW ?s1 _ _)) => assert (HCK : common s1) end.
        { eapply (common_update_check s); [exact HMF | reflexivity | reflexivity | | sacc; reflexivity]. reflexivity. }
        check_tail HC HCK HR1 Ep1 HWB E HP.
      * arun aret_eq.
        match goal with |- POST _ (_ (mkW ?s1 _ _)) => assert (HCK : common s1) end.
        { common_keep HMF. }
        check_tail HC HCK HR1 Ep1 HWB E HP.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  - arun aret_eq. ired. arun set_mode_eq.
    apply (POST_arm LENGTH arm_LENGTH _ _ _ _ arm_LENGTH_safe).
    + winv_split.
      * core_keep HC. apply CORE_length; exact HC.
      * exact HR.
      * exact HMF.
      * exact I.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.


Lemma fixedtables_tables : forall s, tables (fixedtables s).
Proof. intros s. unfold tables, fixedtables. sacc. cbn [cpok]. repeat split; reflexivity. Qed.

Section TypeArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_TYPEDO_core : forall M, (M = TYPE \/ M = TYPEDO) -> arm_safe M (arm_TYPEDO iv flush).
  Proof.
    intros M HM w0 s c r HW E HP.
    assert (HR2 : rank M = 2) by (destruct HM as [-> | ->]; reflexivity).
    assert (HW' : CORE s /\ REGS c r /\ (common s /\ ir_bits r < 8) /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0)).
    { destruct HM as [-> | ->]; [winv_open2 HW E HC HR | winv_open2 HW E HC HR]; repeat (split; [assumption|]); assumption. }
    clear HW. destruct HW' as (HC & HR & [HCm Hb8] & HWF & HWB). regs_open HR.
    assert (HP' : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + 2 <= PHI w0).
    { unfold PHI in HP. cbn [w_s w_c w_r] in HP. rewrite E, HR2 in HP. exact HP. }
    clear HP.
    unfold arm_TYPEDO. arun gs_eq. acase Clast.
    -
      arun BYTEBITS_eq. rewrite set_mode_eq.
      pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
      assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
      apply POST_ARun.
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_drop; [exact HR|]. rewrite L7. exact Hm8.
        * common_keep HCm.
        * exact HWF.
        * exact HWB.
      + phi_goal. rewrite L7. rewrite wrap32_id by lia. lia.
    -
      aflat.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
        aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq. aflat. arun BITS_eq. sacc.
        rewrite (wrap32_id (ir_bits r1 - 1)) by lia.
        assert (HRd : REGS c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 1)) (ir_bits r1 - 1))).
        { rewrite <- (wrap32_id (ir_bits r1 - 1)) by lia. apply REGS_drop; [exact HR1|lia]. }
        assert (HRdd : REGS c (irset_bits (irset_hold (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 1)) (ir_bits r1 - 1))
                                 (Z.shiftr (Z.shiftr (ir_hold r1) 1) 2)) (wrap32 (ir_bits r1 - 1 - 2)))).
        { apply (REGS_drop c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 1)) (ir_bits r1 - 1)) 2); [exact HRd|]. sacc. lia. }
        revert HRdd. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia. intros HRdd.
        assert (Hb8' : ir_bits r1 - 1 - 2 < 8) by lia.
        acase Ct0; [|acase Ct1; [|acase Ct2]].
        *
          aflat. arun set_mode_eq. arun aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. apply CORE_length; exact HC.
             ++ exact HRdd.
             ++ common_keep HCm.
             ++ rewrite Eo1. exact HWF.
             ++ rewrite Ep1. exact HWB.
          -- phi_goal. lia.
        *
          aflat. arun us_eq. aflat. arun set_mode_eq.
          unfold fixedtables.
          acase Cz.
          -- aflat. arun DROPBITS_eq. aleave. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
             winv_split.
             ++ core_keep HC. unfold fixedtables. sacc. apply CORE_length; exact HC.
             ++ exact HRdd.
             ++ split; [common_keep HCm|]. split; [exact Hb8'|]. unfold fixedtables. tables_keep (fixedtables_tables s).
             ++ rewrite Eo1. exact HWF.
             ++ rewrite Ep1. exact HWB.
          -- arun aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
             apply POST_ARun.
             ++ winv_split.
                ** core_keep HC. unfold fixedtables. sacc. apply CORE_length; exact HC.
                ** exact HRdd.
                ** split; [common_keep HCm|]. split; [exact Hb8'|]. unfold fixedtables. tables_keep (fixedtables_tables s).
                ** rewrite Eo1. exact HWF.
                ** rewrite Ep1. exact HWB.
             ++ phi_goal. lia.
        *
          aflat. arun set_mode_eq. arun aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. apply CORE_length; exact HC.
             ++ exact HRdd.
             ++ split; [common_keep HCm|]. lia.
             ++ rewrite Eo1. exact HWF.
             ++ rewrite Ep1. exact HWB.
          -- phi_goal. lia.
        *
          aflat. arun go_bad_eq. arun aret_eq. ired. rewrite DROPBITS_eq. sacc. rewrite (wrap32_id (ir_bits r1 - 1 - 2)) by lia.
          apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. apply CORE_length; exact HC.
             ++ eapply REGS_cview; [exact HRdd|reflexivity|reflexivity].
             ++ exact (proj2 HCm).
             ++ exact I.
             ++ rewrite Ep1. exact HWB.
          -- phi_goal. lia.
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        unfold WINV. cbn [w_s w_c w_r]. rewrite E. split; [exact HC|]. split; [exact HR1|]. split; [|split].
        * destruct HM as [-> | ->]; mred; (split; [exact HCm|lia]).
        * destruct HM as [-> | ->]; mred; rewrite Eo1; exact HWF.
        * rewrite Ep1. exact HWB.
  Qed.

  Lemma arm_TYPEDO_safe : arm_safe TYPEDO (arm_TYPEDO iv flush).
  Proof. apply arm_TYPEDO_core. right; reflexivity. Qed.

  Lemma arm_TYPE_safe : arm_safe TYPE (arm_TYPE iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_TYPE.
    destruct (iv_flush_exits iv && ((flush =? Z_BLOCK) || (flush =? Z_TREES))).
    - rewrite aleave_eq. exact HW.
    - exact (arm_TYPEDO_core TYPE (or_introl eq_refl) w0 s c r HW E HP).
  Qed.
End TypeArms.
