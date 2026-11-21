(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.

Module RefInflateSafeA1.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
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

Lemma arm_SYNC_safe : arm_safe SYNC arm_SYNC.
Proof. intros w0 s c r HW E HP. exfalso. winv_open2 HW E HC HR. exact HMF. Qed.


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
End RefInflateSafeA1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.

Module RefInflateSafeA3.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
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


Lemma match_copy_step : forall win ob put from copy, 0 < copy < 2 ^ 32 ->
  match_copy win (ob, put, from, copy) =
    let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
    let st' := ((arr_set ob put v : arr), put + 1, from_succ from, copy - 1) in
    if copy - 1 =? 0 then st' else match_copy win st'.
Proof.
  intros win ob put from copy Hc. unfold match_copy at 1. cbn [snd]. rewrite loopZ_step by lia. cbv beta iota zeta.
  rewrite (wrap32_id (copy - 1)) by lia.
  destruct (Z.eqb_spec (copy - 1) 0) as [E|E]; cbn [negb]; [reflexivity|].
  unfold match_copy. cbn [snd]. reflexivity.
Qed.

Lemma match_copy_spec : forall m win ob put from, Z.of_nat (S m) < 2 ^ 32 ->
  exists ob' from', match_copy win (ob, put, from, Z.of_nat (S m)) = (ob', put + Z.of_nat (S m), from', 0)
                    /\ arr_len ob' = arr_len ob.
Proof.
  induction m as [|m IH]; intros win ob put from Hm.
  - rewrite match_copy_step by (cbn; lia). cbv zeta. change (Z.of_nat 1 - 1 =? 0) with true. cbv iota.
    eexists _, _. split; [reflexivity|]. apply arr_len_set.
  - rewrite match_copy_step by lia. cbv zeta.
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia.
    lazymatch goal with |- exists _ _, match_copy _ (?ob1, ?p1, ?f1, _) = _ /\ _ =>
      destruct (IH win ob1 p1 f1 ltac:(lia)) as (ob' & from' & E & L) end.
    rewrite E. eexists _, _. split; [f_equal; f_equal; f_equal; lia|]. rewrite L. apply arr_len_set.
Qed.

Lemma match_copy_ok : forall win ob put from copy, 1 <= copy < 2 ^ 32 ->
  exists ob' from', match_copy win (ob, put, from, copy) = (ob', put + copy, from', 0) /\ arr_len ob' = arr_len ob.
Proof.
  intros win ob put from copy Hc.
  destruct (match_copy_spec (Z.to_nat (copy - 1)) win ob put from ltac:(lia)) as (ob' & from' & E & L).
  replace (Z.of_nat (S (Z.to_nat (copy - 1)))) with copy in E by lia.
  eexists _, _. split; [exact E|exact L].
Qed.


Section MatchArm.
  Variable iv : ivariant.

  Lemma match_tail : forall w0 s c r from copy,
    CORE s -> REGS c r -> is_mode s = MATCH ->
    common s -> ir_bits r < 8 -> tables s -> 1 <= is_length s -> 1 <= is_offset s < 2 ^ 32 ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    0 < ir_left r -> 1 <= copy <= is_length s ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + 1 <= PHI w0 ->
    POST w0 ((let copy := if ir_left r <? copy then ir_left r else copy in
              ur (fun r0 => irset_left r0 (wrap32 (ir_left r0 - copy))) ;;
              us (fun s0 => iset_length s0 (wrap32 (is_length s0 - copy))) ;;
              (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
                        ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))) ;;
              do s0 <- gs (fun s0 => s0) ;
              if is_length s0 =? 0 then set_mode LEN else aret tt)%am (mkW s c r)).
  Proof.
    intros w0 s c r from copy HC HR E HCm Hb8 Htb HL HO HWF HWB Hleft Hcp HP.
    regs_open HR. cbv zeta.
    set (cp := if ir_left r <? copy then ir_left r else copy).
    assert (Hc : 1 <= cp <= copy /\ cp <= ir_left r) by (subst cp; destruct (Z.ltb_spec (ir_left r) copy); lia).
    aflat. arun ur_eq. aflat. arun us_eq. cbn [w_s w_c w_r]. sacc.
    destruct (match_copy_ok (is_window s) (ic_outbuf c) (ir_put r) from cp ltac:(lia)) as (ob' & from' & EM & LM).
    aflat. eapply POST_bind_run; [cbv beta; cbn [w_s w_c w_r]; sacc; rewrite EM; reflexivity|]. cbv beta. arun gs_eq. sacc.
    rewrite (wrap32_id (ir_left r - cp)) by lia.
    pose proof (wrap32_range (is_length s - cp)) as WR.
    destruct (Z.eqb_spec (wrap32 (is_length s - cp)) 0) as [L0|L0].
    - rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. lia.
        * unfold REGS. sacc. rewrite LM. regs_solve RIN.
        * split; [common_keep HCm|]. split; [left; exact Hb8 | tables_keep Htb].
        * rewrite LM. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_goal. lia.
    - rewrite aret_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. lia.
        * unfold REGS. sacc. rewrite LM. regs_solve RIN.
        * rewrite E. mred. split; [common_keep HCm|]. split; [exact Hb8|]. split; [tables_keep Htb|]. lia.
        * rewrite E. mred. rewrite LM. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_goal. rewrite E. mred. lia.
  Qed.

  Lemma arm_MATCH_safe : arm_safe MATCH (arm_MATCH iv).
  Proof.
    intros w0 s c r HW E HP. unfold arm_MATCH.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Htb & HL & HO).
    pose proof HC as (_ & _ & _ & CW4 & CW5 & CW6 & CW7 & CW8 & _ & _ & _ & _ & CS & _).
    assert (HP' : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + 1 <= PHI w0).
    { unfold PHI in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. exact HP. }
    arun gr_eq.
    destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0]; [aleave; exact HW0|].
    arun gs_eq. cbv zeta.
    rewrite (wrap32_id (ir_out r - ir_left r)) by lia.
    replace (ir_out r - ir_left r) with (ir_put r) by lia.
    acase Cwin.
    -
      apply Z.ltb_lt in Cwin. cbv zeta.
      rewrite (wrap32_id (is_offset s - ir_put r)) by lia.
      rewrite CS. replace (if iv_aux iv then negb (1 =? 0) else true) with true by (destruct (iv_aux iv); reflexivity).
      rewrite Bool.andb_true_r.
      acase Cfar.
      + aflat. arun go_bad_eq. arun aret_eq. rewrite aret_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply CORE_length; exact HC.
          -- eapply REGS_cview; [exact HR | reflexivity | reflexivity].
          -- exact (proj2 HCm).
          -- exact I.
          -- exact HWB.
        * phi_goal. lia.
      + apply Z.ltb_ge in Cfar.
        destruct (Z.ltb_spec (is_wnext s) (is_offset s - ir_put r)) as [Cwrap|Cwrap].
        * rewrite (wrap32_id (is_offset s - ir_put r - is_wnext s)) by lia.
          arun aret_eq.
          apply match_tail; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r - is_wnext s)); lia.
        * arun aret_eq.
          apply match_tail; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r)); lia.
    -
      arun aret_eq. apply match_tail; try assumption; lia.
  Qed.
End MatchArm.


Lemma add_back_ref : forall v s c r, add_back ivar_ref v (mkW s c r) = ARun tt (mkW (iset_back s (swrap32 (is_back s + v))) c r).
Proof. reflexivity. Qed.
Lemma set_back_ref : forall v s c r, set_back ivar_ref v (mkW s c r) = ARun tt (mkW (iset_back s v) c r).
Proof. reflexivity. Qed.
Lemma aux_ref : forall f s c r, aux ivar_ref f (mkW s c r) = ARun tt (mkW (f s) c r).
Proof. reflexivity. Qed.



Lemma arm_DISTEXT_safe : arm_safe DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_DISTEXT. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL & HX & HO). pose proof (CORE_length s HC) as HL0.
  acase Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15.
      rewrite (wrap32_id (is_offset s + _)) by (change (2 ^ 15) with 32768 in P15; lia).
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (POST_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_safe ivar_ref)).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. change (2 ^ 15) with 32768 in P15. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * phi_norm E HP. lia.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. repeat (split; [first [assumption | lia]|]). lia.
  - apply Z.eqb_eq in Cx || (destruct (Z.eqb_spec (is_extra s) 0) as [Cx'|Cx']; [clear Cx; rename Cx' into Cx|discriminate Cx]).
    arun aret_eq. arun set_mode_eq.
    apply (POST_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_safe ivar_ref)).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.


Lemma dist_tail : forall w0 s c r here,
  CORE s -> REGS c r -> is_mode s = DIST -> common s -> tables s -> 1 <= is_length s ->
  ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
  1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
  ((exists sy, 0 <= sy < nsyms DISTS /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
  64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
  POST w0 ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
            if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s0 => iset_extra (iset_offset s0 (code_val here)) (Z.land (code_op here) 15)) ;;
                 set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am (mkW s c r)).
Proof.
  intros w0 s c r here HC HR E HCm Htb HL HWF HWB Hcb Hb8 Hsh HP.
  regs_open HR. pose proof (CORE_length s HC) as HL0.
  aflat. arun DROPBITS_eq. aflat. arun add_back_ref. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
  assert (HRd : REGS c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))).
  { apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
  assert (BADc : POST w0 ((go_bad MSG_invalid_distance_code) (mkW (iset_back s (swrap32 (is_back s + code_bits here))) c
                             (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))))).
  { unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
    - winv_split.
      + core_keep HC. exact HL0.
      + eapply REGS_cview; [exact HRd|reflexivity|reflexivity].
      + exact (proj2 HCm).
      + exact I.
      + exact HWB.
    - phi_goal. lia. }
  destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
  - cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop, Hv.
    destruct L as [(L1 & L2 & L3)|[L1 L2]].
    + destruct (dist_op_facts op L1) as (F1 & F2 & F3 & F4). rewrite F2, F3. cbn [Z.eqb negb].
      aflat. arun us_eq. arun set_mode_eq.
      pose proof (pow2_le (op - 16) 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13.
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      apply (POST_arm DISTEXT (arm_DISTEXT ivar_ref) _ _ _ _ arm_DISTEXT_safe).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- exact HRd.
        -- split; [common_keep HCm|]. split; [left; exact Hb8|]. split; [tables_keep Htb|]. lia.
        -- exact HWF.
        -- exact HWB.
      * reflexivity.
      * phi_goal. lia.
    + rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  - rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc.
Qed.

Lemma arm_DIST_safe : arm_safe DIST (arm_DIST ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_DIST. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL).
  assert (HP0 : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0).
  { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank DIST) with 0 in HP. lia. }
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
  pose proof (T_root _ _ _ _ HT) as HR15.
  aflat.
  destruct (DECODE1_spec c s (is_distcode s) DISTS (is_distbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
  - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    destruct (root_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
    { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    aflat. acase Clink.
    +
      apply Z.eqb_eq in Clink.
      assert (HLk : is_linkb here = true).
      { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
        apply (notlink_land240 DISTS here SH ltac:(discriminate)); [|exact Clink].
        destruct SH as [[sy (Hsy & Hop & _)]|Hop]; [|rewrite Hop; discriminate].
        cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L. destruct (sym_entry DISTS sy) as [op v]. cbn [fst] in Hop. rewrite Hop. lia. }
      destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
      aflat.
      destruct (DECODE2_spec c s (is_distcode s) DISTS (is_distbits s) used HT r1 here HR1 Eh HLk Hle)
        as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
      * eapply POST_bind_run; [exact EQ2|]. cbv beta iota.
        pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
        pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
        pose proof (sub_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s)
                      (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
        rewrite <- Eh in SC.
        specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
        unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
        aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun aret_eq. sacc.
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
        { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
        assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
        { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
          destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
        apply dist_tail;
          first [ assumption
                | core_keep HC; apply CORE_length; exact HC
                | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                | common_keep HCm
                | tables_keep Htb
                | rewrite Eo2, Eo1; exact HWF
                | rewrite Ep2, Ep1; exact HWB
                | sacc; lia ].
      * eapply POST_bind_leave; [exact EQ2|].
        pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _).
        apply (WINV_regs s c r r2 HW0 HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
        rewrite E. mred. intros _. split; [exact HCm|]. split; [|split; [exact Htb|exact HL]].
        right. rewrite lneed_lneedg. exact Hb2.
    +
      assert (HLk : is_linkb here = false).
      { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
        rewrite (land240_small (code_op here)) in Clink by lia. discriminate Clink. }
      destruct (RNk HLk) as [Hbr SH].
      arun aret_eq.
      assert (B8 : ir_bits r1 - code_bits here < 8).
      { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
        rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
        rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
      apply dist_tail;
        first [ assumption
              | rewrite Eo1; exact HWF
              | rewrite Ep1; exact HWB
              | lia ].
  - eapply POST_bind_leave; [exact EQ|].
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
    apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1).
    rewrite E. mred. intros _. split; [exact HCm|]. split; [|split; [exact Htb|exact HL]].
    right. rewrite lneed_lneedg. pose proof (lneedg_range DISTS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
Qed.


Lemma arm_LENEXT_safe : arm_safe LENEXT (arm_LENEXT ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_LENEXT. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HX & HL). pose proof (CORE_length s HC) as HL0.
  acase Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq. aflat. arun add_back_ref.
      aflat. arun aux_ref. arun set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15. change (2 ^ 15) with 32768 in P15.
      rewrite (wrap32_id (is_length s + _)) by lia.
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (POST_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_safe).
      * winv_split.
        -- core_keep HC. lia.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * phi_norm E HP. lia.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. repeat (split; [first [assumption | lia]|]). lia.
  - arun aret_eq. aflat. arun aux_ref. arun set_mode_eq.
    apply (POST_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_safe).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.
End RefInflateSafeA3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA3.

Module RefInflateSafeF1.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac facc :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
       fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
       x_input x_last x_beg x_end x_wsize x_whave x_wnext x_window x_lmask x_dmask x_sane].
Ltac facc_in H :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
       fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
       x_input x_last x_beg x_end x_wsize x_whave x_wnext x_window x_lmask x_dmask x_sane] in H.

Definition FB (ON : Z) (f : ffs) : Prop :=
  0 <= f_in f /\ 0 <= f_out f /\ 0 <= f_bits f <= 32 /\ 0 <= f_hold f < 2 ^ f_bits f /\ arr_len (f_ob f) = ON.

Definition COPIED (n : Z) (f f' : ffs) : Prop :=
  f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_dist f' = f_dist f
  /\ f_out f' = f_out f + n /\ arr_len (f_ob f') = arr_len (f_ob f).

Lemma COPIED_refl : forall f, COPIED 0 f f.
Proof. intros f. unfold COPIED. repeat split; lia. Qed.
Lemma COPIED_trans : forall a b f f1 f2, COPIED a f f1 -> COPIED b f1 f2 -> COPIED (a + b) f f2.
Proof.
  intros a b f f1 f2 (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). unfold COPIED.
  rewrite B1, B2, B3, B4, B5, B6, A1, A2, A3, A4, A5, A6. repeat split; lia.
Qed.
Lemma cpn_COPIED : forall x n f, COPIED (Z.of_nat n) f (cpn x n f).
Proof.
  intros x n f. destruct (cpn_keep x n f) as (A & B & C & _ & E & _).
  unfold COPIED. rewrite A, B, C, E, cpn_out, cpn_len_ob. repeat split; reflexivity.
Qed.
Lemma COPIED_set_len : forall n f f' v, COPIED n f f' -> COPIED n f (fset_len f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_set_op : forall n f f' v, COPIED n f f' -> COPIED n f (fset_op f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_set_from : forall n f f' v, COPIED n f f' -> COPIED n f (fset_from f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_from_l : forall n f f' v, COPIED n (fset_from f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.
Lemma COPIED_op_l : forall n f f' v, COPIED n (fset_op f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.
Lemma COPIED_len_l : forall n f f' v, COPIED n (fset_len f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.


Definition win_place (x : ffx) (f : ffs) : ffs :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        let f := copy_op x f in
        fset_from f (FOut (f_out f - f_dist f))
      else f
    else f
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f.
Definition dist_tailcopy (x : ffx) (f : ffs) : ffs := copy_tail x (copy_while3 x f).
Definition out_copy (x : ffx) (f : ffs) : ffs :=
  copy_tail x (copy_do3 x (fset_from f (FOut (f_out f - f_dist f)))).

Lemma dodist_S : forall k x s here f,
  dodist (S k) x s here f =
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let f := fset_dist f (code_val here) in
      let op := Z.land op 15 in
      let f := if f_bits f <? op then
                 let f := fpull x f in
                 if f_bits f <? op then fpull x f else f
               else f in
      let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
      let f := fdrop f op in
      let op := wrap32 (f_out f - x_beg x) in
      if op <? f_dist f then
        let op := wrap32 (f_dist f - op) in
        if (x_whave x <? op) && negb (x_sane x =? 0) then
          FBreak (fset_op f op) BAD (Some MSG_invalid_distance_too_far_back)
        else FCont (dist_tailcopy x (win_place x (fset_op f op)))
      else FCont (out_copy x f)
    else if Z.land op 64 =? 0 then
      dodist k x s (code_at s (is_distcode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else FBreak f BAD (Some MSG_invalid_distance_code).
Proof.
  intros. unfold win_place, dist_tailcopy, out_copy. cbv zeta. cbn [dodist].
  lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end.
Qed.

Lemma copy_op_COPIED : forall x f, 1 <= f_op f < 2 ^ 32 -> COPIED (f_op f) f (copy_op x f).
Proof.
  intros x f H. rewrite copy_op_cpn by exact H. apply COPIED_set_op.
  rewrite <- (Z2Nat.id (f_op f)) at 1 by lia. apply cpn_COPIED.
Qed.

Lemma win_place_spec : forall x f,
  1 <= f_op f < 2 ^ 32 -> 0 <= f_len f < 2 ^ 32 -> 0 <= x_wnext x ->
  exists n, COPIED n f (win_place x f) /\ 0 <= n /\ 0 <= f_len (win_place x f)
            /\ n + f_len (win_place x f) = f_len f.
Proof.
  intros x f Hop Hlen Hwn. unfold win_place.
  destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0].
  - facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
    + set (f1 := fset_len (fset_from f (FWin (x_wsize x - f_op f))) (wrap32 (f_len f - f_op f))).
      assert (H1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f) by (subst f1; facc; rewrite wrap32_id by lia; split; reflexivity).
      destruct H1 as [Eo El].
      pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; exact Hop)) as CP. rewrite Eo in CP.
      destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & _).
      exists (f_op f). split; [|split; [lia|]].
      * apply COPIED_set_from. apply (COPIED_from_l _ f _ (FWin (x_wsize x - f_op f))). apply (COPIED_len_l _ _ _ (wrap32 (f_len f - f_op f))). exact CP.
      * facc. rewrite copy_op_cpn by (rewrite Eo; exact Hop). facc. rewrite KL, El. lia.
    + exists 0. split; [apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
  - destruct (Z.ltb_spec (x_wnext x) (f_op f)) as [Cw|Cw].
    + facc. rewrite (wrap32_id (f_op f - x_wnext x)) by lia.
      destruct (Z.ltb_spec (f_op f - x_wnext x) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_op (fset_from f (FWin (x_wsize x + x_wnext x - f_op f))) (f_op f - x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x)))).
        assert (H1 : f_op f1 = f_op f - x_wnext x /\ f_len f1 = f_len f - (f_op f - x_wnext x) /\ f_dist f1 = f_dist f)
          by (subst f1; facc; rewrite wrap32_id by lia; repeat split; reflexivity).
        destruct H1 as (Eo & El & Ed).
        pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; lia)) as CP1. rewrite Eo in CP1.
        set (f2 := copy_op x f1) in *.
        assert (K2 : f_len f2 = f_len f1 /\ f_dist f2 = f_dist f1).
        { subst f2. rewrite copy_op_cpn by (rewrite Eo; lia). facc. destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & KD & _). rewrite KL, KD. split; reflexivity. }
        destruct K2 as [El2 Ed2].
        assert (CPa : COPIED (f_op f - x_wnext x) f f2).
        { apply (COPIED_from_l _ f _ (FWin (x_wsize x + x_wnext x - f_op f))). apply (COPIED_op_l _ _ _ (f_op f - x_wnext x)).
          apply (COPIED_len_l _ _ _ (wrap32 (f_len f - (f_op f - x_wnext x)))). exact CP1. }
        facc. rewrite El2, El.
        destruct (Z.ltb_spec (x_wnext x) (f_len f - (f_op f - x_wnext x))) as [C2|C2].
        -- set (f3 := fset_len (fset_op (fset_from f2 (FWin 0)) (x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x) - x_wnext x))).
           assert (H3 : f_op f3 = x_wnext x /\ f_len f3 = f_len f - (f_op f - x_wnext x) - x_wnext x)
             by (subst f3; facc; rewrite wrap32_id by lia; split; reflexivity).
           destruct H3 as [Eo3 El3].
           pose proof (copy_op_COPIED x f3 ltac:(rewrite Eo3; lia)) as CP3. rewrite Eo3 in CP3.
           destruct (cpn_keep x (Z.to_nat (f_op f3)) f3) as (_ & _ & _ & KL3 & _).
           exists (f_op f - x_wnext x + x_wnext x). split; [|split; [lia|]].
           ++ apply COPIED_set_from. eapply COPIED_trans; [exact CPa|].
              apply (COPIED_from_l _ f2 _ (FWin 0)). apply (COPIED_op_l _ _ _ (x_wnext x)). eapply COPIED_len_l. exact CP3.
           ++ facc. rewrite copy_op_cpn by (rewrite Eo3; lia). facc. rewrite KL3, El3. lia.
        -- exists (f_op f - x_wnext x). split; [apply COPIED_set_from; exact CPa|]. facc. rewrite El2, El. lia.
      * exists 0. split; [apply COPIED_set_op; apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
    + facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_from f (FWin (x_wnext x - f_op f))) (wrap32 (f_len f - f_op f))).
        assert (H1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f) by (subst f1; facc; rewrite wrap32_id by lia; split; reflexivity).
        destruct H1 as [Eo El].
        pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; exact Hop)) as CP. rewrite Eo in CP.
        destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & _).
        exists (f_op f). split; [|split; [lia|]].
        -- apply COPIED_set_from. apply (COPIED_from_l _ f _ (FWin (x_wnext x - f_op f))). eapply COPIED_len_l. exact CP.
        -- facc. rewrite copy_op_cpn by (rewrite Eo; exact Hop). facc. rewrite KL, El. lia.
      * exists 0. split; [apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
Qed.

Lemma dist_tailcopy_spec : forall x f, 0 <= f_len f < 2 ^ 32 -> COPIED (f_len f) f (dist_tailcopy x f).
Proof.
  intros x f H. unfold dist_tailcopy.
  rewrite copy_while3_cpn by exact H.
  set (f1 := fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)).
  assert (El : f_len f1 = f_len f mod 3) by (subst f1; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  rewrite copy_tail_cpn by (rewrite El; lia).
  replace (f_len f) with (Z.of_nat (Z.to_nat (3 * (f_len f / 3))) + Z.of_nat (Z.to_nat (f_len f1))) by (rewrite El; lia).
  eapply COPIED_trans; [|apply cpn_COPIED]. subst f1. apply COPIED_set_len. apply cpn_COPIED.
Qed.

Lemma out_copy_spec : forall x f, 3 <= f_len f < 2 ^ 32 -> COPIED (f_len f) f (out_copy x f).
Proof.
  intros x f H. unfold out_copy.
  set (f0 := fset_from f (FOut (f_out f - f_dist f))).
  assert (El0 : f_len f0 = f_len f) by (subst f0; reflexivity).
  rewrite copy_do3_cpn by (rewrite El0; exact H). rewrite El0.
  set (f1 := fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f0) (f_len f mod 3)).
  assert (El : f_len f1 = f_len f mod 3) by (subst f1; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  rewrite copy_tail_cpn by (rewrite El; lia).
  replace (f_len f) with (Z.of_nat (Z.to_nat (3 * (f_len f / 3))) + Z.of_nat (Z.to_nat (f_len f1))) by (rewrite El; lia).
  eapply COPIED_trans; [|apply cpn_COPIED]. subst f1. apply COPIED_set_len. apply (COPIED_from_l _ f _ (FOut (f_out f - f_dist f))). apply cpn_COPIED.
Qed.


Lemma shiftr_bound : forall h b c, 0 <= h < 2 ^ b -> 0 <= c <= b -> 0 <= Z.shiftr h c < 2 ^ (b - c).
Proof.
  intros h b c Hh Hc. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos c ltac:(lia)).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  rewrite <- Z.pow_add_r by lia. replace (c + (b - c)) with b by lia. lia.
Qed.

Lemma land_zmask : forall h n, 0 <= h -> 0 <= n < 32 -> Z.land h (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. rewrite zmask_pow2 by lia.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. lia.
Qed.

Lemma land_wrap32_zmask : forall h n, 0 <= h -> 0 <= n < 32 -> Z.land (wrap32 h) (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. rewrite land_zmask by (try apply wrap32_range; lia). rewrite wrap32_mod.
  rewrite <- (Z.mod_mod_divide h (2 ^ 32) (2 ^ n)); [reflexivity|]. apply pow2_divide. lia.
Qed.

Lemma shiftr_land_zmask : forall h b o, 0 <= h -> 0 <= b -> 0 <= o < 32 ->
  Z.land (Z.shiftr h b) (zmask o) = h mod 2 ^ (b + o) / 2 ^ b.
Proof.
  intros h b o Hh Hb Ho. rewrite land_zmask by (try (apply Z.shiftr_nonneg; lia); lia).
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.testbit_mod_pow2 by lia. rewrite !Z.div_pow2_bits by lia. rewrite Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i o), (Z.ltb_spec (i + b) (b + o)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma land16_small : forall op, 0 <= op < 16 -> Z.land op 16 = 0.
Proof.
  intros op H. destruct (Z.eq_dec op 0) as [->|]; [reflexivity|].
  pose proof (allz_range 0 16 (fun op => Z.land op 16 =? 0) ltac:(vm_compute; reflexivity) op H) as E. cbn beta in E.
  apply Z.eqb_eq. exact E.
Qed.
Lemma land64_small : forall op, 0 <= op < 64 -> Z.land op 64 = 0.
Proof.
  intros op H.
  pose proof (allz_range 0 64 (fun op => Z.land op 64 =? 0) ltac:(vm_compute; reflexivity) op H) as E. cbn beta in E.
  apply Z.eqb_eq. exact E.
Qed.

Section Prims.
  Variable x : ffx.
Variable ON : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.

  Lemma FB_fdrop : forall f c, FB ON f -> 0 <= c <= f_bits f ->
    FB ON (fdrop f c) /\ f_in (fdrop f c) = f_in f /\ f_out (fdrop f c) = f_out f /\ f_bits (fdrop f c) = f_bits f - c
    /\ f_hold (fdrop f c) = Z.shiftr (f_hold f) c /\ f_len (fdrop f c) = f_len f /\ f_dist (fdrop f c) = f_dist f /\ f_ob (fdrop f c) = f_ob f.
  Proof.
    intros f c (B1 & B2 & B3 & B4 & B5) Hc. unfold fdrop, FB. facc. rewrite wrap32_id by lia.
    pose proof (shiftr_bound (f_hold f) (f_bits f) c B4 Hc). repeat split; try lia; try exact B5; reflexivity.
  Qed.

  Lemma FB_fpull : forall f, FB ON f -> f_bits f <= 24 ->
    FB ON (fpull x f) /\ f_in (fpull x f) = f_in f + 1 /\ f_out (fpull x f) = f_out f /\ f_bits (fpull x f) = f_bits f + 8
    /\ f_hold (fpull x f) mod 2 ^ f_bits f = f_hold f /\ f_len (fpull x f) = f_len f /\ f_dist (fpull x f) = f_dist f /\ f_ob (fpull x f) = f_ob f.
  Proof.
    intros f (B1 & B2 & B3 & B4 & B5) Hb.
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) (Xin _)) as [E Hh]. rewrite E. unfold FB. facc.
    pose proof (Xin (f_in f)). pose proof (pow2_pos (f_bits f) ltac:(lia)).
    repeat split; try lia; try exact B5; try reflexivity.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
End Prims.


Definition DACC (ON : Z) (f f' : ffs) (c : Z) : Prop :=
  FB ON f' /\
  exists p e, 0 <= p <= 2 /\ 0 <= e <= 13 /\ f_in f' = f_in f + p
    /\ f_bits f + 8 * p - c - e <= f_bits f' <= f_bits f + 8 * p - c
    /\ (1 <= p -> f_bits f - c < e) /\ (p = 2 -> f_bits f - c + 8 < e).

Section Dodist.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable used : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis HT : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) used.

  Lemma dodist_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    ((exists sy, 0 <= sy < 32 /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
    match dodist (S k) x s here f with
    | FCont f' => DACC ON f f' (code_bits here) /\ f_out f' = f_out f + f_len f
    | FBreak f' m msg => DACC ON f f' (code_bits here) /\ f_out f' = f_out f /\ m = BAD /\ msg <> None
    end.
  Proof.
    intros k here f HF Hcb Hcf Hlen Hbeg Hroom Hsh. rewrite dodist_S. cbv zeta.
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *.
    pose proof HF as (B1 & B2 & B3 & B4 & B5). pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    assert (BADc : forall msg : Z, DACC ON f f1 (code_bits here) /\ f_out f1 = f_out f /\ BAD = BAD /\ Some msg <> None).
    { intros msg. split; [|split; [exact E1o|split; [reflexivity|discriminate]]].
      split; [exact HF1|]. exists 0, 0. rewrite E1i, E1b. repeat split; lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. apply BADc. }
    pose proof (dists_sym_cases sy Hsy) as SC. destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv. destruct SC as [(O1 & O2 & O3)|[O1 O2]].
    2:{ rewrite O1. cbn [Z.land Z.eqb negb]. apply BADc. }
    destruct (dist_op_facts op O1) as (F1 & F2 & F3 & F4).
    replace (negb (Z.land op 16 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
    rewrite F3. set (e := op - 16) in *.
    assert (He : 0 <= e <= 13) by lia.
    pose proof (pow2_le e 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13. pose proof (pow2_pos e ltac:(lia)) as P0.
    set (f1d := fset_dist f1 v).
    assert (HF1d : FB ON f1d /\ f_in f1d = f_in f /\ f_out f1d = f_out f /\ f_bits f1d = f_bits f - code_bits here /\ f_len f1d = f_len f /\ f_dist f1d = v
                   /\ 0 <= f_hold f1d).
    { subst f1d. unfold FB. facc. repeat split; first [assumption | reflexivity | lia]. }
    clearbody f1d. clear HF1 E1i E1o E1b E1h E1l E1d E1ob C1 C2 C3 C4 C5 BADc f1.
    destruct HF1d as (HF1 & E1i & E1o & E1b & E1l & E1d & E1h0).
    match goal with |- context [fset_dist ?F _] => set (f2 := F) in * end.
    assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ f_len f2 = f_len f /\ f_dist f2 = v /\ e <= f_bits f2 /\
                  exists p, 0 <= p <= 2 /\ f_in f2 = f_in f + p /\ f_bits f2 = f_bits f - code_bits here + 8 * p
                            /\ (1 <= p -> f_bits f - code_bits here < e) /\ (p = 2 -> f_bits f - code_bits here + 8 < e)).
    { subst f2. destruct (Z.ltb_spec (f_bits f1d) e) as [L1|L1].
      - destruct (FB_fpull x ON Xin f1d HF1 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
        destruct (Z.ltb_spec (f_bits (fpull x f1d)) e) as [L2|L2].
        + destruct (FB_fpull x ON Xin (fpull x f1d) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & P2d & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2d, P1o, P1l, P1d, P2b, P1b. repeat (split; [first [assumption | lia]|]).
          exists 2. rewrite P2i, P1i, E1i. repeat split; lia.
        + split; [exact HP1|]. rewrite P1o, P1l, P1d, P1b. repeat (split; [first [assumption | lia]|]).
          exists 1. rewrite P1i, E1i. repeat split; lia.
      - split; [exact HF1|]. repeat (split; [first [assumption | lia]|]). exists 0. rewrite E1i, E1b. repeat split; lia. }
    clearbody f2. destruct HF2 as (HF2 & E2o & E2l & E2d & E2e & p & Hp & E2i & E2b & C1p & C2p).
    pose proof HF2 as (D1 & D2 & D3 & D4 & D5).
    rewrite (land_wrap32_zmask (f_hold f2) e) by lia.
    pose proof (mod_pow2_range (f_hold f2) e ltac:(lia)) as MR.
    rewrite E2d. rewrite (wrap32_id (v + _)) by lia.
    set (dist := v + f_hold f2 mod 2 ^ e) in *.
    destruct (FB_fdrop ON (fset_dist f2 dist) e ltac:(unfold FB in *; facc; repeat split; try lia; exact D5) ltac:(facc; lia))
      as (HF3 & E3i & E3o & E3b & E3h & E3l & E3d & E3ob).
    set (f3 := fdrop (fset_dist f2 dist) e) in *. revert E3i E3o E3b E3l E3d. facc. intros E3i E3o E3b E3l E3d.
    assert (ACC3 : DACC ON f f3 (code_bits here)).
    { split; [exact HF3|]. exists p, e. rewrite E3i, E3b, E2i, E2b. repeat split; lia. }
    rewrite ?E3o, ?E3d, ?E2o. rewrite (wrap32_id (f_out f - x_beg x)) by lia.
    destruct (Z.ltb_spec (f_out f - x_beg x) dist) as [Cw|Cw].
    -
      rewrite (wrap32_id (dist - _)) by lia.
      destruct ((x_whave x <? dist - (f_out f - x_beg x)) && negb (x_sane x =? 0)).
      + split; [|split; [facc; rewrite ?E3o, ?E2o; reflexivity|split; [reflexivity|discriminate]]].
        destruct ACC3 as [HF3' AC]. split; [unfold FB in *; facc; exact HF3'|]. facc. exact AC.
      + set (f4 := fset_op f3 (dist - (f_out f - x_beg x))).
        destruct (win_place_spec x f4 ltac:(subst f4; facc; lia) ltac:(subst f4; facc; lia) Xwn) as (n & CPw & Hn & Hl5 & En).
        apply COPIED_op_l in CPw.
        pose proof (dist_tailcopy_spec x (win_place x f4) ltac:(subst f4; revert Hl5 En; facc; intros; lia)) as CPt.
        pose proof (COPIED_trans _ _ _ _ _ CPw CPt) as (T1 & T2 & T3 & T4 & T5 & T6).
        subst f4. revert En T5. facc. rewrite E3l. intros En T5.
        split; [|rewrite T5, ?E3o, ?E2o; lia].
        destruct ACC3 as [_ AC]. split.
        * unfold FB. rewrite T1, T2, T3, T5, T6. unfold FB in HF3. lia.
        * rewrite T1, T3. exact AC.
    -
      pose proof (out_copy_spec x f3 ltac:(rewrite E3l; lia)) as (T1 & T2 & T3 & T4 & T5 & T6).
      split; [|rewrite T5, ?E3o, ?E2o, ?E3l, ?E2l; lia].
      destruct ACC3 as [_ AC]. split.
      + unfold FB. rewrite T1, T2, T3, T5, T6. unfold FB in HF3. lia.
      + rewrite T1, T3. exact AC.
  Qed.

  Lemma DACC_shift : forall f f1 f' c0 c,
    DACC ON f1 f' c -> f_in f1 = f_in f -> f_bits f1 = f_bits f - c0 -> DACC ON f f' (c0 + c).
  Proof.
    intros f f1 f' c0 c [HF (p & e & Hp & He & Ei & Eb & C1 & C2)] E1 E2. split; [exact HF|].
    exists p, e. rewrite E1 in Ei. rewrite E2 in Eb, C1, C2. repeat split; try lia.
  Qed.

  Lemma dodist_root : forall k f,
    FB ON f -> 15 <= f_bits f -> 3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    exists c, 1 <= c <= 15 /\
    match dodist (S (S k)) x s (code_at s (is_distcode s) (f_hold f mod 2 ^ is_distbits s)) f with
    | FCont f' => DACC ON f f' c /\ f_out f' = f_out f + f_len f
    | FBreak f' m msg => DACC ON f f' c /\ f_out f' = f_out f /\ m = BAD /\ msg <> None
    end.
  Proof.
    intros k f HF Hb Hlen Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HT) as HR15.
    pose proof (ridx_range _ _ _ _ HT (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HT _ XR) as (Hbits & RL & RN).
    set (getD := code_at s (is_distcode s)) in *. set (root := is_distbits s) in *.
    set (here := getD (f_hold f mod 2 ^ root)) in *.
    destruct (is_linkb here) eqn:HL.
    -
      destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dodist_S. cbv zeta.
      rewrite (land16_small (code_op here)) by lia. rewrite (land64_small (code_op here)) by lia. cbn [Z.eqb negb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here).
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      destruct (sub_cell _ _ _ _ HT (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getD root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getD.
      set (here2 := getD (code_val here + y)) in *.
      pose proof (dodist_term k here2 f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia) ltac:(rewrite E1l; exact Hlen)
                    ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o, E1l; exact Hroom) SSh) as DT.
      exists (code_bits here + code_bits here2). split; [lia|].
      revert DT. destruct (dodist (S k) x s here2 f1) as [f'|f' m msg]; intros DT.
      + destruct DT as [DA EO]. split; [exact (DACC_shift f f1 f' _ _ DA E1i E1b)|]. rewrite EO, E1o, E1l. reflexivity.
      + destruct DT as (DA & EO & Hm & Hmsg). split; [exact (DACC_shift f f1 f' _ _ DA E1i E1b)|]. rewrite EO, E1o. repeat split; assumption.
    -
      destruct (RN eq_refl) as [Hbr SH].
      exists (code_bits here). split; [lia|].
      exact (dodist_term (S k) here f HF ltac:(lia) ltac:(lia) Hlen Hbeg Hroom SH).
  Qed.
End Dodist.
End RefInflateSafeF1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.

Module RefInflateSafeF2.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.
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

Definition len_extra (x : ffx) (op : Z) (f : ffs) : ffs :=
  if negb (op =? 0) then
    let f := if f_bits f <? op then fpull x f else f in
    let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
    fdrop f op
  else f.

Lemma dolen_S : forall k x s here f,
  dolen (S k) x s here f =
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then
      FCont (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val here)))) (f_out f + 1))
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      let f := len_extra x op f in
      let f := fpull2_if x f in
      dodist 4 x s (code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask x))) f
    else if Z.land op 64 =? 0 then
      dolen k x s (code_at s (is_lencode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else if negb (Z.land op 32 =? 0) then FBreak f TYPE None
    else FBreak f BAD (Some MSG_invalid_literal_length_code).
Proof.
  intros. unfold len_extra. cbv zeta. cbn [dolen].
  lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end.
Qed.

Definition LACC (ON : Z) (f f' : ffs) (c : Z) : Prop :=
  FB ON f' /\
  exists p, 0 <= p <= 5 /\ (1 <= f_bits f - c -> p <= 4) /\ f_in f' = f_in f + p
    /\ 0 <= f_bits f' <= f_bits f + 8 * p - c
    /\ f_out f <= f_out f' <= f_out f + 258.

Definition break_ok (m : Z) (msg : option Z) : Prop := (m = TYPE /\ msg = None) \/ (m = BAD /\ msg <> None).

Section Dolen.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable usedL : Z.
Variable usedD : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis Xdm : x_dmask x = zmask (is_distbits s).
  Hypothesis Xlm : x_lmask x = zmask (is_lenbits s).
  Hypothesis HTL : TBLg LENS (code_at s (is_lencode s)) (is_lenbits s) usedL.
  Hypothesis HTD : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) usedD.

  Lemma LACC_shift : forall f f1 f' c0 c,
    LACC ON f1 f' c -> f_in f1 = f_in f -> f_bits f1 = f_bits f - c0 -> f_out f1 = f_out f -> LACC ON f f' (c0 + c).
  Proof.
    intros f f1 f' c0 c [HF (p & Hp & Hp4 & Ei & Eb & Eo)] E1 E2 E3. split; [exact HF|].
    exists p. rewrite E1 in Ei. rewrite E2 in Eb, Hp4. rewrite E3 in Eo. repeat split; try lia.
  Qed.

  Lemma dolen_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    x_beg x <= f_out f -> f_out f + 258 <= ON ->
    ((exists sy, 0 <= sy < 288 /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    match dolen (S k) x s here f with
    | FCont f' => LACC ON f f' (code_bits here)
    | FBreak f' m msg => LACC ON f f' (code_bits here) /\ break_ok m msg
    end.
  Proof.
    intros k here f HF Hcb Hcf Hbeg Hroom Hsh. rewrite dolen_S. cbv zeta.
    pose proof HF as (B1 & B2 & B3 & B4 & B5).
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *. pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    assert (STAY : LACC ON f f1 (code_bits here)).
    { split; [exact HF1|]. exists 0. rewrite E1i, E1b, E1o. repeat split; lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate]. }
    pose proof (lens_sym_cases sy Hsy) as SC. destruct (sym_entry LENS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv. destruct SC as [[O1 O2]|[[O1 O2]|[(O1 & O2 & O3)|[O1|O1]]]].
    -
      rewrite O1. cbn [Z.eqb]. split.
      + unfold FB. facc. rewrite arr_len_set. unfold FB in HF1. lia.
      + exists 0. facc. rewrite E1i, E1b, E1o. repeat split; lia.
    -
      rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. left. split; reflexivity.
    -
      destruct (len_op_facts op O1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (negb (Z.land op 16 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
      rewrite F3. set (e := op - 16) in *.
      assert (He : 0 <= e <= 5) by lia.
      pose proof (pow2_le e 5 ltac:(lia)) as P5. change (2 ^ 5) with 32 in P5. pose proof (pow2_pos e ltac:(lia)) as P0.
      set (f2 := len_extra x e (fset_len f1 v)).
      assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ 3 <= f_len f2 <= 258 /\
                    exists p1, 0 <= p1 <= 1 /\ f_in f2 = f_in f + p1 /\ f_bits f2 = f_bits f - code_bits here + 8 * p1 - e
                               /\ (p1 = 1 -> f_bits f - code_bits here < e) /\ 0 <= f_bits f2).
      { subst f2. unfold len_extra. destruct (Z.eqb_spec e 0) as [E0|E0]; cbn [negb].
        - unfold FB. facc. split; [unfold FB in HF1; lia|]. split; [exact E1o|]. split; [lia|].
          exists 0. rewrite E1i, E1b. repeat split; lia.
        - cbv zeta.
          set (f1v := fset_len f1 v) in *.
          assert (HF1v : FB ON f1v /\ f_len f1v = v /\ f_in f1v = f_in f /\ f_out f1v = f_out f /\ f_bits f1v = f_bits f - code_bits here)
            by (subst f1v; unfold FB in *; facc; repeat split; first [assumption | reflexivity | lia]).
          clearbody f1v. destruct HF1v as (HF1v & Vl & Vi & Vo & Vb).
          match goal with |- context [fdrop ?F e] => set (fp := F) in * end.
          assert (HFp : FB ON fp /\ f_out fp = f_out f /\ e <= f_bits fp /\
                        exists p1, 0 <= p1 <= 1 /\ f_in fp = f_in f + p1 /\ f_bits fp = f_bits f - code_bits here + 8 * p1
                                   /\ (p1 = 1 -> f_bits f - code_bits here < e) /\ f_len fp = v + f_hold fp mod 2 ^ e).
          { subst fp. destruct (Z.ltb_spec (f_bits f1v) e) as [L1|L1].
            - destruct (FB_fpull x ON Xin f1v HF1v ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
              unfold FB. facc. unfold FB in HP1. rewrite (land_wrap32_zmask (f_hold (fpull x f1v)) e) by lia.
              rewrite wrap32_id by (pose proof (mod_pow2_range (f_hold (fpull x f1v)) e ltac:(lia)); lia).
              rewrite P1o, P1l, Vl. split; [lia|]. split; [exact Vo|]. split; [lia|].
              exists 1. rewrite P1i, Vi, P1b, Vb. repeat split; lia.
            - unfold FB. facc. unfold FB in HF1v. rewrite (land_wrap32_zmask (f_hold f1v) e) by lia.
              rewrite wrap32_id by (pose proof (mod_pow2_range (f_hold f1v) e ltac:(lia)); lia).
              rewrite Vl. split; [lia|]. split; [exact Vo|]. split; [lia|].
              exists 0. rewrite Vi, Vb. repeat split; lia. }
          clearbody fp. destruct HFp as (HFp & Po & Pe & p1 & Hp1 & Pi & Pb & Pc & Pl).
          destruct (FB_fdrop ON fp e HFp ltac:(lia)) as (HQ & Qi & Qo & Qb & Qh & Ql & Qd & Qob).
          pose proof (mod_pow2_range (f_hold fp) e ltac:(lia)).
          split; [exact HQ|]. rewrite Qo, Ql, Pl. split; [exact Po|]. split; [lia|].
          exists p1. rewrite Qi, Qb, Pi, Pb. unfold FB in HQ. repeat split; lia. }
      clearbody f2. clear STAY. destruct HF2 as (HF2 & E2o & E2l & p1 & Hp1 & E2i & E2b & Cp1 & E2nn).
      set (f3 := fpull2_if x f2).
      assert (HF3 : FB ON f3 /\ f_out f3 = f_out f /\ f_len f3 = f_len f2 /\ 15 <= f_bits f3 /\
                    exists p2, (p2 = 0 \/ p2 = 2) /\ f_in f3 = f_in f2 + p2 /\ f_bits f3 = f_bits f2 + 8 * p2 /\ (p2 = 2 <-> f_bits f2 < 15)).
      { subst f3. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f2) 15) as [L|L].
        - destruct (FB_fpull x ON Xin f2 HF2 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & _ & _).
          destruct (FB_fpull x ON Xin (fpull x f2) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & _ & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2b, P2i, P1o, P1l, P1b, P1i. repeat (split; [first [assumption | lia]|]).
          exists 2. repeat split; lia.
        - split; [exact HF2|]. repeat (split; [first [assumption | lia]|]). exists 0. repeat split; lia. }
      clearbody f3. destruct HF3 as (HF3 & E3o & E3l & E3b & p2 & Hp2 & E3i & E3bb & Cp2).
      rewrite Xdm. rewrite land_zmask by (pose proof (T_root _ _ _ _ HTD); unfold FB in HF3; lia).
      destruct (dodist_root x s ON usedD Xin Xwn Xbeg HON HTD 2 f3 HF3 E3b ltac:(lia) ltac:(lia) ltac:(lia)) as (c2 & Hc2 & DD).
      change 4%nat with (S (S 2)).
      destruct (dodist 4 x s _ f3) as [f'|f' m msg].
      + destruct DD as [[HF' (p3 & e2 & Hp3 & He2 & Ei & Eb & D1 & D2)] Eo].
        split; [exact HF'|]. exists (p1 + p2 + p3). rewrite Ei, E3i, E2i, Eo, E3o. unfold FB in HF'. repeat split; try lia.
      + destruct DD as ([HF' (p3 & e2 & Hp3 & He2 & Ei & Eb & D1 & D2)] & Eo & Hm & Hmsg).
        split; [|right; split; assumption].
        split; [exact HF'|]. exists (p1 + p2 + p3). rewrite Ei, E3i, E2i, Eo, E3o. unfold FB in HF'. repeat split; try lia.
    -
      rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate].
    - rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate].
  Qed.

  Lemma dolen_root : forall k f,
    FB ON f -> 15 <= f_bits f -> x_beg x <= f_out f -> f_out f + 258 <= ON ->
    let c := lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold f) in
    1 <= c <= 15 /\
    match dolen (S (S k)) x s (code_at s (is_lencode s) (f_hold f mod 2 ^ is_lenbits s)) f with
    | FCont f' => LACC ON f f' c
    | FBreak f' m msg => LACC ON f f' c /\ break_ok m msg
    end.
  Proof.
    intros k f HF Hb Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HTL) as HR15.
    pose proof (ridx_range _ _ _ _ HTL (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HTL _ XR) as (Hbits & RL & RN).
    pose proof (lneedg_range _ _ _ _ HTL (f_hold f)) as [LR _].
    cbv zeta. split; [exact LR|].
    set (getL := code_at s (is_lencode s)) in *. set (root := is_lenbits s) in *.
    set (here := getL (f_hold f mod 2 ^ root)) in *.
    unfold lneedg. fold here.
    destruct (is_linkb here) eqn:HL.
    - destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dolen_S. cbv zeta.
      replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite (land16_small (code_op here)) by lia. rewrite (land64_small (code_op here)) by lia. cbn [Z.eqb negb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here).
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      destruct (sub_cell _ _ _ _ HTL (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getL root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getL.
      set (here2 := getL (code_val here + y)) in *.
      pose proof (dolen_term k here2 f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia) ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o; exact Hroom) SSh) as DT.
      revert DT. destruct (dolen (S k) x s here2 f1) as [f'|f' m msg]; intros DT.
      + exact (LACC_shift f f1 f' _ _ DT E1i E1b E1o).
      + destruct DT as [DT BK]. split; [exact (LACC_shift f f1 f' _ _ DT E1i E1b E1o)|exact BK].
    - destruct (RN eq_refl) as [Hbr SH].
      exact (dolen_term (S k) here f HF ltac:(lia) ltac:(lia) Hbeg Hroom SH).
  Qed.

  Lemma fast_trip_spec : forall f,
    FB ON f -> x_beg x <= f_out f -> f_out f + 258 <= ON ->
    let f1 := fpull2_if x f in
    let c := lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold f1) in
    f_hold f1 mod 2 ^ f_bits f = f_hold f /\ 1 <= c <= 15 /\
    match fast_trip x s f with
    | FCont f' | FBreak f' _ _ =>
        FB ON f' /\ f_in f <= f_in f' <= f_in f + 6 /\ f_out f <= f_out f' <= f_out f + 258
        /\ c <= 8 * (f_in f' - f_in f) + f_bits f - f_bits f'
    end /\
    match fast_trip x s f with FCont _ => True | FBreak _ m msg => break_ok m msg end.
  Proof.
    intros f HF Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    unfold fast_trip.
    set (f1 := fpull2_if x f).
    assert (HF1 : FB ON f1 /\ f_out f1 = f_out f /\ 15 <= f_bits f1 /\ f_hold f1 mod 2 ^ f_bits f = f_hold f /\
                  exists p0, (p0 = 0 \/ p0 = 2) /\ f_in f1 = f_in f + p0 /\ f_bits f1 = f_bits f + 8 * p0 /\ (p0 = 2 <-> f_bits f < 15)).
    { subst f1. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f) 15) as [L|L].
      - destruct (FB_fpull x ON Xin f HF ltac:(lia)) as (HP1 & P1i & P1o & P1b & P1m & _ & _ & _).
        destruct (FB_fpull x ON Xin (fpull x f) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & P2m & _ & _ & _).
        split; [exact HP2|]. rewrite P2o, P2b, P2i, P1o, P1b, P1i. split; [reflexivity|]. split; [lia|]. split.
        + rewrite <- P1m. rewrite <- P2m at 1. rewrite P1b. symmetry. apply (mod_down (f_bits f) (f_bits f + 8)); [lia|].
          rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
        + exists 2. repeat split; lia.
      - split; [exact HF|]. split; [reflexivity|]. split; [lia|]. split; [apply Z.mod_small; lia|]. exists 0. repeat split; lia. }
    clearbody f1. destruct HF1 as (HF1 & E1o & E1b & E1m & p0 & Hp0 & E1i & E1bb & C0).
    cbv zeta. split; [exact E1m|].
    rewrite Xlm. rewrite land_zmask by (pose proof (T_root _ _ _ _ HTL); unfold FB in HF1; lia).
    destruct (dolen_root 2 f1 HF1 E1b ltac:(lia) ltac:(lia)) as [Hc DL]. cbv zeta in DL.
    split; [exact Hc|].
    change 4%nat with (S (S 2)).
    destruct (dolen 4 x s _ f1) as [f'|f' m msg].
    - destruct DL as [HF' (p & Hp & Hp4 & Ei & Eb & Eo)]. split; [|exact I].
      split; [exact HF'|]. rewrite Ei, E1i, E1o in *. unfold FB in HF'. repeat split; try lia.
    - destruct DL as [[HF' (p & Hp & Hp4 & Ei & Eb & Eo)] BK]. split; [|exact BK].
      split; [exact HF'|]. rewrite Ei, E1i, E1o in *. unfold FB in HF'. repeat split; try lia.
  Qed.
End Dolen.
End RefInflateSafeF2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF2.

Module RefInflateEqD.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition LIVE_length (m : Z) : bool :=
  (m =? COPY_) || (m =? COPY) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) || (m =? LIT).
Definition LIVE_offset (m : Z) : bool := (m =? DISTEXT) || (m =? MATCH).
Definition LIVE_extra (m : Z) : bool := (m =? LENEXT) || (m =? DISTEXT).
Definition LIVE_codes (m : Z) : bool :=
  (m =? LEN_) || (m =? LEN) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) || (m =? LIT).
Definition LIVE_lenbits (m : Z) : bool := (m =? CODELENS) || LIVE_codes m.
Definition LIVE_nlen (m : Z) : bool := (m =? LENLENS) || (m =? CODELENS).

Definition tbl_eq (codes1 codes2 : arr) (ty : codetype) (p : codeptr) (root : Z) : Prop :=
  match p with
  | CDyn o => exists used, TBLg ty (fun x => arr_get codes1 (o + x)) root used
                           /\ forall i, o <= i < o + used -> arr_get codes2 i = arr_get codes1 i
  | _ => True
  end.


Definition IEQ (s1 s2 : inflate_state) : Prop :=
  let m := is_mode s1 in
  (is_mode s2 = is_mode s1 /\ is_last s2 = is_last s1 /\ is_wrap s2 = is_wrap s1 /\ is_havedict s2 = is_havedict s1
   /\ is_flags s2 = is_flags s1 /\ is_dmax s2 = is_dmax s1 /\ is_total s2 = is_total s1 /\ is_head s2 = is_head s1
   /\ is_wbits s2 = is_wbits s1 /\ is_wsize s2 = is_wsize s1 /\ is_whave s2 = is_whave s1 /\ is_wnext s2 = is_wnext s1
   /\ is_window_blk s2 = is_window_blk s1 /\ is_hold s2 = is_hold s1 /\ is_bits s2 = is_bits s1
   /\ is_lencode s2 = is_lencode s1 /\ is_distcode s2 = is_distcode s1 /\ is_next s2 = is_next s1
   /\ is_sane s2 = is_sane s1 /\ is_back s2 = is_back s1 /\ is_self_blk s2 = is_self_blk s1
   /\ arr_len (is_window s2) = arr_len (is_window s1) /\ arr_len (is_lens s2) = arr_len (is_lens s1)
   /\ arr_len (is_work s2) = arr_len (is_work s1) /\ arr_len (is_codes s2) = arr_len (is_codes s1))
  /\ (is_flags s1 = 0 -> is_check s2 = is_check s1)
  /\ (LIVE_length m = true -> is_length s2 = is_length s1)
  /\ (LIVE_offset m = true -> is_offset s2 = is_offset s1)
  /\ (LIVE_extra m = true -> is_extra s2 = is_extra s1)
  /\ (LIVE_lenbits m = true -> is_lenbits s2 = is_lenbits s1)
  /\ (LIVE_codes m = true -> is_distbits s2 = is_distbits s1)
  /\ (m = LENLENS -> is_ncode s2 = is_ncode s1)
  /\ (LIVE_nlen m = true -> is_nlen s2 = is_nlen s1 /\ is_ndist s2 = is_ndist s1 /\ is_have s2 = is_have s1)
  /\ (forall i, 0 <= i < is_whave s1 -> arr_get (is_window s2) i = arr_get (is_window s1) i)
  /\ (m = LENLENS -> forall k, 0 <= k < is_have s1 -> arr_get (is_lens s2) (arr_get order_a k) = arr_get (is_lens s1) (arr_get order_a k))
  /\ (m = CODELENS -> forall i, (0 <= i < 19 \/ 0 <= i < is_have s1) -> arr_get (is_lens s2) i = arr_get (is_lens s1) i)
  /\ (m = CODELENS -> tbl_eq (is_codes s1) (is_codes s2) CODES (is_lencode s1) (is_lenbits s1))
  /\ (LIVE_codes m = true -> tbl_eq (is_codes s1) (is_codes s2) LENS (is_lencode s1) (is_lenbits s1)
                            /\ tbl_eq (is_codes s1) (is_codes s2) DISTS (is_distcode s1) (is_distbits s1)).

Definition gzb (m : Z) : bool :=
  (m =? FLAGS) || (m =? TIME) || (m =? OS) || (m =? EXLEN) || (m =? EXTRA) || (m =? NAME) || (m =? COMMENT) || (m =? HCRC).
Definition UW (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  is_wrap s = 5 /\ gzb (is_mode s) = false /\
  (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_put r = 0 /\ ir_out r = arr_len (ic_outbuf c))).

Definition WMID (w1 w2 : iw) : Prop :=
  w_c w2 = w_c w1 /\ w_r w2 = w_r w1 /\ IEQ (w_s w1) (w_s w2) /\ UW (w_s w1) (w_c w1) (w_r w1).

Lemma WMID_mk : forall s1 s2 c r, IEQ s1 s2 -> UW s1 c r -> WMID (mkW s1 c r) (mkW s2 c r).
Proof. intros. split; [reflexivity|]. split; [reflexivity|]. split; assumption. Qed.

Definition RES2 {A} (r1 r2 : ares A) : Prop :=
  match r1, r2 with
  | ARun a w1, ARun b w2 => b = a /\ WMID w1 w2
  | ALeave w1, ALeave w2 => WMID w1 w2
  | ARet x w1, ARet y w2 => y = x /\ WMID w1 w2
  | _, _ => False
  end.


Section Rules.
  Context {A B : Type}.

  Lemma RES2_bind : forall (m1 m2 : AM A) (f1 f2 : A -> AM B) w1 w2,
    RES2 (m1 w1) (m2 w2) ->
    (forall a s1 s2 c r, IEQ s1 s2 -> UW s1 c r -> m1 w1 = ARun a (mkW s1 c r) -> RES2 (f1 a (mkW s1 c r)) (f2 a (mkW s2 c r))) ->
    RES2 (abind m1 f1 w1) (abind m2 f2 w2).
  Proof.
    intros m1 m2 f1 f2 w1 w2 H K. unfold abind.
    destruct (m1 w1) as [a w1'|w1'|x w1'] eqn:E1; destruct (m2 w2) as [b w2'|w2'|y w2']; cbn [RES2] in H; try contradiction.
    - destruct H as [-> H]. destruct w1' as [s1 c1 r1], w2' as [s2 c2 r2].
      destruct H as (Ec & Er & HQ & HU). cbn [w_c w_r w_s] in Ec, Er, HQ, HU. subst c2 r2.
      exact (K a s1 s2 c1 r1 HQ HU eq_refl).
    - exact H.
    - exact H.
  Qed.

  Lemma RES2_step : forall (m : AM A) (f : A -> AM B) w1 w2 a1 a2 w1' w2',
    m w1 = ARun a1 w1' -> m w2 = ARun a2 w2' -> a2 = a1 ->
    RES2 (f a1 w1') (f a1 w2') ->
    RES2 (abind m f w1) (abind m f w2).
  Proof. intros m f w1 w2 a1 a2 w1' w2' E1 E2 -> H. unfold abind. rewrite E1, E2. exact H. Qed.

  Lemma RES2_ret : forall (a : A) w1 w2, WMID w1 w2 -> RES2 (aret a w1) (aret a w2).
  Proof. intros. split; [reflexivity|assumption]. Qed.
  Lemma RES2_leave : forall w1 w2, WMID w1 w2 -> RES2 (@aleave A w1) (@aleave A w2).
  Proof. intros. exact H. Qed.
  Lemma RES2_return : forall rc w1 w2, WMID w1 w2 -> RES2 (@areturn A rc w1) (@areturn A rc w2).
  Proof. intros. split; [reflexivity|assumption]. Qed.

  Definition SFREE (m : AM A) : Prop :=
    forall s c r,
      match m (mkW s c r) with
      | ARun a w' => exists r', (forall s', m (mkW s' c r) = ARun a (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      | ALeave w' => exists r', (forall s', m (mkW s' c r) = ALeave (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      | ARet x w' => exists r', (forall s', m (mkW s' c r) = ARet x (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      end.

  Lemma UW_regs : forall s c r r', UW s c r -> ir_put r' = ir_put r -> ir_out r' = ir_out r -> UW s c r'.
  Proof. intros s c r r' (W & G & U) Ep Eo. split; [exact W|]. split; [exact G|]. rewrite Ep, Eo. exact U. Qed.

  Lemma RES2_sfree : forall (m : AM A) s1 s2 c r, SFREE m -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (m (mkW s1 c r)) (m (mkW s2 c r)).
  Proof.
    intros m s1 s2 c r SF HQ HU. specialize (SF s1 c r).
    destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1;
      destruct SF as (r' & E & Ep & Eo); rewrite (E s1) in E1; rewrite (E s2);
      [injection E1; intros <-; split; [reflexivity|] | injection E1; intros <- | injection E1; intros <-; split; [reflexivity|]];
      (apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)]).
  Qed.
End Rules.


Lemma SFREE_gr : forall {A} (f : iregs -> A), SFREE (gr f).
Proof. intros A f s c r. cbn [gr w_r]. exists r. repeat split; reflexivity. Qed.
Lemma SFREE_gc : forall {A} (f : icall -> A), SFREE (gc f).
Proof. intros A f s c r. cbn [gc w_c]. exists r. repeat split; reflexivity. Qed.
Lemma SFREE_ur : forall (f : iregs -> iregs), (forall r, ir_put (f r) = ir_put r /\ ir_out (f r) = ir_out r) -> SFREE (ur f).
Proof. intros f Hf s c r. cbn [ur w_r wset_r]. exists (f r). split; [intros; reflexivity|apply Hf]. Qed.
Lemma SFREE_ret : forall {A} (a : A), SFREE (aret a).
Proof. intros A a s c r. cbn [aret]. exists r. repeat split; reflexivity. Qed.
Lemma SFREE_leave : forall {A}, SFREE (@aleave A).
Proof. intros A s c r. cbn [aleave]. exists r. repeat split; reflexivity. Qed.

Lemma SFREE_bind : forall {A B} (m : AM A) (f : A -> AM B), SFREE m -> (forall a, SFREE (f a)) -> SFREE (abind m f).
Proof.
  intros A B m f Hm Hf s c r. unfold abind. specialize (Hm s c r).
  destruct (m (mkW s c r)) as [a w'|w'|x w'] eqn:E1; destruct Hm as (r' & E & Ep & Eo).
  - rewrite (E s) in E1. injection E1; intros <-. specialize (Hf a s c r').
    destruct (f a (mkW s c r')) as [b w''|w''|y w'']; destruct Hf as (r'' & E' & Ep' & Eo');
      exists r''; (split; [intros s'; rewrite (E s'); apply E' | split; congruence]).
  - exists r'. split; [intros s'; rewrite (E s'); reflexivity | split; assumption].
  - exists r'. split; [intros s'; rewrite (E s'); reflexivity | split; assumption].
Qed.

Lemma SFREE_PULLBYTE : SFREE PULLBYTE.
Proof.
  intros s c r. rewrite PULLBYTE_eq. destruct (ir_have r =? 0) eqn:E.
  - exists r. split; [intros s'; rewrite PULLBYTE_eq, E; reflexivity | split; reflexivity].
  - exists (pullr c r). split; [intros s'; rewrite PULLBYTE_eq, E; reflexivity | split; reflexivity].
Qed.

Lemma SFREE_NEEDBITS_k : forall k n, SFREE (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k].
  - apply SFREE_ret.
  - apply SFREE_bind; [apply SFREE_gr|]. intros b. destruct (b <? n); [|apply SFREE_ret].
    apply SFREE_bind; [apply SFREE_PULLBYTE | intros; apply IH].
Qed.
Lemma SFREE_NEEDBITS : forall n, SFREE (NEEDBITS n).
Proof. intros n. unfold NEEDBITS. apply SFREE_NEEDBITS_k. Qed.
Lemma SFREE_BITS : forall n, SFREE (BITS n). Proof. intros n. unfold BITS. apply SFREE_gr. Qed.
Lemma SFREE_HOLD : SFREE HOLD. Proof. unfold HOLD. apply SFREE_gr. Qed.
Lemma SFREE_DROPBITS : forall n, SFREE (DROPBITS n).
Proof. intros n. unfold DROPBITS. apply SFREE_ur. intros; split; reflexivity. Qed.
Lemma SFREE_INITBITS : SFREE INITBITS.
Proof. unfold INITBITS. apply SFREE_ur. intros; split; reflexivity. Qed.
Lemma SFREE_BYTEBITS : SFREE BYTEBITS.
Proof. unfold BYTEBITS. apply SFREE_ur. intros; split; reflexivity. Qed.


Ltac live_red_in H :=
  cbv beta iota delta [LIVE_length LIVE_offset LIVE_extra LIVE_codes LIVE_lenbits LIVE_nlen
                       Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.
Ltac live_red :=
  cbv beta iota delta [LIVE_length LIVE_offset LIVE_extra LIVE_codes LIVE_lenbits LIVE_nlen
                       Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].

Ltac cond_use H :=
  lazymatch type of H with
  | true = true -> _ => specialize (H eq_refl)
  | false = true -> _ => clear H
  | ?x = ?x -> _ => specialize (H eq_refl)
  | ?n = ?m -> _ => first [ let TMP := fresh in assert (TMP : n <> m) by discriminate; clear TMP; clear H | idtac ]
  | _ => idtac
  end.

Ltac ieq_open HQ E :=
  unfold IEQ in HQ; cbv zeta in HQ; rewrite ?E in HQ;
  destruct HQ as ((Qmode & Qlast & Qwrap & Qhavedict & Qflags & Qdmax & Qtotal & Qhead & Qwbits & Qwsize & Qwhave & Qwnext
                   & Qwblk & Qhold & Qbits & Qlencode & Qdistcode & Qnext & Qsane & Qback & Qself & QLwin & QLlens & QLwork & QLcodes)
                  & Qcheck & Qlength & Qoffset & Qextra & Qlenbits & Qdistbits & Qncode & Qnlen & Qwin & Qlens1 & Qlens2 & Qctbl & Qtbls);
  live_red_in Qlength; live_red_in Qoffset; live_red_in Qextra; live_red_in Qlenbits; live_red_in Qdistbits;
  live_red_in Qncode; live_red_in Qnlen; live_red_in Qlens1; live_red_in Qlens2; live_red_in Qctbl; live_red_in Qtbls;
  cond_use Qlength; cond_use Qoffset; cond_use Qextra; cond_use Qlenbits; cond_use Qdistbits;
  cond_use Qncode; cond_use Qnlen; cond_use Qlens1; cond_use Qlens2; cond_use Qctbl; cond_use Qtbls;
  try lazymatch type of Qnlen with _ /\ _ => destruct Qnlen as (Qnlen & Qndist & Qhave) end;
  try lazymatch type of Qtbls with _ /\ _ => destruct Qtbls as [QtblL QtblD] end.

Ltac ieq_rw s1 s2 :=
  repeat match goal with
         | Q : ?f s2 = ?f s1 |- context [?f s2] => rewrite !Q
         | Q : arr_len (?f s2) = arr_len (?f s1) |- context [arr_len (?f s2)] => rewrite !Q
         end.

Ltac ieq_leaf :=
  first [ assumption | reflexivity | exact I
        | (intros X; discriminate X)
        | (intros _; repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | exact I | solve [congruence] | idtac])
        | solve [congruence]
        | idtac ].
Ltac ieq_close E :=
  unfold IEQ; cbv zeta; unfold fixedtables; sacc; rewrite ?E; live_red; cbn [tbl_eq];
  repeat match goal with |- _ /\ _ => split end; ieq_leaf.


Lemma UW_notHB : forall s c r, UW s c r -> is_mode s <> HEAD -> is_mode s <> BAD -> is_wrap s = 5 /\ is_flags s = 0.
Proof.
  intros s c r (W & G & [F|(F & [M|M] & _)]) NH NB; [split; assumption| exfalso; exact (NH M) | exfalso; exact (NB M)].
Qed.
Lemma UW_gz : forall s c r, UW s c r -> gzb (is_mode s) = false.
Proof. intros s c r (W & G & _). exact G. Qed.
Lemma UW_intro0 : forall s c r, is_wrap s = 5 -> is_flags s = 0 -> gzb (is_mode s) = false -> UW s c r.
Proof. intros s c r W F G. split; [exact W|]. split; [exact G|left; exact F]. Qed.

Lemma RES2_step2 : forall {A B} (m : AM A) (f : A -> AM B) w1 w2 a1 a2 w1' w2',
  m w1 = ARun a1 w1' -> m w2 = ARun a2 w2' ->
  RES2 (f a1 w1') (f a2 w2') ->
  RES2 (abind m f w1) (abind m f w2).
Proof. intros A B m f w1 w2 a1 a2 w1' w2' E1 E2 H. unfold abind. rewrite E1, E2. exact H. Qed.

Definition arm_cong (M : Z) (F : inflate_state -> icall -> iregs -> Prop) (arm : AM unit) : Prop :=
  forall s1 s2 c r, F s1 c r -> is_mode s1 = M -> IEQ s1 s2 -> UW s1 c r ->
  RES2 (arm (mkW s1 c r)) (arm (mkW s2 c r)).
Definition FTrue (s : inflate_state) (c : icall) (r : iregs) : Prop := True.
Definition FCore (s : inflate_state) (c : icall) (r : iregs) : Prop := CORE s.


Definition LOCK {A} (m : AM A) (s1 s2 : inflate_state) : Prop := forall c r,
  match m (mkW s1 c r) with
  | ARun a w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ARun a (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  | ALeave w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ALeave (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  | ARet x w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ARet x (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  end.

Lemma SFREE_LOCK : forall {A} (m : AM A) s1 s2, SFREE m -> LOCK m s1 s2.
Proof.
  intros A m s1 s2 SF c r. specialize (SF s1 c r).
  destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1; destruct SF as (r' & E & Ep & Eo);
    exists r'; rewrite (E s1) in E1; (split; [congruence|]); (split; [apply E|]); split; assumption.
Qed.

Section LockRules.
  Context {A B : Type}.

  Lemma RES2_lock : forall (m : AM A) s1 s2 c r, LOCK m s1 s2 -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (m (mkW s1 c r)) (m (mkW s2 c r)).
  Proof.
    intros m s1 s2 c r L HQ HU. specialize (L c r).
    destruct (m (mkW s1 c r)) as [a w'|w'|x w']; destruct L as (r' & -> & E2 & Ep & Eo); rewrite E2; cbn [RES2];
      [split; [reflexivity|] | | split; [reflexivity|]]; (apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)]).
  Qed.

  Lemma RES2_bind_lock : forall (m : AM A) (f : A -> AM B) s1 s2 c r,
    LOCK m s1 s2 -> IEQ s1 s2 -> UW s1 c r ->
    (forall a r', UW s1 c r' -> m (mkW s1 c r) = ARun a (mkW s1 c r') -> RES2 (f a (mkW s1 c r')) (f a (mkW s2 c r'))) ->
    RES2 (abind m f (mkW s1 c r)) (abind m f (mkW s2 c r)).
  Proof.
    intros m f s1 s2 c r L HQ HU K. unfold abind. specialize (L c r).
    destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1; destruct L as (r' & -> & E2 & Ep & Eo); rewrite E2; cbn [RES2].
    - apply K; [exact (UW_regs _ _ _ _ HU Ep Eo) | reflexivity].
    - apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)].
    - split; [reflexivity|]. apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)].
  Qed.
End LockRules.

Lemma DECODE_k_LOCK : forall k p index need s1 s2,
  (forall h, code_at s2 p (index h) = code_at s1 p (index h)) ->
  LOCK (DECODE_k k p index need) s1 s2.
Proof.
  induction k as [|k IH]; intros p index need s1 s2 HC c r.
  - rewrite !DECODE_k_O. exists r. rewrite (HC _). repeat split; reflexivity.
  - rewrite !DECODE_k_S. rewrite (HC _).
    destruct (need (code_at s1 p (index (ir_hold r))) <=? ir_bits r).
    + exists r. repeat split; reflexivity.
    + destruct (ir_have r =? 0).
      * exists r. repeat split; reflexivity.
      * specialize (IH p index need s1 s2 HC c (pullr c r)).
        destruct (DECODE_k k p index need (mkW s1 c (pullr c r))) as [a w'|w'|x w'];
          destruct IH as (r' & E1 & E2 & Ep & Eo); exists r'; rewrite E2; (split; [exact E1|]); (split; [reflexivity|]);
          rewrite Ep, Eo; unfold pullr; cbn [ir_put ir_out]; split; reflexivity.
Qed.

Lemma DECODE_k_ret : forall k p index need s c r a w',
  DECODE_k k p index need (mkW s c r) = ARun a w' -> exists r', w' = mkW s c r' /\ a = code_at s p (index (ir_hold r')).
Proof.
  induction k as [|k IH]; intros p index need s c r a w' H.
  - rewrite DECODE_k_O in H. injection H; intros <- <-. exists r. split; reflexivity.
  - rewrite DECODE_k_S in H. destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r).
    + injection H; intros <- <-. exists r. split; reflexivity.
    + destruct (ir_have r =? 0); [discriminate H|]. exact (IH _ _ _ _ _ _ _ _ H).
Qed.

Lemma BITSv_bound : forall h n, 0 <= n < 32 -> 0 <= BITSv h n < 2 ^ n.
Proof.
  intros h n Hn. unfold BITSv. pose proof (wrap32_range h).
  rewrite land_zmask by lia. apply Z.mod_pos_bound. apply pow2_pos. lia.
Qed.

Lemma tbl_eq_DECODE1 : forall s1 s2 ty p root, tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  forall h, code_at s2 p (BITSv h root) = code_at s1 p (BITSv h root).
Proof.
  intros s1 s2 ty p root HT h. destruct p as [o| |]; cbn [code_at]; [|reflexivity|reflexivity].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE).
  pose proof (T_root _ _ _ _ HT). pose proof (T_used _ _ _ _ HT). pose proof (BITSv_bound h root ltac:(lia)).
  apply HE. lia.
Qed.

Lemma tbl_eq_DECODE2 : forall s1 s2 ty p root h0, tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  let last := code_at s1 p (BITSv h0 root) in
  match p with CDyn _ => is_linkb last = true | _ => True end ->
  forall h, code_at s2 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last))
            = code_at s1 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last)).
Proof.
  intros s1 s2 ty p root h0 HT last HL h. subst last. destruct p as [o| |]; cbn [code_at] in *; [|reflexivity|reflexivity].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE).
  pose proof (T_root _ _ _ _ HT). pose proof (BITSv_bound h0 root ltac:(lia)) as X0.
  destruct (root_cell _ _ _ _ HT (BITSv h0 root) X0) as (Hb & RL & _). destruct (RL HL) as (Hbr & Hop & Hv1 & Hv2).
  set (L := arr_get (is_codes s1) (o + BITSv h0 root)) in *.
  pose proof (BITSv_bound h (code_bits L + code_op L) ltac:(lia)) as X1.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= BITSv h (code_bits L + code_op L) / 2 ^ code_bits L < 2 ^ code_op L).
  { split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply pow2_pos; lia|]. rewrite <- Z.pow_add_r by lia. first [lia | rewrite Z.add_comm; lia]. }
  apply HE. lia.
Qed.

Definition shaped (ty : codetype) (e : Z) : Prop :=
  (exists sy, 0 <= sy < nsyms ty /\ code_op e = fst (sym_entry ty sy) /\ code_val e = snd (sym_entry ty sy)) \/ code_op e = 64.

Lemma dists_two_contra : forall e, shaped DISTS e -> (Z.land (code_op e) 240 =? 0) = true -> False.
Proof.
  intros e SH TW. apply Z.eqb_eq in TW.
  assert (NZ : code_op e <> 0).
  { destruct SH as [[sy (Hsy & Hop & Hv)]|Hop]; [|rewrite Hop; discriminate].
    cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv. rewrite Hop. destruct L as [(L & _)|[L _]]; lia. }
  exact (notlink_land240 DISTS e SH ltac:(discriminate) NZ TW).
Qed.
Lemma lens_two_contra : forall e, shaped LENS e -> (negb (code_op e =? 0) && (Z.land (code_op e) 240 =? 0)) = true -> False.
Proof.
  intros e SH TW. apply andb_prop in TW as [T1 T2].
  apply Bool.negb_true_iff in T1. apply Z.eqb_neq in T1. apply Z.eqb_eq in T2.
  exact (notlink_land240 LENS e SH ltac:(discriminate) T1 T2).
Qed.

Lemma tbl_eq_link : forall s1 s2 ty p root h0 (P : Z -> bool),
  tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  (forall e, shaped ty e -> P (code_op e) = true -> False) ->
  let last := code_at s1 p (BITSv h0 root) in
  P (code_op last) = true ->
  match p with CDyn _ => is_linkb last = true | _ => True end.
Proof.
  intros s1 s2 ty p root h0 P HT Hc last HP. subst last. destruct p as [o| |]; [|exact I|exact I].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE). cbn [code_at] in *.
  pose proof (T_root _ _ _ _ HT). pose proof (BITSv_bound h0 root ltac:(lia)) as X0.
  destruct (root_cell _ _ _ _ HT (BITSv h0 root) X0) as (Hb & RL & RN).
  destruct (is_linkb (arr_get (is_codes s1) (o + BITSv h0 root))) eqn:HL; [reflexivity|].
  exfalso. destruct (RN eq_refl) as [_ SH]. exact (Hc _ SH HP).
Qed.

Lemma IEQ_set_back : forall s1 s2 v, IEQ s1 s2 -> IEQ (iset_back s1 v) (iset_back s2 v).
Proof.
  intros s1 s2 v H. unfold IEQ in *; cbv zeta in *. sacc.
  destruct H as [A B]. split; [|exact B].
  decompose [and] A. repeat split; first [assumption | reflexivity].
Qed.
End RefInflateEqD.

Module RefInflateEqA1.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rstep lem := aflat; eapply RES2_step2; [apply lem | apply lem |]; cbv beta iota.
Ltac rstepr := aflat; eapply RES2_step2; [reflexivity | reflexivity |]; cbv beta iota.
Ltac rfin_run := cbn [RES2]; split; [reflexivity|].
Ltac rlast := unfold us, uc, ur; cbv beta iota delta [w_s w_c w_r wset_s wset_c wset_r]; rfin_run.
Ltac uw0 W5 F0 := apply UW_intro0; unfold fixedtables; sacc; [exact W5 | exact F0 | first [reflexivity | match goal with H : is_mode ?s = _ |- _ => rewrite H; reflexivity end]].
Ltac wmid E W5 F0 := apply WMID_mk; [ieq_close E | uw0 W5 F0].
Ltac notHB HU E W5 F0 := destruct (UW_notHB _ _ _ HU ltac:(rewrite E; first [discriminate | congruence]) ltac:(rewrite E; first [discriminate | congruence])) as [W5 F0].
Ltac lits := repeat (first [ progress change (Z.land 5 4 =? 0) with false | progress change (Z.land 5 2 =? 0) with true
                            | progress change (Z.land 5 1 =? 0) with false | progress change (5 =? 0) with false
                            | progress change (0 =? 0) with true ]); cbn [negb andb orb].
Ltac nrm s1 s2 W5 F0 := unfold fixedtables; sacc; ieq_rw s1 s2; rewrite ?W5, ?F0; lits.
Ltac rlock SF := eapply RES2_bind_lock; [apply SFREE_LOCK; apply SF | | |].

Section Simple.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_BAD_cong : forall F, arm_cong BAD F arm_BAD.
  Proof.
    intros F s1 s2 c r _ E HQ HU. unfold arm_BAD. apply RES2_sfree; [|exact HQ|exact HU].
    apply SFREE_bind; [apply SFREE_ur; intros; split; reflexivity | intros; apply SFREE_leave].
  Qed.
  Lemma arm_DONE_cong : forall M F, arm_cong M F arm_DONE.
  Proof.
    intros M F s1 s2 c r _ E HQ HU. unfold arm_DONE. apply RES2_sfree; [|exact HQ|exact HU].
    apply SFREE_bind; [apply SFREE_ur; intros; split; reflexivity | intros; apply SFREE_leave].
  Qed.
  Lemma arm_MEM_cong : forall F, arm_cong MEM F arm_MEM.
  Proof. intros F s1 s2 c r _ E HQ HU. unfold arm_MEM. apply RES2_return. apply WMID_mk; assumption. Qed.
  Lemma arm_SYNC_cong : forall F, arm_cong SYNC F arm_SYNC.
  Proof. intros F s1 s2 c r _ E HQ HU. unfold arm_SYNC. apply RES2_return. apply WMID_mk; assumption. Qed.

  Lemma arm_LIT_cong : arm_cong LIT FTrue arm_LIT.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LIT.
    rstep gr_eq. destruct (ir_left r =? 0).
    { apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU]. }
    rstep gs_eq. ieq_rw s1 s2.
    rstep uc_eq. rstep ur_eq. unfold set_mode, us. cbn [w_s w_c w_r wset_s]. rfin_run. wmid E W5 F0.
  Qed.

  Lemma arm_LENGTH_cong : forall M F, M <> HEAD -> M <> BAD -> arm_cong M F arm_LENGTH.
  Proof.
    intros M F NH NB s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LENGTH.
    rstep gs_eq. ieq_rw s1 s2. rewrite W5, F0. cbn [Z.eqb negb andb].
    rstep aret_eq. unfold set_mode. rstep us_eq.
    apply (arm_DONE_cong DONE FTrue); [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_CHECK_cong : arm_cong CHECK FTrue arm_CHECK.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. specialize (Qcheck F0). unfold arm_CHECK.
    rstep gs_eq. nrm s1 s2 W5 F0.
    aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta. aflat.
    rstep gr_eq. rstep ur_eq. rstep uc_eq. rstep us_eq. rstep gs_eq. unfold UPDATE_CHECK_bytes. nrm s1 s2 W5 F0.
    destruct (wrap32 (ir_out r1 - ir_left r1) =? 0); cbn [negb].
    - rstep aret_eq. rstep ur_eq. unfold HOLD. rstep gr_eq. rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (ZSWAP32 _ =? is_check s1); cbn [negb].
      + unfold INITBITS. rstep ur_eq. rstep aret_eq. unfold set_mode. rstep us_eq.
        apply (arm_LENGTH_cong LENGTH FTrue); [discriminate | discriminate | exact I | reflexivity | ieq_close E | uw0 W5 F0].
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
    - rstepr. unfold set_adler_check. rstep us_eq. rstep uc_eq. rstep ur_eq. unfold HOLD. rstep gr_eq. rstep gs_eq. nrm s1 s2 W5 F0.
      match goal with |- context [if ?cnd then _ else _] => destruct cnd end.
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
      + unfold INITBITS. rstep ur_eq. rstep aret_eq. unfold set_mode. rstep us_eq.
        apply (arm_LENGTH_cong LENGTH FTrue); [discriminate | discriminate | exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_TYPEDO_cong : forall M, M = TYPE \/ M = TYPEDO -> arm_cong M FTrue (arm_TYPEDO iv flush).
  Proof.
    intros M HM s1 s2 c r _ E HQ HU.
    assert (NH : M <> HEAD) by (destruct HM as [-> | ->]; discriminate).
    assert (NB : M <> BAD) by (destruct HM as [-> | ->]; discriminate).
    notHB HU E W5 F0. pose proof HQ as HQ0.
    assert (E' : is_mode s1 = TYPE \/ is_mode s1 = TYPEDO) by (rewrite E; exact HM).
    clear E HM. destruct E' as [E|E]; ieq_open HQ E; unfold arm_TYPEDO.
    all: rstep gs_eq; nrm s1 s2 W5 F0.
    all: destruct (negb (is_last s1 =? 0)).
    1,3: rlock SFREE_BYTEBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta;
         unfold set_mode; rlast; wmid E W5 F0.
    all: rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    all: unfold BITS at 1; rstep gr_eq; rstep us_eq; unfold DROPBITS at 1; rstep ur_eq; unfold BITS at 1; rstep gr_eq.
    all: destruct (BITSv _ 2 =? 0); [|destruct (BITSv _ 2 =? 1); [|destruct (BITSv _ 2 =? 2)]].
    all: unfold set_mode, go_bad, set_msg, set_mode, DROPBITS.
    1,5: rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.
    1,4: rstep us_eq; rstep us_eq; destruct (iv_flush_exits iv && (flush =? Z_TREES));
         [ rstep ur_eq; apply RES2_leave; wmid E W5 F0 | rstep aret_eq; rlast; wmid E W5 F0 ].
    1,3: rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.
    all: rstep uc_eq; rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.
  Qed.

  Lemma arm_TYPE_cong : arm_cong TYPE FTrue (arm_TYPE iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. unfold arm_TYPE.
    destruct (iv_flush_exits iv && ((flush =? Z_BLOCK) || (flush =? Z_TREES))).
    - apply RES2_leave. apply WMID_mk; assumption.
    - apply (arm_TYPEDO_cong TYPE (or_introl eq_refl) s1 s2 c r I E HQ HU).
  Qed.

  Lemma arm_COPY_cong : arm_cong COPY FTrue arm_COPY.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_COPY.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (negb (is_length s1 =? 0)).
    - rstep gr_eq.
      match goal with |- context [if ?cnd then aleave else _] => destruct cnd end.
      + apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU].
      + rstep uc_eq. rstep ur_eq. rlast. wmid E W5 F0.
    - unfold set_mode. rlast. wmid E W5 F0.
  Qed.

  Lemma arm_COPY__cong : arm_cong COPY_ FTrue arm_COPY_.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_COPY_, set_mode.
    rstep us_eq. apply arm_COPY_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_STORED_cong : arm_cong STORED FTrue (arm_STORED iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_STORED.
    rlock SFREE_BYTEBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    rlock SFREE_NEEDBITS; [exact HQ0 | exact HU1 |]; intros [] r2 HU2 _; cbv beta.
    unfold HOLD. rstep gr_eq.
    match goal with |- context [if ?cnd then _ else _] => destruct cnd end.
    - unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. wmid E W5 F0.
    - rstep us_eq. unfold INITBITS. rstep ur_eq. unfold set_mode at 1. rstep us_eq.
      destruct (iv_flush_exits iv && (flush =? Z_TREES)).
      + apply RES2_leave. wmid E W5 F0.
      + apply arm_COPY__cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_DICT_cong : arm_cong DICT FTrue (arm_DICT iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DICT.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (is_havedict s1 =? 0).
    - rstep amodify_eq. unfold RESTORE. cbn [w_s w_c w_r]. apply RES2_return. wmid E W5 F0.
    - unfold set_adler_check. rstep us_eq. rstep uc_eq. unfold set_mode at 1. rstep us_eq.
      apply arm_TYPE_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_DICTID_cong : arm_cong DICTID FTrue (arm_DICTID iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DICTID.
    rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    unfold HOLD. rstep gr_eq. unfold set_adler_check. rstep us_eq. rstep uc_eq. unfold INITBITS. rstep ur_eq.
    unfold set_mode at 1. rstep us_eq.
    apply arm_DICT_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.
End Simple.


Lemma UW_bad : forall s s' c r r', UW s c r -> is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_mode s' = BAD ->
  ir_put r' = ir_put r -> ir_out r' = ir_out r -> UW s' c r'.
Proof.
  intros s s' c r r' (W & G & F) Ew Ef Em Ep Eo. split; [rewrite Ew; exact W|]. rewrite Em. split; [reflexivity|].
  rewrite Ef, Ep, Eo. destruct F as [F|(F & _ & P & O)]; [left; exact F | right]. repeat split; try assumption. right; reflexivity.
Qed.

Section Head.
  Variable iv : ivariant.

  Lemma arm_HEAD_cong : arm_cong HEAD FTrue (arm_HEAD iv).
  Proof.
    intros s1 s2 c r _ E HQ HU. pose proof HQ as HQ0. pose proof HU as [W5 HF]. ieq_open HQ E. unfold arm_HEAD.
    rstep gs_eq. nrm s1 s2 W5 W5.
    aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta.
    pose proof HU1 as [_ HF1].
    assert (PO : ir_put r1 = ir_put r1 /\ ir_out r1 = ir_out r1) by (split; reflexivity).
    unfold HOLD. rstep gr_eq. lits.
    unfold BITS at 1. aflat. rstep gr_eq.
    match goal with |- context [if ?cnd then go_bad _ else _] => destruct cnd end.
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }
    unfold BITS at 1. rstep gr_eq.
    destruct (negb (BITSv (ir_hold r1) 4 =? Z_DEFLATED)).
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }
    unfold DROPBITS at 1. rstep ur_eq. unfold BITS at 1. rstep gr_eq.
    rstep gs_eq. sacc. ieq_rw s1 s2.
    match goal with |- context [if ?cnd then go_bad _ else _] => destruct cnd end.
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }
    assert (STEP : forall (K : AM unit) ,
      (forall s1' s2', IEQ s1' s2' -> is_wrap s1' = 5 -> is_flags s1' = is_flags s1 -> is_mode s1' = HEAD ->
         RES2 (K (mkW s1' c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))
              (K (mkW s2' c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))) ->
      RES2 (((if is_wbits s1 =? 0 then us (fun s : inflate_state => iset_wbits s (BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8)) else aret tt);; K)%am
              (mkW s1 c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))
           (((if is_wbits s1 =? 0 then us (fun s : inflate_state => iset_wbits s (BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8)) else aret tt);; K)%am
              (mkW s2 c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))).
    { intros K HK. destruct (is_wbits s1 =? 0).
      - rstep us_eq. apply HK; [ieq_close E | sacc; exact W5 | reflexivity | sacc; exact E].
      - rstep aret_eq. apply HK; [exact HQ0 | exact W5 | reflexivity | exact E]. }
    sacc. apply STEP. clear STEP. intros s1' s2' HQ' W5' EF' E'. clear Qmode Qlast Qwrap Qhavedict Qflags Qdmax Qtotal Qhead Qwbits Qwsize Qwhave Qwnext Qwblk Qhold Qbits Qlencode Qdistcode Qnext Qsane Qback Qself QLwin QLlens QLwork QLcodes Qcheck Qwin.
    pose proof HQ' as HQ1. ieq_open HQ' E'.
    unfold aux. destruct (iv_aux iv); cbv iota; [rstep us_eq|rstep aret_eq]; rstep us_eq; unfold set_adler_check; aflat; rstep us_eq; rstep uc_eq;
      unfold HOLD; rstep gr_eq; unfold set_mode; rstep us_eq; unfold INITBITS; rlast;
      match goal with |- context [if ?cnd then DICTID else TYPE] => destruct cnd end;
      (apply WMID_mk; [ ieq_close E' | apply UW_intro0; sacc; [exact W5' | reflexivity | reflexivity] ]).
  Qed.
End Head.


Lemma arm_gz_cong : forall M F (arm : AM unit), gzb M = true -> arm_cong M F arm.
Proof.
  intros M F arm HM s1 s2 c r _ E HQ HU. exfalso. pose proof (UW_gz _ _ _ HU) as G. rewrite E, HM in G. discriminate G.
Qed.
End RefInflateEqA1.

Module RefInflateEqA2.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA1.
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


Lemma match_copy_out : forall m win1 win2 ob put i, Z.of_nat (S m) < 2 ^ 32 ->
  match_copy win2 (ob, put, FOut i, Z.of_nat (S m)) = match_copy win1 (ob, put, FOut i, Z.of_nat (S m)).
Proof.
  induction m as [|m IH]; intros win1 win2 ob put i Hm.
  - rewrite !match_copy_step by (cbn; lia). reflexivity.
  - rewrite !match_copy_step by lia. cbv zeta. cbn [from_succ].
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia. apply IH. lia.
Qed.

Lemma match_copy_win : forall m win1 win2 ob put i, Z.of_nat (S m) < 2 ^ 32 ->
  (forall j, i <= j < i + Z.of_nat (S m) -> arr_get win2 j = arr_get win1 j) ->
  match_copy win2 (ob, put, FWin i, Z.of_nat (S m)) = match_copy win1 (ob, put, FWin i, Z.of_nat (S m)).
Proof.
  induction m as [|m IH]; intros win1 win2 ob put i Hm Hw.
  - rewrite !match_copy_step by (cbn; lia). cbv zeta. rewrite (Hw i) by (cbn; lia). reflexivity.
  - rewrite !match_copy_step by lia. cbv zeta. cbn [from_succ]. rewrite (Hw i) by lia.
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia. apply IH; [lia|]. intros j Hj. apply Hw. lia.
Qed.

Lemma match_copy_cong : forall win1 win2 ob put from n, 1 <= n < 2 ^ 32 ->
  (forall i j, from = FWin i -> i <= j < i + n -> arr_get win2 j = arr_get win1 j) ->
  match_copy win2 (ob, put, from, n) = match_copy win1 (ob, put, from, n).
Proof.
  intros win1 win2 ob put from n Hn Hw.
  replace n with (Z.of_nat (S (Z.to_nat (n - 1)))) in * by lia.
  destruct from as [i|i].
  - apply match_copy_win; [lia|]. intros j Hj. apply (Hw i j eq_refl). lia.
  - apply match_copy_out. lia.
Qed.

Section Code.
  Definition iv : ivariant := ivar_ref.
  Variable flush : Z.
  Ltac auxt := cbv beta iota delta [set_back add_back aux iv_aux iv ivar_ref].


  Lemma match_copy_agree : forall s1 s2 ob put from n,
    (forall i, 0 <= i < is_whave s1 -> arr_get (is_window s2) i = arr_get (is_window s1) i) ->
    n < 2 ^ 32 ->
    (forall i, from = FWin i -> 1 <= n -> 0 <= i /\ i + n <= is_whave s1) ->
    match_copy (is_window s2) (ob, put, from, n) = match_copy (is_window s1) (ob, put, from, n).
  Proof.
    intros s1 s2 ob put from n Qwin Hn Hfrom.
    destruct (Z.lt_ge_cases n 1) as [Z0|Z0].
    - unfold match_copy. cbn [snd]. rewrite !loopZ_le0 by lia. reflexivity.
    - apply match_copy_cong; [lia|]. intros i j Ei Hj. apply Qwin. destruct (Hfrom i Ei Z0). lia.
  Qed.

  Ltac mc_step MC1 MC2 :=
    aflat; eapply RES2_step2;
    [ cbv beta; cbn [w_s w_c w_r wset_c wset_r]; sacc; rewrite MC1; reflexivity
    | cbv beta; cbn [w_s w_c w_r wset_c wset_r]; sacc; rewrite MC2; reflexivity | ].

  Lemma arm_MATCH_cong : arm_cong MATCH FCore (arm_MATCH iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_MATCH.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    rstep gr_eq. destruct (ir_left r =? 0).
    { apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU]. }
    rstep gs_eq. nrm s1 s2 W5 F0.
    set (copy := wrap32 (ir_out r - ir_left r)). pose proof (wrap32_range (ir_out r - ir_left r)) as CR. fold copy in CR.
    destruct (Z.ltb_spec copy (is_offset s1)) as [Cw|Cw].
    -
      set (copy' := wrap32 (is_offset s1 - copy)). pose proof (wrap32_range (is_offset s1 - copy)) as CR'. fold copy' in CR'.
      destruct ((is_whave s1 <? copy') && (if iv_aux iv then negb (is_sane s1 =? 0) else true)) eqn:G.
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
      + assert (Gw : copy' <= is_whave s1).
        { rewrite C13 in G. destruct (Z.ltb_spec (is_whave s1) copy'); [|lia]. exfalso. destruct (iv_aux iv); discriminate G. }
        assert (Hcf : exists cp from, (if is_wnext s1 <? copy' then (wrap32 (copy' - is_wnext s1), FWin (is_wsize s1 - wrap32 (copy' - is_wnext s1))) else (copy', FWin (is_wnext s1 - copy')))
                                     = (cp, from) /\ 0 <= cp <= copy'
                                     /\ forall i, from = FWin i -> 0 <= i /\ i + cp <= is_whave s1).
        { destruct (Z.ltb_spec (is_wnext s1) copy') as [W1|W1].
          - eexists _, _. split; [reflexivity|]. rewrite wrap32_id by lia. split; [lia|].
            intros i Ei. injection Ei; intros <-.
            assert (WS : is_wsize s1 <> 0) by (intros Z0; destruct (C6 Z0); lia).
            destruct (C7 WS) as [N1 N2].
            assert (is_whave s1 = is_wsize s1) by (destruct (Z.eq_dec (is_whave s1) (is_wsize s1)); [assumption|]; pose proof (C8 WS ltac:(lia)); lia).
            lia.
          - eexists _, _. split; [reflexivity|]. split; [lia|]. intros i Ei. injection Ei; intros <-.
            destruct (Z.eq_dec (is_wsize s1) 0) as [Z0|WS]; [destruct (C6 Z0); lia|].
            destruct (C7 WS) as [N1 N2].
            destruct (Z.lt_ge_cases (is_whave s1) (is_wsize s1)) as [L|L]; [pose proof (C8 WS L); lia | lia]. }
        destruct Hcf as (cp & from & Ecf & Hcp & Hfrom). rewrite Ecf.
        rstep aret_eq.
        set (cp2 := if is_length s1 <? cp then is_length s1 else cp).
        set (cp3 := if ir_left r <? cp2 then ir_left r else cp2).
        assert (Hcp3 : cp3 <= cp) by (subst cp3 cp2; destruct (Z.ltb_spec (is_length s1) cp); destruct (Z.ltb_spec (ir_left r) (is_length s1)); destruct (Z.ltb_spec (ir_left r) cp); lia).
        rstep ur_eq. rstep us_eq.
        destruct (match_copy (is_window s1) (ic_outbuf c, ir_put r, from, cp3)) as [[[ob put'] fr'] cc] eqn:MC1.
        assert (MC2 : match_copy (is_window s2) (ic_outbuf c, ir_put r, from, cp3) = (ob, put', fr', cc)).
        { rewrite <- MC1. apply match_copy_agree; [exact Qwin | lia |]. intros i Ei Hn. destruct (Hfrom i Ei). lia. }
        mc_step MC1 MC2.
        rstep gs_eq. nrm s1 s2 W5 F0.
        destruct (wrap32 (is_length s1 - cp3) =? 0); [unfold set_mode; rlast | apply RES2_ret]; wmid E W5 F0.
    -
      rstep aret_eq.
      set (cp3 := if ir_left r <? is_length s1 then ir_left r else is_length s1).
      assert (Hcp3 : cp3 <= is_length s1) by (subst cp3; destruct (Z.ltb_spec (ir_left r) (is_length s1)); lia).
      rstep ur_eq. rstep us_eq.
      destruct (match_copy (is_window s1) (ic_outbuf c, ir_put r, FOut (ir_put r - is_offset s1), cp3)) as [[[ob put'] fr'] cc] eqn:MC1.
      assert (MC2 : match_copy (is_window s2) (ic_outbuf c, ir_put r, FOut (ir_put r - is_offset s1), cp3) = (ob, put', fr', cc)).
      { rewrite <- MC1. apply match_copy_agree; [exact Qwin | lia |]. intros i Ei. discriminate Ei. }
      mc_step MC1 MC2.
      rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (wrap32 (is_length s1 - cp3) =? 0); [unfold set_mode; rlast | apply RES2_ret]; wmid E W5 F0.
  Qed.

  Lemma land_65535_32 : forall a, 0 <= Z.land a 65535 < 2 ^ 32.
  Proof. intros a. pose proof (land_65535 a). lia. Qed.

  Ltac core_of HC := apply (CORE_keep _ _ HC); unfold fixedtables; sacc; rewrite ?arr_len_set; try reflexivity; try (apply CORE_length; exact HC); try apply wrap32_range; try (unfold code_val; apply land_65535_32).


  Lemma arm_DISTEXT_cong : arm_cong DISTEXT FCore (arm_DISTEXT iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DISTEXT.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (negb (is_extra s1 =? 0)).
    - aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta.
      unfold BITS. rstep gr_eq. rstep us_eq. nrm s1 s2 W5 F0. unfold DROPBITS. rstep ur_eq. unfold add_back, aux.
      destruct (iv_aux iv).
      + rstep us_eq. nrm s1 s2 W5 F0. unfold set_mode at 1. rstep us_eq.
        apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
      + rstep aret_eq. unfold set_mode at 1. rstep us_eq.
        apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
    - rstep aret_eq. unfold set_mode at 1. rstep us_eq.
      apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.


  Lemma dist_tail_cong : forall here0 s1 s2 c r, CORE s1 -> is_mode s1 = DIST -> IEQ s1 s2 -> UW s1 c r ->
    RES2 ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           (if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s : inflate_state => iset_extra (iset_offset s (code_val here0)) (Z.land (code_op here0) 15));; set_mode DISTEXT;; arm_DISTEXT iv))%am (mkW s1 c r))
         ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           (if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s : inflate_state => iset_extra (iset_offset s (code_val here0)) (Z.land (code_op here0) 15));; set_mode DISTEXT;; arm_DISTEXT iv))%am (mkW s2 c r)).
  Proof.
    intros here0 s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    unfold DROPBITS. rstep ur_eq. unfold add_back, aux.
    destruct (iv_aux iv); [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0.
    all: destruct (negb (Z.land (code_op here0) 64 =? 0));
      [ unfold go_bad, set_msg, set_mode; rstep uc_eq; rlast; wmid E W5 F0
      | rstep us_eq; unfold set_mode at 1; rstep us_eq; apply arm_DISTEXT_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0] ].
  Qed.

  Lemma arm_DIST_cong : arm_cong DIST FCore (arm_DIST iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DIST.
    rstep gs_eq. nrm s1 s2 W5 F0.
    unfold DECODE1 at 1 2. aflat. eapply RES2_bind_lock; [apply DECODE_k_LOCK; intros h; exact (tbl_eq_DECODE1 s1 s2 DISTS _ _ QtblD h) | exact HQ0 | exact HU |].
    intros here r1 HU1 E1. cbv beta.
    destruct (DECODE_k_ret _ _ _ _ _ _ _ _ _ E1) as (r1' & Ew & Ehere). injection Ew; intros <-.
    destruct (Z.land (code_op here) 240 =? 0) eqn:T240.
    - aflat. unfold DECODE2 at 1 2. eapply RES2_bind_lock; [ | exact HQ0 | exact HU1 |].
      { apply DECODE_k_LOCK. intros h. rewrite Ehere. apply (tbl_eq_DECODE2 s1 s2 DISTS _ _ (ir_hold r1) QtblD).
        apply (tbl_eq_link s1 s2 DISTS _ _ (ir_hold r1) (fun op => Z.land op 240 =? 0) QtblD dists_two_contra). rewrite <- Ehere. exact T240. }
      intros here2 r2 HU2 E2. cbv beta. unfold DROPBITS at 1 3. rstep ur_eq. unfold add_back at 1 3. unfold aux.
      destruct (iv_aux iv) eqn:AUX; [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; rstep aret_eq.
      + apply dist_tail_cong; [core_of HC | sacc; exact E | ieq_close E | uw0 W5 F0].
      + apply dist_tail_cong; [exact HC | exact E | exact HQ0 | eapply UW_regs; [exact HU2 | reflexivity | reflexivity]].
    - rstep aret_eq. apply dist_tail_cong; [exact HC | exact E | exact HQ0 | exact HU1].
  Qed.


  Ltac to_DIST HC E W5 F0 s1 s2 :=
    first [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; unfold set_mode at 1; rstep us_eq;
    apply arm_DIST_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].

  Lemma arm_LENEXT_cong : arm_cong LENEXT FCore (arm_LENEXT iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LENEXT, add_back, aux.
    destruct (iv_aux iv); cbv iota.
    all: rstep gs_eq; nrm s1 s2 W5 F0.
    all: destruct (negb (is_extra s1 =? 0)); [| rstep aret_eq; to_DIST HC E W5 F0 s1 s2].
    all: aflat; rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    all: unfold BITS; rstep gr_eq; rstep us_eq; nrm s1 s2 W5 F0; unfold DROPBITS; rstep ur_eq.
    all: first [rstep us_eq; nrm s1 s2 W5 F0 | rstep aret_eq]; to_DIST HC E W5 F0 s1 s2.
  Qed.


  Definition FASTC : Prop := forall s1 s2 c r,
    CORE s1 -> is_mode s1 = LEN -> IEQ s1 s2 -> UW s1 c r -> 6 <= ir_have r -> 258 <= ir_left r ->
    RES2 (amodify (fun w => LOAD (inflate_fast (RESTORE w))) (mkW s1 c r))
         (amodify (fun w => LOAD (inflate_fast (RESTORE w))) (mkW s2 c r)).
  Hypothesis fastc : FASTC.

  Lemma len_tail_cong : forall here0 s1 s2 c r, CORE s1 -> is_mode s1 = LEN -> IEQ s1 s2 -> UW s1 c r ->
    RES2 ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           us (fun s : inflate_state => iset_length s (code_val here0));;
           (if code_op here0 =? 0 then set_mode LIT
            else if negb (Z.land (code_op here0) 32 =? 0) then set_back iv (-1);; set_mode TYPE
            else if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_literal_length_code
            else us (fun s : inflate_state => iset_extra s (Z.land (code_op here0) 15));; set_mode LENEXT;; arm_LENEXT iv))%am (mkW s1 c r))
         ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           us (fun s : inflate_state => iset_length s (code_val here0));;
           (if code_op here0 =? 0 then set_mode LIT
            else if negb (Z.land (code_op here0) 32 =? 0) then set_back iv (-1);; set_mode TYPE
            else if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_literal_length_code
            else us (fun s : inflate_state => iset_extra s (Z.land (code_op here0) 15));; set_mode LENEXT;; arm_LENEXT iv))%am (mkW s2 c r)).
  Proof.
    intros here0 s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    unfold DROPBITS, add_back, set_back, aux. rstep ur_eq.
    destruct (iv_aux iv); cbv iota; [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; rstep us_eq.
    all: destruct (code_op here0 =? 0); [unfold set_mode; rlast; wmid E W5 F0|].
    all: destruct (negb (Z.land (code_op here0) 32 =? 0)); [first [rstep us_eq | rstep aret_eq]; unfold set_mode; rlast; wmid E W5 F0|].
    all: destruct (negb (Z.land (code_op here0) 64 =? 0)); [unfold go_bad, set_msg, set_mode; rstep uc_eq; rlast; wmid E W5 F0|].
    all: rstep us_eq; unfold set_mode at 1; rstep us_eq; apply arm_LENEXT_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_LEN_cong : arm_cong LEN FCore (arm_LEN iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LEN.
    rstep gr_eq.
    destruct (iv_fast iv && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) eqn:FP.
    - apply andb_prop in FP as [FP _].
      apply andb_prop in FP as [FP F2]. apply andb_prop in FP as [_ F1]. apply Z.leb_le in F1. apply Z.leb_le in F2.
      aflat. eapply RES2_bind; [exact (fastc s1 s2 c r HC E HQ0 HU F1 F2)|].
      intros [] s1' s2' c' r' HQ' HU' _. 
      rstep gs_eq. pose proof HQ' as HQ1. 
      destruct HQ' as ((Qm & _) & _). rewrite Qm.
      destruct (Z.eqb_spec (is_mode s1') TYPE) as [ET|ET].
      + auxt. rlast. apply WMID_mk.
        * apply IEQ_set_back. exact HQ1.
        * destruct HU' as (W' & G' & D'). split; [exact W'|]. sacc. split; [exact G'|]. destruct D' as [D'|(D' & M' & P')]; [left; exact D'|right]. exact (conj D' (conj M' P')).
      + apply RES2_ret. apply WMID_mk; assumption.
    - auxt. rstep us_eq.
      all: rstep gs_eq; nrm s1 s2 W5 F0.
      all: unfold DECODE1 at 1 2; aflat; eapply RES2_bind_lock; [apply DECODE_k_LOCK; intros h; exact (tbl_eq_DECODE1 s1 s2 LENS _ _ QtblL h) | first [exact HQ0 | ieq_close E] | first [exact HU | uw0 W5 F0] |].
      all: intros here r1 HU1 E1; cbv beta.
      all: destruct (DECODE_k_ret _ _ _ _ _ _ _ _ _ E1) as (r1' & Ew & Ehere); injection Ew; intros <-.
      all: destruct (negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0)) eqn:T2.
      1: aflat; unfold DECODE2 at 1 2; eapply RES2_bind_lock; [ | first [exact HQ0 | ieq_close E] | exact HU1 |];
        [ apply DECODE_k_LOCK; intros h; rewrite Ehere; sacc; apply (tbl_eq_DECODE2 s1 s2 LENS _ _ (ir_hold r1) QtblL);
          apply (tbl_eq_link s1 s2 LENS _ _ (ir_hold r1) (fun op => negb (op =? 0) && (Z.land op 240 =? 0)) QtblL lens_two_contra); revert T2; rewrite Ehere; sacc; intros T2; exact T2
        | ].
      1: intros here2 r2 HU2 E2; cbv beta; unfold DROPBITS at 1 3; rstep ur_eq;
           rstep us_eq; nrm s1 s2 W5 F0; rstep aret_eq;
           (apply len_tail_cong; [core_of HC | sacc; exact E | ieq_close E | uw0 W5 F0]).
      all: rstep aret_eq; apply len_tail_cong; [core_of HC | sacc; exact E | first [exact HQ0 | ieq_close E] | first [exact HU1 | uw0 W5 F0]].
  Qed.

  Lemma arm_LEN__cong : arm_cong LEN_ FCore (arm_LEN_ iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LEN_, set_mode.
    rstep us_eq. apply arm_LEN_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.
End Code.
End RefInflateEqA2.

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


Section FastLoop.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable usedL : Z.
Variable usedD : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis Xend : x_end x + 257 = ON.
  Hypothesis Xdm : x_dmask x = zmask (is_distbits s).
  Hypothesis Xlm : x_lmask x = zmask (is_lenbits s).
  Hypothesis HTL : TBLg LENS (code_at s (is_lencode s)) (is_lenbits s) usedL.
  Hypothesis HTD : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) usedD.

  Definition fstep (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
    | FBreak f' mode msg => inr (f', Some (mode, msg))
    end.

  Definition LPOST (f : ffs) (res : ffs * option (Z * option Z)) : Prop :=
    let '(f', mm) := res in
    FB ON f' /\ f_in f <= f_in f' <= x_last x + 5 /\ f_out f <= f_out f' <= ON
    /\ lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold (fpull2_if x f)) <= 8 * (f_in f' - f_in f) + f_bits f - f_bits f'
    /\ (mm = None \/ exists m msg, mm = Some (m, msg) /\ break_ok m msg).

  Lemma fast_loop_nat : forall m f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= x_last x + 5 -> f_out f + 258 <= ON ->
    8 * (x_last x + 5 - f_in f) + f_bits f + (ON - f_out f) < Z.of_nat m ->
    LPOST f (iterZ (Z.of_nat m) fstep (fun f0 => (f0, None)) f).
  Proof.
    induction m as [|m IH]; intros f HF Hbeg Hin Hout HM.
    { exfalso. unfold FB in HF. cbn in HM. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    pose proof (fast_trip_spec x s ON usedL usedD Xin Xwn Xbeg HON Xdm Xlm HTL HTD f HF Hbeg Hout) as TS.
    cbv zeta in TS. destruct TS as (Hmod & Hc & T1 & T2).
    unfold fstep at 1. destruct (fast_trip x s f) as [f'|f' md msg].
    - destruct T1 as (HF' & Hi' & Ho' & Hcons).
      destruct (Z.ltb_spec (f_in f') (x_last x)); destruct (Z.ltb_spec (f_out f') (x_end x)); cbn [andb].
      +
        specialize (IH f' HF' ltac:(lia) ltac:(lia) ltac:(lia)).
        assert (HM' : 8 * (x_last x + 5 - f_in f') + f_bits f' + (ON - f_out f') < Z.of_nat m) by lia.
        specialize (IH HM'). unfold LPOST in *. destruct (iterZ (Z.of_nat m) fstep _ f') as [f'' mm].
        destruct IH as (A & B & C & D & E).
        pose proof (lneedg_range _ _ _ _ HTL (f_hold (fpull2_if x f'))) as [LR _].
        split; [exact A|]. split; [lia|]. split; [lia|]. split; [lia|exact E].
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
    - destruct T1 as (HF' & Hi' & Ho' & Hcons).
      unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exists md, msg. split; [reflexivity|exact T2].
  Qed.

  Lemma fast_loop_spec : forall n f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= x_last x + 5 -> f_out f + 258 <= ON ->
    8 * (x_last x + 5 - f_in f) + f_bits f + (ON - f_out f) < n ->
    LPOST f (iterZ n fstep (fun f0 => (f0, None)) f).
  Proof.
    intros n f HF Hbeg Hin Hout HM.
    assert (Hn : 0 <= n) by (unfold FB in HF; lia).
    rewrite <- (Z2Nat.id n) by exact Hn. apply fast_loop_nat; try assumption. rewrite Z2Nat.id by exact Hn. exact HM.
  Qed.
End FastLoop.


Lemma fpull2_if_mod : forall x ON f, (forall i, 0 <= arr_get (x_input x) i < 256) -> FB ON f ->
  f_hold (fpull2_if x f) mod 2 ^ f_bits f = f_hold f.
Proof.
  intros x ON f Xin HF. pose proof HF as (B1 & B2 & B3 & B4 & B5). unfold fpull2_if.
  destruct (Z.ltb_spec (f_bits f) 15) as [L|L].
  - destruct (FB_fpull x ON Xin f HF ltac:(lia)) as (HP1 & _ & _ & P1b & P1m & _).
    destruct (FB_fpull x ON Xin (fpull x f) HP1 ltac:(lia)) as (HP2 & _ & _ & P2b & P2m & _).
    rewrite <- P1m. rewrite <- P2m at 1. rewrite P1b. symmetry. apply (mod_down (f_bits f) (f_bits f + 8)); [lia|].
    rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
  - apply Z.mod_small. lia.
Qed.

Section LenArm.

  Lemma inflate_fast_post : forall w0 s c r,
    WINV (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r -> PHI (mkW s c r) <= PHI w0 ->
    POST w0 ((amodify (fun w => LOAD (inflate_fast (RESTORE w))) ;;
              do s0 <- gs (fun s0 => s0) ;
              if is_mode s0 =? TYPE then set_back ivar_ref (-1) else aret tt)%am (mkW s c r)).
  Proof.
    intros w0 s c r HW E Hh6 Hl258 HP.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hbx & Htb). pose proof (CORE_length s HC) as HL0.
    pose proof HC as (_ & _ & _ & _ & CW5 & _).
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (usedL & HTL & _).
    destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (usedD & HTD & _).
    pose proof (T_root _ _ _ _ HTL) as RL15. pose proof (T_root _ _ _ _ HTD) as RD15.
    assert (Hb14 : ir_bits r <= 14).
    { destruct Hbx as [Hbx|Hbx]; [lia|]. rewrite lneed_lneedg in Hbx. pose proof (lneedg_range _ _ _ _ HTL (ir_hold r)). lia. }
    arun amodify_eq. unfold RESTORE. cbn [w_s w_c w_r].
    set (sR := iset_bits (iset_hold s (ir_hold r)) (ir_bits r)).
    set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)).
    rewrite inflate_fast_eq.
    set (x := ffx_of sR cR r).
    assert (HX : x_input x = ic_input c /\ x_last x = ir_next r + ir_have r - 5 /\ x_beg x = 0 /\ x_end x = ir_put r + ir_left r - 257
                 /\ x_wnext x = is_wnext s /\ x_dmask x = zmask (is_distbits sR) /\ x_lmask x = zmask (is_lenbits sR)).
    { subst x sR cR. unfold ffx_of. cbn [x_input x_last x_beg x_end x_wnext x_dmask x_lmask]. sacc.
      rewrite !wrap32_id by lia. repeat split; try reflexivity; lia. }
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    assert (HTL' : TBLg LENS (code_at sR (is_lencode sR)) (is_lenbits sR) usedL) by exact HTL.
    assert (HTD' : TBLg DISTS (code_at sR (is_distcode sR)) (is_distbits sR) usedD) by exact HTD.
    assert (EsR : is_hold sR = ir_hold r /\ is_bits sR = ir_bits r /\ is_lenbits sR = is_lenbits s /\ code_at sR (is_lencode sR) = code_at s (is_lencode s))
      by (subst sR; repeat split; reflexivity).
    destruct EsR as (EsRh & EsRb & EsRl & EsRc).
    set (ON := arr_len (ic_outbuf c)).
    assert (HF0 : FB ON (ff0_of sR cR)).
    { subst sR cR. unfold ff0_of, FB. cbn [f_in f_out f_bits f_hold f_ob]. sacc. repeat split; try lia. }
    unfold ff_loop. fold x. fold (fstep x sR).
    pose proof (fast_loop_spec x sR ON usedL usedD ltac:(rewrite X1; exact RIN) ltac:(rewrite X5; exact CW5) ltac:(rewrite X3; lia)
                  ltac:(subst ON; lia) ltac:(rewrite X4; subst ON; lia) X6 X7 HTL' HTD'
                  (8 * ic_avail_in cR + ic_avail_out cR + 80) (ff0_of sR cR) HF0) as L.
    pose proof (fpull2_if_mod x ON _ ltac:(rewrite X1; exact RIN) HF0) as HM.
    subst cR. unfold ff0_of in L, HM |- *. cbn [f_in f_out f_bits f_hold] in L, HM. rewrite EsRh, EsRb in L, HM |- *.
    revert L HM. sacc. intros L HM.
    specialize (L ltac:(lia) ltac:(lia) ltac:(subst ON; lia) ltac:(subst ON; lia)).
    unfold LPOST in L.
    match goal with |- POST _ (_ (LOAD (let '(f, mm) := ?it in _))) => destruct it as [f mm] end.
    destruct L as (HFf & Hin & Hout & Hcons & Hmm). pose proof HFf as (B1 & B2 & B3 & B4 & B5).
    cbn [f_in f_out f_bits f_hold] in Hin, Hout, Hcons, HM. rewrite EsRl, EsRc in Hcons.
    lazymatch type of Hcons with lneedg ?g ?rt ?h <= _ => pose proof (lneedg_range _ _ _ _ HTL h) as [LR _] end.
    assert (Hc8 : ir_bits r - 8 < 8 * (f_in f - ir_next r) + ir_bits r - f_bits f).
    { destruct Hbx as [Hbx|Hbx]; [lia|].
      rewrite lneed_lneedg in Hbx.
      pose proof (lneedg_mono LENS _ _ usedL HTL (ir_hold r) _ (ir_bits r) ltac:(lia) ltac:(rewrite HM; symmetry; apply Z.mod_small; lia) Hbx) as MONO. lia. }
    pose proof (Z.div_mod (f_bits f) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)) as M8.
    pose proof (Z.div_pos (f_bits f) 8 ltac:(lia) ltac:(lia)) as Q8.
    pose proof (mod_pow2_range (f_hold f) (f_bits f mod 8) ltac:(lia)) as HM8.
    rewrite ff_fin_eq by lia.
    unfold ff_post. cbn [f_in f_out f_hold f_bits f_ob].
    rewrite X2, X4.
    replace (if f_in f - f_bits f / 8 <? ir_next r + ir_have r - 5 then 5 + (ir_next r + ir_have r - 5 - (f_in f - f_bits f / 8)) else 5 - (f_in f - f_bits f / 8 - (ir_next r + ir_have r - 5)))
      with (ir_next r + ir_have r - (f_in f - f_bits f / 8)) by (destruct (_ <? _); lia).
    replace (if f_out f <? ir_put r + ir_left r - 257 then 257 + (ir_put r + ir_left r - 257 - f_out f) else 257 - (f_out f - (ir_put r + ir_left r - 257)))
      with (ir_put r + ir_left r - f_out f) by (destruct (_ <? _); lia).
    rewrite !wrap32_id by (subst ON; lia).
    assert (CASES : mm = None \/ mm = Some (TYPE, None) \/ exists mg, mm = Some (BAD, Some mg)).
    { destruct Hmm as [->|(m & msg & -> & [[-> ->]|[-> Hm]])]; [left; reflexivity|right; left; reflexivity|].
      right; right. destruct msg as [mg|]; [exists mg; reflexivity|congruence]. }
    destruct CASES as [-> | [-> | [mg ->]]]; cbv iota beta; unfold LOAD; cbn [w_s w_c w_r]; subst sR; sacc.
    - arun gs_eq. sacc. rewrite E. change (LEN =? TYPE) with false. cbv iota. rewrite aret_eq. apply POST_ARun.
      + winv_splitE E.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * split; [common_keep HCm|]. split; [left; lia|tables_keep Htb].
        * rewrite B5. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
    - arun gs_eq. sacc. change (TYPE =? TYPE) with true. cbv iota. rewrite set_back_ref. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * split; [common_keep HCm|lia].
        * rewrite B5. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
    - arun gs_eq. sacc. change (BAD =? TYPE) with false. cbv iota. rewrite aret_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * exact (proj2 HCm).
        * exact I.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
  Qed.
End LenArm.


Section LenSlow.

  Lemma len_tail : forall w0 s c r here,
    CORE s -> REGS c r -> is_mode s = LEN -> common s -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
    ((exists sy, 0 <= sy < nsyms LENS /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
    POST w0 ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
              us (fun s0 => iset_length s0 (code_val here)) ;;
              if code_op here =? 0 then set_mode LIT
              else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
              else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
              else us (fun s0 => iset_extra s0 (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am
             (mkW s c r)).
  Proof.
    intros w0 s c r here HC HR E HCm Htb HWF HWB Hcb Hb8 Hsh HP.
    regs_open HR. pose proof (CORE_length s HC) as HL0.
    pose proof (code_val_nonneg here) as HV0.
    assert (HV16 : code_val here < 65536) by (unfold code_val; pose proof (land_65535 (Z.shiftr here 16)); lia).
    aflat. arun DROPBITS_eq. aflat. arun add_back_ref. aflat. arun us_eq. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
    set (r1 := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)).
    assert (HRd : REGS c r1).
    { subst r1. apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
    set (s1 := iset_length (iset_back s (swrap32 (is_back s + code_bits here))) (code_val here)).
    assert (HC1 : CORE s1) by (subst s1; core_keep HC; lia).
    assert (BADc : POST w0 ((go_bad MSG_invalid_literal_length_code) (mkW s1 c r1))).
    { unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. subst s1. sacc. lia.
        + eapply REGS_cview; [exact HRd|reflexivity|reflexivity].
        + exact (proj2 HCm).
        + exact I.
        + subst r1. sacc. exact HWB.
      - phi_goal. subst r1. sacc. lia. }
    assert (TYPEc : POST w0 ((set_back ivar_ref (-1) ;; set_mode TYPE)%am (mkW s1 c r1))).
    { arun set_back_ref. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. subst s1. sacc. lia.
        + exact HRd.
        + split; [common_keep HCm | subst r1; sacc; exact Hb8].
        + subst r1. sacc. exact HWF.
        + subst r1. sacc. exact HWB.
      - phi_goal. subst r1. sacc. lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc. }
    cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
    destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop. rewrite Hv in *.
    destruct L as [[L1 L2]|[[L1 L2]|[(L1 & L2 & L3)|[L1|L1]]]].
    -
      rewrite L1. cbn [Z.eqb]. rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC1. subst s1. sacc. lia.
        * exact HRd.
        * split; [common_keep HCm|]. split; [subst r1; sacc; exact Hb8 | tables_keep Htb].
        * subst r1. sacc. exact HWF.
        * subst r1. sacc. exact HWB.
      + phi_goal. subst r1. sacc. lia.
    -
      rewrite L1. cbn [Z.land Z.eqb negb]. exact TYPEc.
    -
      destruct (len_op_facts op L1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite F5, F2, F3. cbn [Z.eqb negb].
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm LENEXT (arm_LENEXT ivar_ref) _ _ _ _ arm_LENEXT_safe).
      + winv_split.
        * core_keep HC1. subst s1. sacc. lia.
        * exact HRd.
        * split; [common_keep HCm|]. split; [left; subst r1; sacc; exact Hb8|]. split; [tables_keep Htb|]. subst s1. sacc. lia.
        * subst r1. sacc. exact HWF.
        * subst r1. sacc. exact HWB.
      + reflexivity.
      + phi_goal. subst r1. sacc. lia.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  Qed.

  Lemma len_slow : forall w0 s c r,
    CORE s -> REGS c r -> is_mode s = LEN -> common s ->
    (ir_bits r < 8 \/ ir_bits r < lneed s (is_lencode s) (is_lenbits s) (ir_hold r)) -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
    POST w0 ((do s0 <- gs (fun s0 => s0) ;
              do here <- DECODE1 (is_lencode s0) (is_lenbits s0) ;
              do here <- (if negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0) then
                            let last := here in
                            do here <- DECODE2 (is_lencode s0) last ;
                            DROPBITS (code_bits last) ;;
                            add_back ivar_ref (code_bits last) ;;
                            aret here
                          else aret here) ;
              DROPBITS (code_bits here) ;;
              add_back ivar_ref (code_bits here) ;;
              us (fun s1 => iset_length s1 (code_val here)) ;;
              if code_op here =? 0 then set_mode LIT
              else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
              else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
              else
                us (fun s1 => iset_extra s1 (Z.land (code_op here) 15)) ;;
                set_mode LENEXT ;; arm_LENEXT ivar_ref)%am (mkW s c r)).
  Proof.
    intros w0 s c r HC HR E HCm Hbx Htb HWF HWB HP0. arun gs_eq. regs_open HR.
    assert (HW0 : WINV (mkW s c r)).
    { unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred. split; [exact HC|]. split; [exact HR|]. split; [|split; [exact HWF|exact HWB]].
      split; [exact HCm|]. split; [exact Hbx|exact Htb]. }
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (used & HT & _).
    pose proof (T_root _ _ _ _ HT) as HR15.
    aflat.
    destruct (DECODE1_spec c s (is_lencode s) LENS (is_lenbits s) used HT r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      destruct (root_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
      rewrite <- Eh in Hbits, RLk, RNk.
      assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
      { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
      aflat. acase Clink.
      +
        apply andb_prop in Clink as [Cnz Clink]. apply Z.eqb_eq in Clink. apply Bool.negb_true_iff in Cnz. apply Z.eqb_neq in Cnz.
        assert (HLk : is_linkb here = true).
        { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
          exact (notlink_land240 LENS here SH ltac:(discriminate) Cnz Clink). }
        destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
        aflat.
        destruct (DECODE2_spec c s (is_lencode s) LENS (is_lenbits s) used HT r1 here HR1 Eh HLk Hle)
          as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
        * eapply POST_bind_run; [exact EQ2|]. cbv beta iota.
          pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
          pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
          pose proof (sub_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s)
                        (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
          rewrite <- Eh in SC.
          specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
          unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
          aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun aret_eq. sacc.
          rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
          assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
          { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
          assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
          { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
            destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
            rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
            rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
          apply len_tail;
            first [ assumption
                  | core_keep HC; apply CORE_length; exact HC
                  | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                  | common_keep HCm
                  | tables_keep Htb
                  | rewrite Eo2, Eo1; exact HWF
                  | rewrite Ep2, Ep1; exact HWB
                  | sacc; lia ].
        * eapply POST_bind_leave; [exact EQ2|].
          pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _).
          apply (WINV_regs s c r r2 HW0 HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
          rewrite E. mred. intros _. split; [exact HCm|]. split; [|exact Htb].
          right. rewrite lneed_lneedg. exact Hb2.
      +
        assert (HLk : is_linkb here = false).
        { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
          rewrite (land240_small (code_op here)) in Clink by lia.
          replace (code_op here =? 0) with false in Clink by (symmetry; apply Z.eqb_neq; lia). discriminate Clink. }
        destruct (RNk HLk) as [Hbr SH].
        arun aret_eq.
        assert (B8 : ir_bits r1 - code_bits here < 8).
        { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
        apply len_tail;
          first [ assumption
                | rewrite Eo1; exact HWF
                | rewrite Ep1; exact HWB
                | lia ].
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1).
      rewrite E. mred. intros _. split; [exact HCm|]. split; [|exact Htb].
      right. rewrite lneed_lneedg. pose proof (lneedg_range LENS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
  Qed.

  Lemma arm_LEN_safe : arm_safe LEN (arm_LEN ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LEN. arun gr_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb).
    assert (HP0 : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank LEN) with 0 in HP. lia. }
    acase Cfast.
    - (* zlib 1.4: the guard's extra conjunct [ir_bits r <? 8] is not needed here *)
      apply andb_prop in Cfast as [Cfast _].
      apply andb_prop in Cfast as [Cfast C2]. apply andb_prop in Cfast as [_ C1]. apply Z.leb_le in C1. apply Z.leb_le in C2.
      exact (inflate_fast_post w0 s c r HW0 E C1 C2 HP).
    - aflat. arun set_back_ref.
      apply len_slow; first [ assumption
                              | core_keep HC; apply CORE_length; exact HC
                              | common_keep HCm
                              | rewrite (lneed_keep s (iset_back s 0)) by reflexivity; exact Hbx
                              | tables_keep Htb ].
  Qed.

  Lemma arm_LEN__safe : arm_safe LEN_ (arm_LEN_ ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LEN_. arun set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hb8 & Htb).
    apply (POST_arm LEN (arm_LEN ivar_ref) _ _ _ _ arm_LEN_safe).
    - winv_split.
      + core_keep HC. apply CORE_length; exact HC.
      + exact HR.
      + split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
      + exact HWF.
      + exact HWB.
    - reflexivity.
    - phi_norm E HP. lia.
  Qed.
End LenSlow.
