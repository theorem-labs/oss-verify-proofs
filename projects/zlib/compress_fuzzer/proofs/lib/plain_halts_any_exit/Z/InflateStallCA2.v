(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC InflateStallCA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section StoredArms.
  Variable iv : ivariant.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Lemma arm_COPY_sq0 : forall s c r, is_mode s = COPY -> 0 <= is_length s -> SQ (arm_COPY (mkW s c r)).
  Proof.
    intros s c r E HL0. unfold arm_COPY. arun3 gs_eq. cbv zeta.
    acase3 Clen.
    - arun3 gr_eq. cbv zeta.
      assert (Hnz : is_length s <> 0) by (intros X; rewrite X in Clen; discriminate Clen).
      acase3 Ccp.
      + aleave3. apply Z.eqb_eq in Ccp.
        destruct (Z.ltb_spec (ir_have r) (is_length s)) as [A|A].
        * destruct (Z.ltb_spec (ir_left r) (ir_have r)) as [B|B].
          -- apply LV_left; [exact Ccp|]. unfold OC. rewrite E. oc_red. lia.
          -- apply LV_stall; [exact Ccp|]. unfold SC. rewrite E. sc_red. lia.
        * destruct (Z.ltb_spec (ir_left r) (is_length s)) as [B|B].
          -- apply LV_left; [exact Ccp|]. unfold OC. rewrite E. oc_red. lia.
          -- exfalso. exact (Hnz Ccp).
      + aflat. arun3 uc_eq. aflat. arun3 ur_eq. rewrite us_eq. exact I.
    - rewrite set_mode_eq. exact I.
  Qed.

  Lemma arm_COPY_sq : arm_sq COPY arm_COPY.
  Proof.
    intros s c r HW _ E. winv_open2 HW E HC HR. apply (arm_COPY_sq0 s c r E). exact (proj1 (CORE_length s HC)).
  Qed.

  Lemma arm_COPY__sq0 : forall s c r, 0 <= is_length s -> SQ (arm_COPY_ (mkW s c r)).
  Proof.
    intros s c r HL0. unfold arm_COPY_. arun3 set_mode_eq. apply arm_COPY_sq0; sacc; [reflexivity|exact HL0].
  Qed.

  Lemma arm_COPY__sq : arm_sq COPY_ arm_COPY_.
  Proof.
    intros s c r HW _ E. winv_open2 HW E HC HR. apply arm_COPY__sq0. exact (proj1 (CORE_length s HC)).
  Qed.

  Lemma arm_STORED_sq : arm_sq STORED (arm_STORED iv flush).
  Proof.
    intros s c r HW _ E. unfold arm_STORED.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    arun3 BYTEBITS_eq.
    pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
    assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
    set (rb := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7))).
    assert (HRb : REGS c rb) by (subst rb; apply REGS_drop; [exact HR|lia]).
    assert (Ebb : ir_bits rb = ir_bits r - ir_bits r mod 8) by (subst rb; sacc; rewrite L7; apply wrap32_id; lia).
    destruct (NEEDBITS_spec c 32 s rb HRb ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply SQ_bind_run; [exact EQ|]. cbv beta.
      arun3 HOLD_eq. acase3 Cbad.
      + arun3 set_msg_eq. rewrite set_mode_eq. exact I.
      + aflat. arun3 us_eq. aflat. arun3 INITBITS_eq. aflat. arun3 set_mode_eq.
        destruct Hfl as [F1 F2]. rewrite F2, Bool.andb_false_r.
        apply arm_COPY__sq0. sacc. pose proof (land_65535 (wrap32 (ir_hold r1))). lia.
    - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red.
      split; [|exact Hb1].
      destruct HP1 as (k & Hk & _ & _ & _ & Bk & _). rewrite Bk, Ebb.
      pose proof (Z.div_mod (ir_bits r) 8 ltac:(lia)) as DM.
      replace (ir_bits r - ir_bits r mod 8 + 8 * k) with ((ir_bits r / 8 + k) * 8) by lia.
      apply Z_mod_mult.
  Qed.
End StoredArms.

Section DictArms.
  Variable iv : ivariant.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Lemma arm_DICT_sq0 : forall s c r, REGS c r -> SQ (arm_DICT iv flush (mkW s c r)).
  Proof.
    intros s c r HR. unfold arm_DICT. arun3 gs_eq.
    acase3 Chd.
    - (* zlib 1.4: total_in += in - avail_in after RESTORE, before Z_NEED_DICT *)
      arun3 amodify_eq. arun3 gr_eq. arun3 uc_eq. aleave3. intros X; discriminate X.
    - aflat. arun3 set_adler_check_eq. arun3 set_mode_eq.
      apply (arm_TYPE_sq0 iv flush Hfl); [|reflexivity].
      eapply REGS_cview; [exact HR | reflexivity | reflexivity].
  Qed.

  Lemma arm_DICT_sq : arm_sq DICT (arm_DICT iv flush).
  Proof. intros s c r HW _ E. winv_open2 HW E HC HR. exact (arm_DICT_sq0 s c r HR). Qed.

  Lemma arm_DICTID_sq : arm_sq DICTID (arm_DICTID iv flush).
  Proof.
    intros s c r HW _ E. unfold arm_DICTID.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply SQ_bind_run; [exact EQ|]. cbv beta.
      arun3 HOLD_eq. aflat. arun3 set_adler_check_eq. aflat. arun3 INITBITS_eq. aflat. arun3 set_mode_eq.
      apply arm_DICT_sq0. eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
    - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. exact Hb1.
  Qed.
End DictArms.
