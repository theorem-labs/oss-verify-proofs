(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma arm_BAD_sq0 : forall s c r, SQ (arm_BAD (mkW s c r)).
Proof. intros s c r. unfold arm_BAD. arun3 ur_eq. rewrite aleave_eq. cbn [SQ]. lv_ret. Qed.
Lemma arm_BAD_sq : arm_sq BAD arm_BAD.
Proof. intros s c r _ _ _. apply arm_BAD_sq0. Qed.

Lemma arm_DONE_sq0 : forall s c r, SQ (arm_DONE (mkW s c r)).
Proof. intros s c r. unfold arm_DONE. arun3 ur_eq. rewrite aleave_eq. cbn [SQ]. lv_ret. Qed.
Lemma arm_DONE_sq : arm_sq DONE arm_DONE.
Proof. intros s c r _ _ _. apply arm_DONE_sq0. Qed.

Lemma arm_MEM_sq : arm_sq MEM arm_MEM.
Proof. intros s c r _ _ _. unfold arm_MEM. rewrite areturn_eq. cbn [SQ]. intros X; discriminate X. Qed.

Lemma arm_LIT_sq0 : forall s c r, is_mode s = LIT -> SQ (arm_LIT (mkW s c r)).
Proof.
  intros s c r E. unfold arm_LIT. arun3 gr_eq.
  destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0].
  { rewrite aleave_eq. cbn [SQ]. apply LV_left; [exact L0|]. unfold OC. rewrite E. oc_red. exact I. }
  arun3 gs_eq. arun3 uc_eq. arun3 ur_eq. rewrite set_mode_eq. exact I.
Qed.
Lemma arm_LIT_sq : arm_sq LIT arm_LIT.
Proof. intros s c r _ _ E. apply arm_LIT_sq0. exact E. Qed.

Section MatchArm.
  Variable iv : ivariant.

  Lemma arm_MATCH_sq0 : forall s c r, is_mode s = MATCH -> SQ (arm_MATCH iv (mkW s c r)).
  Proof.
    intros s c r E. unfold arm_MATCH. arun3 gr_eq.
    destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0].
    { rewrite aleave_eq. cbn [SQ]. apply LV_left; [exact L0|]. unfold OC. rewrite E. oc_red. exact I. }
    arun3 gs_eq. cbv zeta.
    apply SQ_bind_any.
    -
      lazymatch goal with |- SQ ((if ?cnd then _ else _) _) => destruct cnd end.
      + cbv zeta. lazymatch goal with |- SQ ((if ?cnd then _ else _) _) => destruct cnd end.
        * aflat. arun3 go_bad_eq. rewrite aret_eq. exact I.
        * destruct (is_wnext s <? _); rewrite aret_eq; exact I.
      + rewrite aret_eq. exact I.
    - intros fc w'. destruct fc as [[from copy]|]; [|destruct w'; rewrite aret_eq; exact I].
      destruct w' as [s' c' r']. cbv zeta. arun3 ur_eq. arun3 us_eq.
      apply SQ_bind_any.
      + cbn [w_s w_c w_r].
        destruct (match_copy _ _) as [[[ob put] ff] cc]. exact I.
      + intros u w2. destruct w2 as [s2 c2 r2]. arun3 gs_eq.
        destruct (is_length s2 =? 0); [rewrite set_mode_eq|rewrite aret_eq]; exact I.
  Qed.
  Lemma arm_MATCH_sq : arm_sq MATCH (arm_MATCH iv).
  Proof. intros s c r _ _ E. apply arm_MATCH_sq0. exact E. Qed.
End MatchArm.

Lemma arm_LENGTH_sq0 : forall s c r, is_flags s = 0 -> SQ (arm_LENGTH (mkW s c r)).
Proof.
  intros s c r HF. unfold arm_LENGTH. arun3 gs_eq. rewrite HF.
  replace (negb (is_wrap s =? 0) && negb (0 =? 0)) with false by (rewrite Bool.andb_false_r; reflexivity).
  arun3 aret_eq. arun3 set_mode_eq. apply arm_DONE_sq0.
Qed.
Lemma arm_LENGTH_sq : arm_sq LENGTH arm_LENGTH.
Proof.
  intros s c r HW [HWR HF] E. apply arm_LENGTH_sq0.
  destruct HF as [F|[F|[F|F]]]; [exact F| | |]; rewrite E in F; discriminate F.
Qed.

Ltac check_tail3 F0 :=
  aflat; arun3 ur_eq; aflat; arun3 HOLD_eq; aflat; arun3 gs_eq; cbv zeta;
  let Cbad := fresh "Cbad" in
  acase3 Cbad;
  [ aflat; arun3 go_bad_eq; arun3 aret_eq; cbv iota; rewrite aret_eq; exact I
  | aflat; arun3 INITBITS_eq; arun3 aret_eq; cbv iota; arun3 set_mode_eq; apply arm_LENGTH_sq0; sacc; exact F0 ].

Lemma arm_CHECK_sq : arm_sq CHECK arm_CHECK.
Proof.
  intros s c r HW [HWR HF] E. unfold arm_CHECK. arun3 gs_eq.
  assert (F0 : is_flags s = 0) by (destruct HF as [F|[F|[F|F]]]; [exact F| | |]; rewrite E in F; discriminate F).
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  rewrite HWR. change (negb (5 =? 0)) with true. cbv iota.
  aflat.
  destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
  - eapply SQ_bind_run; [exact EQ|]. cbv beta.
    aflat. arun3 gr_eq. cbv zeta. aflat. arun3 ur_eq. aflat. arun3 uc_eq. aflat. arun3 us_eq. aflat. arun3 gs_eq.
    acase3 Cupd.
    + aflat. arun03. cbn [w_s w_c w_r]. arun3 set_adler_check_eq. check_tail3 F0.
    + arun3 aret_eq. check_tail3 F0.
  - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. exact Hb1.
Qed.

Section TypeArms.
  Variable iv : ivariant.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Lemma arm_TYPEDO_sq0 : forall M s c r, (M = TYPE \/ M = TYPEDO) -> REGS c r -> is_mode s = M ->
    SQ (arm_TYPEDO iv flush (mkW s c r)).
  Proof.
    intros M s c r HM HR E. regs_open HR.
    unfold arm_TYPEDO. arun3 gs_eq. acase3 Clast.
    - arun3 BYTEBITS_eq. rewrite set_mode_eq. exact I.
    - assert (L0 : is_last s = 0) by (destruct (Z.eqb_spec (is_last s) 0); [assumption|discriminate Clast]).
      aflat.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply SQ_bind_run; [exact EQ|]. cbv beta.
        aflat. arun3 BITS_eq. aflat. arun3 us_eq. aflat. arun3 DROPBITS_eq. aflat. arun3 BITS_eq. sacc.
        destruct Hfl as [F1 F2].
        acase3 Ct0; [|acase3 Ct1; [|acase3 Ct2]].
        * aflat. arun3 set_mode_eq. arun3 aret_eq. cbv iota. rewrite DROPBITS_eq. exact I.
        * aflat. arun3 us_eq. aflat. arun3 set_mode_eq. rewrite F2, Bool.andb_false_r.
          arun3 aret_eq. cbv iota. rewrite DROPBITS_eq. exact I.
        * aflat. arun3 set_mode_eq. arun3 aret_eq. cbv iota. rewrite DROPBITS_eq. exact I.
        * aflat. arun3 go_bad_eq. arun3 aret_eq. cbv iota. rewrite DROPBITS_eq. exact I.
      + eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|].
        unfold SC. rewrite E. destruct HM as [-> | ->]; sc_red; (split; [exact L0|exact Hb1]).
  Qed.

  Lemma arm_TYPEDO_sq : arm_sq TYPEDO (arm_TYPEDO iv flush).
  Proof. intros s c r HW _ E. winv_open2 HW E HC HR. exact (arm_TYPEDO_sq0 TYPEDO s c r (or_intror eq_refl) HR E). Qed.

  Lemma arm_TYPE_sq0 : forall s c r, REGS c r -> is_mode s = TYPE -> SQ (arm_TYPE iv flush (mkW s c r)).
  Proof.
    intros s c r HR E. unfold arm_TYPE. destruct Hfl as [F1 F2]. rewrite F1, F2. cbn [orb]. rewrite Bool.andb_false_r.
    exact (arm_TYPEDO_sq0 TYPE s c r (or_introl eq_refl) HR E).
  Qed.

  Lemma arm_TYPE_sq : arm_sq TYPE (arm_TYPE iv flush).
  Proof. intros s c r HW _ E. winv_open2 HW E HC HR. exact (arm_TYPE_sq0 s c r HR E). Qed.
End TypeArms.
