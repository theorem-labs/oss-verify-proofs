(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC InflateStallCA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma arm_DISTEXT_sq0 : forall s c r,
  REGS c r -> is_mode s = DISTEXT -> 0 <= is_extra s <= 48 -> SQ (arm_DISTEXT ivar_ref (mkW s c r)).
Proof.
  intros s c r HR E HX. unfold arm_DISTEXT. arun3 gs_eq. regs_open HR.
  acase3 Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply SQ_bind_run; [exact EQ|]. cbv beta iota.
      aflat. arun3 BITS_eq. aflat. arun3 us_eq. aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref. arun3 set_mode_eq.
      apply arm_MATCH_sq0. sacc. reflexivity.
    + eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. split; [exact Xnz|exact Hb1].
  - arun3 aret_eq. arun3 set_mode_eq. apply arm_MATCH_sq0. sacc. reflexivity.
Qed.

Lemma arm_DISTEXT_sq : arm_sq DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros s c r HW _ E. winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb & HL & HX & HO).
  apply arm_DISTEXT_sq0; [exact HR|exact E|lia].
Qed.

Lemma dist_tail_sq : forall s c r here,
  REGS c r -> 1 <= code_bits here <= ir_bits r ->
  SQ ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
       if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
       else us (fun s0 => iset_extra (iset_offset s0 (code_val here)) (Z.land (code_op here) 15)) ;;
            set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am (mkW s c r)).
Proof.
  intros s c r here HR Hcb. regs_open HR.
  aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
  acase3 Cbad.
  - unfold go_bad. arun3 set_msg_eq. rewrite set_mode_eq. exact I.
  - aflat. arun3 us_eq. arun3 set_mode_eq. apply arm_DISTEXT_sq0; sacc; [|reflexivity|].
    + apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia].
    + pose proof (land15_range (code_op here) (code_op_nonneg here)). lia.
Qed.

Lemma arm_DIST_sqW : forall s c r, WINV (mkW s c r) -> is_mode s = DIST -> SQ (arm_DIST ivar_ref (mkW s c r)).
Proof.
  intros s c r HW E. unfold arm_DIST. arun3 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL).
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
  pose proof (T_root _ _ _ _ HT) as HR15.
  aflat.
  destruct (DECODE1_spec c s (is_distcode s) DISTS (is_distbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
  - eapply SQ_bind_run; [exact EQ|]. cbv beta iota.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    destruct (root_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    aflat. acase3 Clink.
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
      * eapply SQ_bind_run; [exact EQ2|]. cbv beta iota.
        pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
        aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref. arun3 aret_eq. sacc.
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        apply dist_tail_sq; [|sacc; lia].
        apply REGS_holdbits; [exact HR2|]. apply HB_drop; [split; [exact RB2|exact RHO2]|lia].
      * eapply SQ_bind_leave; [exact EQ2|]. apply LV_stall; [exact Hh2|]. unfold SC. rewrite E. sc_red.
        rewrite lneed_lneedg. exact Hb2.
    + arun3 aret_eq. apply dist_tail_sq; [exact HR1|lia].
  - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. rewrite lneed_lneedg.
    pose proof (lneedg_range DISTS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
Qed.

Lemma arm_DIST_sq : arm_sq DIST (arm_DIST ivar_ref).
Proof. intros s c r HW _ E. exact (arm_DIST_sqW s c r HW E). Qed.

Lemma arm_LENEXT_sqW : forall s c r, WINV (mkW s c r) -> is_mode s = LENEXT -> SQ (arm_LENEXT ivar_ref (mkW s c r)).
Proof.
  intros s c r HW E. unfold arm_LENEXT. arun3 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HX & HL). pose proof (CORE_length s HC) as HL0.
  pose proof (pow2_pos (is_extra s) ltac:(lia)) as P0.
  acase3 Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply SQ_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun3 BITS_eq. aflat. arun3 us_eq. aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref.
      aflat. arun3 aux_ref. arun3 set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15. change (2 ^ 15) with 32768 in P15.
      rewrite (wrap32_id (is_length s + _)) by lia.
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply arm_DIST_sqW; [|reflexivity].
      winv_split.
      * core_keep HC. lia.
      * apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * rewrite Eo1. exact HWF.
      * rewrite Ep1. exact HWB.
    + eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. split; [exact Xnz|exact Hb1].
  - apply Z.eqb_eq in Cx || (destruct (Z.eqb_spec (is_extra s) 0) as [Cx'|Cx']; [clear Cx; rename Cx' into Cx|discriminate Cx]).
    arun3 aret_eq. aflat. arun3 aux_ref. arun3 set_mode_eq.
    apply arm_DIST_sqW; [|reflexivity].
    winv_split.
    + core_keep HC. exact HL0.
    + exact HR.
    + split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
    + exact HWF.
    + exact HWB.
Qed.

Lemma arm_LENEXT_sq : arm_sq LENEXT (arm_LENEXT ivar_ref).
Proof. intros s c r HW _ E. exact (arm_LENEXT_sqW s c r HW E). Qed.
