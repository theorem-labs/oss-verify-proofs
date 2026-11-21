(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).
  Local Notation LRNGq := (LRNGq NI NO WN TOT0).
  Local Notation CINV := (CINV NI NO).
  Local Notation RINV := (RINV NI NO).
  Local Notation WINV := (WINV WN).
  Local Notation CROSS := (CROSS TOT0).


  Lemma P_DONE : forall w, pinv w -> apost w (arm_DONE w).
  Proof.
    intros w PI. dworld w. destruct PI as (B & LR & SI & XI & BI & CI). unfold arm_DONE, apost. wred.
    split; [revert LR; clear; intros LR; exact LR|]. split; [exact SI|].
    unfold binv, cinv in *. cbn [w_s w_c w_r ir_bits ir_hold is_mode] in *. split; [exact BI | exact (proj1 CI)].
  Qed.
  Lemma P_BAD : forall w, pinv w -> apost w (arm_BAD w).
  Proof.
    intros w PI. dworld w. destruct PI as (B & LR & SI & XI & BI & CI). unfold arm_BAD, apost. wred.
    split; [revert LR; clear; intros LR; exact LR|]. split; [exact SI|].
    unfold binv, cinv in *. cbn [w_s w_c w_r ir_bits ir_hold is_mode] in *. split; [exact BI | exact (proj1 CI)].
  Qed.
  Lemma P_MEM : forall w, pinv w -> is_mode (w_s w) = MEM -> apost w (arm_MEM w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. destruct PI as (B & LR & SI & XI & BI & CI). unfold arm_MEM, apost. wred.
    split; [exact LR|]. split; [exact SI|].
    subst f_mode. unfold binv, binv_saved, cinv in *. cbn [w_s w_c w_r ir_bits ir_hold is_mode is_hold is_bits] in *.
    split; [exact BI | split; [| exact (proj1 CI)]].
    destruct CI as (_ & _ & Yms & _). destruct (Yms ltac:(clear; unfold MEM, SYNC; lia)) as (_ & E1 & E2 & _). split; [exact E1 | exact E2].
  Qed.
  Lemma P_SYNC : forall w, pinv w -> is_mode (w_s w) = SYNC -> apost w (arm_SYNC w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. destruct PI as (B & LR & SI & XI & BI & CI). unfold arm_SYNC, apost. wred.
    split; [exact LR|]. split; [exact SI|].
    subst f_mode. unfold binv, binv_saved, cinv in *. cbn [w_s w_c w_r ir_bits ir_hold is_mode is_hold is_bits] in *.
    split; [exact BI | split; [| exact (proj1 CI)]].
    destruct CI as (_ & _ & Yms & _). destruct (Yms ltac:(clear; unfold MEM, SYNC; lia)) as (_ & E1 & E2 & _). split; [exact E1 | exact E2].
  Qed.


  Lemma P_LIT : forall w, pinv w -> is_mode (w_s w) = LIT -> gLIT w = true /\ apost w (arm_LIT w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    split.
    { unfold gLIT, olen. cbn [w_r w_c ir_left ir_put ic_outbuf]. destruct (Z.eqb_spec r_left 0); [reflexivity|]. cbn [orb].
      apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    unfold arm_LIT, apost. wred. destruct (Z.eqb_spec r_left 0) as [L0|L0]; [leave_post|].
    rewrite (wrap32_id (r_left - 1)) by lia. split; [| phi_auto]. unfold InflateInv.pinv. cbn [w_s].
    split; [exact B|]. split; [|split; [|split; [|split]]].
    - apply LRNGq_mk.
      + srng_close. conj_solve.
      + cinv_close. rewrite arr_len_set. conj_solve.
        intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap8_range f_length); lia|]. apply Coutb. exact Hi.
      + rinv_close. conj_solve.
      + winv_close. exact WI.
      + cross_close. replace (c_total_out + (r_out - (r_left - 1))) with (c_total_out + (r_out - r_left) + 1) by lia.
        rewrite (Z.add_assoc TOT0 r_put 1). apply wrap64_add_eq. exact CR.
    - apply (sinv_to_LEN (mkIS LIT f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk)); [exact SIr | reflexivity].
    - xinv_close. split; [destruct Xret as [Xr|Xr]; [left; exact Xr | exfalso; lia]|]. split; [lia|]. left. destruct Xol as [Xol|[_ X4]]; [lia|]. exfalso; lia.
    - binv_close. binv_auto.
    - kinv_close. kinv_auto.
  Qed.


  Local Notation SS := (mkIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (only parsing).

  Lemma P_LENGTH : forall w, pinv w -> is_mode (w_s w) = LENGTH -> apost w (arm_LENGTH w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_LENGTH. wred.
    destruct (negb (f_wrap =? 0) && negb (f_flags =? 0)); wred.
    2:{ eapply apost_mono; [| apply P_DONE; pinv_auto]. phi_auto. }
    needbits_run 32 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    destruct (negb (Z.land f_wrap 4 =? 0) && negb (ho1 =? Z.land f_total 4294967295)); wred.
    - cbn [apost]. arun_post.
    - eapply apost_mono; [| apply P_DONE; pinv_auto]. phi_auto.
  Qed.

  Lemma P_CHECK : forall w, pinv w -> is_mode (w_s w) = CHECK -> gCHECK w = true /\ apost w (arm_CHECK w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    assert (OL : wrap32 (r_out - r_left) = r_out - r_left) by (apply wrap32_id; glia).
    split.
    { unfold gCHECK. cbn [w_s w_r is_wrap ir_out ir_left ir_put]. rewrite OL.
      destruct (f_wrap =? 0); [reflexivity|]. cbn [orb]. apply Z.leb_le. glia. }
    unfold arm_CHECK. wred.
    destruct (negb (f_wrap =? 0)); wred.
    2:{ chain_tail P_LENGTH. }
    needbits_run 32 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1. rewrite OL.
    set (out := r_out - r_left).
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice c_outbuf (r_put - out) out)).
    { apply (slice_bytes c_outbuf NO); [exact Coutb | glia | glia | glia]. }
    destruct (negb (Z.land f_wrap 4 =? 0) && negb (out =? 0)); wred.
    - set (ck := UPDATE_CHECK_bytes _ _ _).
      assert (CK : 0 <= ck < 2 ^ 64) by (apply UPDATE_CHECK_range; exact BY).
      destruct (negb (Z.land f_wrap 4 =? 0) && negb ((if negb (f_flags =? 0) then ho1 else ZSWAP32 ho1) =? ck)); wred.
      + cbn [apost]. split; [| phi_auto]. pinv_auto; try apply wrap64_range.
        cross_close. rewrite Z.sub_diag, Z.add_0_r, wrap64_idem. exact CR.
      + eapply apost_mono; [| apply P_LENGTH; [| reflexivity]]; [phi_auto|]. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
        pinv_auto; try apply wrap64_range.
        cross_close. rewrite Z.sub_diag, Z.add_0_r, wrap64_idem. exact CR.
    - destruct (negb (Z.land f_wrap 4 =? 0) && negb ((if negb (f_flags =? 0) then ho1 else ZSWAP32 ho1) =? f_check)); wred.
      + cbn [apost]. split; [| phi_auto]. pinv_auto; try apply wrap64_range.
        cross_close. rewrite Z.sub_diag, Z.add_0_r, wrap64_idem. exact CR.
      + eapply apost_mono; [| apply P_LENGTH; [| reflexivity]]; [phi_auto|]. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
        pinv_auto; try apply wrap64_range.
        cross_close. rewrite Z.sub_diag, Z.add_0_r, wrap64_idem. exact CR.
  Qed.
End Arms.
