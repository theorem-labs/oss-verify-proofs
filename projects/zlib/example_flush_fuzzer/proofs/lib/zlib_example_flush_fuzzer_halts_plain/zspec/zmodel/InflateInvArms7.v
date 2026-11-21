(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb
  InftreesCoverage ItCovIface ItCovRep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvCov InflateInvArms1 InflateInvArms3 InflateInvArms4 InflateInvArms5 InflateInvArms6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).
  Hypothesis FAST : forall w, pinv w -> is_mode (w_s w) = LEN -> fastcond iv (w_r w) = true -> DEBT w ->
    gFAST w = true /\ pinv (LOAD (inflate_fast (RESTORE w))) /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE w)))) < 8
    /\ PHI (LOAD (inflate_fast (RESTORE w))) < PHI w.
  Let P_CODELENS_c := P_CODELENS iv flush NI NO WN TOT0 NI32 NO32 FAST.
  Let LL1c := LL1 NI NO WN TOT0 NI32 NO32.
  Let LL2c := LL2 NI NO WN TOT0 NI32 NO32.
  Ltac msimp := cbn [Z.eqb Pos.eqb Z.compare Pos.compare Pos.compare_cont CODELENS BAD LEN_ LENLENS TABLE].


  Lemma P_LENLENS : forall w, pinv w -> is_mode (w_s w) = LENLENS -> gLENLENS iv flush w = true /\ apost w (arm_LENLENS iv flush w).
  Proof.
    intros w PI Hm. pose proof (LL1c 19 w PI Hm) as W1.
    unfold gLENLENS, arm_LENLENS. unfold after at 1. unfold abind at 1.
    destruct (lenlens_while1 19 w) as [u w1|w1|rc w1]; [| split; [reflexivity | destruct W1 as (WL & WA & WB & WC & _); exact (conj WL (conj WA (conj WB WC)))] | destruct W1].
    destruct W1 as (PI1 & M1 & WLE).
    lazymatch goal with |- ?g = true /\ apost _ ?A =>
      enough (E : g = true /\ apost w1 A)
        by (destruct E as [E1 E2]; split; [exact E1|]; eapply apost_mono; [| exact E2];
            pose proof (PHI_wle _ _ WLE) as PW; rewrite Hm, M1 in PW; revert PW; clear; lia)
    end.
    clear PI Hm WLE.
    unfold after at 1. unfold abind at 1.
    assert (HV0 : 19 - is_have (w_s w1) <= Z.of_nat 19).
    { clear - PI1 M1. destruct w1 as [s c r]. cbn [w_s] in *. destruct PI1 as (_ & _ & SI & _).
      destruct SI as (_ & _ & _ & _ & QL & _). destruct (QL M1) as (_ & _ & _ & QH & _). cbn [w_s] in QH. lia. }
    destruct (LL2c 19 w1 PI1 M1 HV0) as (w2 & E2 & PI2 & M2 & H19 & ER & _).
    rewrite E2. clear E2 PI1 HV0.
    lazymatch goal with |- ?g = true /\ apost _ ?A =>
      enough (E : g = true /\ apost w2 A)
        by (destruct E as [E1 E2']; split; [exact E1|]; eapply apost_mono; [| exact E2'];
            revert ER M1 M2; clear; intros ER M1 M2; unfold PHI; rewrite ER, M1, M2; lia)
    end.
    clear M1 ER.
    dworld w2. cbn [w_s is_mode is_have] in M2, H19. pinv_open PI2. subst f_mode. subst f_have. sinv_triage.
    destruct Qlenlens as (QN & QD & QC & QH & QL).
    unfold after. wred.
    pose proof (inflate_table_lengths CODES f_lens 0 19 f_codes 0 7 f_work) as LEN1. cbv zeta in LEN1.
    pose proof (inflate_table_fail_shape CODES f_lens 0 19 f_codes 0 7 f_work) as FL1. cbv zeta in FL1.
    assert (L7 : forall s, 0 <= s < 19 -> 0 <= arr_get f_lens (0 + s) <= 7).
    { intros s Hs. rewrite Z.add_0_l. destruct (order_cover s Hs) as (i & Hi & <-). apply QL. lia. }
    pose proof (tab_ok_of_shape CODES f_lens 0 19 f_codes 0 7 f_work ltac:(lia)
                  ltac:(intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros _; split; [lia|]; split; [reflexivity|]; intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros X; discriminate X) ltac:(lia) ltac:(lia)
                  ltac:(cbn [it_room]; rewrite Acodes; lia) ltac:(rewrite Awork; lia)) as TS1.
    pose proof (rep_ok_of_shape CODES f_lens 0 19 f_codes 0 7 f_work ltac:(lia)
                  ltac:(intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros _; split; [lia|]; split; [reflexivity|]; intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros X; discriminate X) ltac:(lia) ltac:(lia)
                  ltac:(cbn [it_room]; rewrite Acodes; lia) ltac:(rewrite Awork; lia)) as RS1.
    pose proof (ARRB_table CODES f_lens 0 19 f_codes 0 7 f_work Sarrb Acodes Awork) as AR1.
    destruct (inflate_table CODES f_lens 0 19 f_codes 0 7 f_work) as [[[[ret1 tbl1] next1] lb1] work1] eqn:IT1.
    cbn [fst snd] in LEN1, FL1, TS1, RS1. destruct LEN1 as [LT1 LW1]. destruct AR1 as (AR1 & _ & _ & _). wred.
    destruct (Z.eqb_spec ret1 0) as [R1|R1]; wred.
    2:{ destruct (FL1 R1) as [-> ->]. split; [reflexivity|]. cbn [apost]. arun_post. }
    destruct (TS1 R1) as (TC1 & BC1 & NX1 & TL1 & OUT1). cbn [it_room] in NX1. rewrite Z.sub_0_r in TC1. specialize (RS1 R1).
    chain_both P_CODELENS_c.
    { intros _. split; [lia|]. split; [lia|]. split; [lia|]. split; [| intros; lia].
      unfold ctab_ok. cbn [is_lencode is_lenbits is_next is_codes]. apply ctab_okf_intro; [lia | exact TC1]. }
  Qed.


  Lemma P_TABLE : forall w, pinv w -> is_mode (w_s w) = TABLE -> gTABLE iv flush w = true /\ apost w (arm_TABLE iv flush w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold gTABLE, arm_TABLE. unfold after. wred.
    needbits_run 14 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. split; [reflexivity|]. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    pose proof (BITSv_bound ho1 5 ltac:(lia)) as B5. change (2 ^ 5) with 32 in B5.
    dropbits 5%Z RI1 RI2 NI32 NO32. rinv_open RI2.
    pose proof (BITSv_bound (Z.shiftr ho1 5) 5 ltac:(lia)) as B5'. change (2 ^ 5) with 32 in B5'.
    dropbits 5%Z RI2 RI3 NI32 NO32. rinv_open RI3.
    pose proof (BITSv_bound (Z.shiftr (Z.shiftr ho1 5) 5) 4 ltac:(lia)) as B4. change (2 ^ 4) with 16 in B4.
    dropbits 4%Z RI3 RI4 NI32 NO32. rinv_open RI4.
    destruct ((286 <? BITSv ho1 5 + 257) || (30 <? BITSv (Z.shiftr ho1 5) 5 + 1)) eqn:OR; wred.
    { split; [reflexivity|]. cbn [apost]. arun_post. }
    apply Bool.orb_false_elim in OR. destruct OR as [O1 O2]. apply Z.ltb_ge in O1. apply Z.ltb_ge in O2.
    chain_both P_LENLENS.
  Qed.
End Arms.
