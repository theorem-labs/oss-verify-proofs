(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb
  InftreesCoverage ItCovIface ItCovRep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvCov InflateInvArms1 InflateInvArms3 InflateInvArms4 InflateInvArms5.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInvTbl.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

Lemma ARRB_table : forall ty lens lo n codes table bits work,
  ARRB lens work codes -> arr_len codes = 1444 -> arr_len work = 288 ->
  let '(ret, tbl', table', bits', work') := inflate_table ty lens lo n codes table bits work in
  ARRB lens work' tbl' /\ arr_len tbl' = 1444 /\ arr_len work' = 288 /\ (ret = 0 \/ ret = 1 \/ ret = -1).
Proof.
  intros ty lens lo n codes table bits work (AL & AW & AC) LC LW.
  pose proof (inflate_table_ranges ty lens lo n codes table bits work) as R.
  destruct (inflate_table ty lens lo n codes table bits work) as [[[[ret tbl'] table'] bits'] work'].
  destruct R as (R1 & R2 & R3 & R4 & R5).
  assert (C1 : cells_below (2 ^ 32) tbl') by (apply R2; intros i Hi; apply AC; rewrite <- LC; exact Hi).
  assert (C2 : cells_below (2 ^ 16) work') by (apply R3; intros i Hi; apply AW; rewrite <- LW; exact Hi).
  split; [| split; [lia | split; [lia | exact R1]]].
  split; [exact AL|]. split.
  - intros i Hi. apply C2. rewrite R5, LW. exact Hi.
  - intros i Hi. apply C1. rewrite R4, LC. exact Hi.
Qed.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).
  Hypothesis FAST : forall w, pinv w -> is_mode (w_s w) = LEN -> fastcond iv (w_r w) = true -> DEBT w ->
    gFAST w = true /\ pinv (LOAD (inflate_fast (RESTORE w))) /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE w)))) < 8
    /\ PHI (LOAD (inflate_fast (RESTORE w))) < PHI w.
  Let P_LEN_c := P_LEN_ iv NI NO WN TOT0 NI32 NO32 FAST.
  Let CBc := CB NI NO WN TOT0 NI32 NO32.
  Ltac msimp := cbn [Z.eqb Pos.eqb Z.compare Pos.compare Pos.compare_cont CODELENS BAD LEN_ LENLENS TABLE].

  Lemma LLc : forall k w, pinv w -> is_mode (w_s w) = CODELENS ->
    match codelens_while k w with
    | ARun _ w' => pinv w' /\ (is_mode (w_s w') = BAD
                   \/ (is_mode (w_s w') = CODELENS /\ is_nlen (w_s w') = is_nlen (w_s w) /\ is_ndist (w_s w') = is_ndist (w_s w)
                       /\ ((is_nlen (w_s w) + is_ndist (w_s w) <= is_have (w_s w') /\ ir_bits (w_r w') < 8)
                           \/ is_have (w_s w) + Z.of_nat k <= is_have (w_s w')))) /\ wle w w'
    | ALeave w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w') /\ xinv w' /\ cinv w'
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros w PI Hm.
    { cbn [codelens_while aret]. split; [exact PI|]. split; [| apply wle_refl]. right. repeat split; try assumption. right. lia. }
    cbn [codelens_while]. unfold abind at 1. unfold gs.
    destruct (Z.ltb_spec (is_have (w_s w)) (is_nlen (w_s w) + is_ndist (w_s w))) as [LT|GE].
    2:{ cbn [aret]. split; [exact PI|]. split; [| apply wle_refl]. right. split; [exact Hm|]. split; [reflexivity|]. split; [reflexivity|]. left. split; [lia|].
        destruct w as [s c r]. destruct PI as (_ & _ & _ & _ & BI & _). unfold binv in BI. cbn [w_s w_r] in BI, Hm, GE |- *.
        rewrite Hm in BI. pend_red_in BI. lia. }
    unfold abind at 1. pose proof (CBc w PI Hm LT) as HB.
    destruct (codelens_body w) as [c w1|w1|rc w1]; [| exact HB | exact HB].
    destruct HB as (P1 & N1 & D1 & T1 & F1 & W1).
    destruct c.
    - destruct (T1 eq_refl) as (M1 & H1 & B1). pose proof (IH w1 P1 M1) as R.
      destruct (codelens_while k w1) as [u w2|w2|rc w2]; [| exact R | exact R].
      destruct R as (P2 & R & W2). split; [exact P2|]. split; [| exact (wle_trans _ _ _ W1 W2)]. destruct R as [R|(R1 & R2 & R3 & R4)]; [left; exact R | right].
      rewrite N1, D1 in *. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. destruct R4 as [[R4 R5]|R4]; [left; split; [lia | exact R5] | right; lia].
    - cbn [aret]. split; [exact P1|]. split; [| exact W1]. left. exact (F1 eq_refl).
  Qed.


  Lemma P_CODELENS : forall w, pinv w -> is_mode (w_s w) = CODELENS -> gCODELENS iv flush w = true /\ apost w (arm_CODELENS iv flush w).
  Proof.
    intros w PI Hm. pose proof (LLc 321 w PI Hm) as WL.
    unfold gCODELENS, arm_CODELENS. unfold after at 1. unfold abind at 1.
    destruct (codelens_while 321 w) as [u w1|w1|rc w1]; [| split; [reflexivity | destruct WL as (WL' & WA & WB & WC & _); exact (conj WL' (conj WA (conj WB WC)))] | destruct WL].
    destruct WL as (PI1 & CASES & WLE).
    assert (HW0 : 0 <= is_have (w_s w)).
    { clear - PI. destruct w as [s c r]. destruct PI as (_ & LR & _). apply LRNGq_S in LR. unfold SRNGq in LR. cbn [w_s]. lia. }
    pose proof (PHI_wle _ _ WLE) as PW. rewrite Hm in PW.
    destruct CASES as [MB | (MC & EN & ED & HV)].
    {
      rewrite MB in PW. unfold after. cbv beta iota delta [gs abind]. rewrite MB, Z.eqb_refl. cbv beta iota delta [ctrue aret]. cbn [apost].
      split; [reflexivity|]. split; [exact PI1|]. revert PW. clear.
      cbv beta iota delta [mrank Z.eqb Pos.eqb orb CODELENS BAD EXLEN EXTRA NAME COMMENT COPY_ HCRC HEAD DICT COPY LENLENS TYPE TYPEDO DISTEXT
                           CHECK LENGTH FLAGS STORED LEN_ LENEXT MATCH]. lia. }
    rewrite MC in PW.
    lazymatch goal with |- ?g = true /\ apost _ ?A =>
      enough (E : g = true /\ apost w1 A)
        by (destruct E as [E1 E2]; split; [exact E1|]; eapply apost_mono; [| exact E2]; revert PW; clear;
            cbv beta iota delta [mrank Z.eqb Pos.eqb orb CODELENS BAD EXLEN EXTRA NAME COMMENT COPY_ HCRC HEAD DICT COPY LENLENS TYPE TYPEDO DISTEXT
                                 CHECK LENGTH FLAGS STORED LEN_ LENEXT MATCH]; lia)
    end.
    clear PI Hm WLE PW.
    dworld w1. cbn [w_s is_mode is_nlen is_ndist is_have] in MC, EN, ED, HV. pinv_open PI1.
    subst f_mode. sinv_triage. destruct Qcodelens as (QN & QD & QH & QCT & QL15).
    rewrite <- EN, <- ED in HV. cbn [w_r ir_bits] in HV.
    assert (HVE : f_have = f_nlen + f_ndist /\ r_bits < 8) by (cbn in HV; lia). clear HV EN ED. destruct HVE as [HVE HB8].
    unfold after. wred. msimp. wred.
    destruct (Z.eqb_spec (arr_get f_lens 256) 0) as [E256|E256]; wred.
    { split; [reflexivity|]. cbn [apost]. arun_post. }
    pose proof (inflate_table_lengths LENS f_lens 0 f_nlen f_codes 0 9 f_work) as LEN1. cbv zeta in LEN1.
    pose proof (inflate_table_fail_shape LENS f_lens 0 f_nlen f_codes 0 9 f_work) as FL1. cbv zeta in FL1.
    pose proof (tab_ok_of_shape LENS f_lens 0 f_nlen f_codes 0 9 f_work ltac:(clear - QN; lia)
                  ltac:(intros s Hs; rewrite Z.add_0_l; apply QL15; clear - Hs HVE QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros X; discriminate X) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite Acodes; clear; lia) ltac:(rewrite Awork; clear - QN; lia)) as TS1.
    pose proof (ARRB_table LENS f_lens 0 f_nlen f_codes 0 9 f_work Sarrb Acodes Awork) as AR1.
    destruct (inflate_table LENS f_lens 0 f_nlen f_codes 0 9 f_work) as [[[[ret1 tbl1] next1] lb1] work1] eqn:IT1.
    cbn [fst snd] in LEN1, FL1, TS1. destruct LEN1 as [LT1 LW1]. destruct AR1 as (AR1 & _ & _ & _). wred.
    destruct (Z.eqb_spec ret1 0) as [R1|R1]; wred.
    2:{ destruct (FL1 R1) as [-> ->]. split; [reflexivity|]. cbn [apost]. arun_post. }
    destruct (TS1 R1) as (TL1 & BL1 & NX1 & _ & OUT1). cbn [it_room] in NX1. unfold ENOUGH_LENS in NX1.
    pose proof (inflate_table_lengths DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1) as LEN2. cbv zeta in LEN2.
    pose proof (inflate_table_fail_shape DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1) as FL2. cbv zeta in FL2.
    pose proof (tab_ok_of_shape DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 ltac:(clear - QD; lia)
                  ltac:(intros s Hs; apply QL15; clear - Hs HVE QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros _; clear - QD; lia) ltac:(clear; lia) ltac:(clear - NX1 BL1; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite LT1, Acodes; clear - NX1 BL1; lia) ltac:(rewrite LW1, Awork; clear - QD; lia)) as TS2.
    pose proof (ARRB_table DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 AR1 ltac:(rewrite LT1; exact Acodes) ltac:(rewrite LW1; exact Awork)) as AR2.
    destruct (inflate_table DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1) as [[[[ret2 tbl2] next2] db2] work2] eqn:IT2.
    cbn [fst snd] in LEN2, FL2, TS2. destruct LEN2 as [LT2 LW2]. destruct AR2 as (AR2 & _ & _ & _). wred.
    destruct (Z.eqb_spec ret2 0) as [R2|R2]; wred.
    2:{ destruct (FL2 R2) as [-> ->]. split; [reflexivity|]. cbn [apost]. arun_post. }
    destruct (TS2 R2) as (TD2 & BD2 & NX2 & _ & OUT2). cbn [it_room] in NX2. unfold ENOUGH_DISTS in NX2.
    assert (TL2 : tab_ok LENS (cat tbl2 (CDyn 0)) lb1 next1 = true).
    { apply (tab_ok_ext LENS (cat tbl1 (CDyn 0))). 2:{ replace next1 with (next1 - 0) by lia. exact TL1. }
      intros i Hi. cbn [cat]. Transparent cat. unfold cat. apply OUT2. lia. }
    assert (TOK : tables_okf (CDyn 0) (CDyn next1) lb1 db2 next2 tbl2 = true).
    { apply tables_okf_dyn_intro; [clear - NX1 NX2 BL1 BD2; lia | clear - NX1 NX2 BL1 BD2; lia | exact TL2 | exact TD2]. }
    pose proof (rep_ok_of_shape LENS f_lens 0 f_nlen f_codes 0 9 f_work ltac:(clear - QN; lia)
                  ltac:(intros s Hs; rewrite Z.add_0_l; apply QL15; clear - Hs HVE QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros X; discriminate X) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite Acodes; clear; lia) ltac:(rewrite Awork; clear - QN; lia)) as RS1.
    rewrite IT1 in RS1. cbn [fst snd] in RS1. specialize (RS1 R1).
    pose proof (rep_ok_of_shape DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 ltac:(clear - QD; lia)
                  ltac:(intros s Hs; apply QL15; clear - Hs HVE QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros _; clear - QD; lia) ltac:(clear; lia) ltac:(clear - NX1 BL1; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite LT1, Acodes; clear - NX1 BL1; lia) ltac:(rewrite LW1, Awork; clear - QD; lia)) as RS2.
    rewrite IT2 in RS2. cbn [fst snd] in RS2. specialize (RS2 R2).
    assert (RL2 : rep_ok (cat tbl2 (CDyn 0)) lb1).
    { apply (rep_ok_ext LENS (cat tbl1 (CDyn 0)) _ lb1 (next1 - 0) TL1); [| exact RS1].
      intros i Hi. Transparent cat. unfold cat. apply OUT2. lia. }
    assert (TREP : rep_ok (cat tbl2 (CDyn 0)) lb1 /\ rep_ok (cat tbl2 (CDyn next1)) db2) by (split; [exact RL2 | exact RS2]).
    destruct (iv_flush_exits iv && (flush =? Z_TREES)); wred.
    - split; [reflexivity|]. cbn [apost w_s]. leave_post; intros; first [exact TOK | exact TREP].
    - chain_both P_LEN_c; intros; first [exact TOK | exact TREP].
  Qed.
End Arms.
