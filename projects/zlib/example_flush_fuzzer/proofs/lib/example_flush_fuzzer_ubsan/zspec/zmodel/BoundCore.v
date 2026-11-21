(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvHash DeflateInvKeep OverlayFBS OverlayRace OverlayFlush DeflRoom SendModel
  LmatchModel FillWinModel DeflFastModel DeflSlowModel TreesTab
  RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr5
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2 DeflInvCore
  BoundArith BoundTfb BoundInv BoundSlow.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Record bif (s s' : deflate_state) : Prop := MkBIF {
  f_str : ds_strstart s' = ds_strstart s;
  f_bs : ds_block_start s' = ds_block_start s;
  f_ma : ds_match_available s' = ds_match_available s;
  f_ml : ds_match_length s' = ds_match_length s;
  f_ms : ds_match_start s' = ds_match_start s;
  f_ws : ds_w_size s' = ds_w_size s;
  f_syms : forall sy, dsyms sy s' <-> dsyms sy s }.

Lemma BI_transfer : forall s s', bif s s' -> BI s -> BI s'.
Proof.
  intros s s' [E1 E2 E3 E4 E5 E6 SY] B. constructor.
  - intros sy D. rewrite E3, E1, E2. apply (bi_cov _ B). apply SY. exact D.
  - intros sy D. apply (bi_tf _ B). apply SY. exact D.
  - rewrite E4, E1, E5. exact (bi_tfc _ B).
  - rewrite E4, E3. exact (bi_mla _ B).
  - rewrite E2, E6, E1. exact (bi_nb _ B).
Qed.

Lemma ep_spo_fields : forall a b st po, eproj (set_pending_out (set_strm b st) po) = eproj a ->
  ds_strstart b = ds_strstart a /\ ds_block_start b = ds_block_start a /\ ds_lookahead b = ds_lookahead a
  /\ ds_match_available b = ds_match_available a /\ ds_match_length b = ds_match_length a /\ ds_match_start b = ds_match_start a
  /\ ds_w_size b = ds_w_size a /\ ds_status b = ds_status a /\ ds_wrap b = ds_wrap a /\ ds_level b = ds_level a
  /\ ds_strategy b = ds_strategy a /\ ds_sym_next b = ds_sym_next a /\ ds_lit_bufsize b = ds_lit_bufsize a.
Proof.
  intros a b st po E.
  pose proof (ep_strstart _ _ E) as Q1. rewrite strstart_set_pending_out, strstart_set_strm in Q1.
  pose proof (ep_block_start _ _ E) as Q2. rewrite block_start_set_pending_out, block_start_set_strm in Q2.
  pose proof (ep_lookahead _ _ E) as Q3. rewrite lookahead_set_pending_out, lookahead_set_strm in Q3.
  pose proof (ep_match_available _ _ E) as Q4. rewrite match_available_set_pending_out, match_available_set_strm in Q4.
  pose proof (ep_match_length _ _ E) as Q5. rewrite match_length_set_pending_out, match_length_set_strm in Q5.
  pose proof (ep_match_start _ _ E) as Q6. rewrite match_start_set_pending_out, match_start_set_strm in Q6.
  pose proof (ep_w_size _ _ E) as Q7. rewrite w_size_set_pending_out, w_size_set_strm in Q7.
  pose proof (ep_status _ _ E) as Q8. rewrite status_set_pending_out, status_set_strm in Q8.
  pose proof (ep_wrap _ _ E) as Q9. rewrite wrap_set_pending_out, wrap_set_strm in Q9.
  pose proof (ep_level _ _ E) as Q10. rewrite level_set_pending_out, level_set_strm in Q10.
  pose proof (ep_strategy _ _ E) as Q11. rewrite strategy_set_pending_out, strategy_set_strm in Q11.
  pose proof (ep_sym_next _ _ E) as Q12. rewrite sym_next_set_pending_out, sym_next_set_strm in Q12.
  pose proof (ep_lit_bufsize _ _ E) as Q13. rewrite lit_bufsize_set_pending_out, lit_bufsize_set_strm in Q13.
  repeat split; assumption.
Qed.

Lemma dsyms_iff_nil : forall a b, dsyms [] a -> dsyms [] b -> forall sy, dsyms sy b <-> dsyms sy a.
Proof.
  intros a b Da Db sy. split; intros D.
  - rewrite (dsyms_unique _ _ _ D Db). exact Da.
  - rewrite (dsyms_unique _ _ _ D Da). exact Db.
Qed.

Lemma dsyms_nil_of : forall s sy, dsyms sy s -> ds_sym_next s = 0 -> dsyms [] s.
Proof.
  intros s sy D SN. pose proof (sy_next _ _ D) as X. rewrite SN in X. destruct sy; [exact D | cbn in X; lia].
Qed.


Lemma set_strm_pending_out_self : forall x, set_pending_out (set_strm x (ds_strm x)) (ds_pending_out x) = x.
Proof. intros x; destruct x; reflexivity. Qed.

Lemma fp_frame : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_pending (bi_flush s) < 2 ^ 32 -> 0 <= cs_avail_out (ds_strm s) ->
  let s' := flush_pending s in
  Mloc s' = Mloc s /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s) /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s)
  /\ eproj (set_pending_out (set_strm s' (ds_strm s)) (ds_pending_out s)) = eproj s
  /\ 0 <= ds_bi_valid s' <= 16.
Proof.
  intros s Hb Hp Hao. destruct (flush_pending_M s Hb Hp Hao) as (M & N & A & B). cbv zeta. split; [exact M|]. split; [exact N|]. split; [exact A|].
  split; [| exact B].
  rewrite (flush_pending_eqm s Hp). change (tr_flush_bits s) with (bi_flush s). cbv zeta.
  pose proof (ep_bi_flush s) as E1. destruct (bi_flush_M s Hb) as (_ & S1 & _ & _).
  assert (PO1 : ds_pending_out (bi_flush s) = ds_pending_out s).
  { unfold bi_flush, put_short, put_byte. destruct (ds_bi_valid s =? 16); [| destruct (8 <=? ds_bi_valid s)]; dsr; reflexivity. }
  destruct (Z.eqb_spec (fpm_len (bi_flush s)) 0).
  - rewrite <- S1, <- PO1, set_strm_pending_out_self. exact E1.
  - pose proof (fpm_post_fields (bi_flush s) (fpm_len (bi_flush s))) as F. cbv zeta in F.
    destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EP & _). rewrite S1, PO1 in EP. rewrite EP. exact E1.
Qed.

Lemma ep_spo_bif : forall a b st po, eproj (set_pending_out (set_strm b st) po) = eproj a ->
  dsyms [] a -> bif a b.
Proof.
  intros a b st po E Da. destruct (ep_spo_fields _ _ _ _ E) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
  constructor; try assumption. apply dsyms_iff_nil; [exact Da | exact (dsyms_nil_through _ _ _ _ Da E)].
Qed.



Section CORE.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HWS : ws = 32768.
  Hypothesis HLBS : PBL = 4 * 16384.
  Variable flush : Z.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.
  Variable IN0 : Z.

  Let DCORE := dcore ws hs PBL ILEN OCAP tot0.
  Local Notation Phi := (Phi IN0).
  Local Notation Aof := (Aof IN0).

  Lemma HF16 : 0 <= flush < 16.
  Proof. destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia. Qed.
  Lemma HF5 : flush <= 5.
  Proof. destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia. Qed.

  Definition CFGX (s : deflate_state) : Prop :=
    4 <= ds_level s <= 9 /\ ds_strategy s = 0 /\ (ds_wrap s = 1 \/ ds_wrap s = -1)
    /\ (ds_status s = INIT_STATE -> ds_strstart s = 0 /\ ds_wrap s = 1 /\ ds_lookahead s = 0 /\ ds_block_start s = 0).


  Definition SAME (s s' : deflate_state) : Prop :=
    BI s' /\ CFGX s' /\ Mloc s' = Mloc s /\ Phi s' = Phi s.

  Lemma SAME_of_fields : forall s s', BI s -> CFGX s -> bif s s' ->
    Mloc s' = Mloc s -> cs_next_in (ds_strm s') = cs_next_in (ds_strm s) -> ds_lookahead s' = ds_lookahead s ->
    ds_status s' = ds_status s -> ds_wrap s' = ds_wrap s -> ds_level s' = ds_level s -> ds_strategy s' = ds_strategy s ->
    SAME s s'.
  Proof.
    intros s s' B C F M N L St W Lv Sg. split; [exact (BI_transfer _ _ F B)|].
    split.
    { destruct C as (C1 & C2 & C3 & C4). unfold CFGX. rewrite Lv, Sg, W, St, (f_str _ _ F), L, (f_bs _ _ F).
      split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact C4]. }
    split; [exact M|]. unfold Phi. rewrite (Aof_frame IN0 s s' N L), St, W; [reflexivity|]. rewrite (f_str _ _ F), (f_bs _ _ F). reflexivity.
  Qed.


  Lemma SAME_last_flush : forall s v, BI s -> CFGX s -> SAME s (set_last_flush s v).
  Proof.
    intros s v B C. apply SAME_of_fields; try assumption; dsr; try reflexivity.
    constructor; dsr; try reflexivity. apply dsyms_iff; dsr; reflexivity.
  Qed.




  Lemma putShortMSB_acct : forall s b, ds_pending (putShortMSB s b) = ds_pending s + 2 /\ ds_bi_valid (putShortMSB s b) = ds_bi_valid s
    /\ ds_strm (putShortMSB s b) = ds_strm s.
  Proof.
    intros s b. unfold putShortMSB. destruct (put_byte_acct s (Z.shiftr b 8)) as (A & B & _).
    destruct (put_byte_acct (put_byte s (Z.shiftr b 8)) (Z.land b 255)) as (A' & B' & _).
    rewrite A', B', A, B, !strm_put_byte. repeat split; lia || reflexivity.
  Qed.


  Lemma zhdr_cb : forall s, DCORE s -> BI s -> CFGX s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
    let s' := flush_pending (zlib_s3_spec s) in
    BI s' /\ CFGX s' /\ Mloc s' = Mloc s + 2 /\ Phi s' = Phi s + 2 /\ ds_status s' = BUSY_STATE.
  Proof.
    intros s D B C P0 SI. pose proof D as [Cf I CL Ews Ehs Epbl].
    destruct C as (CL1 & CS & CW & CI). destruct (CI SI) as (ST0 & W1 & LK0 & BS0).
    destruct (di_init _ _ _ _ I (or_introl SI)) as (_ & _ & SN).
    pose proof (di_bv _ _ _ _ I) as Hbv. pose proof (dc_ao _ _ _ _ CL) as Hao.
    change (zlib_s3_spec s) with (zl_s3_raw s (zhdr s)). set (h := zhdr s). unfold zl_s3_raw. cbv zeta.
    rewrite (ep_strstart _ _ (ep_putShortMSB s h)), ST0. cbn [Z.eqb negb].
    destruct (putShortMSB_acct s h) as (P1 & V1 & S1).
    pose proof (ep_putShortMSB s h) as E1. remember (putShortMSB s h) as s1 eqn:Es1. clear Es1.
    rewrite <- (set_strm_pending_out_self s1) in E1.
    destruct (ep_spo_fields _ _ _ _ E1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    destruct (di_syms _ _ _ _ I) as (sy & Dy & _). pose proof (dsyms_nil_of _ _ Dy SN) as D0.
    pose proof (dsyms_nil_through _ _ _ _ D0 E1) as D1.
    set (s3 := set_status (set_strm s1 (cset_adler (ds_strm s1) adler32_init)) BUSY_STATE).
    assert (E3 : ds_pending s3 = 2 /\ ds_bi_valid s3 = ds_bi_valid s /\ cs_out_rev (ds_strm s3) = cs_out_rev (ds_strm s)
                 /\ cs_next_in (ds_strm s3) = cs_next_in (ds_strm s) /\ cs_avail_out (ds_strm s3) = cs_avail_out (ds_strm s)
                 /\ ds_status s3 = BUSY_STATE /\ ds_wrap s3 = ds_wrap s /\ ds_level s3 = ds_level s /\ ds_strategy s3 = ds_strategy s
                 /\ ds_lookahead s3 = ds_lookahead s /\ ds_strstart s3 = ds_strstart s /\ ds_block_start s3 = ds_block_start s
                 /\ ds_match_available s3 = ds_match_available s /\ ds_match_length s3 = ds_match_length s /\ ds_match_start s3 = ds_match_start s
                 /\ ds_w_size s3 = ds_w_size s /\ dsyms [] s3).
    { subst s3. dsr. rewrite S1, P1, P0, V1. dsr. repeat (split; [first [reflexivity | assumption] |]).
      eapply dsyms_keep; [exact D1 | dsr; reflexivity ..]. }
    destruct E3 as (P3 & V3 & O3 & N3 & AO3 & St3 & W3 & Lv3 & Sg3 & Lk3 & Str3 & Bs3 & Ma3 & Ml3 & Ms3 & Ws3 & D3).
    destruct (bi_flush_M s3 ltac:(rewrite V3; lia)) as (X1 & _ & X2 & X3).
    pose proof (cdiv8_le (ds_bi_valid s3) ltac:(rewrite V3; lia)) as C1. pose proof (cdiv8_le (ds_bi_valid (bi_flush s3)) ltac:(lia)) as C2.
    destruct (fp_frame s3 ltac:(rewrite V3; lia) ltac:(rewrite P3 in *; lia) ltac:(rewrite AO3; exact Hao)) as (M4 & N4 & A4 & EP4 & Bv4).
    remember (flush_pending s3) as s4 eqn:Es4. clear Es4.
    destruct (ep_spo_fields _ _ _ _ EP4) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
    pose proof (dsyms_nil_through _ _ _ _ D3 EP4) as D4.
    split.
    { apply (BI_transfer s). 2: exact B. constructor; try congruence. exact (dsyms_iff_nil _ _ D0 D4). }
    split.
    { unfold CFGX. rewrite R10, R11, R9, R8, Lv3, Sg3, W3, St3. split; [exact CL1|]. split; [exact CS|]. split; [exact CW|].
      intros X; discriminate X. }
    split.
    { rewrite M4. unfold Mloc. rewrite O3, P3, V3, P0. lia. }
    split.
    { unfold Phi. rewrite (Aof_frame IN0 s s4); [| rewrite N4, N3; reflexivity | rewrite R3, Lk3; reflexivity | rewrite R1, R2, Str3, Bs3; reflexivity].
      rewrite R8, R9, St3, W3, SI, W1. cbn. lia. }
    rewrite R8. exact St3.
  Qed.

  Lemma psm_facts : forall s b, dsyms [] s ->
    let s1 := putShortMSB s b in
    ds_pending s1 = ds_pending s + 2 /\ ds_bi_valid s1 = ds_bi_valid s /\ ds_strm s1 = ds_strm s
    /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s /\ ds_lookahead s1 = ds_lookahead s
    /\ ds_match_available s1 = ds_match_available s /\ ds_match_length s1 = ds_match_length s /\ ds_match_start s1 = ds_match_start s
    /\ ds_w_size s1 = ds_w_size s /\ ds_status s1 = ds_status s /\ ds_wrap s1 = ds_wrap s /\ ds_level s1 = ds_level s
    /\ ds_strategy s1 = ds_strategy s /\ ds_sym_next s1 = ds_sym_next s /\ ds_pending_out s1 = ds_pending_out s /\ dsyms [] s1
    /\ Mloc s1 = Mloc s + 2.
  Proof.
    intros s b D0. destruct (putShortMSB_acct s b) as (P1 & V1 & S1).
    pose proof (ep_putShortMSB s b) as E1. cbv zeta. remember (putShortMSB s b) as s1 eqn:Es1. clear Es1.
    pose proof (ep_pending_out _ _ E1) as PO.
    rewrite <- (set_strm_pending_out_self s1) in E1.
    destruct (ep_spo_fields _ _ _ _ E1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (dsyms_nil_through _ _ _ _ D0 E1) as D1.
    repeat (split; [first [assumption | reflexivity] |]). unfold Mloc. rewrite S1, P1, V1. lia.
  Qed.

  Local Ltac gen_close GEN BIFS := apply GEN;
    [ apply BIFS; dsr; try reflexivity; first [apply dsyms_iff; dsr; reflexivity | intros ?; reflexivity]
    | apply Mloc_frame; dsr; reflexivity
    | apply Aof_frame; dsr; reflexivity
    | dsr; reflexivity | dsr; reflexivity | dsr; reflexivity
    | dsr ].





End CORE.
