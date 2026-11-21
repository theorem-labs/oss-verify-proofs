(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel TreeModel CompressModel FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeZ RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflFastM RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI1 RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeZ.BoundArith OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundDefs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.BoundFw OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.BoundTfb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.BoundMc OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition BVW (s : deflate_state) :=
  ((ds_pending_buf s, ds_lit_bufsize s, ds_sym_next s, ds_strstart s, ds_block_start s, ds_match_available s),
   (ds_match_length s, ds_match_start s, ds_w_size s, ds_lookahead s, cs_next_in (ds_strm s))).

Lemma BVW_fields : forall s s', BVW s' = BVW s ->
  ds_pending_buf s' = ds_pending_buf s /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s
  /\ ds_strstart s' = ds_strstart s /\ ds_block_start s' = ds_block_start s /\ ds_match_available s' = ds_match_available s
  /\ ds_match_length s' = ds_match_length s /\ ds_match_start s' = ds_match_start s /\ ds_w_size s' = ds_w_size s
  /\ ds_lookahead s' = ds_lookahead s /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros s s' E. unfold BVW in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11. repeat split; assumption.
Qed.

Lemma COV_BVW : forall s s', BVW s' = BVW s -> COV s -> COV s'.
Proof.
  intros s s' E C. destruct (BVW_fields _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  apply (COV_same s s'); try assumption.
  - rewrite E4, E5. reflexivity.
  - unfold nbP. rewrite E5, E9, E4. exact (cv_nb _ C).
  - rewrite E4, E8. reflexivity.
Qed.

Lemma Apos_BVW : forall IN0 s s', BVW s' = BVW s -> Apos IN0 s' = Apos IN0 s.
Proof.
  intros IN0 s s' E. destruct (BVW_fields _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  unfold Apos. rewrite E11, E10, E4, E5. reflexivity.
Qed.

Lemma COV_symsame : forall s s',
  (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) -> ds_sym_next s' = ds_sym_next s ->
  ds_strstart s' = ds_strstart s -> ds_block_start s' = ds_block_start s -> ds_match_available s' = ds_match_available s ->
  ds_match_length s' = ds_match_length s -> ds_match_start s' = ds_match_start s -> ds_w_size s' = ds_w_size s ->
  COV s -> COV s'.
Proof.
  intros s s' SB EN ES EB EM EML EMS EW [C1 C2 C3 C4 C5].
  destruct (sym_readers_same s s' SB) as [RL RD].
  assert (ENS : nsym s' = nsym s) by (unfold nsym; rewrite EN; reflexivity).
  constructor.
  - rewrite (cov_ext s s' ENS), ES, EB, EM; [exact C1|]. intros j Hj. split; [apply RD | apply RL]; lia.
  - intros j Hj. rewrite ENS in Hj. apply (near3_same s s' j); [apply RD; lia | apply RL; lia | exact (C2 j Hj)].
  - rewrite EB, EW, ES. exact C3.
  - rewrite EML, ES, EMS. exact C4.
  - rewrite EML, EM. exact C5.
Qed.


Lemma put_byte_bound : forall IN0 s b, 0 <= ds_pending s < ds_lit_bufsize s ->
  let s' := put_byte s b in
  Mc s' = Mc s + 1 /\ Apos IN0 s' = Apos IN0 s /\ CF s' = CF s /\ AIN s' = AIN s /\ (COV s -> COV s')
  /\ ds_pending s' = ds_pending s + 1 /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_strstart s' = ds_strstart s.
Proof.
  intros IN0 s b Hp s'. subst s'.
  split; [unfold Mc, olen, Mloc, put_byte; dsred; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [| unfold put_byte; dsred; repeat split; reflexivity].
  apply COV_symsame; try reflexivity. intros i Hi. apply sym_buf_get_put_byte; lia.
Qed.

Lemma putShortMSB_bound : forall IN0 s w, 0 <= ds_pending s -> ds_pending s + 1 < ds_lit_bufsize s ->
  let s' := putShortMSB s w in
  Mc s' = Mc s + 2 /\ Apos IN0 s' = Apos IN0 s /\ CF s' = CF s /\ AIN s' = AIN s /\ (COV s -> COV s')
  /\ ds_pending s' = ds_pending s + 2 /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_strstart s' = ds_strstart s.
Proof.
  intros IN0 s w Hp0 Hp s'. subst s'. unfold putShortMSB.
  destruct (put_byte_bound IN0 s (Z.shiftr w 8) ltac:(lia)) as (M1 & A1 & C1 & I1 & V1 & P1 & L1 & S1).
  set (s1 := put_byte s (Z.shiftr w 8)) in *. clearbody s1.
  destruct (put_byte_bound IN0 s1 (Z.land w 255) ltac:(lia)) as (M2 & A2 & C2 & I2 & V2 & P2 & L2 & S2).
  set (s2 := put_byte s1 (Z.land w 255)) in *. clearbody s2.
  split; [lia|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [tauto|]. split; [lia|]. split; congruence.
Qed.


Lemma hdr_fin_bound : forall IN0 u a st,
  let h := set_status (set_strm u (cset_adler (ds_strm u) a)) st in
  Mc h = Mc u /\ Apos IN0 h = Apos IN0 u /\ AIN h = AIN u /\ BVW h = BVW u
  /\ ds_level h = ds_level u /\ ds_strategy h = ds_strategy u /\ ds_wrap h = ds_wrap u /\ fwT h = fwT u /\ ds_status h = st.
Proof. intros IN0 u a st h. subst h. repeat split; reflexivity. Qed.

Lemma zhdr_bound : forall IN0 s, ds_pending s = 0 -> 2048 <= ds_lit_bufsize s -> ds_strstart s = 0 ->
  let h := zhdr_st s in
  Mc h = Mc s + 2 /\ Apos IN0 h = Apos IN0 s /\ AIN h = AIN s /\ (COV s -> COV h)
  /\ ds_level h = ds_level s /\ ds_strategy h = ds_strategy s /\ ds_wrap h = ds_wrap s /\ fwT h = fwT s
  /\ ds_status h = BUSY_STATE.
Proof.
  intros IN0 s Hp Hl Hs0 h. subst h. unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => generalize hd end. intros hdr.
  destruct (putShortMSB_bound IN0 s hdr ltac:(lia) ltac:(lia)) as (M1 & A1 & C1 & I1 & V1 & P1 & L1 & S1).
  set (s1 := putShortMSB s hdr) in *. clearbody s1.
  rewrite S1, Hs0. change (negb (0 =? 0)) with false. cbv iota.
  destruct (hdr_fin_bound IN0 s1 adler32_init BUSY_STATE) as (M2 & A2 & I2 & B2 & E1 & E2 & E3 & E4 & E5).
  set (h := set_status (set_strm s1 (cset_adler (ds_strm s1) adler32_init)) BUSY_STATE) in *. clearbody h.
  destruct (CF_fields _ _ C1) as (F1 & F2 & F3 & _ & F5).
  split; [lia|]. split; [congruence|]. split; [congruence|]. split; [intros C; exact (COV_BVW s1 h B2 (V1 C))|].
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence | exact E5].
Qed.

Lemma trailer_bound : forall IN0 s, ds_pending s = 0 -> 2048 <= ds_lit_bufsize s -> ds_wrap s <> 2 ->
  let h := trailer_st s in
  Mc h = Mc s + 4 /\ Apos IN0 h = Apos IN0 s /\ AIN h = AIN s /\ CF h = CF s.
Proof.
  intros IN0 s Hp Hl Hw h. subst h. unfold trailer_st. cbv zeta.
  destruct (Z.eqb_spec (ds_wrap s) 2) as [E|_]; [contradiction|].
  generalize (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16)), (Z.land (cs_adler (ds_strm s)) 65535). intros w1 w2.
  destruct (putShortMSB_bound IN0 s w1 ltac:(lia) ltac:(lia)) as (M1 & A1 & C1 & I1 & _ & P1 & L1 & _).
  set (s1 := putShortMSB s w1) in *. clearbody s1.
  destruct (putShortMSB_bound IN0 s1 w2 ltac:(lia) ltac:(lia)) as (M2 & A2 & C2 & I2 & _).
  set (s2 := putShortMSB s1 w2) in *. clearbody s2.
  split; [lia|]. split; [congruence|]. split; congruence.
Qed.

Lemma GI_putShortMSB : forall u w, GI (putShortMSB u w) = GI u. Proof. reflexivity. Qed.
Lemma GI_hdr_fin : forall u a st, GI (set_status (set_strm u (cset_adler (ds_strm u) a)) st) = GI u. Proof. reflexivity. Qed.
Lemma GI_zhdr : forall s, ds_strstart s = 0 -> GI (zhdr_st s) = GI s.
Proof.
  intros s Hs0. unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => generalize hd end. intros hdr.
  assert (S1 : ds_strstart (putShortMSB s hdr) = ds_strstart s) by reflexivity.
  pose proof (GI_putShortMSB s hdr) as G1.
  set (s1 := putShortMSB s hdr) in *. clearbody s1.
  rewrite S1, Hs0. change (negb (0 =? 0)) with false. cbv iota. rewrite GI_hdr_fin. exact G1.
Qed.
Lemma GI_trailer : forall s, ds_wrap s <> 2 -> GI (trailer_st s) = GI s.
Proof.
  intros s Hw. unfold trailer_st. cbv zeta. destruct (Z.eqb_spec (ds_wrap s) 2) as [E|_]; [contradiction|].
  rewrite !GI_putShortMSB. reflexivity.
Qed.
Lemma GI_set_status : forall u v, GI (set_status u v) = GI u. Proof. reflexivity. Qed.
Lemma GI_set_wrap : forall u v, GI (set_wrap u v) = GI u. Proof. reflexivity. Qed.

Lemma slf_bound : forall IN0 u v, let h := set_last_flush u v in
  Mc h = Mc u /\ Apos IN0 h = Apos IN0 u /\ AIN h = AIN u /\ BVW h = BVW u /\ CF h = CF u /\ ds_pending h = ds_pending u
  /\ ds_strm h = ds_strm u.
Proof. intros IN0 u v h. subst h. repeat split; reflexivity. Qed.

Lemma sst_bound : forall IN0 u v, let h := set_status u v in
  Mc h = Mc u /\ Apos IN0 h = Apos IN0 u /\ AIN h = AIN u /\ BVW h = BVW u
  /\ ds_level h = ds_level u /\ ds_strategy h = ds_strategy u /\ ds_wrap h = ds_wrap u /\ fwT h = fwT u /\ ds_status h = v
  /\ ds_pending h = ds_pending u /\ ds_strm h = ds_strm u.
Proof. intros IN0 u v h. subst h. repeat split; reflexivity. Qed.

Lemma swr_bound : forall IN0 u v, let h := set_wrap u v in
  Mc h = Mc u /\ Apos IN0 h = Apos IN0 u /\ AIN h = AIN u /\ BVW h = BVW u
  /\ ds_level h = ds_level u /\ ds_strategy h = ds_strategy u /\ ds_wrap h = v /\ fwT h = fwT u /\ ds_status h = ds_status u
  /\ ds_pending h = ds_pending u /\ ds_strm h = ds_strm u.
Proof. intros IN0 u v h. subst h. repeat split; reflexivity. Qed.

Lemma fp_bound : forall IN0 c0 s, C0OK c0 -> DC c0 s ->
  let s' := flush_pending s in
  Mc s' = Mc s /\ Apos IN0 s' = Apos IN0 s /\ AIN s' = AIN s /\ BVW s' = BVW s /\ CF s' = CF s.
Proof.
  intros IN0 c0 s HC0 HDC s'. pose proof HDC as [[D X] V].
  pose proof (DC_flush_pending c0 s HC0 HDC) as F. cbv zeta in F. fold s' in F.
  destruct F as (_ & _ & _ & EC & _ & _ & _ & _ & _ & EPB & _ & ENI).
  pose proof (dx_core2_fields _ _ EC) as (_ & _ & _ & _ & _ & _ & _ & _ & Ews & Eml & _ & Ema & _ & _ & _ & _ & Elk & Ebs & Estr & Esn & _ & _ & Elbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ems).
  assert (EB : BVW s' = BVW s) by (unfold BVW; rewrite EPB, Elbs, Esn, Estr, Ebs, Ema, Eml, Ems, Ews, Elk, ENI; reflexivity).
  pose proof (df_bi _ D) as (B1 & _). pose proof (df_pend _ D) as (P1 & P2 & P3). pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (dx_biv _ X) as B7.
  split.
  { subst s'. apply Mc_flush_pending; [exact B1 | rewrite (tr_flush_bits_id7 s B7); lia | rewrite (tr_flush_bits_id7 s B7); exact (sv_aout _ _ V)]. }
  split; [exact (Apos_BVW IN0 s s' EB)|].
  split; [subst s'; exact (AIN_flush_pending s)|].
  split; [exact EB | subst s'; apply CF_flush_pending].
Qed.


Section Core.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Variable IN0 : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Hypothesis HFB : FB_CALL.
  Hypothesis HLBS : ds_lit_bufsize s0 = 16384.
  Hypothesis HWS : ds_w_size s0 = 32768.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Local Abbreviation ST := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.ST c0 s0).

  Definition paid (s : deflate_state) : Z :=
    (if ds_status s =? INIT_STATE then 0 else 2) + (if ds_status s =? FINISH_STATE then 5 else 0) + (if ds_wrap s <=? 0 then 4 else 0).
  Definition Gs (s : deflate_state) : Z := phi0 (Apos IN0 s) + paid s - Mc s.

  Definition SHAPE (s : deflate_state) : Prop :=
    (ds_status s = INIT_STATE /\ ds_wrap s = 1 /\ ds_strstart s = 0)
    \/ (ds_status s = BUSY_STATE /\ ds_wrap s = 1)
    \/ (ds_status s = FINISH_STATE /\ (ds_wrap s = 1 \/ ds_wrap s = -1)).

  Record CI (s : deflate_state) : Prop := {
    ci_st : ST s;
    ci_lvl : ds_level s = 6;
    ci_strat : ds_strategy s = 0;
    ci_fwT : fwT s = fwT s0;
    ci_shape : SHAPE s;
    ci_cov : ds_status s <> FINISH_STATE -> COV s;
    ci_apos : 0 <= Apos IN0 s;
    ci_fin : ds_status s = FINISH_STATE -> AIN s = 0;
    ci_G : Gs s0 <= Gs s;
    ci_gz : GZ s = 0;
    ci_ins : INS s = 0 \/ ds_status s = FINISH_STATE }.

  Lemma ST_sizes : forall s, ST s -> ds_lit_bufsize s = 16384 /\ ds_w_size s = 32768.
  Proof. intros s [_ K]. pose proof (KV_fields _ _ K) as (A & _ & B & _). rewrite A, B. auto. Qed.

  Lemma paid_CF : forall s s', CF s' = CF s -> paid s' = paid s.
  Proof. intros s s' E. destruct (CF_fields _ _ E) as (_ & _ & Ew & Est & _). unfold paid. rewrite Ew, Est. reflexivity. Qed.

  Lemma CI_same : forall s s', CI s -> ST s' -> BVW s' = BVW s -> CF s' = CF s -> Mc s' = Mc s -> AIN s' = AIN s -> GI s' = GI s -> CI s'.
  Proof.
    intros s s' [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11] HS EB EC EM EA EG. destruct (GI_fields _ _ EG) as [Eg Ei].
    destruct (CF_fields _ _ EC) as (El & Es & Ew & Est & Ef).
    destruct (BVW_fields _ _ EB) as (_ & _ & _ & Estr & _).
    constructor.
    - exact HS.
    - rewrite El; exact C2.
    - rewrite Es; exact C3.
    - rewrite Ef; exact C4.
    - unfold SHAPE in *. rewrite Est, Ew, Estr. exact C5.
    - rewrite Est. intros H. exact (COV_BVW s s' EB (C6 H)).
    - rewrite (Apos_BVW IN0 s s' EB). exact C7.
    - rewrite Est, EA. exact C8.
    - unfold Gs in *. rewrite (Apos_BVW IN0 s s' EB), (paid_CF _ _ EC), EM. exact C9.
    - rewrite Eg. exact C10.
    - rewrite Ei, Est. exact C11.
  Qed.

  Lemma CI_slf : forall s v, CI s -> - 2 <= v <= 5 -> CI (set_last_flush s v).
  Proof.
    intros s v C Hv. destruct (slf_bound IN0 s v) as (M & _ & A & B & F & _).
    exact (CI_same s _ C (ST_set_last_flush c0 s0 s v (ci_st _ C) Hv) B F M A eq_refl).
  Qed.

  Lemma CI_fp : forall s, CI s ->
    CI (flush_pending s) /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0).
  Proof.
    intros s C. pose proof (ci_st _ C) as HS.
    destruct (ST_flush_pending c0 s0 HC0 s HS) as (HS' & _ & Hor & _).
    destruct (fp_bound IN0 c0 s HC0w (proj1 HS)) as (M & _ & A & B & F).
    split; [exact (CI_same s _ C HS' B F M A (GI_PF _ _ (PF_flush_pending s))) | exact Hor].
  Qed.

  Lemma CI_hdr : forall s, CI s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
    let h := flush_pending (zhdr_st s) in
    CI h /\ ds_status h = BUSY_STATE /\ (ds_pending h = 0 \/ cs_avail_out (ds_strm h) = 0).
  Proof.
    intros s C Hp Hst h. pose proof (ci_st _ C) as HS. destruct (ST_sizes s HS) as [Elbs Ews].
    destruct (hdr_zlib c0 s0 HC0 Hs0 D0 s HS Hp Hst) as (_ & HSh & Sth & Horh & _). fold h in HSh, Sth, Horh.
    destruct (zhdr_facts c0 s (proj1 HS) Hp Hst) as ((DCz & _) & _).
    assert (Hstr : ds_strstart s = 0).
    { destruct (ci_shape _ C) as [(_ & _ & E)|[(E & _)|(E & _)]]; [exact E | |]; rewrite Hst in E; discriminate E. }
    destruct (zhdr_bound IN0 s Hp ltac:(lia) Hstr) as (M1 & A1 & I1 & V1 & E1 & E2 & E3 & E4 & E5).
    destruct (fp_bound IN0 c0 (zhdr_st s) HC0w DCz) as (M2 & A2 & I2 & B2 & F2). fold h in M2, A2, I2, B2, F2.
    destruct (CF_fields _ _ F2) as (G1 & G2 & G3 & G4 & G5).
    pose proof (GI_zhdr s Hstr) as GIz. pose proof (GI_PF _ _ (PF_flush_pending (zhdr_st s))) as GIh. fold h in GIh.
    set (z := zhdr_st s) in *. clearbody z.
    destruct (GI_fields _ _ GIz) as [Gz1 Iz1]. destruct (GI_fields _ _ GIh) as [Gz2 Iz2].
    assert (Wr : ds_wrap s = 1).
    { destruct (ci_shape _ C) as [(_ & E & _)|[(_ & E)|(E & _)]]; [exact E | exact E |]. rewrite Hst in E; discriminate E. }
    split; [| split; [exact Sth | exact Horh]].
    constructor.
    - exact HSh.
    - rewrite G1, E1. exact (ci_lvl _ C).
    - rewrite G2, E2. exact (ci_strat _ C).
    - rewrite G5, E4. exact (ci_fwT _ C).
    - right. left. split; [exact Sth | rewrite G3, E3; exact Wr].
    - intros _. apply (COV_BVW z h B2). apply V1. apply (ci_cov _ C). rewrite Hst. discriminate.
    - rewrite A2, A1. exact (ci_apos _ C).
    - rewrite Sth. intros H; discriminate H.
    - pose proof (ci_G _ C) as G. unfold Gs, paid in *. rewrite A2, A1, M2, M1, Sth, G3, E3, Hst in *.
      change (INIT_STATE =? INIT_STATE) with true in G. change (BUSY_STATE =? INIT_STATE) with false.
      change (INIT_STATE =? FINISH_STATE) with false in G. change (BUSY_STATE =? FINISH_STATE) with false.
      cbv iota in G |- *. lia.
    - rewrite Gz2, Gz1. exact (ci_gz _ C).
    - left. rewrite Iz2, Iz1. destruct (ci_ins _ C) as [E|E]; [exact E | rewrite Hst in E; discriminate E].
  Qed.

  Lemma dmode4 : forall s, ds_level s = 6 -> ds_strategy s = 0 -> dmode s = 4.
  Proof. intros s E1 E2. unfold dmode. rewrite E1, E2. reflexivity. Qed.

  Lemma CI_blocks : forall s flush, CI s -> ds_pending s = 0 -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
    ds_status s <> INIT_STATE ->
    let r := deflate_blocks s flush in
    CI (fst r) /\ (snd r = None \/ snd r = Some Z_OK)
    /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE))
    /\ (flush = Z_NO_FLUSH -> ds_status s <> FINISH_STATE -> ds_status (fst r) <> FINISH_STATE).
  Proof.
    intros s flush C Hp HFL Hni. pose proof (ci_st _ C) as HS. pose proof HS as [H K]. pose proof H as [[D X] V].
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    unfold deflate_blocks.
    match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [exact C|]. split; [left; reflexivity|]. split.
        - intros _. split; [exact Hp|]. intros Hf.
          apply orb_false_iff in Hcond as [Hcond C3]. apply andb_false_iff in C3. destruct C3 as [C3|C3].
          + exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
          + destruct (Z.eqb_spec (ds_status s) FINISH_STATE); [assumption | discriminate C3].
        - intros _ Hnf. exact Hnf. }
    assert (Hst0 : ds_status s <> FINISH_STATE).
    { intros Ef. pose proof (ci_fin _ C Ef) as A0. unfold AIN in A0.
      rewrite A0, (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    clear Hcond.
    assert (Em : dmode s = 4) by (apply dmode4; [exact (ci_lvl _ C) | exact (ci_strat _ C)]).
    assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
    destruct (slow_bf_spec HFB c0 s flush PRE Em) as [_ POST].
    destruct (ST_sizes s HS) as [Elbs Ews].
    pose proof (bslow c0 s flush IN0 HFB PRE Em Elbs Ews HFL (conj (ci_cov _ C Hst0) (ci_apos _ C))) as BS. cbv zeta in BS.
    assert (SB : ds_status s = BUSY_STATE /\ ds_wrap s = 1).
    { destruct (ci_shape _ C) as [(E & _)|[(E & W)|(E & _)]]; [contradiction | split; assumption | contradiction]. }
    destruct SB as [SB1 SB2].
    rewrite run_compress_func_dmode, Em. cbv iota.
    unfold BFPOST in POST.
    destruct (deflate_slow s flush) as [s1 bst]. cbn [fst snd] in POST, BS. cbv beta iota zeta.
    destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd). destruct BS as (B1 & B2 & B3 & B4 & B5).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    destruct (CF_fields _ _ B3) as (El & Es & Ew & Est & Ef).
    pose proof (ci_G _ C) as G0.
    destruct bst; cbn [block_state_eqb orb]; cbv iota.
    -
      destruct (B1 eq_refl) as [[CV1 AP1] PS1].
      assert (C1 : CI s1).
      { constructor.
        - exact HS1.
        - rewrite El. exact (ci_lvl _ C).
        - rewrite Es. exact (ci_strat _ C).
        - rewrite Ef. exact (ci_fwT _ C).
        - right. left. rewrite Est, Ew. split; assumption.
        - intros _. exact CV1.
        - exact AP1.
        - rewrite Est. intros E. contradiction.
        - unfold Gs in *. rewrite (paid_CF _ _ B3). unfold Psi in PS1. lia.
        - rewrite B4. exact (ci_gz _ C).
        - left. apply (B5 eq_refl). destruct (ci_ins _ C) as [E|E]; [exact E | contradiction]. }
      assert (N1 : ds_status s1 <> FINISH_STATE) by (rewrite Est; exact Hst0).
      destruct (cs_avail_out (ds_strm s1) =? 0); cbn [fst snd].
      + split; [apply CI_slf; [exact C1 | lia]|]. split; [right; reflexivity|]. split; [intros E; discriminate E|].
        intros _ _. exact N1.
      + split; [exact C1|]. split; [right; reflexivity|]. split; [intros E; discriminate E|]. intros _ _. exact N1.
    -
      exfalso. destruct (B2 ltac:(discriminate)) as (_ & _ & _ & [E|E] & _); discriminate E.
    -
      destruct (B2 ltac:(discriminate)) as (F4 & AP1 & PS1 & _ & AI1).
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_introl eq_refl)))) as (H2 & K2 & S2).
      destruct (sst_bound IN0 s1 FINISH_STATE) as (M2 & A2 & I2 & BV2 & L2 & SG2 & W2 & FT2 & ST2 & P2 & SM2).
      assert (GZ2 : GZ (set_status s1 FINISH_STATE) = GZ s1) by reflexivity.
      set (s2 := set_status s1 FINISH_STATE) in *. clearbody s2.
      assert (C2 : CI s2).
      { constructor.
        - split; [exact H2 | rewrite K2, K1; exact K].
        - rewrite L2, El. exact (ci_lvl _ C).
        - rewrite SG2, Es. exact (ci_strat _ C).
        - rewrite FT2, Ef. exact (ci_fwT _ C).
        - right. right. split; [exact ST2 | left; rewrite W2, Ew; exact SB2].
        - intros N. contradiction.
        - rewrite A2. exact AP1.
        - intros _. rewrite I2. rewrite AIN_def. exact AI1.
        - unfold Gs, paid in *. rewrite ST2, W2, Ew, SB2, A2, M2. rewrite SB1, SB2 in G0.
          change (BUSY_STATE =? INIT_STATE) with false in G0. change (BUSY_STATE =? FINISH_STATE) with false in G0.
          change (FINISH_STATE =? INIT_STATE) with false. change (FINISH_STATE =? FINISH_STATE) with true.
          change (1 <=? 0) with false in *. cbv iota in G0 |- *. unfold Psi in PS1. lia.
        - rewrite GZ2, B4. exact (ci_gz _ C).
        - right. exact ST2. }
      assert (NF : flush = Z_NO_FLUSH -> False) by (intros F0; rewrite F0 in F4; discriminate F4).
      destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst snd].
      + split; [apply CI_slf; [exact C2 | lia]|]. split; [right; reflexivity|]. split; [intros E; discriminate E|].
        intros F0. exfalso. exact (NF F0).
      + split; [exact C2|]. split; [right; reflexivity|]. split; [intros E; discriminate E|]. intros F0. exfalso. exact (NF F0).
    -
      destruct (B2 ltac:(discriminate)) as (F4 & AP1 & PS1 & _ & AI1).
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_intror eq_refl)))) as (H2 & K2 & S2).
      destruct (sst_bound IN0 s1 FINISH_STATE) as (M2 & A2 & I2 & BV2 & L2 & SG2 & W2 & FT2 & ST2 & P2 & SM2).
      assert (GZ2 : GZ (set_status s1 FINISH_STATE) = GZ s1) by reflexivity.
      set (s2 := set_status s1 FINISH_STATE) in *. clearbody s2.
      assert (C2 : CI s2).
      { constructor.
        - split; [exact H2 | rewrite K2, K1; exact K].
        - rewrite L2, El. exact (ci_lvl _ C).
        - rewrite SG2, Es. exact (ci_strat _ C).
        - rewrite FT2, Ef. exact (ci_fwT _ C).
        - right. right. split; [exact ST2 | left; rewrite W2, Ew; exact SB2].
        - intros N. contradiction.
        - rewrite A2. exact AP1.
        - intros _. rewrite I2. rewrite AIN_def. exact AI1.
        - unfold Gs, paid in *. rewrite ST2, W2, Ew, SB2, A2, M2. rewrite SB1, SB2 in G0.
          change (BUSY_STATE =? INIT_STATE) with false in G0. change (BUSY_STATE =? FINISH_STATE) with false in G0.
          change (FINISH_STATE =? INIT_STATE) with false. change (FINISH_STATE =? FINISH_STATE) with true.
          change (1 <=? 0) with false in *. cbv iota in G0 |- *. unfold Psi in PS1. lia.
        - rewrite GZ2, B4. exact (ci_gz _ C).
        - right. exact ST2. }
      assert (NF : flush = Z_NO_FLUSH -> False) by (intros F0; rewrite F0 in F4; discriminate F4).
      cbn [fst snd]. split; [exact C2|]. split; [left; reflexivity|].
      split; [intros _; split; [rewrite P2; exact (Pfd eq_refl) | intros _; exact ST2]|]. intros F0. exfalso. exact (NF F0).
  Qed.

  Lemma CI_trailer : forall s, CI s -> ds_pending s = 0 -> ds_status s = FINISH_STATE -> 0 < ds_wrap s ->
    let r := deflate_trailer s in CI (fst r) /\ (snd r = Z_OK \/ snd r = Z_STREAM_END) /\ ds_status (fst r) = FINISH_STATE.
  Proof.
    intros s C Hp Hst Hw. pose proof (ci_st _ C) as HS. destruct (ST_sizes s HS) as [Elbs Ews].
    assert (W1 : ds_wrap s = 1).
    { destruct (ci_shape _ C) as [(E & _)|[(E & _)|(_ & [E|E])]]; [rewrite Hst in E; discriminate E | rewrite Hst in E; discriminate E | exact E | lia]. }
    destruct (finish_stage c0 s0 HC0 Hs0 D0 s Z_FINISH HS Hp ltac:(unfold Z_FINISH; lia) ltac:(intros _; exact Hst)) as [_ HT].
    specialize (HT eq_refl Hw).
    destruct (trailer_facts c0 s (proj1 HS) Hp) as ((DCt & _) & _).
    destruct (trailer_bound IN0 s Hp ltac:(lia) ltac:(lia)) as (M1 & A1 & I1 & F1).
    destruct (fp_bound IN0 c0 (trailer_st s) HC0w DCt) as (M2 & A2 & I2 & B2 & F2).
    pose proof (GI_trailer s ltac:(lia)) as GIt. pose proof (GI_PF _ _ (PF_flush_pending (trailer_st s))) as GI2.
    revert HT. rewrite deflate_trailer_eq. cbv zeta.
    set (t := trailer_st s) in *. clearbody t. set (s2 := flush_pending t) in *. clearbody s2.
    destruct (CF_fields _ _ F2) as (G1 & G2 & G3 & G4 & G5). destruct (CF_fields _ _ F1) as (J1 & J2 & J3 & J4 & J5).
    assert (W2 : ds_wrap s2 = 1) by congruence.
    rewrite W2. change (0 <? 1) with true. cbv iota. change (Z.opp 1) with (-1). intros HT. cbn [fst snd] in HT |- *.
    destruct (swr_bound IN0 s2 (- 1)) as (M3 & A3 & I3 & B3 & L3 & SG3 & W3 & FT3 & ST3 & P3 & SM3).
    pose proof (GI_set_wrap s2 (-1)) as GI3.
    set (s3 := set_wrap s2 (-1)) in *. clearbody s3.
    destruct (GI_fields _ _ GIt) as [Gt _]. destruct (GI_fields _ _ GI2) as [G2' _]. destruct (GI_fields _ _ GI3) as [G3' _].
    assert (St3 : ds_status s3 = FINISH_STATE) by congruence.
    split; [| split; [destruct (negb (ds_pending s3 =? 0)); [left | right]; reflexivity | exact St3]].
    constructor.
    - exact HT.
    - rewrite L3, G1, J1. exact (ci_lvl _ C).
    - rewrite SG3, G2, J2. exact (ci_strat _ C).
    - rewrite FT3, G5, J5. exact (ci_fwT _ C).
    - right. right. split; [exact St3 | right; exact W3].
    - intros N. contradiction.
    - rewrite A3, A2, A1. exact (ci_apos _ C).
    - intros _. rewrite I3, I2, I1. exact (ci_fin _ C Hst).
    - pose proof (ci_G _ C) as G0. unfold Gs, paid in *. rewrite St3, W3, A3, A2, A1, M3, M2, M1. rewrite Hst, W1 in G0.
      change (FINISH_STATE =? INIT_STATE) with false in *. change (FINISH_STATE =? FINISH_STATE) with true in *.
      change (1 <=? 0) with false in G0. change (-1 <=? 0) with true. cbv iota in G0 |- *. lia.
    - rewrite G3', G2', Gt. exact (ci_gz _ C).
    - right. exact St3.
  Qed.


  Definition RESOK (flush : Z) (r : deflate_state * Z) : Prop :=
    CI (fst r) /\ (snd r = Z_OK \/ (flush = Z_FINISH /\ snd r = Z_STREAM_END /\ ds_status (fst r) = FINISH_STATE))
    /\ (flush = Z_NO_FLUSH -> ds_status (fst r) <> FINISH_STATE).

  Lemma RESOK_ok : forall flush s, CI s -> (flush = Z_NO_FLUSH -> ds_status s <> FINISH_STATE) -> RESOK flush (s, Z_OK).
  Proof. intros flush s C N. split; [exact C|]. split; [left; reflexivity | exact N]. Qed.

  Lemma status_slf : forall u v, ds_status (set_last_flush u v) = ds_status u. Proof. reflexivity. Qed.

  Theorem bcore : forall flush, CI s0 -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
    (flush = Z_NO_FLUSH -> 0 < cs_avail_in c0 /\ ds_status s0 <> FINISH_STATE) ->
    0 < cs_avail_out c0 ->
    RESOK flush (deflate_core s0 flush).
  Proof.
    intros flush C0 HFL HNF Hao. pose proof (ci_st _ C0) as HS0. pose proof HS0 as [H K]. pose proof H as [[D X] V].
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    unfold deflate_core.
    assert (Echk : (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) = false).
    { apply orb_false_iff. split; [apply orb_false_iff; split|]; [| apply Z.ltb_ge; unfold Z_BLOCK; lia | apply Z.ltb_ge; lia].
      unfold deflateStateCheck. cbv zeta.
      destruct (ci_shape _ C0) as [(E & _)|[(E & _)|(E & _)]]; rewrite E; reflexivity. }
    rewrite Echk.
    assert (E2 : ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) = false).
    { destruct HFL as [F|F]; [| rewrite F; apply andb_false_r].
      destruct (HNF F) as [_ N]. destruct (Z.eqb_spec (ds_status s0) FINISH_STATE); [contradiction | reflexivity]. }
    rewrite E2.
    assert (E3 : (cs_avail_out (ds_strm s0) =? 0) = false) by (rewrite Hs0; apply Z.eqb_neq; lia).
    rewrite E3. cbv zeta.
    pose proof (CI_slf s0 flush C0 ltac:(lia)) as C1.
    assert (A1 : AIN (set_last_flush s0 flush) = cs_avail_in c0) by (rewrite <- Hs0; reflexivity).
    assert (P1 : ds_pending (set_last_flush s0 flush) = ds_pending s0) by reflexivity.
    assert (St1 : ds_status (set_last_flush s0 flush) = ds_status s0) by reflexivity.
    assert (N1 : flush = Z_NO_FLUSH -> ds_status (set_last_flush s0 flush) <> FINISH_STATE) by (intros F; rewrite St1; exact (proj2 (HNF F))).
    set (s1 := set_last_flush s0 flush) in *. clearbody s1.
    match goal with |- RESOK flush (let '(s, r) := ?head in _) => destruct head as [s2 r2] eqn:Ehead end.
    assert (H2 : CI s2 /\ (flush = Z_NO_FLUSH -> ds_status s2 <> FINISH_STATE) /\ (r2 = None \/ r2 = Some Z_OK) /\ (r2 = None -> ds_pending s2 = 0)).
    { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
      - destruct (CI_fp s1 C1) as [Cf Hor].
        assert (Stf : ds_status (flush_pending s1) = ds_status s1) by (destruct (CF_fields _ _ (CF_flush_pending s1)) as (_ & _ & _ & E & _); exact E).
        destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst s2 r2.
        + split; [apply CI_slf; [exact Cf | lia]|]. split; [rewrite status_slf, Stf; exact N1|]. split; [right; reflexivity | intros HH; discriminate HH].
        + split; [exact Cf|]. split; [rewrite Stf; exact N1|]. split; [left; reflexivity | intros _; lia].
      - assert (Eb : ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)) = false).
        { destruct HFL as [F|F]; [| rewrite F; apply andb_false_r].
          destruct (HNF F) as [Ai _]. rewrite AIN_def in A1. rewrite A1.
          destruct (Z.eqb_spec (cs_avail_in c0) 0); [lia | reflexivity]. }
        rewrite Eb in Ehead. inversion Ehead; subst s2 r2. split; [exact C1|]. split; [exact N1|]. split; [left; reflexivity|].
        intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
    clear Ehead. destruct H2 as (C2 & N2 & R2 & Hp2).
    destruct R2 as [-> | ->]; [| apply RESOK_ok; assumption]. specialize (Hp2 eq_refl).
    assert (Efa : ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status s2) FINISH_STATE) as [E|E]; [| reflexivity].
      pose proof (ci_fin _ C2 E) as A. rewrite AIN_def in A. rewrite A. reflexivity. }
    rewrite Efa.
    assert (E4 : ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) = false).
    { destruct (ci_shape _ C2) as [(_ & E & _)|[(_ & E)|(E & _)]]; [rewrite E; apply andb_false_r | rewrite E; apply andb_false_r | rewrite E; reflexivity]. }
    rewrite E4.
    rewrite deflate_zlib_header_eq.
    match goal with |- RESOK flush (let '(s, r) := ?head in _) => destruct head as [s5 r5] eqn:Ehead end.
    assert (H5 : CI s5 /\ (flush = Z_NO_FLUSH -> ds_status s5 <> FINISH_STATE) /\ (r5 = None \/ r5 = Some Z_OK)
                 /\ (r5 = None -> ds_pending s5 = 0 /\ ds_status s5 <> INIT_STATE)).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E].
      - destruct (CI_hdr s2 C2 Hp2 E) as (Ch & Sth & Horh).
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s2)) =? 0)) eqn:Ep; inversion Ehead; subst s5 r5.
        + split; [apply CI_slf; [exact Ch | lia]|]. split; [intros _; rewrite status_slf, Sth; discriminate|].
          split; [right; reflexivity | intros HH; discriminate HH].
        + split; [exact Ch|]. split; [intros _; rewrite Sth; discriminate|]. split; [left; reflexivity|].
          intros _. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s2))) 0); [assumption | discriminate Ep]|].
          rewrite Sth. discriminate.
      - inversion Ehead; subst s5 r5. split; [exact C2|]. split; [exact N2|]. split; [left; reflexivity|]. intros _. split; assumption. }
    clear Ehead. destruct H5 as (C5 & N5 & R5 & Hr5).
    destruct R5 as [-> | ->]; [| apply RESOK_ok; assumption]. destruct (Hr5 eq_refl) as [Hp5 Hni5].
    assert (E6 : (ds_status s5 =? GZIP_STATE) = false).
    { destruct (ci_shape _ C5) as [(E & _)|[(E & _)|(E & _)]]; rewrite E; reflexivity. }
    rewrite E6.
    destruct (CI_blocks s5 flush C5 Hp5 HFL Hni5) as (C7 & R7 & Hr7 & N7). cbv zeta in C7, R7, Hr7, N7.
    destruct (deflate_blocks s5 flush) as [s7 r7]. cbn [fst snd] in C7, R7, Hr7, N7.
    assert (N7' : flush = Z_NO_FLUSH -> ds_status s7 <> FINISH_STATE) by (intros F; exact (N7 F (N5 F))).
    destruct R7 as [-> | ->]; [| apply RESOK_ok; assumption]. destruct (Hr7 eq_refl) as [Hp7 Hfin7].
    destruct (Z.eqb_spec flush Z_FINISH) as [Ef|Ef]; cbn [negb]; [| apply RESOK_ok; assumption].
    destruct (Z.leb_spec (ds_wrap s7) 0) as [Hw|Hw].
    - split; [exact C7|]. split; [right; split; [exact Ef | split; [reflexivity | exact (Hfin7 Ef)]]|]. intros F. rewrite F in Ef. discriminate Ef.
    - destruct (CI_trailer s7 C7 Hp7 (Hfin7 Ef) Hw) as (Ct & Rt & Stt). cbv zeta in Ct, Rt, Stt.
      destruct (deflate_trailer s7) as [s8 rc8]. cbn [fst snd] in Ct, Rt, Stt.
      split; [exact Ct|]. split; [destruct Rt as [-> | ->]; [left; reflexivity | right; split; [exact Ef | split; [reflexivity | exact Stt]]]|].
      intros F. rewrite F in Ef. discriminate Ef.
  Qed.
End Core.
