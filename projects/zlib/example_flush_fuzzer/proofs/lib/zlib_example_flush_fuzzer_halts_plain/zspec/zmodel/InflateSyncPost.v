(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateSync InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall InflateCall.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac srng_setter :=
  intros; match goal with H : SRNGq ?s |- _ => ds s; unfold SRNGq in *;
    cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *;
    repeat match goal with K : _ /\ _ |- _ => destruct K end;
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia] end.

Lemma SRNGq_hb : forall s h b, SRNGq s -> 0 <= h < 2 ^ 64 -> 0 <= b < 2 ^ 32 -> SRNGq (iset_bits (iset_hold s h) b).
Proof. srng_setter. Qed.
Lemma SRNGq_mode' : forall s m, SRNGq s -> HEAD <= m <= SYNC -> SRNGq (iset_mode s m).
Proof. srng_setter. Qed.
Lemma SRNGq_have : forall s v, SRNGq s -> 0 <= v < 2 ^ 32 -> SRNGq (iset_have s v).
Proof. srng_setter. Qed.
Lemma SRNGq_wrap : forall s v, SRNGq s -> 0 <= v < 16 -> SRNGq (iset_wrap s v).
Proof. srng_setter. Qed.
Lemma SRNGq_flags : forall s v, SRNGq s -> - 2 ^ 31 <= v < 2 ^ 31 -> SRNGq (iset_flags s v).
Proof. srng_setter. Qed.


Lemma syncsearch_loop_bound : forall buf got next, 0 <= got -> 0 <= next ->
  let '(got', next') := syncsearch_loop buf got next in 0 <= got' <= Z.max got 4 /\ next <= next' <= next + zlength buf.
Proof.
  induction buf as [|b rest IH]; intros got next Hg Hn; cbn [syncsearch_loop].
  - change (zlength (@nil Z)) with 0. lia.
  - rewrite (zlength_cons (A:=Z)). destruct (Z.ltb_spec got 4) as [L|L]; [| pose proof (zlength_nonneg rest); lia].
    match goal with |- let '(_, _) := syncsearch_loop rest ?G (next + 1) in _ => set (g := G) end.
    assert (Hg' : 0 <= g <= 4) by (subst g; destruct (b =? _); [lia|]; destruct (negb (b =? 0)); lia).
    specialize (IH g (next + 1) ltac:(lia) ltac:(lia)). destruct (syncsearch_loop rest g (next + 1)) as [g' n']. lia.
Qed.

Lemma syncsearch_bound : forall have buf, 0 <= have ->
  0 <= fst (syncsearch have buf) <= Z.max have 4 /\ 0 <= snd (syncsearch have buf) <= zlength buf.
Proof.
  intros have buf H. unfold syncsearch. pose proof (syncsearch_loop_bound buf have 0 H ltac:(lia)) as X.
  destruct (syncsearch_loop buf have 0) as [g n]. cbn [fst snd]. lia.
Qed.

Lemma sync_drain_facts : forall fuel s acc, 0 <= is_bits s -> 0 <= is_hold s < 2 ^ is_bits s -> Z.of_nat fuel > is_bits s / 8 ->
  let s' := fst (sync_drain fuel s acc) in
  icore s' = icore s /\ is_whave s' = is_whave s /\ is_wnext s' = is_wnext s /\ is_wsize s' = is_wsize s
  /\ is_window s' = is_window s /\ is_window_blk s' = is_window_blk s /\ is_wbits s' = is_wbits s /\ is_check s' = is_check s
  /\ 0 <= is_bits s' < 8 /\ 0 <= is_hold s' < 2 ^ is_bits s'
  /\ (SRNGq s -> SRNGq s').
Proof.
  induction fuel as [|f IH]; intros s acc Hb Hh Hf; cbn [sync_drain fst]; [cbn [Z.of_nat] in Hf; pose proof (Z.div_pos (is_bits s) 8); lia|].
  destruct (Z.leb_spec 8 (is_bits s)) as [L|L].
  - replace (is_bits (iset_hold s (Z.shiftr (is_hold s) 8))) with (is_bits s) by (destruct s; reflexivity).
    set (s1 := iset_bits (iset_hold s (Z.shiftr (is_hold s) 8)) (is_bits s - 8)).
    assert (E1 : is_bits s1 = is_bits s - 8 /\ is_hold s1 = Z.shiftr (is_hold s) 8) by (subst s1; destruct s; split; reflexivity).
    destruct E1 as [Eb Eh].
    assert (Hh1 : 0 <= is_hold s1 < 2 ^ is_bits s1).
    { rewrite Eb, Eh, Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (8 + (is_bits s - 8)) with (is_bits s) by lia. lia. }
    specialize (IH s1 (acc ++ [Z.land (is_hold s) 255]) ltac:(lia) Hh1).
    assert (Hf1 : Z.of_nat f > is_bits s1 / 8).
    { rewrite Eb. rewrite Nat2Z.inj_succ in Hf. replace (is_bits s - 8) with (is_bits s + (-1) * 8) by lia. rewrite Z.div_add by lia. lia. }
    specialize (IH Hf1). cbv zeta in IH. destruct (sync_drain f s1 _) as [s' acc']. cbn [fst] in IH |- *.
    destruct IH as (C & W1 & W2 & W3 & W4 & W5 & W6 & W7 & B1 & B2 & PP).
    assert (K : icore s1 = icore s /\ is_whave s1 = is_whave s /\ is_wnext s1 = is_wnext s /\ is_wsize s1 = is_wsize s
                /\ is_window s1 = is_window s /\ is_window_blk s1 = is_window_blk s /\ is_wbits s1 = is_wbits s /\ is_check s1 = is_check s)
      by (subst s1; destruct s; repeat split; reflexivity).
    destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
    repeat match goal with |- _ /\ _ => split end; try congruence; try lia.
    intros SR. apply PP. subst s1.
    pose proof SR as SR'. destruct SR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [X1 X2] & [Y1 Y2] & _).
    apply SRNGq_hb; [exact SR | | lia].
    rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. nia.
  - cbn [fst]. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. intros SR; exact SR.
Qed.

Definition icore2 (s : inflate_state) :=
  (is_length s, is_offset s, is_extra s,
   is_lencode s, is_distcode s, is_lenbits s, is_distbits s, is_ncode s, is_nlen s, is_ndist s,
   is_next s, is_lens s, is_work s, is_codes s).

Lemma icore2_of_icore : forall s s', icore s' = icore s -> icore2 s' = icore2 s.
Proof. intros s s' E. destruct s; destruct s'. unfold icore in E. cbn in E. injection E; intros; subst. reflexivity. Qed.

Lemma sinv_quiet : forall s s', icore2 s' = icore2 s ->
  (is_mode s' = SYNC \/ is_mode s' = TYPE) ->
  0 <= is_whave s' <= is_wsize s' -> 0 <= is_wnext s' <= is_wsize s' -> sinv s -> sinv s'.
Proof.
  intros s s' E M W1 W2 SI. destruct SI as (_ & _ & AL & _).
  destruct s; destruct s'. unfold icore2 in E. cbn in E, M, W1, W2 |- *. injection E; intros; subst.
  unfold sinv. cbn -[Z.le Z.lt Z.add Z.shiftl arr_len arr_get tables_ok ctab_ok tables_rep ctab_rep codes_live].
  split; [exact W1|]. split; [exact W2|]. split; [exact AL|].
  destruct M as [M|M]; rewrite M;
    repeat match goal with |- _ /\ _ => split end; intros HX;
    first [discriminate HX | destruct HX as [HX|HX]; discriminate HX | cbn in HX; discriminate HX].
Qed.


Section S.
  Variable iv : ivariant.

  Definition sync_entry (s : inflate_state) : inflate_state :=
    let s := iset_mode s SYNC in
    let k := Z.land (is_bits s) 7 in
    let s := iset_hold s (Z.shiftr (is_hold s) k) in
    let s := iset_bits s (is_bits s - k) in
    let '(s, buf) := sync_drain (S (Z.to_nat (Z.shiftr (is_bits s) 3))) s [] in
    let s := iset_have s 0 in
    let '(got, _) := syncsearch (is_have s) buf in
    iset_have s got.

  Lemma UI_sync_entry : forall s, UI s ->
    let s1 := sync_entry s in
    UI s1 /\ is_mode s1 = SYNC /\ 0 <= is_have s1 <= 4 /\ is_bits s1 < 8
    /\ is_flags s1 = is_flags s /\ is_wrap s1 = is_wrap s
    /\ arr_len (is_lens s1) = 320 /\ arr_len (is_work s1) = 288 /\ arr_len (is_codes s1) = 1444.
  Proof.
    intros s (R & SI & BI & CK). cbv zeta. unfold sync_entry.
    destruct R as (SR & [Hb Hh] & WS).
    set (k := Z.land (is_bits (iset_mode s SYNC)) 7).
    assert (Hk : 0 <= k <= 7 /\ k <= is_bits s).
    { subst k. replace (is_bits (iset_mode s SYNC)) with (is_bits s) by (destruct s; reflexivity).
      change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
      pose proof (Z.mod_pos_bound (is_bits s) 8 ltac:(lia)). pose proof (Z.mod_le (is_bits s) 8 ltac:(lia) ltac:(lia)).
      change (Z.ones 3) with 7. lia. }
    replace (is_bits (iset_hold (iset_mode s SYNC) (Z.shiftr (is_hold (iset_mode s SYNC)) k))) with (is_bits (iset_mode s SYNC)) by (destruct s; reflexivity).
    set (s2 := iset_bits (iset_hold (iset_mode s SYNC) (Z.shiftr (is_hold (iset_mode s SYNC)) k)) (is_bits (iset_mode s SYNC) - k)).
    assert (E2 : is_bits s2 = is_bits s - k /\ is_hold s2 = Z.shiftr (is_hold s) k /\ is_mode s2 = SYNC /\ icore s2 = icore (iset_mode s SYNC)
                 /\ is_whave s2 = is_whave s /\ is_wnext s2 = is_wnext s /\ is_wsize s2 = is_wsize s /\ is_window s2 = is_window s
                 /\ is_window_blk s2 = is_window_blk s /\ is_wbits s2 = is_wbits s /\ is_flags s2 = is_flags s /\ is_wrap s2 = is_wrap s).
    { subst s2. destruct s; repeat split; reflexivity. }
    destruct E2 as (Eb & Eh & Em & Ec & Ewh & Ewn & Ews & Ew & Ewb & Ewbits & Efl & Ewr).
    assert (Hh2 : 0 <= is_hold s2 < 2 ^ is_bits s2).
    { rewrite Eb, Eh, Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (is_bits s - k)) with (is_bits s) by lia. lia. }
    pose proof SR as SR'. destruct SR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [X1 X2] & [Y1 Y2] & _).
    assert (SR2 : SRNGq s2).
    { subst s2. replace (is_bits (iset_mode s SYNC)) with (is_bits s) in * by (destruct s; reflexivity).
      replace (is_hold (iset_mode s SYNC)) with (is_hold s) by (destruct s; reflexivity).
      apply SRNGq_hb; [apply SRNGq_mode'; [exact SR | unfold HEAD, SYNC; lia] | | lia].
      rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|]. nia. }
    pose proof (sync_drain_facts (S (Z.to_nat (Z.shiftr (is_bits s2) 3))) s2 [] ltac:(lia) Hh2) as D.
    assert (HF : Z.of_nat (S (Z.to_nat (Z.shiftr (is_bits s2) 3))) > is_bits s2 / 8).
    { rewrite Nat2Z.inj_succ, Z2Nat.id by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
    specialize (D HF). cbv zeta in D.
    destruct (sync_drain _ s2 []) as [s3 buf]. cbn [fst] in D. cbv beta iota.
    destruct D as (C3 & W13 & W23 & W33 & W43 & W53 & W63 & W73 & B3 & H3 & PP).
    specialize (PP SR2).
    replace (is_have (iset_have s3 0)) with 0 by (destruct s3; reflexivity).
    pose proof (syncsearch_bound 0 buf ltac:(lia)) as [G _].
    destruct (syncsearch 0 buf) as [got nx]. cbn [fst] in G. cbv beta iota.
    assert (M3 : is_mode s3 = SYNC /\ is_flags s3 = is_flags s /\ is_wrap s3 = is_wrap s
                 /\ arr_len (is_lens s3) = 320 /\ arr_len (is_work s3) = 288 /\ arr_len (is_codes s3) = 1444).
    { destruct SI as (_ & _ & (A1 & A2 & A3) & _). rewrite Ec in C3. clear -C3 Efl Ewr A1 A2 A3.
      destruct s3; destruct s; unfold icore in C3; cbn in *. injection C3; intros; subst. repeat split; first [reflexivity | assumption]. }
    destruct M3 as (M3 & F3 & R3 & A13 & A23 & A33).
    set (s4 := iset_have (iset_have s3 0) got).
    assert (E4 : icore2 s4 = icore2 s3 /\ is_mode s4 = is_mode s3 /\ is_have s4 = got /\ is_bits s4 = is_bits s3 /\ is_hold s4 = is_hold s3
                 /\ is_whave s4 = is_whave s3 /\ is_wnext s4 = is_wnext s3 /\ is_wsize s4 = is_wsize s3 /\ is_window s4 = is_window s3
                 /\ is_window_blk s4 = is_window_blk s3 /\ is_wbits s4 = is_wbits s3 /\ is_flags s4 = is_flags s3 /\ is_wrap s4 = is_wrap s3
                 /\ is_lens s4 = is_lens s3 /\ is_work s4 = is_work s3 /\ is_codes s4 = is_codes s3 /\ is_check s4 = is_check s3).
    { subst s4. clear. destruct s3; repeat split; reflexivity. }
    destruct E4 as (C4 & M4 & Hv4 & B4 & Ho4 & Wh4 & Wn4 & Wsz4 & Win4 & Wb4 & Wbits4 & Fl4 & Wr4 & L4 & Wk4 & Cd4 & Ck4).
    rewrite M3 in M4.
    split; [| rewrite M4, Hv4, B4, Fl4, Wr4, L4, Wk4, Cd4; repeat split; first [reflexivity | lia | congruence]].
    split; [| split; [| split]].
    -
      split; [| split].
      + subst s4. apply SRNGq_have; [apply SRNGq_have; [exact PP | lia] | lia].
      + rewrite B4, Ho4. lia.
      + rewrite Wb4, Win4, Wbits4, Wsz4, W53, W43, W63, W33, Ewb, Ew, Ewbits, Ews. exact WS.
    - apply (sinv_quiet s); [| left; exact M4 | rewrite Wh4, Wsz4 | rewrite Wn4, Wsz4 | exact SI].
      + rewrite C4. rewrite (icore2_of_icore (iset_mode s SYNC) s3) by (rewrite C3; exact Ec). destruct s; reflexivity.
      + rewrite W13, W33, Ewh, Ews. destruct SI as (Q1 & _); exact Q1.
      + rewrite W23, W33, Ewn, Ews. destruct SI as (_ & Q2 & _); exact Q2.
    - left. rewrite B4. lia.
    - unfold cks. rewrite M4. intros X. exfalso. unfold TYPE, CHECK, SYNC in X. lia.
  Qed.

  Lemma reset_facts : forall s z, inflateStateCheck s = false -> SRNGq s ->
    let '(s', z', rc) := inflateReset iv s z in
    rc = Z_OK /\ SRNGq s' /\ is_bits s' = 0 /\ is_hold s' = 0 /\ is_wsize s' = 0 /\ is_whave s' = 0 /\ is_wnext s' = 0
    /\ is_window_blk s' = is_window_blk s /\ is_window s' = is_window s /\ is_wbits s' = is_wbits s
    /\ is_wrap s' = is_wrap s /\ is_mode s' = HEAD /\ icore2 (iset_mode s' HEAD) = icore2 (iset_next (iset_distcode (iset_lencode s (CDyn 0)) (CDyn 0)) 0)
    /\ arr_len (is_lens s') = arr_len (is_lens s) /\ arr_len (is_work s') = arr_len (is_work s) /\ arr_len (is_codes s') = arr_len (is_codes s)
    /\ (zs_adler z' = zs_adler z \/ zs_adler z' = Z.land (is_wrap s) 1) /\ zs_data_type z' = zs_data_type z.
  Proof.
    intros s z CK SR. unfold inflateReset, inflateResetKeep, auxp. rewrite CK.
    replace (inflateStateCheck (iset_wnext (iset_whave (iset_wsize s 0) 0) 0)) with false by (rewrite <- CK; destruct s; reflexivity).
    ds s. unfold SRNGq in SR. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in SR.
    repeat match goal with K : _ /\ _ |- _ => destruct K end.
    destruct (iv_aux iv); cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB Z.land]; destruct (negb (f_wrap =? 0));
      cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB Z.land];
      unfold SRNGq; cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB Z.land]; unfold HEAD, SYNC in *;
      (repeat match goal with |- _ /\ _ => split end); first [assumption | reflexivity | lia | (left; reflexivity) | (right; reflexivity)].
  Qed.

  Lemma land_lnot4 : forall x, 0 <= x < 16 -> 0 <= Z.land x (Z.lnot 4) <= x /\ Z.land (Z.land x (Z.lnot 4)) 4 = 0.
  Proof.
    intros x Hx. rewrite <- (Z2Nat.id x) by lia. remember (Z.to_nat x) as n eqn:En.
    assert (Hn : (n < 16)%nat) by lia. clear En Hx.
    do 16 (destruct n as [|n]; [cbv -[Z.le Z.lt]; lia|]). lia.
  Qed.

  Lemma land_le1 : forall x, 0 <= x < 16 -> 0 <= Z.land x 1 <= 1.
  Proof.
    intros x Hx. rewrite <- (Z2Nat.id x) by lia. remember (Z.to_nat x) as n eqn:En.
    assert (Hn : (n < 16)%nat) by lia. clear En Hx.
    do 16 (destruct n as [|n]; [cbv -[Z.le Z.lt]; lia|]). lia.
  Qed.

  Definition SPOST (zc : ZCall) (r : ZRet) : Prop :=
    zret_ok r /\ 0 <= zr_consumed r <= zlength (zc_input zc) /\ zr_output r = []
    /\ In (zr_rc r) [Z_OK; Z_STREAM_ERROR; Z_BUF_ERROR; Z_DATA_ERROR]
    /\ zs_total_out (zr_strm r) = zs_total_out (zc_strm zc)
    /\ zs_data_type (zr_strm r) = zs_data_type (zc_strm zc).

  Theorem inflateSync_post : forall s zc, UI s -> zcall_ok zc ->
    let '(s', r) := inflateSync_m iv s zc in
    UI s' /\ SPOST zc r /\ (zr_rc r = Z_OK -> is_mode s' = TYPE /\ is_bits s' = 0 /\ is_hold s' = 0 /\ Z.land (is_wrap s') 4 = 0).
  Proof.
    intros s zc U ZC. pose proof U as (R & SI & BI & CK). pose proof R as (SR & [Hb Hh] & WS).
    destruct ZC as (_ & _ & _ & Ti & To & Ad & Dt).
    unfold inflateSync_m.
    destruct (inflateStateCheck s) eqn:CHK.
    { split; [exact U|]. split; [| intros X; discriminate X]. unfold SPOST, zret_ok; cbn. pose proof (zlength_nonneg (zc_input zc)).
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity. }
    destruct ((zlength (zc_input zc) =? 0) && (is_bits s <? 8)).
    { split; [exact U|]. split; [| intros X; discriminate X]. unfold SPOST, zret_ok; cbn. pose proof (zlength_nonneg (zc_input zc)).
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity. }
    change (if negb (is_mode s =? SYNC) then _ else s) with (if negb (is_mode s =? SYNC) then sync_entry s else s).
    assert (S1 : exists s1, (if negb (is_mode s =? SYNC) then sync_entry s else s) = s1 /\ UI s1 /\ is_mode s1 = SYNC
                 /\ is_flags s1 = is_flags s /\ is_wrap s1 = is_wrap s
                 /\ arr_len (is_lens s1) = 320 /\ arr_len (is_work s1) = 288 /\ arr_len (is_codes s1) = 1444).
    { destruct (Z.eqb_spec (is_mode s) SYNC) as [M|M]; cbn [negb].
      - exists s. destruct SI as (_ & _ & (A1 & A2 & A3) & _). split; [reflexivity|]. split; [exact U|]. repeat split; auto.
      - exists (sync_entry s). pose proof (UI_sync_entry s U) as X. cbv zeta in X.
        destruct X as (U1 & M1 & _ & _ & F1 & W1 & L1 & L2 & L3). split; [reflexivity|]. split; [exact U1|]. repeat split; auto. }
    destruct S1 as (s1 & -> & U1 & M1 & F1 & W1 & L1 & L2 & L3).
    pose proof U1 as (R1 & SI1 & BI1 & CK1). pose proof R1 as (SR1 & [Hb1 Hh1] & WS1).
    assert (HV1 : 0 <= is_have s1 < 2 ^ 32) by (clear -SR1; destruct SR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (syncsearch_bound (is_have s1) (zc_input zc) ltac:(lia)) as [G1 G2].
    destruct (syncsearch (is_have s1) (zc_input zc)) as [got len]. cbn [fst snd] in G1, G2.
    replace (is_have (iset_have s1 got)) with got by (destruct s1; reflexivity).
    set (s5 := iset_have s1 got).
    assert (E5 : icore2 s5 = icore2 s1 /\ is_mode s5 = SYNC /\ is_bits s5 = is_bits s1 /\ is_hold s5 = is_hold s1
                 /\ is_whave s5 = is_whave s1 /\ is_wnext s5 = is_wnext s1 /\ is_wsize s5 = is_wsize s1 /\ is_window s5 = is_window s1
                 /\ is_window_blk s5 = is_window_blk s1 /\ is_wbits s5 = is_wbits s1 /\ is_flags s5 = is_flags s /\ is_wrap s5 = is_wrap s
                 /\ arr_len (is_lens s5) = 320 /\ arr_len (is_work s5) = 288 /\ arr_len (is_codes s5) = 1444 /\ is_check s5 = is_check s1).
    { subst s5. rewrite <- M1, <- F1, <- W1, <- L1, <- L2, <- L3. clear. destruct s1; repeat split; reflexivity. }
    destruct E5 as (C5 & M5 & B5 & Ho5 & Wh5 & Wn5 & Ws5 & Wi5 & Wb5 & Wbits5 & F5 & W5 & L15 & L25 & L35 & Ck5).
    assert (SR5 : SRNGq s5) by (subst s5; apply SRNGq_have; [exact SR1 | lia]).
    assert (U5 : UI s5).
    { split; [| split; [| split]].
      - split; [exact SR5|]. split; [rewrite B5, Ho5; lia|]. rewrite Wb5, Wi5, Wbits5, Ws5. exact WS1.
      - apply (sinv_quiet s1); [exact C5 | left; exact M5 | rewrite Wh5, Ws5 | rewrite Wn5, Ws5 | exact SI1];
          [destruct SI1 as (Q1 & _); exact Q1 | destruct SI1 as (_ & Q2 & _); exact Q2].
      - unfold binv_saved. rewrite M5. right. unfold PEND, SYNC. cbn. exact I.
      - unfold cks. rewrite M5. intros X. exfalso. unfold TYPE, CHECK, SYNC in X. lia. }
    assert (ZOK : forall rc, In rc [Z_OK; Z_STREAM_ERROR; Z_BUF_ERROR; Z_DATA_ERROR] ->
              SPOST zc (mkZRet len [] (zs_set_total_in (wrap64 (zs_total_in (zc_strm zc) + len)) (zc_strm zc)) rc)).
    { intros rc Hrc. unfold SPOST, zret_ok. cbn. pose proof (wrap64_range (zs_total_in (zc_strm zc) + len)).
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity. exact Hrc. }
    destruct (Z.eqb_spec got 4) as [G4|G4]; cbn [negb].
    2:{ split; [exact U5|]. split; [apply ZOK; right; right; right; left; reflexivity | intros X; discriminate X]. }
    set (sw := if is_flags s5 =? -1 then iset_wrap s5 0 else iset_wrap s5 (Z.land (is_wrap s5) (Z.lnot 4))).
    assert (WR : 0 <= is_wrap s5 < 16) by (clear -SR5; destruct SR5 as (_ & _ & X & _); exact X).
    assert (Ew : exists v, sw = iset_wrap s5 v /\ 0 <= v < 16 /\ Z.land v 4 = 0).
    { subst sw. destruct (is_flags s5 =? -1).
      - exists 0. repeat split; try reflexivity; lia.
      - exists (Z.land (is_wrap s5) (Z.lnot 4)). pose proof (land_lnot4 (is_wrap s5) WR). repeat split; try reflexivity; lia. }
    destruct Ew as (v & Esw & Hv & Hv4). rewrite Esw. clear sw Esw.
    assert (SRw : SRNGq (iset_wrap s5 v)) by (apply SRNGq_wrap; [exact SR5 | exact Hv]).
    assert (CKw : inflateStateCheck (iset_wrap s5 v) = false).
    { unfold inflateStateCheck. replace (is_mode (iset_wrap s5 v)) with SYNC by (rewrite <- M5; destruct s5; reflexivity).
      reflexivity. }
    replace (is_flags (iset_wrap s5 v)) with (is_flags s) by (rewrite <- F5; destruct s5; reflexivity).
    pose proof (reset_facts (iset_wrap s5 v) (zs_set_total_in (wrap64 (zs_total_in (zc_strm zc) + len)) (zc_strm zc)) CKw SRw) as RF.
    destruct (inflateReset iv (iset_wrap s5 v) _) as [[sr zr] rc] eqn:ER.
    destruct RF as (Hrc & SRr & Br & Hr & Wsr & Whr & Wnr & Wbr & Wir & Wbitsr & Wrr & Mr & Cr & L1r & L2r & L3r & Adr & Dtr).
    assert (SIr : sinv sr).
    { assert (AL : arr_len (is_lens (iset_wrap s5 v)) = 320 /\ arr_len (is_work (iset_wrap s5 v)) = 288 /\ arr_len (is_codes (iset_wrap s5 v)) = 1444).
      { rewrite <- L15, <- L25, <- L35. clear. destruct s5; repeat split; reflexivity. }
      destruct AL as (AL1 & AL2 & AL3).
      destruct (reset_ok iv _ _ sr zr rc ER Hrc AL1 AL2 AL3) as (X & _ & _). exact X. }
    assert (FLr : - 2 ^ 31 <= is_flags s < 2 ^ 31) by (clear -SR; destruct SR as (_ & _ & _ & _ & X & _); exact X).
    set (s6 := iset_mode (iset_flags sr (is_flags s)) TYPE).
    assert (E6 : icore2 s6 = icore2 (iset_mode sr HEAD) /\ is_mode s6 = TYPE /\ is_bits s6 = is_bits sr /\ is_hold s6 = is_hold sr
                 /\ is_whave s6 = is_whave sr /\ is_wnext s6 = is_wnext sr /\ is_wsize s6 = is_wsize sr /\ is_window s6 = is_window sr
                 /\ is_window_blk s6 = is_window_blk sr /\ is_wbits s6 = is_wbits sr /\ is_wrap s6 = is_wrap sr).
    { subst s6. clear. destruct sr; repeat split; reflexivity. }
    destruct E6 as (C6 & M6 & B6 & Ho6 & Wh6 & Wn6 & Ws6 & Wi6 & Wb6 & Wbits6 & W6).
    rewrite Br in B6. rewrite Hr in Ho6. rewrite Whr in Wh6. rewrite Wnr in Wn6. rewrite Wsr in Ws6.
    assert (Wv : is_wrap (iset_wrap s5 v) = v) by (destruct s5; reflexivity).
    split; [| split].
    - split; [| split; [| split]].
      + split; [subst s6; apply SRNGq_mode'; [apply SRNGq_flags; [exact SRr | exact FLr] | unfold HEAD, TYPE, SYNC; lia]|].
        split; [rewrite B6, Ho6; cbn; lia|].
        rewrite Wb6, Wi6, Wbits6, Ws6, Wbr, Wir, Wbitsr.
        replace (is_window_blk (iset_wrap s5 v)) with (is_window_blk s5) by (destruct s5; reflexivity).
        replace (is_window (iset_wrap s5 v)) with (is_window s5) by (destruct s5; reflexivity).
        replace (is_wbits (iset_wrap s5 v)) with (is_wbits s5) by (destruct s5; reflexivity).
        rewrite Wb5, Wi5, Wbits5. destruct (is_window_blk s1); [destruct WS1 as [X _]; split; [exact X | left; reflexivity] | destruct WS1 as [X _]; split; [exact X | reflexivity]].
      + apply (sinv_quiet sr); [exact C6 | right; exact M6 | rewrite Wh6, Ws6; lia | rewrite Wn6, Ws6; lia | exact SIr].
      + left. rewrite B6. lia.
      + unfold cks. rewrite W6, Wrr, Wv, Hv4. intros _ X. exfalso. exact (X eq_refl).
    - unfold SPOST, zret_ok. cbn. pose proof (wrap64_range (zs_total_in (zc_strm zc) + len)).
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
      + destruct Adr as [-> | ->]; [cbn; lia | rewrite Wv; apply Z.land_nonneg; lia].
      + destruct Adr as [-> | ->]; [cbn; lia | rewrite Wv]. pose proof (land_le1 v ltac:(lia)). lia.
      + rewrite Dtr. cbn. lia.
      + rewrite Dtr. cbn. lia.
      + rewrite Dtr. reflexivity.
    - intros _. rewrite M6, B6, Ho6, W6, Wrr, Wv, Hv4. repeat split; reflexivity.
  Qed.
End S.
