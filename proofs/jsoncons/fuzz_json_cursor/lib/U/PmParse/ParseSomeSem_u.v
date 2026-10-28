(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSS.

Definition upd (ps : pstate) (st sst nst : Z) (more done : bool) (bcap bptr : Z) (buf : list Z) (w : option (Z * Z)) : pstate :=
  PS st sst nst more done (ps_level ps) (ps_stack ps) (ps_sb ps) (ps_scap ps) bcap bptr buf w.

Lemma wf_stop : forall ps st sst nst done bcap bptr buf w, wf_ps ps -> 0 <= sst <= 11 -> 0 <= nst <= 7 -> wf_ps (upd ps st sst nst false done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hs Hn. unfold wf_ps, upd. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [exact Hs|]. split; [exact Hn|]. split; [exact W3|]. split; [exact W4|]. exists C, T. split; [exact W5|]. split; [exact W6|]. intros X. discriminate X.
Qed.

Lemma wf_plain : forall ps st sst nst done bcap bptr buf w,
  wf_ps ps -> ps_more ps = true -> ~ comment_or_cr (ps_st ps) -> ps_st ps <> ST_STRING ->
  handled st -> ~ comment_or_cr st -> (st = ST_EXPECT_COMMA_OR_END -> 1 <= ps_level ps) -> (st = ST_NUMBER -> num_prefix nst buf) -> 0 <= sst <= 11 -> 0 <= nst <= 7 ->
  wf_ps (upd ps st sst nst true done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hnc Hns Hh Hnc' H7 Hnum Hs Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (HT : T = []).
  { destruct X4 as [(HT & _)|[(_ & Hst)|[(S & _ & _ & Hc)|(S & _ & _ & Hc)]]]; [exact HT | contradiction | contradiction | exfalso; apply Hnc; right; exact Hc]. }
  unfold wf_ps, upd. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [exact Hs|]. split; [exact Hn|]. split; [exact W3|]. split; [exact W4|]. exists C, T. split; [exact W5|]. split; [exact W6|]. intros _.
  split; [exact X1|]. split; [exact X2|]. split; [exact Hh|]. split; [left; split; [exact HT | exact Hnc']|].
  split; [intros [Hc|Hc]; [exact (H7 Hc) | rewrite HT in Hc; destruct Hc] | exact Hnum].
Qed.

Lemma wf_pop : forall ps rest x sst nst done bcap bptr buf w,
  wf_ps ps -> ps_more ps = true -> comment_or_cr (ps_st ps) -> ps_stack ps = rest ++ [x] -> 0 <= sst <= 11 -> 0 <= nst <= 7 ->
  wf_ps (PS x sst nst true done (ps_level ps) rest (ps_sb ps) (ps_scap ps) bcap bptr buf w) /\ (is_expect x \/ (x = ST_SLASH_STAR /\ ps_st ps = ST_CR)).
Proof.
  intros ps rest x sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hc Hstk Hs Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (HEX : forall S, is_expect S -> handled S /\ ~ comment_or_cr S /\ S <> ST_NUMBER).
  { intros S HS. unfold is_expect in HS. cbn [In] in HS. unfold handled, comment_or_cr, ST_CR, ST_NUMBER. lia. }
  assert (LEN : (length rest <= 1027)%nat) by (rewrite Hstk, length_app in W3; cbn [length] in W3; lia).
  destruct X4 as [(HT & Hnc)|[(_ & Hst)|[(S & HS & HT & _)|(S & HS & HT & Hcr)]]].
  - contradiction.
  - exfalso. rewrite Hst in Hc. unfold comment_or_cr, ST_STRING, ST_CR in Hc. lia.
  -
    assert (Hx : rest = ST_ROOT :: C /\ x = S).
    { rewrite W5, HT in Hstk. change (ST_ROOT :: C ++ [S]) with ((ST_ROOT :: C) ++ [S]) in Hstk. apply app_inj_tail in Hstk. destruct Hstk as [<- <-]. split; reflexivity. }
    destruct Hx as [-> ->]. destruct (HEX S HS) as (Hh & Hnc & Hnn). split; [|left; exact HS].
    unfold wf_ps. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
    split; [exact Hs|]. split; [exact Hn|]. split; [exact LEN|]. split; [exact W4|]. exists C, []. split; [rewrite app_nil_r; reflexivity|]. split; [exact W6|]. intros _.
    split; [exact X1|]. split; [exact X2|]. split; [exact Hh|]. split; [left; split; [reflexivity | exact Hnc]|].
    split; [intros [He|[]]; apply X5; right; rewrite HT; left; exact He | intros He; contradiction].
  -
    assert (Hx : rest = ST_ROOT :: C ++ [S] /\ x = ST_SLASH_STAR).
    { rewrite W5, HT in Hstk.
      replace (ST_ROOT :: C ++ [S; ST_SLASH_STAR]) with ((ST_ROOT :: C ++ [S]) ++ [ST_SLASH_STAR]) in Hstk by (cbn [app]; rewrite <- app_assoc; reflexivity).
      apply app_inj_tail in Hstk. destruct Hstk as [<- <-]. split; reflexivity. }
    destruct Hx as [-> ->]. split; [|right; split; [reflexivity | exact Hcr]].
    unfold wf_ps. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
    split; [exact Hs|]. split; [exact Hn|]. split; [exact LEN|]. split; [exact W4|]. exists C, [S]. split; [reflexivity|]. split; [exact W6|]. intros _.
    split; [exact X1|]. split; [exact X2|]. split; [unfold handled, ST_SLASH_STAR; lia|].
    split; [right; right; left; exists S; split; [exact HS | split; [reflexivity | unfold comment_or_cr, ST_SLASH_STAR; lia]]|].
    split; [intros [He|He]; [unfold ST_SLASH_STAR, ST_EXPECT_COMMA_OR_END in He; lia | apply X5; right; rewrite HT; destruct He as [He|[]]; left; exact He]
           | intros He; unfold ST_SLASH_STAR, ST_NUMBER in He; lia].
Qed.

Lemma wf_comment : forall ps st sst nst done bcap bptr buf w,
  wf_ps ps -> ps_more ps = true -> 3 <= ps_st ps <= 6 -> 3 <= st <= 6 -> 0 <= sst <= 11 -> 0 <= nst <= 7 ->
  wf_ps (upd ps st sst nst true done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hc Hc' Hs Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  unfold wf_ps, upd. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [exact Hs|]. split; [exact Hn|]. split; [exact W3|]. split; [exact W4|]. exists C, T. split; [exact W5|]. split; [exact W6|]. intros _.
  split; [exact X1|]. split; [exact X2|]. split; [unfold handled; lia|].
  split; [|split; [intros [He|He]; [unfold ST_EXPECT_COMMA_OR_END in He; lia | exact (X5 (or_intror He))] | intros He; unfold ST_NUMBER in He; lia]].
  destruct X4 as [(_ & Hnc)|[(_ & Hst)|[(S & HS & HT & _)|(S & _ & _ & Hcr)]]].
  - exfalso. apply Hnc. left. exact Hc.
  - unfold ST_STRING in Hst. lia.
  - right. right. left. exists S. split; [exact HS | split; [exact HT | left; exact Hc']].
  - unfold ST_CR in Hcr. lia.
Qed.

Lemma wf_push_slash : forall ps sst nst done bcap bptr buf w sb' scap',
  wf_ps ps -> ps_more ps = true -> is_expect (ps_st ps) -> In scap' [66; 132; 264; 528; 1056] -> 0 <= sst <= 11 -> 0 <= nst <= 7 ->
  wf_ps (PS ST_SLASH sst nst true done (ps_level ps) (ps_stack ps ++ [ps_st ps]) sb' scap' bcap bptr buf w) /\ (length (ps_stack ps) <= 1025)%nat.
Proof.
  intros ps sst nst done bcap bptr buf w sb' scap' (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm He Hsc Hs Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (Hnc : ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING) by (unfold is_expect in He; cbn [In] in He; unfold comment_or_cr, ST_CR, ST_STRING; lia).
  assert (HT : T = []).
  { destruct X4 as [(HT & _)|[(_ & Hst)|[(S & _ & _ & Hc)|(S & _ & _ & Hc)]]]; [exact HT | destruct Hnc; contradiction | destruct Hnc; contradiction | exfalso; apply (proj1 Hnc); right; exact Hc]. }
  assert (LEN : (length (ps_stack ps) <= 1025)%nat) by (rewrite W5, HT, app_nil_r; cbn [length]; lia).
  split; [|exact LEN].
  unfold wf_ps. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [exact Hs|]. split; [exact Hn|]. split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hsc|]. exists C, [ps_st ps].
  split; [rewrite W5, HT, app_nil_r; reflexivity|]. split; [exact W6|]. intros _.
  split; [exact X1|]. split; [exact X2|]. split; [unfold handled, ST_SLASH; lia|].
  split; [right; right; left; exists (ps_st ps); split; [exact He | split; [reflexivity | unfold comment_or_cr, ST_SLASH; lia]]|].
  split; [intros [Hx|[Hx|[]]]; [unfold ST_SLASH, ST_EXPECT_COMMA_OR_END in Hx; lia | exact (X5 (or_introl Hx))] | intros Hx; unfold ST_SLASH, ST_NUMBER in Hx; lia].
Qed.

Lemma wf_push_cr : forall ps sst nst done bcap bptr buf w sb' scap',
  wf_ps ps -> ps_more ps = true -> ps_st ps = ST_SLASH_STAR -> In scap' [66; 132; 264; 528; 1056] -> 0 <= sst <= 11 -> 0 <= nst <= 7 ->
  wf_ps (PS ST_CR sst nst true done (ps_level ps) (ps_stack ps ++ [ST_SLASH_STAR]) sb' scap' bcap bptr buf w) /\ (length (ps_stack ps) <= 1026)%nat.
Proof.
  intros ps sst nst done bcap bptr buf w sb' scap' (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hst Hsc Hs Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (HT : exists S, is_expect S /\ T = [S]).
  { rewrite Hst in X4. unfold transient, comment_or_cr, ST_SLASH_STAR, ST_STRING, ST_CR in X4.
    destruct X4 as [(_ & Hc)|[(_ & Hc)|[(S & HS & HT & _)|(S & _ & _ & Hc)]]]; [exfalso; apply Hc; lia | discriminate Hc | exists S; split; assumption | discriminate Hc]. }
  destruct HT as (S & HS & ->).
  assert (LEN : (length (ps_stack ps) <= 1026)%nat) by (rewrite W5; cbn [length]; rewrite length_app; cbn [length]; lia).
  split; [|exact LEN].
  unfold wf_ps. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [exact Hs|]. split; [exact Hn|]. split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hsc|]. exists C, [S; ST_SLASH_STAR].
  split; [rewrite W5; cbn [app]; rewrite <- app_assoc; reflexivity|]. split; [exact W6|]. intros _.
  split; [exact X1|]. split; [exact X2|]. split; [unfold handled, ST_CR; lia|].
  split; [right; right; right; exists S; split; [exact HS | split; reflexivity]|].
  split; [intros [Hx|[Hx|[Hx|[]]]]; [unfold ST_CR, ST_EXPECT_COMMA_OR_END in Hx; lia | apply X5; right; left; exact Hx | unfold ST_SLASH_STAR, ST_EXPECT_COMMA_OR_END in Hx; lia]
         | intros Hx; unfold ST_CR, ST_NUMBER in Hx; lia].
Qed.

Lemma wf_push_member : forall ps nst done bcap bptr buf w sb' scap',
  wf_ps ps -> ps_more ps = true -> (ps_st ps = ST_EXPECT_MEMBER_NAME_OR_END \/ ps_st ps = ST_EXPECT_MEMBER_NAME) -> In scap' [66; 132; 264; 528; 1056] -> 0 <= nst <= 7 ->
  wf_ps (PS ST_STRING 0 nst true done (ps_level ps) (ps_stack ps ++ [ST_MEMBER_NAME]) sb' scap' bcap bptr buf w) /\ (length (ps_stack ps) <= 1025)%nat.
Proof.
  intros ps nst done bcap bptr buf w sb' scap' (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hst Hsc Hn.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (Hnc : ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING) by (unfold comment_or_cr, ST_CR, ST_STRING, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME in *; lia).
  assert (HT : T = []).
  { destruct X4 as [(HT & _)|[(_ & Hc)|[(S & _ & _ & Hc)|(S & _ & _ & Hc)]]]; [exact HT | destruct Hnc; contradiction | destruct Hnc; contradiction | exfalso; apply (proj1 Hnc); right; exact Hc]. }
  assert (LEN : (length (ps_stack ps) <= 1025)%nat) by (rewrite W5, HT, app_nil_r; cbn [length]; lia).
  split; [|exact LEN].
  unfold wf_ps. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [lia|]. split; [exact Hn|]. split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hsc|]. exists C, [ST_MEMBER_NAME].
  split; [rewrite W5, HT, app_nil_r; reflexivity|]. split; [exact W6|]. intros _.
  split; [exact X1|]. split; [exact X2|]. split; [unfold handled, ST_STRING; lia|].
  split; [right; left; split; reflexivity|].
  split; [intros [Hx|[Hx|[]]]; [unfold ST_STRING, ST_EXPECT_COMMA_OR_END in Hx; lia | unfold ST_MEMBER_NAME, ST_EXPECT_COMMA_OR_END in Hx; lia] | intros Hx; unfold ST_STRING, ST_NUMBER in Hx; lia].
Qed.

Lemma stk_grow : forall (L : heap_layout) (cr : credit) cap scap kx bx, 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> 0 <= kx -> 0 <= bx -> In scap [66; 132; 264; 528] ->
  PPS.bufcred L cr cap (PPS.stk_kx L scap + kx) (PPS.stk_bx L scap + bx) ->
  credit_ok L cr (2 * scap) /\ PPS.bufcred L (debit L cr (2 * scap)) cap (PPS.stk_kx L (2 * scap) + kx) (PPS.stk_bx L (2 * scap) + bx).
Proof.
  intros L cr cap scap kx bx Hk Hb Hkx Hbx Hs (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.log2_nonneg (2 ^ 27 / cap)) as L0. set (lb := Z.log2 (2 ^ 27 / cap)) in *.
  unfold PPS.stk_kx, PPS.stk_bx in *. unfold credit_ok, debit, PPS.bufcred. cbn [fst snd]. fold lb.
  pose proof (Z.mul_nonneg_nonneg lb _ L0 Hk) as N1. pose proof (Z.mul_nonneg_nonneg lb _ L0 Hb) as N2.
  set (pk := lb * hl_k_per_malloc L) in *. set (pb := lb * hl_b_overhead L) in *.
  cbn [In] in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]].
  - change (Z.log2 (1056 / 66)) with 4 in *. change (Z.log2 (1056 / (2 * 66))) with 3. repeat split; lia.
  - change (Z.log2 (1056 / 132)) with 3 in *. change (Z.log2 (1056 / (2 * 132))) with 2. repeat split; lia.
  - change (Z.log2 (1056 / 264)) with 2 in *. change (Z.log2 (1056 / (2 * 264))) with 1. repeat split; lia.
  - change (Z.log2 (1056 / 528)) with 1 in *. change (Z.log2 (1056 / (2 * 528))) with 0. repeat split; lia.
Qed.
End PSS.
