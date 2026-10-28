(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Wf_nat Wellfounded.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMRF2.
Import PML PMR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fcall (f : PMW.fname) (c : ctrl) (w : list Z) : res :=
  match f with
  | PMW.FSkipSpace => skip_space_r c w
  | PMW.FBeginMember => begin_member c w
  | PMW.FAfterValue => after_value c w
  | PMW.FBeginObject => begin_container false c w
  | PMW.FBeginArray => begin_container true c w
  | PMW.FEndObject => end_container false c w
  | PMW.FEndArray => end_container true c w
  | PMW.FParseTrue => parse_true c w
  | PMW.FParseFalse => parse_false c w
  | PMW.FParseNull => parse_null c w
  | PMW.FParseString => parse_string c w
  | PMW.FParseNumber => parse_number c w
  | PMW.FParseSome => parse_some c w
  | PMW.FCheckDone => pcheck_done c w
  | _ => err c w E_STUCK
  end.
Definition win_callee (f : PMW.fname) : bool :=
  match f with PMW.FEndStringValue | PMW.FEndInt | PMW.FEndFrac | PMW.FSkipWs => false | _ => true end.
Lemma rstep_fcall : forall f c w, win_callee f = true -> rstep f c w = r_of w (fcall f c w).
Proof. intros f c w H. destruct f; try reflexivity; discriminate H. Qed.
(* [comment removed for export] *)
Lemma r_of_ctrl : forall w q, PMW.r_ctrl (r_of w q) = q_c q.    Proof. reflexivity. Qed.
Lemma r_of_evs : forall w q, PMW.r_evs (r_of w q) = q_evs q.    Proof. reflexivity. Qed.
Lemma r_of_code : forall w q, PMW.r_code (r_of w q) = q_code q.  Proof. reflexivity. Qed.
Lemma r_of_allow : forall w q, PMW.r_allow (r_of w q) = q_al q.  Proof. reflexivity. Qed.
Lemma r_of_used : forall w q, PMW.r_used (r_of w q) = Z.of_nat (length w) - Z.of_nat (length (q_w q)).  Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nst_of_byte (b : Z) : Z := if b =? 45 then NS_MINUS else if b =? 48 then NS_ZERO else NS_INTEGER.
Definition string_entry (key : bool) (c : ctrl) : ctrl := tok_clear (set_sst (set_st (if key then push c ST_MEMBER_NAME else c) ST_STRING) SS_TEXT).
Definition number_entry (c : ctrl) (b : Z) : ctrl := set_nst (set_st (tok1 (tok_clear c) b) ST_NUMBER) (nst_of_byte b).
Definition call_of (a : act) (c : ctrl) (b : Z) (r : list Z) : option (PMW.fname * ctrl * list Z) :=
  match a with
  | ASkip => Some (PMW.FSkipSpace, c, b :: r)
  | ABegin arr => Some ((if arr then PMW.FBeginArray else PMW.FBeginObject), c, r)
  | AEnd arr => Some ((if arr then PMW.FEndArray else PMW.FEndObject), c, r)
  | AString key => Some (PMW.FParseString, string_entry key c, r)
  | ANumber => Some (PMW.FParseNumber, number_entry c b, r)
  | ALit which => Some ((if which =? 0 then PMW.FParseNull else if which =? 1 then PMW.FParseTrue else PMW.FParseFalse), c, b :: r)
  | AComma => Some (PMW.FBeginMember, c, b :: r)
  | AParseString => Some (PMW.FParseString, c, b :: r)
  | AParseNumber => Some (PMW.FParseNumber, c, b :: r)
  | _ => None
  end.
Lemma call_of_win : forall a c b r f c' w', call_of a c b r = Some (f, c', w') -> win_callee f = true /\ (w' = b :: r \/ w' = r).
Proof.
  intros a c b r f c' w' H. destruct a; cbn in H; try discriminate H; injection H as <- <- <-; (split; [| first [left; reflexivity | right; reflexivity]]);
    try reflexivity.
  - destruct arr; reflexivity.
  - destruct arr; reflexivity.
  - destruct (which =? 0); [reflexivity|]. destruct (which =? 1); reflexivity.
Qed.
Lemma call_of_fn : forall a c b r f c' w', call_of a c b r = Some (f, c', w') -> f <> PMW.FParseSome /\ f <> PMW.FCheckDone.
Proof.
  intros a c b r f c' w' H. destruct a; cbn in H; try discriminate H; injection H as <- _ _; try (split; discriminate).
  - destruct arr; split; discriminate.
  - destruct arr; split; discriminate.
  - destruct (which =? 0); [split; discriminate|]. destruct (which =? 1); split; discriminate.
Qed.
Lemma iter_call : forall a c b r f c' w', call_of a c b r = Some (f, c', w') -> a <> AComma -> act_run a c b r = fcall f c' w'.
Proof.
  intros a c b r f c' w' H Hn. destruct a; cbn in H; try discriminate H; injection H as <- <- <-;
    first [ exfalso; exact (Hn eq_refl)
          | destruct arr; reflexivity
          | cbn [act_run]; destruct (which =? 0); [reflexivity|]; destruct (which =? 1); reflexivity
          | reflexivity ].
Qed.
Lemma iter_comma : forall c b r, act_run AComma c b r = bind (begin_member c (b :: r)) (fun c1 _ => ret c1 r).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_all : forall {A} (w : list A), skipn (length w) w = [].
Proof. intros A w. apply skipn_all. Qed.
Lemma skipn_length_min : forall {A} u (w : list A), length (skipn u w) = (length w - Nat.min u (length w))%nat.
Proof. intros A u w. rewrite length_skipn. lia. Qed.
(* [comment removed for export] *)
Lemma skipn_used : forall {A} u (w : list A), skipn (length w - length (skipn u w)) w = skipn u w.
Proof.
  intros A u w. rewrite length_skipn.
  destruct (Nat.le_gt_cases u (length w)) as [H|H].
  - replace (length w - (length w - u))%nat with u by lia. reflexivity.
  - replace (length w - (length w - u))%nat with (length w) by lia. rewrite skipn_all. symmetry. apply skipn_all2. lia.
Qed.
Lemma used_to_nat : forall {A} u (w : list A), Z.to_nat (Z.of_nat (length w) - Z.of_nat (length (skipn u w))) = (length w - length (skipn u w))%nat.
Proof. intros A u w. pose proof (PMRF.length_skipn_le u w). lia. Qed.

Definition wsuf (q : res) (w : list Z) : Prop := exists u, q_w q = skipn u w.
Lemma wsuf_same : forall q w, q_w q = w -> wsuf q w.      Proof. intros q w H. exists 0%nat. exact H. Qed.
Lemma wsuf_tl : forall q b r, wsuf q r -> wsuf q (b :: r). Proof. intros q b r [u Hu]. exists (S u). exact Hu. Qed.
Lemma wsuf_nil : forall q w, q_w q = [] -> wsuf q w.      Proof. intros q w H. exists (length w). rewrite H. symmetry. apply skipn_all. Qed.

Lemma skip_space_suffix : forall w c, exists u, snd (skip_space c w) = skipn u w.
Proof.
  intros w. induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length Z))). intros c. unfold Wf_nat.ltof in IH.
  destruct w as [|b r]; [exists 0%nat; reflexivity|]. cbn -[Z.eqb skipn].
  destruct ((b =? 32) || (b =? 9) || (b =? 10)).
  - destruct (IH r ltac:(cbn; lia) c) as [u Hu]. exists (S u). exact Hu.
  - destruct (b =? 13).
    + destruct r as [|b2 r2]; [exists 1%nat; reflexivity|]. destruct (b2 =? 10).
      * destruct (IH r2 ltac:(cbn; lia) c) as [u Hu]. exists (S (S u)). exact Hu.
      * destruct (IH (b2 :: r2) ltac:(cbn; lia) c) as [u Hu]. exists (S u). exact Hu.
    + exists 0%nat. reflexivity.
Qed.
Lemma end_number_w : forall c w, q_w (end_number c w) = w.
Proof. intros c w. exact (proj1 (PMRF.end_number_shape c w)). Qed.
Lemma end_string_suffix : forall c w, wsuf (end_string c w) w.
Proof.
  intros c w. unfold end_string.
  destruct (negb (u8_finish (c_u8 c) =? 0)); [apply wsuf_same; reflexivity|].
  destruct (top c =? ST_MEMBER_NAME); [exists 1%nat; destruct w; reflexivity|].
  destruct ((top c =? ST_OBJECT) || (top c =? ST_ARRAY)); [exists 1%nat; destruct w; reflexivity|].
  destruct (top c =? ST_ROOT); [exists 1%nat; destruct w; reflexivity|]. apply wsuf_same; reflexivity.
Qed.
Lemma parse_string_suffix : forall w c, wsuf (parse_string c w) w.
Proof.
  induction w as [|b r IH]; intros c; [apply wsuf_same; reflexivity|].
  cbn -[Z.eqb is_ctl hexval is_high_surr utf8_of pair_cp tok1 tokn hexstep end_string set_sst set_cp set_cp2 skipn].
  repeat lazymatch goal with
  | |- wsuf (if ?x then _ else _) _ => destruct x
  | |- wsuf (match hexval b with _ => _ end) _ => destruct (hexval b)
  | |- wsuf (parse_string _ r) _ => apply wsuf_tl; apply IH
  | |- wsuf (err _ _ _) _ => apply wsuf_same; reflexivity
  | |- wsuf (ret _ r) _ => exists 1%nat; reflexivity
  | |- wsuf (end_string _ _) _ => apply end_string_suffix
  end.
Qed.
Lemma parse_number_suffix : forall w c, wsuf (parse_number c w) w.
Proof.
  induction w as [|b r IH]; intros c; [apply wsuf_nil; reflexivity|].
  cbn -[Z.eqb is_nzdigit is_digit is_exp tok1 set_nst end_number skipn].
  repeat lazymatch goal with
  | |- wsuf (if ?x then _ else _) _ => destruct x
  | |- wsuf (parse_number _ r) _ => apply wsuf_tl; apply IH
  | |- wsuf (err _ _ _) _ => apply wsuf_same; reflexivity
  | |- wsuf (end_number _ _) _ => apply wsuf_same; apply end_number_w
  end.
Qed.
Lemma parse_lit_suffix : forall tail s c w, wsuf (parse_lit tail s c w) w.
Proof.
  intros tail s c w. unfold parse_lit.
  destruct (S (length tail) <=? length w)%nat.
  - destruct (forallb _ _); [exists (S (length tail)); reflexivity | apply wsuf_same; reflexivity].
  - exists 1%nat. destruct w; reflexivity.
Qed.
Lemma begin_container_w : forall a c w, q_w (begin_container a c w) = w.
Proof. intros a c w. unfold begin_container. destruct (1024 <? _); reflexivity. Qed.
Lemma end_container_w : forall a c w, q_w (end_container a c w) = w.
Proof.
  intros a c w. unfold end_container. destruct (c_level c <? 1); [reflexivity|].
  destruct (top c =? _); [reflexivity|]. destruct (top c =? _); reflexivity.
Qed.
Lemma begin_member_w : forall c w, q_w (begin_member c w) = w.
Proof. intros c w. unfold begin_member. destruct (top c =? _); [reflexivity|]. destruct (top c =? _); [reflexivity|]. destruct (top c =? _); reflexivity. Qed.
Lemma after_value_w : forall c w, q_w (after_value c w) = w.
Proof. intros c w. exact (proj1 (PMRF.after_value_shape c w)). Qed.
Lemma fcall_suffix : forall f c w, win_callee f = true -> f <> PMW.FParseSome -> f <> PMW.FCheckDone -> wsuf (fcall f c w) w.
Proof.
  intros f c w Hf H1 H2. destruct f; try discriminate Hf; cbn [fcall].
  - destruct (skip_space_suffix w c) as [u Hu]. exists u. unfold skip_space_r. cbn. exact Hu.
  - apply wsuf_same. apply begin_member_w.
  - apply wsuf_same. apply after_value_w.
  - apply wsuf_same. apply begin_container_w.
  - apply wsuf_same. apply begin_container_w.
  - apply wsuf_same. apply end_container_w.
  - apply wsuf_same. apply end_container_w.
  - apply parse_lit_suffix.
  - apply parse_lit_suffix.
  - apply parse_lit_suffix.
  - apply parse_string_suffix.
  - apply parse_number_suffix.
  - exfalso; exact (H1 eq_refl).
  - exfalso; exact (H2 eq_refl).
Qed.
(* [comment removed for export] *)
Lemma fcall_after : forall f c w, win_callee f = true -> f <> PMW.FParseSome -> f <> PMW.FCheckDone ->
  skipn (Z.to_nat (PMW.r_used (rstep f c w))) w = q_w (fcall f c w).
Proof.
  intros f c w Hf H1 H2. rewrite (rstep_fcall f c w Hf), r_of_used. destruct (fcall_suffix f c w Hf H1 H2) as [u Hu]. rewrite Hu, used_to_nat. apply skipn_used.
Qed.
Lemma fcall_used_range : forall f c w, win_callee f = true -> f <> PMW.FParseSome -> f <> PMW.FCheckDone ->
  0 <= PMW.r_used (rstep f c w) <= Z.of_nat (length w) /\ Z.of_nat (length (q_w (fcall f c w))) = Z.of_nat (length w) - PMW.r_used (rstep f c w).
Proof.
  intros f c w Hf H1 H2. rewrite (rstep_fcall f c w Hf), r_of_used. destruct (fcall_suffix f c w Hf H1 H2) as [u Hu]. rewrite Hu, length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctrl_but_tok (c1 c2 : ctrl) : Prop :=
  c_st c1 = c_st c2 /\ c_sst c1 = c_sst c2 /\ c_nst c1 = c_nst c2 /\ c_more c1 = c_more c2 /\ c_done c1 = c_done c2 /\ c_level c1 = c_level c2 /\
  c_stack c1 = c_stack c2 /\ c_cp c1 = c_cp c2 /\ c_cp2 c1 = c_cp2 c2.
Lemma but_tok_set_st : forall c1 c2 x, ctrl_but_tok c1 c2 -> ctrl_but_tok (set_st c1 x) (set_st c2 x).
Proof. intros c1 c2 x (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9). unfold ctrl_but_tok, set_st. cbn. repeat split; assumption. Qed.
Lemma but_tok_set_more : forall c1 c2 x, ctrl_but_tok c1 c2 -> ctrl_but_tok (set_more c1 x) (set_more c2 x).
Proof. intros c1 c2 x (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9). unfold ctrl_but_tok, set_more. cbn. repeat split; first [assumption | reflexivity]. Qed.
Lemma but_tok_of_text : forall c txt, ctrl_but_tok c (of_text c txt).
Proof. intros c txt. unfold ctrl_but_tok, of_text, set_tok. cbn. repeat split; reflexivity. Qed.
Lemma after_value_tok : forall c1 c2 w, ctrl_but_tok c1 c2 ->
  let q1 := after_value c1 w in let q2 := after_value c2 w in
  q_code q1 = q_code q2 /\ q_evs q1 = q_evs q2 /\ q_al q1 = q_al q2 /\ q_w q1 = q_w q2 /\ ctrl_but_tok (q_c q1) (q_c q2) /\
  (q_code q1 = 0 -> c_st (q_c q1) <> ST_STRING /\ c_st (q_c q1) <> ST_NUMBER /\ c_more (q_c q1) = c_more c1).
Proof.
  intros c1 c2 w H. pose proof H as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  assert (HT : top c2 = top c1) by (unfold top; rewrite E7; reflexivity).
  unfold after_value. rewrite HT.
  destruct ((top c1 =? ST_ARRAY) || (top c1 =? ST_OBJECT)).
  { cbn [q_code q_evs q_al q_w q_c ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply but_tok_set_st; exact H|]. intros _. rewrite PMRF.st_set_st, PMRF.more_set_st. split; [discriminate|]. split; [discriminate | reflexivity]. }
  destruct (top c1 =? ST_ROOT).
  { cbn [q_code q_evs q_al q_w q_c ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply but_tok_set_st; exact H|]. intros _. rewrite PMRF.st_set_st, PMRF.more_set_st. split; [discriminate|]. split; [discriminate | reflexivity]. }
  cbn [q_code q_evs q_al q_w q_c err]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply but_tok_set_more; exact H|]. intros X. exfalso. revert X. PMRF.ured. discriminate.
Qed.
Lemma end_number_text : forall c txt, c_dlen c = Z.of_nat (length txt) ->
  let q1 := end_number c [] in let q2 := end_number (of_text c txt) [] in
  q_code q1 = q_code q2 /\ q_evs q1 = q_evs q2 /\ q_al q1 = q_al q2 /\ q_w q1 = [] /\ q_w q2 = [] /\ ctrl_but_tok (q_c q1) (q_c q2) /\
  (q_code q1 = 0 -> c_st (q_c q1) <> ST_STRING /\ c_st (q_c q1) <> ST_NUMBER /\ c_more (q_c q1) = true).
Proof.
  intros c txt Hd.
  assert (HT : ctrl_but_tok (set_more c true) (set_more (of_text c txt) true)) by (apply but_tok_set_more; apply but_tok_of_text).
  destruct (after_value_tok _ _ [] HT) as (E1 & E2 & E3 & E4 & E5 & E6).
  assert (Hal : al_num (c_dlen c) = al_num (c_dlen (of_text c txt))) by (unfold of_text, set_tok; cbn; rewrite Hd; reflexivity).
  unfold end_number, PMR.bind. cbn [q_code q_c q_w q_evs q_al negb Z.eqb]. rewrite E1, E2, E3, Hal.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply after_value_w|]. split; [apply after_value_w|]. split; [exact E5|].
  intros H0. destruct (E6 ltac:(rewrite E1; exact H0)) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. rewrite X3. reflexivity.
Qed.
Lemma rm_match_but_tok : forall c1 c2 (M : mem) P ps, ctrl_but_tok c1 c2 -> ps_st ps <> ST_STRING -> ps_st ps <> ST_NUMBER -> rm_match c2 M P ps -> rm_match c1 M P ps.
Proof.
  intros c1 c2 M P ps H Hs Hn [(R1 & R2 & R3 & R4 & R5) _]. destruct H as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _).
  split; [split; [congruence|]; split; [congruence|]; split; [congruence|]; split; congruence|].
  split; intros X; exfalso; [exact (Hs X) | exact (Hn X)].
Qed.
Lemma stack_ok_but_tok : forall c1 c2, ctrl_but_tok c1 c2 -> PMRF.stack_ok c2 -> PMRF.stack_ok c1.
Proof. intros c1 c2 (_ & _ & _ & _ & _ & _ & E & _) H. exact (PMRF.stack_ok_iff c2 c1 E H). Qed.
(* [comment removed for export] *)
Lemma prologue_end_number : forall c, c_st c = ST_NUMBER -> In (c_nst c) [NS_ZERO; NS_INTEGER; NS_FRAC2; NS_EXP3] -> prologue c = end_number c [].
Proof.
  intros c Hs Hn. unfold prologue. rewrite Hs. change (ST_NUMBER =? ST_NUMBER) with true. cbv iota.
  destruct Hn as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
Qed.
Lemma parse_some_prologue : forall c, c_st c <> ST_ACCEPT -> c_more c = true -> parse_some c [] = prologue c.
Proof. intros c Ha Hm. unfold parse_some. destruct (Z.eqb_spec (c_st c) ST_ACCEPT); [contradiction|]. rewrite Hm. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dispatch_string : forall p b, dispatch ST_STRING p b = AParseString.  Proof. reflexivity. Qed.
Lemma dispatch_number : forall p b, dispatch ST_NUMBER p b = AParseNumber.  Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma begin_member_cases : forall c w, let q := begin_member c w in
  q_w q = w /\ q_evs q = [] /\ q_al q = 0 /\
  (q_code q = 0 -> c_more (q_c q) = c_more c /\ c_stack (q_c q) = c_stack c /\
                   (c_st (q_c q) = ST_EXPECT_MEMBER_NAME \/ c_st (q_c q) = ST_EXPECT_VALUE \/ q_c q = c)).
Proof.
  intros c w. unfold begin_member.
  destruct (top c =? ST_OBJECT).
  { cbn [q_w q_evs q_al q_code q_c ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros _. split; [reflexivity|]. split; [reflexivity|]. left; reflexivity. }
  destruct (top c =? ST_ARRAY).
  { cbn [q_w q_evs q_al q_code q_c ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros _. split; [reflexivity|]. split; [reflexivity|]. right; left; reflexivity. }
  destruct (top c =? ST_ROOT).
  { cbn [q_w q_evs q_al q_code q_c ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros _. split; [reflexivity|]. split; [reflexivity|]. right; right; reflexivity. }
  cbn [q_w q_evs q_al q_code q_c err]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros X. exfalso. revert X. PMRF.ured. discriminate.
Qed.
(* [comment removed for export] *)
Lemma comma_iter : forall c b r, let q := act_run AComma c b r in let q1 := begin_member c (b :: r) in
  q_code q = q_code q1 /\ q_evs q = [] /\ q_al q = 0 /\ (q_code q = 0 -> q_c q = q_c q1 /\ q_w q = r).
Proof.
  intros c b r. rewrite iter_comma. destruct (begin_member_cases c (b :: r)) as (W1 & W2 & W3 & _).
  unfold PMR.bind. destruct (Z.eqb_spec (q_code (begin_member c (b :: r))) 0) as [E|E]; cbn [negb q_code q_c q_w q_evs q_al ret].
  - rewrite W2, W3. split; [rewrite E; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros _. split; reflexivity.
  - split; [reflexivity|]. split; [exact W2|]. split; [exact W3|]. intros X; exfalso; exact (E X).
Qed.
Lemma string_entry_fields : forall key c,
  c_st (string_entry key c) = ST_STRING /\ c_sst (string_entry key c) = SS_TEXT /\ c_nst (string_entry key c) = c_nst c /\
  c_more (string_entry key c) = c_more c /\ c_done (string_entry key c) = c_done c /\ c_level (string_entry key c) = c_level c /\
  c_stack (string_entry key c) = (if key then c_stack c ++ [ST_MEMBER_NAME] else c_stack c) /\ c_dlen (string_entry key c) = 0 /\ c_u8 (string_entry key c) = u8_init.
Proof. intros key c. destruct key, c; cbn; repeat split; reflexivity. Qed.
Lemma number_entry_fields : forall c b,
  c_st (number_entry c b) = ST_NUMBER /\ c_nst (number_entry c b) = nst_of_byte b /\
  c_more (number_entry c b) = c_more c /\ c_done (number_entry c b) = c_done c /\ c_level (number_entry c b) = c_level c /\
  c_stack (number_entry c b) = c_stack c /\ c_dlen (number_entry c b) = 1.
Proof. intros c b. destruct c; cbn; repeat split; reflexivity. Qed.
End PMRF2.
