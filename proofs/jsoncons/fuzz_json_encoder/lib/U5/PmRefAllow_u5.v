(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Wf_nat Wellfounded.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMRA.
Import PML PMR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Dst (c : ctrl) : Z :=
  if c_st c =? ST_NUMBER then 28 + c_dlen c else if c_st c =? ST_STRING then 6 * c_dlen c else 0.
Definition D (c : ctrl) : Z := if c_more c then Dst c else 0.
Definition nots (s : Z) : Prop := s <> ST_STRING /\ s <> ST_NUMBER.
Definition SI (c : ctrl) : Prop := 0 <= c_dlen c /\ Forall nots (c_stack c).
(* [comment removed for export] *)
Definition aok (c : ctrl) (w : list Z) (q : res) : Prop :=
  q_al q + D (q_c q) <= 32 * (Z.of_nat (length w) - Z.of_nat (length (q_w q))) + D c /\ SI (q_c q).

Lemma Dst_nonneg : forall c, 0 <= c_dlen c -> 0 <= Dst c.
Proof. intros c H. unfold Dst. destruct (c_st c =? ST_NUMBER); [lia|]. destruct (c_st c =? ST_STRING); lia. Qed.
Lemma D_nonneg : forall c, SI c -> 0 <= D c.
Proof. intros c [H _]. unfold D. destruct (c_more c); [apply Dst_nonneg; exact H | lia]. Qed.
Lemma D_more : forall c, c_more c = true -> D c = Dst c.
Proof. intros c H. unfold D. rewrite H. reflexivity. Qed.
Lemma Dst_plain : forall c, nots (c_st c) -> Dst c = 0.
Proof. intros c [H1 H2]. unfold Dst. destruct (Z.eqb_spec (c_st c) ST_NUMBER); [contradiction|]. destruct (Z.eqb_spec (c_st c) ST_STRING); [contradiction | reflexivity]. Qed.
Lemma D_plain : forall c, nots (c_st c) -> D c = 0.
Proof. intros c H. unfold D. rewrite (Dst_plain c H). destruct (c_more c); reflexivity. Qed.
Lemma D_string : forall c, c_more c = true -> c_st c = ST_STRING -> D c = 6 * c_dlen c.
Proof. intros c Hm Hs. unfold D, Dst. rewrite Hm, Hs. reflexivity. Qed.
Lemma D_number : forall c, c_more c = true -> c_st c = ST_NUMBER -> D c = 28 + c_dlen c.
Proof. intros c Hm Hs. unfold D, Dst. rewrite Hm, Hs. reflexivity. Qed.
Lemma D_le_Dst : forall c, 0 <= c_dlen c -> D c <= Dst c.
Proof. intros c H. unfold D. pose proof (Dst_nonneg c H). destruct (c_more c); lia. Qed.
(* [comment removed for export] *)
Lemma st_set_sst : forall c x, c_st (set_sst c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_sst : forall c x, c_dlen (set_sst c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_sst : forall c x, c_more (set_sst c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_sst : forall c x, c_stack (set_sst c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_tok1 : forall c b, c_st (tok1 c b) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_tok1 : forall c b, c_dlen (tok1 c b) = c_dlen c + 1.  Proof. destruct c; reflexivity. Qed.
Lemma more_tok1 : forall c b, c_more (tok1 c b) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_tok1 : forall c b, c_stack (tok1 c b) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_tokn : forall c bs, c_st (tokn c bs) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_tokn : forall c bs, c_dlen (tokn c bs) = c_dlen c + Z.of_nat (length bs).  Proof. destruct c; reflexivity. Qed.
Lemma more_tokn : forall c bs, c_more (tokn c bs) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_tokn : forall c bs, c_stack (tokn c bs) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_set_cp : forall c x, c_st (set_cp c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_cp : forall c x, c_dlen (set_cp c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_cp : forall c x, c_more (set_cp c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_cp : forall c x, c_stack (set_cp c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_set_cp2 : forall c x, c_st (set_cp2 c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_cp2 : forall c x, c_dlen (set_cp2 c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_cp2 : forall c x, c_more (set_cp2 c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_cp2 : forall c x, c_stack (set_cp2 c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_hexstep : forall c s v, c_st (hexstep c s v) = c_st c.  Proof. intros c s v. unfold hexstep. destruct s; destruct c; reflexivity. Qed.
Lemma dlen_hexstep : forall c s v, c_dlen (hexstep c s v) = c_dlen c.  Proof. intros c s v. unfold hexstep. destruct s; destruct c; reflexivity. Qed.
Lemma more_hexstep : forall c s v, c_more (hexstep c s v) = c_more c.  Proof. intros c s v. unfold hexstep. destruct s; destruct c; reflexivity. Qed.
Lemma stack_hexstep : forall c s v, c_stack (hexstep c s v) = c_stack c.  Proof. intros c s v. unfold hexstep. destruct s; destruct c; reflexivity. Qed.
Lemma more_set_st : forall c x, c_more (set_st c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_st : forall c x, c_dlen (set_st c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma st_set_more : forall c x, c_st (set_more c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_more : forall c x, c_dlen (set_more c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_more : forall c x, c_stack (set_more c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_more : forall c x, c_more (set_more c x) = x.  Proof. destruct c; reflexivity. Qed.
Lemma st_pop : forall c, c_st (pop c) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_pop : forall c, c_dlen (pop c) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_pop : forall c, c_more (pop c) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_pop : forall c, c_stack (pop c) = removelast (c_stack c).  Proof. destruct c; reflexivity. Qed.
Lemma st_push : forall c s, c_st (push c s) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_push : forall c s, c_dlen (push c s) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_push : forall c s, c_more (push c s) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_push : forall c s, c_stack (push c s) = c_stack c ++ [s].  Proof. destruct c; reflexivity. Qed.
Lemma st_set_level : forall c x, c_st (set_level c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_level : forall c x, c_dlen (set_level c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_level : forall c x, c_more (set_level c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_level : forall c x, c_stack (set_level c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_done : forall c x, c_more (set_done c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma st_set_done : forall c x, c_st (set_done c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_done : forall c x, c_dlen (set_done c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_done : forall c x, c_stack (set_done c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma st_set_nst : forall c x, c_st (set_nst c x) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_set_nst : forall c x, c_dlen (set_nst c x) = c_dlen c.  Proof. destruct c; reflexivity. Qed.
Lemma more_set_nst : forall c x, c_more (set_nst c x) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_set_nst : forall c x, c_stack (set_nst c x) = c_stack c.  Proof. destruct c; reflexivity. Qed.
Lemma dlen_tok_clear : forall c, c_dlen (tok_clear c) = 0.  Proof. destruct c; reflexivity. Qed.
Lemma st_tok_clear : forall c, c_st (tok_clear c) = c_st c.  Proof. destruct c; reflexivity. Qed.
Lemma more_tok_clear : forall c, c_more (tok_clear c) = c_more c.  Proof. destruct c; reflexivity. Qed.
Lemma stack_tok_clear : forall c, c_stack (tok_clear c) = c_stack c.  Proof. destruct c; reflexivity. Qed.

#[export] Hint Rewrite st_set_sst dlen_set_sst more_set_sst stack_set_sst st_tok1 dlen_tok1 more_tok1 stack_tok1 st_tokn dlen_tokn more_tokn stack_tokn
  st_set_cp dlen_set_cp more_set_cp stack_set_cp st_set_cp2 dlen_set_cp2 more_set_cp2 stack_set_cp2 st_hexstep dlen_hexstep more_hexstep stack_hexstep
  PMRF.st_set_st PMRF.stack_set_st more_set_st dlen_set_st st_set_more dlen_set_more stack_set_more more_set_more st_pop dlen_pop more_pop stack_pop
  st_push dlen_push more_push stack_push st_set_level dlen_set_level more_set_level stack_set_level st_set_nst dlen_set_nst more_set_nst stack_set_nst
  dlen_tok_clear st_tok_clear more_tok_clear stack_tok_clear more_set_done st_set_done dlen_set_done stack_set_done : fld.

Lemma utf8_len : forall cp, (length (utf8_of cp) <= 4)%nat.
Proof.
  intros cp. unfold utf8_of. destruct (is_surr cp); [cbn; lia|]. destruct (cp <? 128); [cbn; lia|]. destruct (cp <? 2048); [cbn; lia|].
  destruct (cp <? 65536); [cbn; lia|]. destruct (cp <=? 1114111); cbn; lia.
Qed.
Lemma nots_removelast : forall l, Forall nots l -> Forall nots (removelast l).
Proof.
  intros l H. induction l as [|x l IH]; [constructor|]. inversion H; subst. cbn. destruct l as [|y l']; [constructor|]. constructor; [assumption | apply IH; assumption].
Qed.
Lemma nots_last : forall l d, Forall nots l -> nots d -> nots (last l d).
Proof. intros l d H Hd. induction l as [|x l IH]; [exact Hd|]. inversion H; subst. cbn. destruct l; [assumption | apply IH; assumption]. Qed.
Lemma top_nots : forall c, SI c -> nots (top c).
Proof. intros c [_ H]. unfold top. apply nots_last; [exact H|]. unfold nots, ST_STRING, ST_NUMBER. lia. Qed.

(* [comment removed for export] *)
Lemma aok_err : forall c w k, SI c -> aok c w (err c w k).
Proof.
  intros c w k HS. unfold aok, err. cbn [q_al q_c q_w]. split; [|destruct HS as [H1 H2]; split; [rewrite dlen_set_more; exact H1 | rewrite stack_set_more; exact H2]].
  unfold D at 1. rewrite more_set_more. pose proof (D_nonneg c HS). lia.
Qed.
Lemma aok_err' : forall c c' w w' k, SI c -> SI c' -> (length w' <= length w)%nat -> aok c w (err c' w' k).
Proof.
  intros c c' w w' k HS HS' HL. unfold aok, err. cbn [q_al q_c q_w]. split; [|destruct HS' as [H1 H2]; split; [rewrite dlen_set_more; exact H1 | rewrite stack_set_more; exact H2]].
  unfold D at 1. rewrite more_set_more. pose proof (D_nonneg c HS). lia.
Qed.
Lemma aok_ret_plain : forall c c' w w', SI c -> SI c' -> nots (c_st c') -> (length w' <= length w)%nat -> aok c w (ret c' w').
Proof.
  intros c c' w w' HS HS' Hn HL. unfold aok, ret. cbn [q_al q_c q_w]. split; [|exact HS']. rewrite (D_plain c' Hn). pose proof (D_nonneg c HS). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_value_aok : forall c w, SI c -> nots (c_st c) \/ D c = 0 -> aok c w (after_value c w) /\ q_w (after_value c w) = w.
Proof.
  intros c w HS HD. unfold after_value.
  destruct ((top c =? ST_ARRAY) || (top c =? ST_OBJECT)).
  { split; [|reflexivity]. unfold aok, ret. cbn [q_al q_c q_w]. split; [|destruct HS as [H1 H2]; split; [rewrite dlen_set_st; exact H1 | rewrite PMRF.stack_set_st; exact H2]].
    rewrite (D_plain (set_st c ST_EXPECT_COMMA_OR_END)) by (rewrite PMRF.st_set_st; unfold nots, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia). pose proof (D_nonneg c HS). lia. }
  destruct (top c =? ST_ROOT).
  { split; [|reflexivity]. unfold aok, ret. cbn [q_al q_c q_w]. split; [|destruct HS as [H1 H2]; split; [rewrite dlen_set_st; exact H1 | rewrite PMRF.stack_set_st; exact H2]].
    rewrite (D_plain (set_st c ST_ACCEPT)) by (rewrite PMRF.st_set_st; unfold nots, ST_ACCEPT, ST_STRING, ST_NUMBER; lia). pose proof (D_nonneg c HS). lia. }
  split; [apply aok_err; exact HS | reflexivity].
Qed.
Lemma end_number_aok : forall c w, SI c -> c_st c = ST_NUMBER -> c_more c = true -> aok c w (end_number c w).
Proof.
  intros c w HS Hs Hm. unfold end_number, bind. cbn [q_code q_c q_w q_evs q_al negb Z.eqb].
  assert (HS1 : SI (set_more c true)) by (destruct HS as [H1 H2]; split; [rewrite dlen_set_more; exact H1 | rewrite stack_set_more; exact H2]).
  assert (HD : D c = 28 + c_dlen c) by (unfold D, Dst; rewrite Hm, Hs; reflexivity).
  assert (HD1 : D (set_more c true) = 28 + c_dlen c) by (unfold D, Dst; rewrite more_set_more, st_set_more, dlen_set_more, Hs; reflexivity).
  unfold after_value. cbv zeta.
  assert (HT : top (set_more c true) = top c) by (unfold top; rewrite stack_set_more; reflexivity). rewrite !HT.
  destruct ((top c =? ST_ARRAY) || (top c =? ST_OBJECT)).
  { unfold aok. cbn [q_code q_c q_w q_evs q_al ret]. split; [|destruct HS1 as [H1 H2]; split; [rewrite dlen_set_st; exact H1 | rewrite PMRF.stack_set_st; exact H2]].
    rewrite (D_plain (set_st _ ST_EXPECT_COMMA_OR_END)) by (rewrite PMRF.st_set_st; unfold nots, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia). unfold al_num. lia. }
  destruct (top c =? ST_ROOT).
  { unfold aok. cbn [q_code q_c q_w q_evs q_al ret]. split; [|destruct HS1 as [H1 H2]; split; [rewrite dlen_set_st; exact H1 | rewrite PMRF.stack_set_st; exact H2]].
    rewrite (D_plain (set_st _ ST_ACCEPT)) by (rewrite PMRF.st_set_st; unfold nots, ST_ACCEPT, ST_STRING, ST_NUMBER; lia). unfold al_num. lia. }
  unfold aok, err. cbn [q_code q_c q_w q_evs q_al]. split; [|destruct HS1 as [H1 H2]; split; [rewrite !dlen_set_more; exact H1 | rewrite !stack_set_more; exact H2]].
  unfold D at 1. rewrite more_set_more. unfold al_num. lia.
Qed.
Lemma end_string_aok : forall c w, SI c -> c_st c = ST_STRING -> c_more c = true -> aok c w (end_string c w).
Proof.
  intros c w HS Hs Hm. pose proof HS as [H1 H2]. unfold end_string.
  assert (HD : D c = 6 * c_dlen c) by (unfold D, Dst; rewrite Hm, Hs; reflexivity).
  destruct (negb (u8_finish (c_u8 c) =? 0)); [apply aok_err; exact HS|].
  assert (Htl : (length (tl w) <= length w)%nat) by (destruct w; cbn; lia).
  destruct (top c =? ST_MEMBER_NAME).
  { unfold aok. cbn [q_al q_c q_w]. split.
    - rewrite (D_plain (set_st _ ST_EXPECT_COLON)) by (rewrite PMRF.st_set_st; unfold nots, ST_EXPECT_COLON, ST_STRING, ST_NUMBER; lia). unfold al_str. lia.
    - split; [rewrite dlen_set_st, dlen_pop, dlen_set_more; exact H1 | rewrite PMRF.stack_set_st, stack_pop, stack_set_more; apply nots_removelast; exact H2]. }
  destruct ((top c =? ST_OBJECT) || (top c =? ST_ARRAY)).
  { unfold aok. cbn [q_al q_c q_w]. split.
    - rewrite (D_plain (set_st _ ST_EXPECT_COMMA_OR_END)) by (rewrite PMRF.st_set_st; unfold nots, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia). unfold al_str. lia.
    - split; [rewrite dlen_set_st, dlen_set_more; exact H1 | rewrite PMRF.stack_set_st, stack_set_more; exact H2]. }
  destruct (top c =? ST_ROOT).
  { unfold aok. cbn [q_al q_c q_w]. split.
    - rewrite (D_plain (set_st _ ST_ACCEPT)) by (rewrite PMRF.st_set_st; unfold nots, ST_ACCEPT, ST_STRING, ST_NUMBER; lia). unfold al_str. lia.
    - split; [rewrite dlen_set_st, dlen_set_more; exact H1 | rewrite PMRF.stack_set_st, stack_set_more; exact H2]. }
  apply aok_err; exact HS.
Qed.

(* [comment removed for export] *)
Lemma aok_step : forall c c' b r q, aok c' r q -> D c' <= D c + 32 -> aok c (b :: r) q.
Proof. intros c c' b r q [A S] HD. unfold aok. cbn [length]. split; [|exact S]. lia. Qed.

Lemma SI_string_variant : forall c, SI c ->
  SI (set_sst c SS_TEXT) /\ (forall x, SI (set_sst c x)) /\ (forall b, SI (tok1 c b)) /\ (forall x, SI (set_cp c x)) /\ (forall x, SI (set_cp2 c x)) /\
  (forall s v, SI (hexstep c s v)) /\ (forall bs, SI (tokn c bs)).
Proof.
  intros c [H1 H2]. unfold SI.
  split; [autorewrite with fld; split; [exact H1 | exact H2]|].
  split; [intros x; autorewrite with fld; split; [exact H1 | exact H2]|].
  split; [intros b; autorewrite with fld; split; [lia | exact H2]|].
  split; [intros x; autorewrite with fld; split; [exact H1 | exact H2]|].
  split; [intros x; autorewrite with fld; split; [exact H1 | exact H2]|].
  split; [intros s v; autorewrite with fld; split; [exact H1 | exact H2]|].
  intros bs; autorewrite with fld; split; [lia | exact H2].
Qed.

Lemma parse_string_aok : forall w c, SI c -> c_st c = ST_STRING -> c_more c = true -> aok c w (parse_string c w).
Proof.
  induction w as [|b r IH]; intros c HS Hs Hm.
  - cbn. unfold aok, ret. cbn [q_al q_c q_w length]. split; [lia | exact HS].
  - pose proof HS as [H1 H2].
    assert (HD : D c = 6 * c_dlen c) by (unfold D, Dst; rewrite Hm, Hs; reflexivity).
    assert (REC : forall c', SI c' -> c_st c' = ST_STRING -> c_more c' = true -> c_dlen c' <= c_dlen c + 4 -> aok c (b :: r) (parse_string c' r)).
    { intros c' HS' Hs' Hm' Hd'. apply (aok_step c c' b r _ (IH c' HS' Hs' Hm')). unfold D, Dst. rewrite Hm, Hs, Hm', Hs'. change (ST_STRING =? ST_NUMBER) with false. cbn. lia. }
    assert (ERR : forall c' k, SI c' -> aok c (b :: r) (err c' (b :: r) k)) by (intros c' k HS'; apply (aok_err' c c' _ _ k HS HS'); lia).
    cbn -[Z.eqb is_ctl hexval is_high_surr utf8_of pair_cp tok1 tokn hexstep end_string set_sst set_cp set_cp2 skipn Z.mul Z.add Z.of_nat length err ret].
    repeat lazymatch goal with
    | |- aok _ _ (if ?x then _ else _) => destruct x
    | |- aok _ _ (match hexval b with _ => _ end) => destruct (hexval b)
    | |- aok _ _ (parse_string ?c' r) => apply (REC c'); [unfold SI; autorewrite with fld; split; [lia | exact H2] | autorewrite with fld; exact Hs | autorewrite with fld; exact Hm | autorewrite with fld; try lia]
    | |- aok _ _ (err ?c' _ _) => apply (ERR c'); unfold SI; autorewrite with fld; split; [lia | exact H2]
    | |- aok _ _ (end_string _ _) => apply end_string_aok; [exact HS | exact Hs | exact Hm]
    end.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- aok _ (_ :: ?rr) (ret (set_sst (tokn ?c1 (utf8_of ?cp)) ?x) ?rr) =>
             unfold aok, ret; cbn [q_al q_c q_w]; split;
             [ rewrite (D_string (set_sst (tokn c1 (utf8_of cp)) x)) by (autorewrite with fld; assumption); autorewrite with fld; rewrite HD; cbn [length];
               pose proof (utf8_len cp); lia
             | unfold SI; autorewrite with fld; split; [lia | exact H2] ]
         | |- context [utf8_of ?cp] => pose proof (utf8_len cp); lia
         | _ => idtac
         end.
    all: try lia.
Qed.

Lemma parse_number_aok : forall w c, SI c -> c_st c = ST_NUMBER -> c_more c = true -> aok c w (parse_number c w).
Proof.
  induction w as [|b r IH]; intros c HS Hs Hm.
  - cbn -[Z.eqb set_nst]. pose proof HS as [H1 H2]. destruct (c_nst c =? NS_ZERO); unfold aok, ret; cbn [q_al q_c q_w length].
    + split; [|unfold SI; autorewrite with fld; exact HS]. rewrite (D_number (set_nst c NS_INTEGER)) by (autorewrite with fld; assumption). autorewrite with fld. rewrite (D_number c Hm Hs). lia.
    + split; [lia | exact HS].
  - pose proof HS as [H1 H2]. pose proof (D_number c Hm Hs) as HD.
    assert (GO : forall k, aok c (b :: r) (parse_number (set_nst (tok1 c b) k) r)).
    { intros k. apply (aok_step c (set_nst (tok1 c b) k) b r _ (IH (set_nst (tok1 c b) k) ltac:(unfold SI; autorewrite with fld; split; [lia | exact H2]) ltac:(autorewrite with fld; exact Hs) ltac:(autorewrite with fld; exact Hm))).
      rewrite (D_number (set_nst (tok1 c b) k)) by (autorewrite with fld; assumption). autorewrite with fld. rewrite HD. lia. }
    assert (ERR : forall k, aok c (b :: r) (err c (b :: r) k)) by (intros k; apply aok_err; exact HS).
    assert (EN : aok c (b :: r) (end_number c (b :: r))) by (apply end_number_aok; assumption).
    cbn -[Z.eqb is_nzdigit is_digit is_exp tok1 set_nst end_number err].
    repeat lazymatch goal with
    | |- aok _ _ (if ?x then _ else _) => destruct x
    | |- aok _ _ (parse_number _ r) => apply GO
    | |- aok _ _ (err _ _ _) => apply ERR
    | |- aok _ _ (end_number _ _) => exact EN
    end.
Qed.

Lemma skip_space_cons : forall c b r, skip_space c (b :: r) =
  if (b =? 32) || (b =? 9) || (b =? 10) then skip_space c r
  else if b =? 13 then match r with [] => (set_st (push c (c_st c)) ST_CR, []) | b2 :: r2 => if b2 =? 10 then skip_space c r2 else skip_space c r end
  else (c, b :: r).
Proof. reflexivity. Qed.
Lemma skip_space_aok : forall w c, SI c -> nots (c_st c) -> aok c w (skip_space_r c w) /\ c_more (q_c (skip_space_r c w)) = c_more c.
Proof.
  intros w. induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length Z))). intros c HS Hn. unfold Wf_nat.ltof in IH.
  unfold skip_space_r. destruct w as [|b r]; [cbn; split; [apply aok_ret_plain; auto | reflexivity]|].
  rewrite skip_space_cons.
  assert (SUB : forall r', (length r' < length (b :: r))%nat -> aok c (b :: r) (ret (fst (skip_space c r')) (snd (skip_space c r'))) /\ c_more (fst (skip_space c r')) = c_more c).
  { intros r' Hl. destruct (IH r' Hl c HS Hn) as [[A S] M]. unfold skip_space_r in A, S, M. cbn [q_al q_c q_w ret] in A, S, M.
    split; [|exact M]. unfold aok, ret. cbn [q_al q_c q_w]. split; [|exact S]. cbn [length] in Hl |- *. lia. }
  destruct ((b =? 32) || (b =? 9) || (b =? 10)); [apply SUB; cbn; lia|].
  destruct (b =? 13).
  - destruct r as [|b2 r2].
    + cbn [skip_space fst snd q_c ret]. split; [|autorewrite with fld; reflexivity].
      unfold aok, ret. cbn [q_al q_c q_w length]. split.
      * rewrite (D_plain (set_st (push c (c_st c)) ST_CR)) by (autorewrite with fld; unfold nots, ST_CR, ST_STRING, ST_NUMBER; lia). pose proof (D_nonneg c HS). lia.
      * unfold SI. autorewrite with fld. destruct HS as [H1 H2]. split; [exact H1|]. apply Forall_app. split; [exact H2 | constructor; [exact Hn | constructor]].
    + destruct (b2 =? 10); apply SUB; cbn; lia.
  - cbn [fst snd q_c ret]. split; [apply aok_ret_plain; auto | reflexivity].
Qed.

Lemma lit_done_aok : forall c b r, SI c -> nots (c_st c) -> aok c (b :: r) (lit_done c r).
Proof.
  intros c b r HS Hn. unfold lit_done, aok. cbn [q_al q_c q_w length]. split.
  - rewrite (D_plain c Hn). rewrite D_plain; [unfold AL_LIT; lia|]. autorewrite with fld. unfold st_after, nots, ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER. destruct (_ =? 0); lia.
  - unfold SI. autorewrite with fld. exact HS.
Qed.
Lemma parse_lit_aok : forall tail s c b r, SI c -> nots (c_st c) -> nots s -> aok c (b :: r) (parse_lit tail s c (b :: r)).
Proof.
  intros tail s c b r HS Hn Hs. unfold parse_lit.
  destruct (S (length tail) <=? length (b :: r))%nat eqn:HL.
  - destruct (forallb _ _).
    + unfold lit_done, aok. cbn [q_al q_c q_w]. rewrite length_skipn. apply Nat.leb_le in HL. split.
      * rewrite (D_plain c Hn). rewrite D_plain; [unfold AL_LIT; cbn [length] in HL |- *; lia|]. autorewrite with fld. unfold st_after, nots, ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER. destruct (_ =? 0); lia.
      * unfold SI. autorewrite with fld. exact HS.
    + apply aok_err. exact HS.
  - cbn [tl]. apply aok_ret_plain; [exact HS | unfold SI; autorewrite with fld; exact HS | autorewrite with fld; exact Hs | cbn; lia].
Qed.
Lemma begin_container_aok : forall a c w, SI c -> nots (c_st c) -> aok c w (begin_container a c w).
Proof.
  intros a c w HS Hn. unfold begin_container.
  assert (HS1 : SI (set_level c (c_level c + 1))) by (unfold SI; autorewrite with fld; exact HS).
  destruct (1024 <? _); [apply (aok_err' c _ w w _ HS HS1); lia|].
  unfold aok. cbn [q_al q_c q_w]. split.
  - rewrite (D_plain c Hn). rewrite D_plain; [lia|]. autorewrite with fld. destruct a; unfold nots, ST_EXPECT_VALUE_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_STRING, ST_NUMBER; lia.
  - unfold SI. autorewrite with fld. destruct HS as [H1 H2]. split; [exact H1|]. apply Forall_app. split; [exact H2 | constructor; [destruct a; unfold nots, ST_ARRAY, ST_OBJECT, ST_STRING, ST_NUMBER; lia | constructor]].
Qed.
Lemma end_container_aok : forall a c w, SI c -> nots (c_st c) -> aok c w (end_container a c w).
Proof.
  intros a c w HS Hn. unfold end_container. destruct (c_level c <? 1); [apply aok_err; exact HS|].
  assert (HS1 : SI (set_st (pop c) (top c))) by (unfold SI; autorewrite with fld; destruct HS as [H1 H2]; split; [exact H1 | apply nots_removelast; exact H2]).
  pose proof (top_nots c HS) as HT.
  destruct (top c =? _).
  - unfold aok. cbn [q_al q_c q_w]. split; [|unfold SI; autorewrite with fld; destruct HS as [H1 H2]; split; [exact H1 | apply nots_removelast; exact H2]].
    rewrite (D_plain c Hn). rewrite D_plain; [lia|]. autorewrite with fld. unfold st_after. autorewrite with fld. unfold nots, ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER. destruct (_ =? 0); lia.
  - destruct (top c =? _); apply (aok_err' c _ w w _ HS HS1); lia.
Qed.
Lemma begin_member_aok : forall c w, SI c -> nots (c_st c) -> aok c w (begin_member c w) /\ q_w (begin_member c w) = w /\ q_evs (begin_member c w) = [] /\
  (q_code (begin_member c w) = 0 -> nots (c_st (q_c (begin_member c w))) /\ SI (q_c (begin_member c w))).
Proof.
  intros c w HS Hn. unfold begin_member.
  destruct (top c =? ST_OBJECT).
  { cbn [q_w q_evs q_code q_c ret]. split; [apply aok_ret_plain; [exact HS | unfold SI; autorewrite with fld; exact HS | autorewrite with fld; unfold nots, ST_EXPECT_MEMBER_NAME, ST_STRING, ST_NUMBER; lia | lia]|].
    split; [reflexivity|]. split; [reflexivity|]. intros _. autorewrite with fld. split; [unfold nots, ST_EXPECT_MEMBER_NAME, ST_STRING, ST_NUMBER; lia | unfold SI; autorewrite with fld; exact HS]. }
  destruct (top c =? ST_ARRAY).
  { cbn [q_w q_evs q_code q_c ret]. split; [apply aok_ret_plain; [exact HS | unfold SI; autorewrite with fld; exact HS | autorewrite with fld; unfold nots, ST_EXPECT_VALUE, ST_STRING, ST_NUMBER; lia | lia]|].
    split; [reflexivity|]. split; [reflexivity|]. intros _. autorewrite with fld. split; [unfold nots, ST_EXPECT_VALUE, ST_STRING, ST_NUMBER; lia | unfold SI; autorewrite with fld; exact HS]. }
  destruct (top c =? ST_ROOT).
  { cbn [q_w q_evs q_code q_c ret]. split; [apply aok_ret_plain; [exact HS | exact HS | exact Hn | lia]|]. split; [reflexivity|]. split; [reflexivity|]. intros _. exact (conj Hn HS). }
  cbn [q_w q_evs q_code q_c err]. split; [apply aok_err; exact HS|]. split; [reflexivity|]. split; [reflexivity|]. intros X. exfalso. revert X. PMRF.ured. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dispatch_string' : forall p b, dispatch ST_STRING p b = AParseString.  Proof. reflexivity. Qed.
Lemma dispatch_number' : forall p b, dispatch ST_NUMBER p b = AParseNumber.  Proof. reflexivity. Qed.
Theorem iter_aok : forall c b r, SI c -> c_more c = true -> aok c (b :: r) (iter c b r).
Proof.
  intros c b r HS Hm. pose proof HS as [H1 H2]. unfold iter.
  destruct (Z.eq_dec (c_st c) ST_STRING) as [Hs|Hs]; [rewrite Hs, dispatch_string'; cbn [act_run]; apply parse_string_aok; assumption|].
  destruct (Z.eq_dec (c_st c) ST_NUMBER) as [Hnm|Hnm]; [rewrite Hnm, dispatch_number'; cbn [act_run]; apply parse_number_aok; assumption|].
  assert (Hn : nots (c_st c)) by (split; assumption). pose proof (D_plain c Hn) as HD.
  pose proof (PMRF.dispatch_fact (c_st c) (top c) b) as DF. pose proof (PMRF.dispatch_push (c_st c) (top c) b) as DP. revert DF DP.
  destruct (dispatch (c_st c) (top c) b) as [code k| | | |arr|arr|key| |which| |s k|k| | | | |] eqn:Hdis; cbn [PMRF.act_fact PMRF.act_push_ok act_run]; intros DF DP.
  - (* [comment removed for export] *) destruct k; [apply (aok_err' c c _ _ _ HS HS); cbn; lia | apply aok_err; exact HS].
  - (* [comment removed for export] *) unfold aok, ret. cbn [q_al q_c q_w]. split; [|unfold SI; autorewrite with fld; exact HS].
    unfold D at 1. autorewrite with fld. rewrite HD. cbn [length]. lia.
  - (* [comment removed for export] *) exact (proj1 (skip_space_aok (b :: r) c HS Hn)).
  - (* [comment removed for export] *) apply aok_ret_plain; [exact HS | | autorewrite with fld; unfold nots, ST_SLASH, ST_STRING, ST_NUMBER; lia | cbn; lia].
    unfold SI. autorewrite with fld. split; [exact H1|]. apply Forall_app. split; [exact H2 | constructor; [exact Hn | constructor]].
  - (* [comment removed for export] *) apply (aok_step c c); [apply begin_container_aok; assumption | lia].
  - (* [comment removed for export] *) apply (aok_step c c); [apply end_container_aok; assumption | lia].
  - (* [comment removed for export] *) unfold start_string. apply (aok_step c (tok_clear (set_sst (set_st (if key then push c ST_MEMBER_NAME else c) ST_STRING) SS_TEXT))).
    + apply parse_string_aok; [| destruct key; autorewrite with fld; reflexivity | destruct key; autorewrite with fld; exact Hm].
      unfold SI. destruct key; autorewrite with fld; (split; [lia|]); [apply Forall_app; split; [exact H2 | constructor; [unfold nots, ST_MEMBER_NAME, ST_STRING, ST_NUMBER; lia | constructor]] | exact H2].
    + rewrite D_string; [| destruct key; autorewrite with fld; exact Hm | destruct key; autorewrite with fld; reflexivity]. destruct key; autorewrite with fld; rewrite HD; lia.
  - (* [comment removed for export] *) unfold start_number. eapply (aok_step c).
    + apply parse_number_aok; [unfold SI; autorewrite with fld; split; [lia | exact H2] | autorewrite with fld; reflexivity | autorewrite with fld; exact Hm].
    + rewrite D_number by (autorewrite with fld; first [exact Hm | reflexivity]). autorewrite with fld. rewrite HD. lia.
  - (* [comment removed for export] *) destruct (which =? 0); [|destruct (which =? 1)]; apply parse_lit_aok; try assumption; PMRF.ured; unfold nots, ST_STRING, ST_NUMBER; lia.
  - (* [comment removed for export] *) destruct (begin_member_aok c (b :: r) HS Hn) as ([A S] & W & _ & C). unfold bind.
    destruct (Z.eqb_spec (q_code (begin_member c (b :: r))) 0) as [Hc|Hc]; cbn [negb].
    + destruct (C Hc) as [Hn1 HS1]. unfold aok. cbn [q_al q_c q_w ret length]. rewrite W in A. cbn [length] in A. split; [|exact HS1]. rewrite Z.add_0_r. rewrite (D_plain _ Hn1) in A |- *. lia.
    + split; [|exact S]. rewrite W in A |- *. exact A.
  - (* [comment removed for export] *) destruct (PMRF.dispatch_goto (c_st c) (top c) b s k Hdis) as (_ & G1 & G2).
    destruct k; apply aok_ret_plain; try exact HS; try (unfold SI; autorewrite with fld; exact HS); try (autorewrite with fld; split; assumption); cbn; lia.
  - (* [comment removed for export] *) destruct k; (apply aok_ret_plain; [exact HS | unfold SI; autorewrite with fld; split; [exact H1 | apply nots_removelast; exact H2] | autorewrite with fld; exact (top_nots c HS) | cbn; lia]).
  - (* [comment removed for export] *) apply aok_ret_plain; [exact HS | | autorewrite with fld; unfold nots, ST_CR, ST_STRING, ST_NUMBER; lia | cbn; lia].
    unfold SI. autorewrite with fld. split; [exact H1|]. apply Forall_app. split; [exact H2 | constructor; [exact Hn | constructor]].
  - (* [comment removed for export] *) apply lit_done_aok; assumption.
  - (* [comment removed for export] *) exfalso. exact (Hs DF).
  - (* [comment removed for export] *) exfalso. exact (Hnm DF).
  - (* [comment removed for export] *) apply aok_err. exact HS.
Qed.

Lemma aok_bind : forall c w q1 k, aok c w q1 -> (q_code q1 = 0 -> aok (q_c q1) (q_w q1) (k (q_c q1) (q_w q1))) -> aok c w (bind q1 k).
Proof.
  intros c w q1 k [A1 S1] H2. unfold bind. destruct (Z.eqb_spec (q_code q1) 0) as [Hc|Hc]; cbn [negb]; [|split; [exact A1 | exact S1]].
  destruct (H2 Hc) as [A2 S2]. unfold aok. cbn [q_al q_c q_w]. split; [lia | exact S2].
Qed.
Theorem loop_aok : forall F c w, SI c -> aok c w (loop F c w).
Proof.
  induction F as [|F IH]; intros c w HS.
  - destruct w as [|b r]; cbn; [unfold aok; cbn; split; [lia | exact HS]|]. destruct (c_more c); cbn; [apply aok_err; exact HS | unfold aok; cbn; split; [lia | exact HS]].
  - destruct w as [|b r]; [rewrite PMRF.loop_nil; unfold aok; cbn; split; [lia | exact HS]|].
    destruct (c_more c) eqn:Hm; [|rewrite (PMRF.loop_stopped _ _ _ Hm); unfold aok; cbn; split; [lia | exact HS]].
    rewrite (PMRF.loop_step F c b r Hm). apply aok_bind; [exact (iter_aok c b r HS Hm)|]. intros _. apply IH. exact (proj2 (iter_aok c b r HS Hm)).
Qed.
Lemma prologue_aok : forall c, SI c -> c_more c = true -> aok c [] (prologue c).
Proof.
  intros c HS Hm. pose proof HS as [H1 H2]. unfold prologue.
  destruct (Z.eqb_spec (c_st c) ST_NUMBER) as [Hs|Hs].
  - destruct (_ || _); [apply end_number_aok; assumption | apply aok_err; exact HS].
  - destruct (c_st c =? ST_ACCEPT).
    { unfold aok, ret. cbn [q_al q_c q_w length]. split; [|unfold SI; autorewrite with fld; exact HS]. rewrite D_plain by (autorewrite with fld; unfold nots, ST_DONE, ST_STRING, ST_NUMBER; lia). pose proof (D_nonneg c HS). lia. }
    destruct (c_st c =? ST_START); [apply aok_err; exact HS|].
    destruct (c_st c =? ST_DONE).
    { unfold aok, ret. cbn [q_al q_c q_w length]. split; [|unfold SI; autorewrite with fld; exact HS]. unfold D at 1. autorewrite with fld. pose proof (D_nonneg c HS). lia. }
    destruct (c_st c =? ST_CR); [|apply aok_err; exact HS].
    unfold aok, ret. cbn [q_al q_c q_w length]. split.
    + rewrite D_plain by (autorewrite with fld; exact (top_nots c HS)). pose proof (D_nonneg c HS). lia.
    + unfold SI. autorewrite with fld. split; [exact H1 | apply nots_removelast; exact H2].
Qed.
Theorem parse_some_aok : forall c w, SI c -> aok c w (parse_some c w).
Proof.
  intros c w HS. unfold parse_some.
  destruct (c_st c =? ST_ACCEPT).
  { unfold aok, ret. cbn [q_al q_c q_w]. split; [|unfold SI; autorewrite with fld; exact HS]. rewrite D_plain by (autorewrite with fld; unfold nots, ST_DONE, ST_STRING, ST_NUMBER; lia). pose proof (D_nonneg c HS). lia. }
  destruct w as [|b r]; [|apply loop_aok; exact HS].
  destruct (c_more c) eqn:Hm; [apply prologue_aok; assumption | unfold aok, ret; cbn; split; [lia | exact HS]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T (rs : rstate) : Z := Z.of_nat (length (r_w rs)) + Z.of_nat (length (r_rest rs)).
Lemma refill_facts : forall rs, r_c (fst (refill rs)) = r_c rs /\ T (fst (refill rs)) <= T rs /\ 0 <= T (fst (refill rs)).
Proof.
  intros [c0 w0 rest0 bof0 eof0]. unfold refill, T. cbn [r_c r_w r_rest r_bof r_eof].
  pose proof (firstn_skipn (Z.to_nat CHUNK) rest0) as HL. apply (f_equal (@length Z)) in HL. rewrite length_app in HL.
  destruct w0 as [|b0 w0]; [|cbn; split; [reflexivity | lia]].
  destruct eof0; [cbn; split; [reflexivity | lia]|].
  destruct (firstn (Z.to_nat CHUNK) rest0) as [|b1 s1] eqn:Hs; [cbn [fst r_c r_w r_rest]; cbn [length] in HL |- *; split; [reflexivity | lia]|].
  destruct bof0; [|cbn [fst r_c r_w r_rest]; cbn [length] in HL |- *; split; [reflexivity | lia]].
  destruct (detect (b1 :: s1)) as [k|]; cbn [fst r_c r_w r_rest]; [rewrite length_skipn; cbn [length] in HL |- *; split; [reflexivity | lia] | cbn [length] in HL |- *; split; [reflexivity | lia]].
Qed.
Theorem rloop_aok : forall F rs, SI (r_c rs) ->
  let t := rloop F rs in snd (fst t) + D (r_c (fst (fst (fst t)))) <= 32 * (T rs - T (fst (fst (fst t)))) + D (r_c rs) /\ SI (r_c (fst (fst (fst t)))).
Proof.
  induction F as [|F IH]; intros rs HS; cbv zeta.
  - cbn. split; [lia | exact HS].
  - cbn [rloop]. destruct (c_more (r_c rs)) eqn:Hm; cbn [negb].
    2:{ cbn [fst snd]. split; [lia | exact HS]. }
    destruct (refill_facts rs) as (RC & RT & RT0). destruct (refill rs) as [rs1 e]. cbn [fst snd] in RC, RT, RT0. cbv zeta. cbn [fst snd].
    rewrite <- RC in HS |- *.
    destruct (Z.eqb_spec e 0) as [He|He]; cbn [negb].
    2:{ cbn [fst snd]. split; [lia | exact HS]. }
    pose proof (parse_some_aok (r_c rs1) (r_w rs1) HS) as [A S]. set (q := parse_some (r_c rs1) (r_w rs1)) in *.
    unfold T in RT, RT0 |- *.
    destruct (negb (q_code q =? 0)); [cbn [fst snd r_c r_w r_rest]; split; [lia | exact S]|].
    destruct (_ && (c_st (q_c q) =? ST_START)); [cbn [fst snd r_c r_w r_rest]; split; [lia | exact S]|].
    destruct (_ && negb _); [cbn [fst snd r_c r_w r_rest]; split; [lia | exact S]|].
    specialize (IH (RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1)) S). cbv zeta in IH. unfold T in IH. cbn [r_c r_w r_rest] in IH.
    destruct (rloop F _) as [[[rs3 evs3] al3] code3]. cbn [fst snd] in IH |- *. destruct IH as [IA IS]. split; [lia | exact IS].
Qed.
Lemma ALLOW_rloop : forall p, ALLOW p = snd (fst (rloop (rfuel p) (RS ctrl0 [] p true false))).
Proof.
  intros p. unfold ALLOW, READ. cbv zeta.
  destruct (rloop (rfuel p) (RS ctrl0 [] p true false)) as [[[rs evs] al] code]. cbn [fst snd].
  destruct (negb (code =? 0)); [reflexivity|]. destruct (rtail _ _) as [rs' u]. cbn [fst snd]. destruct (negb (u =? 0)); reflexivity.
Qed.
(* [comment removed for export] *)
Theorem ALLOW_bound : forall p, ALLOW p <= 32 * Z.of_nat (length p) + 32.
Proof.
  intros p. rewrite ALLOW_rloop.
  assert (HS0 : SI ctrl0) by (split; [cbn; lia | cbn; constructor; [unfold nots, ST_ROOT, ST_STRING, ST_NUMBER; lia | constructor]]).
  pose proof (rloop_aok (rfuel p) (RS ctrl0 [] p true false) HS0) as H. cbv zeta in H. destruct H as [A S].
  pose proof (D_nonneg _ S) as HD. unfold T in A. cbn [r_w r_rest r_c length Z.of_nat] in A. change (D ctrl0) with 0 in A.
  pose proof (Nat2Z.is_nonneg (length (r_w (fst (fst (fst (rloop (rfuel p) {| r_c := ctrl0; r_w := []; r_rest := p; r_bof := true; r_eof := false |}))))))).
  pose proof (Nat2Z.is_nonneg (length (r_rest (fst (fst (fst (rloop (rfuel p) {| r_c := ctrl0; r_w := []; r_rest := p; r_bof := true; r_eof := false |}))))))).
  lia.
Qed.
(* [comment removed for export] *)
Theorem ALLOW_bound0 : forall p, ALLOW p <= 32 * Z.of_nat (length p).
Proof.
  intros p. rewrite ALLOW_rloop.
  assert (HS0 : SI ctrl0) by (split; [cbn; lia | cbn; constructor; [unfold nots, ST_ROOT, ST_STRING, ST_NUMBER; lia | constructor]]).
  pose proof (rloop_aok (rfuel p) (RS ctrl0 [] p true false) HS0) as H. cbv zeta in H. destruct H as [A S].
  pose proof (D_nonneg _ S) as HD. unfold T in A. cbn [r_w r_rest r_c length Z.of_nat] in A. change (D ctrl0) with 0 in A.
  pose proof (Nat2Z.is_nonneg (length (r_w (fst (fst (fst (rloop (rfuel p) {| r_c := ctrl0; r_w := []; r_rest := p; r_bof := true; r_eof := false |}))))))).
  pose proof (Nat2Z.is_nonneg (length (r_rest (fst (fst (fst (rloop (rfuel p) {| r_c := ctrl0; r_w := []; r_rest := p; r_bof := true; r_eof := false |}))))))).
  lia.
Qed.
End PMRA.
