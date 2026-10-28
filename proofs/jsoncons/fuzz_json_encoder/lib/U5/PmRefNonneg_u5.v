(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Wf_nat Wellfounded.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefAllow_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMRN.
Import PML PMR. Import PMRA.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tok (c : ctrl) : Prop := c_st c = ST_STRING \/ c_st c = ST_NUMBER.
Definition SIq (c : ctrl) : Prop := (tok c -> 0 <= c_dlen c) /\ Forall PMRA.nots (c_stack c).
(* [comment removed for export] *)
Definition alnn (q : res) : Prop := 0 <= q_al q /\ SIq (q_c q).

Lemma SI_SIq : forall c, PMRA.SI c -> SIq c.
Proof. intros c [H1 H2]. split; [intros _; exact H1 | exact H2]. Qed.
Lemma SIq_plain : forall c, ~ tok c -> Forall PMRA.nots (c_stack c) -> SIq c.
Proof. intros c Hn Hs. split; [intros Ht; exfalso; exact (Hn Ht) | exact Hs]. Qed.
Lemma alnn_err : forall c w k, SIq c -> alnn (err c w k).
Proof. intros c w k [H1 H2]. unfold alnn, err. cbn [q_al q_c]. split; [lia|]. split; [intros Ht; apply H1; exact Ht | rewrite PMRA.stack_set_more; exact H2]. Qed.
Lemma alnn_ret : forall c w, SIq c -> alnn (ret c w).
Proof. intros c w HS. unfold alnn, ret. cbn [q_al q_c]. split; [lia | exact HS]. Qed.
Lemma alnn_bind : forall q k, alnn q -> (forall c w, SIq c -> q_code q = 0 -> c = q_c q -> alnn (k c w)) -> alnn (bind q k).
Proof.
  intros q k [A S] K. unfold bind. destruct (negb (q_code q =? 0)) eqn:E; [split; [exact A | exact S]|].
  apply negb_false_iff in E. apply Z.eqb_eq in E. destruct (K (q_c q) (q_w q) S E eq_refl) as [A2 S2]. unfold alnn. cbn [q_al q_c]. split; [lia | exact S2].
Qed.
(* [comment removed for export] *)
Lemma SIq_set_st_plain : forall c x, x <> ST_STRING -> x <> ST_NUMBER -> Forall PMRA.nots (c_stack c) -> SIq (set_st c x).
Proof. intros c x N1 N2 Hs. split; [intros [Ht|Ht]; rewrite PMRF.st_set_st in Ht; congruence | rewrite PMRF.stack_set_st; exact Hs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_value_alnn : forall c w, SIq c -> alnn (after_value c w).
Proof.
  intros c w HS. pose proof HS as [H1 H2]. unfold after_value.
  destruct ((top c =? ST_ARRAY) || (top c =? ST_OBJECT)); [apply alnn_ret; apply SIq_set_st_plain; [discriminate | discriminate | exact H2]|].
  destruct (top c =? ST_ROOT); [apply alnn_ret; apply SIq_set_st_plain; [discriminate | discriminate | exact H2] | apply alnn_err; exact HS].
Qed.
Lemma begin_member_alnn : forall c w, SIq c -> ~ tok c -> alnn (begin_member c w).
Proof.
  intros c w HS Hn. pose proof HS as [H1 H2]. unfold begin_member.
  destruct (top c =? ST_OBJECT); [apply alnn_ret; apply SIq_set_st_plain; [discriminate | discriminate | exact H2]|].
  destruct (top c =? ST_ARRAY); [apply alnn_ret; apply SIq_set_st_plain; [discriminate | discriminate | exact H2]|].
  destruct (top c =? ST_ROOT); [apply alnn_ret; exact HS | apply alnn_err; exact HS].
Qed.
Lemma end_number_alnn : forall c w, SIq c -> c_st c = ST_NUMBER -> alnn (end_number c w).
Proof.
  intros c w [H1 H2] Hs. unfold end_number. apply alnn_bind.
  - unfold alnn. cbn [q_al q_c]. split; [unfold al_num; pose proof (H1 (or_intror Hs)); lia|].
    split; [intros _; rewrite PMRA.dlen_set_more; exact (H1 (or_intror Hs)) | rewrite PMRA.stack_set_more; exact H2].
  - intros c1 w1 S1 _ _. apply after_value_alnn. exact S1.
Qed.
Lemma begin_container_alnn : forall a c w, SIq c -> alnn (begin_container a c w).
Proof.
  intros a c w [H1 H2]. unfold begin_container.
  destruct (1024 <? c_level (set_level c (c_level c + 1))).
  - apply alnn_err. split; [intros Ht; rewrite PMRA.dlen_set_level; apply H1; unfold tok in *; rewrite PMRA.st_set_level in Ht; exact Ht | rewrite PMRA.stack_set_level; exact H2].
  - unfold alnn. cbn [q_al q_c]. split; [lia|]. split.
    + intros [Ht|Ht]; rewrite PMRA.st_set_more, PMRF.st_set_st in Ht; destruct a; discriminate Ht.
    + rewrite PMRA.stack_set_more, PMRF.stack_set_st, PMRA.stack_push, PMRA.stack_set_level. apply Forall_app. split; [exact H2|].
      constructor; [|constructor]. unfold PMRA.nots. destruct a; unfold ST_ARRAY, ST_OBJECT, ST_STRING, ST_NUMBER; lia.
Qed.
Lemma end_container_alnn : forall a c w, SIq c -> alnn (end_container a c w).
Proof.
  intros a c w HS. pose proof HS as [H1 H2]. unfold end_container.
  destruct (c_level c <? 1); [apply alnn_err; exact HS|]. cbv zeta.
  assert (NT : PMRA.nots (top c)) by (unfold top; apply PMRA.nots_last; [exact H2 | unfold PMRA.nots, ST_STRING, ST_NUMBER; lia]).
  assert (S1 : forall x, SIq (set_st (pop c) x) -> True) by (intros; exact I).
  destruct (top c =? (if a then ST_ARRAY else ST_OBJECT)).
  - unfold alnn. cbn [q_al q_c]. split; [lia|]. split.
    + intros [Ht|Ht]; rewrite PMRF.st_set_st in Ht; unfold st_after in Ht; destruct (_ =? 0); discriminate Ht.
    + rewrite PMRF.stack_set_st, PMRA.stack_set_level, PMRA.stack_set_more, PMRF.stack_set_st, PMRA.stack_pop. apply PMRA.nots_removelast. exact H2.
  - destruct (top c =? (if a then ST_OBJECT else ST_ARRAY)); apply alnn_err; (split; [intros [Ht|Ht]; rewrite PMRF.st_set_st in Ht; destruct NT as [N1 N2]; congruence | rewrite PMRF.stack_set_st, PMRA.stack_pop; apply PMRA.nots_removelast; exact H2]).
Qed.
Lemma lit_done_alnn : forall c r, SIq c -> alnn (lit_done c r).
Proof.
  intros c r [H1 H2]. unfold lit_done, alnn. cbn [q_al q_c]. split; [unfold AL_LIT; lia|].
  apply SIq_set_st_plain; [unfold st_after; destruct (_ =? 0); discriminate | unfold st_after; destruct (_ =? 0); discriminate | rewrite PMRA.stack_set_more; exact H2].
Qed.

(* [comment removed for export] *)
Lemma end_string_alnn : forall c w, SIq c -> c_st c = ST_STRING -> alnn (end_string c w).
Proof.
  intros c w HS Hs. pose proof HS as [H1 H2]. pose proof (H1 (or_introl Hs)) as D0. unfold end_string.
  destruct (negb (u8_finish (c_u8 c) =? 0)); [apply alnn_err; exact HS|].
  destruct (top c =? ST_MEMBER_NAME).
  { unfold alnn. cbn [q_al q_c]. split; [unfold al_str; lia|]. apply SIq_set_st_plain; [discriminate | discriminate|]. rewrite PMRA.stack_pop, PMRA.stack_set_more. apply PMRA.nots_removelast. exact H2. }
  destruct ((top c =? ST_OBJECT) || (top c =? ST_ARRAY)).
  { unfold alnn. cbn [q_al q_c]. split; [unfold al_str; lia|]. apply SIq_set_st_plain; [discriminate | discriminate|]. rewrite PMRA.stack_set_more. exact H2. }
  destruct (top c =? ST_ROOT).
  { unfold alnn. cbn [q_al q_c]. split; [unfold al_str; lia|]. apply SIq_set_st_plain; [discriminate | discriminate|]. rewrite PMRA.stack_set_more. exact H2. }
  apply alnn_err; exact HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma parse_string_alnn : forall w c, SIq c -> c_st c = ST_STRING -> alnn (parse_string c w).
Proof.
  induction w as [|b r IH]; intros c HS Hs.
  - cbn. apply alnn_ret. exact HS.
  - pose proof HS as [H1 H2]. pose proof (H1 (or_introl Hs)) as D0.
    assert (REC : forall c', SIq c' -> c_st c' = ST_STRING -> alnn (parse_string c' r)) by (intros c' HS' Hs'; exact (IH c' HS' Hs')).
    assert (ERR : forall c' w' k, SIq c' -> alnn (err c' w' k)) by (intros c' w' k HS'; apply alnn_err; exact HS').
    cbn -[Z.eqb is_ctl hexval is_high_surr utf8_of pair_cp tok1 tokn hexstep end_string set_sst set_cp set_cp2 skipn Z.mul Z.add Z.of_nat length err ret alnn].
    repeat lazymatch goal with
    | |- alnn (if ?x then _ else _) => destruct x
    | |- alnn (match hexval b with _ => _ end) => destruct (hexval b)
    | |- alnn (parse_string ?c' r) => apply (REC c'); [unfold SIq, tok; autorewrite with fld; split; [intros _; lia | exact H2] | autorewrite with fld; exact Hs]
    | |- alnn (err ?c' _ _) => apply (ERR c'); unfold SIq, tok; autorewrite with fld; split; [intros _; lia | exact H2]
    | |- alnn (end_string ?c' _) => apply end_string_alnn; [unfold SIq, tok; autorewrite with fld; split; [intros _; lia | exact H2] | autorewrite with fld; exact Hs]
    | |- alnn (ret ?c' _) => apply alnn_ret; unfold SIq, tok; autorewrite with fld; split; [intros _; try (pose proof (PMRA.utf8_len 0)); lia | exact H2]
    end.
    all: lazymatch goal with
         | |- context [utf8_of ?cp] => pose proof (PMRA.utf8_len cp); lia
         | _ => idtac
         end.
    all: try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma parse_number_alnn : forall w c, SIq c -> c_st c = ST_NUMBER -> alnn (parse_number c w).
Proof.
  induction w as [|b r IH]; intros c HS Hs.
  - pose proof HS as [H1 H2]. pose proof (H1 (or_intror Hs)) as D0. cbn -[Z.eqb set_nst].
    destruct (c_nst c =? NS_ZERO); apply alnn_ret; [unfold SIq, tok; autorewrite with fld; split; [intros _; exact D0 | exact H2] | exact HS].
  - pose proof HS as [H1 H2]. pose proof (H1 (or_intror Hs)) as D0.
    assert (GO : forall k, alnn (parse_number (set_nst (tok1 c b) k) r)).
    { intros k. apply IH; [unfold SIq, tok; autorewrite with fld; split; [intros _; lia | exact H2] | autorewrite with fld; exact Hs]. }
    assert (ERR : forall k, alnn (err c (b :: r) k)) by (intros k; apply alnn_err; exact HS).
    assert (EN : alnn (end_number c (b :: r))) by (apply end_number_alnn; assumption).
    cbn -[Z.eqb is_nzdigit is_digit is_exp tok1 set_nst end_number err alnn].
    repeat lazymatch goal with
    | |- alnn (if ?x then _ else _) => destruct x
    | |- alnn (parse_number _ r) => apply GO
    | |- alnn (err _ _ _) => apply ERR
    | |- alnn (end_number _ _) => exact EN
    end.
Qed.

Lemma skip_space_alnn : forall w c, SIq c -> ~ tok c -> alnn (skip_space_r c w) /\ c_more (q_c (skip_space_r c w)) = c_more c.
Proof.
  intros w. induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length Z))). intros c HS Hn. unfold Wf_nat.ltof in IH.
  pose proof HS as [H1 H2].
  unfold skip_space_r. destruct w as [|b r]; [cbn; split; [apply alnn_ret; exact HS | reflexivity]|].
  rewrite PMRA.skip_space_cons.
  assert (SUB : forall r', (length r' < length (b :: r))%nat -> alnn (ret (fst (skip_space c r')) (snd (skip_space c r'))) /\ c_more (fst (skip_space c r')) = c_more c).
  { intros r' Hl. destruct (IH r' Hl c HS Hn) as [[A S] M]. unfold skip_space_r in A, S, M. cbn [q_al q_c q_w ret] in A, S, M.
    split; [|exact M]. unfold alnn, ret. cbn [q_al q_c q_w]. split; [lia | exact S]. }
  destruct ((b =? 32) || (b =? 9) || (b =? 10)); [apply SUB; cbn; lia|].
  destruct (b =? 13).
  - destruct r as [|b2 r2].
    + cbn [skip_space fst snd q_c ret]. split; [|autorewrite with fld; reflexivity].
      apply alnn_ret. apply SIq_set_st_plain; [discriminate | discriminate|]. autorewrite with fld. apply Forall_app. split; [exact H2 | constructor; [|constructor]].
      unfold nots, tok in *. split; intros X; apply Hn; [left | right]; exact X.
    + destruct (b2 =? 10); apply SUB; cbn; lia.
  - cbn [fst snd q_c ret]. split; [apply alnn_ret; exact HS | reflexivity].
Qed.

Lemma parse_lit_alnn : forall tail s c w, SIq c -> s <> ST_STRING -> s <> ST_NUMBER -> alnn (parse_lit tail s c w).
Proof.
  intros tail s c w HS N1 N2. pose proof HS as [H1 H2]. unfold parse_lit.
  destruct (S (length tail) <=? length w)%nat.
  - destruct (forallb _ _); [apply lit_done_alnn; exact HS | apply alnn_err; exact HS].
  - apply alnn_ret. apply SIq_set_st_plain; [exact N1 | exact N2 | autorewrite with fld; exact H2].
Qed.

(* [comment removed for export] *)
Theorem iter_alnn : forall c b r, SIq c -> c_more c = true -> alnn (iter c b r).
Proof.
  intros c b r HS Hm. pose proof HS as [H1 H2]. unfold iter.
  destruct (Z.eq_dec (c_st c) ST_STRING) as [Hs|Hs]; [rewrite Hs, PMRA.dispatch_string'; cbn [act_run]; apply parse_string_alnn; assumption|].
  destruct (Z.eq_dec (c_st c) ST_NUMBER) as [Hnm|Hnm]; [rewrite Hnm, PMRA.dispatch_number'; cbn [act_run]; apply parse_number_alnn; assumption|].
  assert (Hn : ~ tok c) by (intros [X|X]; [exact (Hs X) | exact (Hnm X)]). assert (Hnn : nots (c_st c)) by (split; assumption).
  pose proof (PMRF.dispatch_fact (c_st c) (top c) b) as DF. pose proof (PMRF.dispatch_push (c_st c) (top c) b) as DP. revert DF DP.
  destruct (dispatch (c_st c) (top c) b) as [code k| | | |arr|arr|key| |which| |s k|k| | | | |] eqn:Hdis; cbn [PMRF.act_fact PMRF.act_push_ok act_run]; intros DF DP.
  - (* [comment removed for export] *) destruct k; apply alnn_err; exact HS.
  - (* [comment removed for export] *) apply alnn_ret. unfold SIq, tok. autorewrite with fld. split; [intros [X|X]; discriminate X | exact H2].
  - (* [comment removed for export] *) exact (proj1 (skip_space_alnn (b :: r) c HS Hn)).
  - (* [comment removed for export] *) apply alnn_ret. apply SIq_set_st_plain; [discriminate | discriminate|]. autorewrite with fld. apply Forall_app. split; [exact H2 | constructor; [exact Hnn | constructor]].
  - (* [comment removed for export] *) apply begin_container_alnn; exact HS.
  - (* [comment removed for export] *) apply end_container_alnn; exact HS.
  - (* [comment removed for export] *) unfold start_string. apply parse_string_alnn; [| destruct key; autorewrite with fld; reflexivity].
    unfold SIq, tok. destruct key; autorewrite with fld; (split; [intros _; try rewrite PMRA.dlen_tok_clear; cbn; lia|]);
      [apply Forall_app; split; [exact H2 | constructor; [unfold nots, ST_MEMBER_NAME, ST_STRING, ST_NUMBER; lia | constructor]] | exact H2].
  - (* [comment removed for export] *) unfold start_number. apply parse_number_alnn; [| autorewrite with fld; reflexivity].
    unfold SIq, tok. autorewrite with fld. split; [intros _; try rewrite PMRA.dlen_tok_clear; cbn; lia | exact H2].
  - (* [comment removed for export] *) destruct (which =? 0); [|destruct (which =? 1)]; apply parse_lit_alnn; try exact HS; PMRF.ured; unfold ST_STRING, ST_NUMBER; lia.
  - (* [comment removed for export] *) apply alnn_bind; [apply begin_member_alnn; [exact HS | exact Hn]|]. intros c1 w1 S1 _ _. apply alnn_ret. exact S1.
  - (* [comment removed for export] *) destruct (PMRF.dispatch_goto (c_st c) (top c) b s k Hdis) as (_ & G1 & G2).
    destruct k; apply alnn_ret; apply SIq_set_st_plain; try assumption.
  - (* [comment removed for export] *) assert (NT : nots (top c)) by (unfold top; apply nots_last; [exact H2 | unfold nots, ST_STRING, ST_NUMBER; lia]). destruct NT as [NT1 NT2].
    destruct k; (apply alnn_ret; apply SIq_set_st_plain; [exact NT1 | exact NT2 | autorewrite with fld; apply nots_removelast; exact H2]).
  - (* [comment removed for export] *) apply alnn_ret. apply SIq_set_st_plain; [discriminate | discriminate|]. autorewrite with fld. apply Forall_app. split; [exact H2 | constructor; [exact Hnn | constructor]].
  - (* [comment removed for export] *) apply lit_done_alnn; exact HS.
  - (* [comment removed for export] *) exfalso. exact (Hs DF).
  - (* [comment removed for export] *) exfalso. exact (Hnm DF).
  - (* [comment removed for export] *) apply alnn_err. exact HS.
Qed.

Theorem loop_alnn : forall F c w, SIq c -> alnn (loop F c w).
Proof.
  induction F as [|F IH]; intros c w HS.
  - destruct w as [|b r]; cbn; [apply alnn_ret; exact HS|]. destruct (c_more c); cbn; [apply alnn_err; exact HS | apply alnn_ret; exact HS].
  - destruct w as [|b r]; [rewrite PMRF.loop_nil; apply alnn_ret; exact HS|].
    destruct (c_more c) eqn:Hm; [|rewrite (PMRF.loop_stopped _ _ _ Hm); apply alnn_ret; exact HS].
    rewrite (PMRF.loop_step F c b r Hm). apply alnn_bind; [exact (iter_alnn c b r HS Hm)|]. intros c1 w1 S1 _ _. apply IH. exact S1.
Qed.
Theorem prologue_alnn : forall c, SIq c -> alnn (prologue c).
Proof.
  intros c HS. pose proof HS as [H1 H2]. unfold prologue.
  destruct (Z.eqb_spec (c_st c) ST_NUMBER) as [Hs|Hs].
  - destruct (_ || _); [apply end_number_alnn; assumption | apply alnn_err; exact HS].
  - destruct (c_st c =? ST_ACCEPT); [apply alnn_ret; unfold SIq, tok; autorewrite with fld; split; [intros [X|X]; discriminate X | exact H2]|].
    destruct (c_st c =? ST_START); [apply alnn_err; exact HS|].
    destruct (c_st c =? ST_DONE); [apply alnn_ret; unfold SIq, tok; autorewrite with fld; split; [intros X; apply H1; exact X | exact H2]|].
    destruct (c_st c =? ST_CR); [|apply alnn_err; exact HS].
    assert (NT : nots (top c)) by (unfold top; apply nots_last; [exact H2 | unfold nots, ST_STRING, ST_NUMBER; lia]). destruct NT as [NT1 NT2].
    apply alnn_ret. apply SIq_set_st_plain; [exact NT1 | exact NT2 | autorewrite with fld; apply nots_removelast; exact H2].
Qed.
Theorem parse_some_alnn : forall c w, SIq c -> alnn (parse_some c w).
Proof.
  intros c w HS. pose proof HS as [H1 H2]. unfold parse_some.
  destruct (c_st c =? ST_ACCEPT); [apply alnn_ret; unfold SIq, tok; autorewrite with fld; split; [intros [X|X]; discriminate X | exact H2]|].
  destruct w as [|b r]; [|apply loop_alnn; exact HS].
  destruct (c_more c) eqn:Hm; [apply prologue_alnn; exact HS | apply alnn_ret; exact HS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SIq_intro : forall c ps, PMR.rm_core c ps -> (tok c -> c_dlen c = Z.of_nat (length (PML.ps_buf ps))) -> Forall nots (PML.ps_stack ps) -> SIq c.
Proof.
  intros c ps (R1 & R2 & R3 & R4 & R5) HD HS. split; [intros Ht; rewrite (HD Ht); lia | rewrite R5; exact HS].
Qed.
End PMRN.
