From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_text disco_json_reader_model.
Import ListNotations.
Open Scope Z_scope.

Definition tok_inb (B : list Z) (t : tokv) : Prop :=
  tv_kind t = 0 \/ (0 <= snd (fst t) /\ 0 <= snd t /\ snd (fst t) + snd t <= jlen B).

Lemma json_ws_f_ge : forall B f i, i <= json_ws_f B i f.
Proof.
  intros B f. induction f as [|f IH]; intros i; cbn [json_ws_f].
  - lia.
  - destruct ((i <? jlen B) && jws_char (jbyte B i)).
    + specialize (IH (i + 1)). lia.
    + lia.
Qed.

Lemma json_ws_ge : forall B i, i <= json_ws B i.
Proof. intros B i. unfold json_ws. apply json_ws_f_ge. Qed.

Lemma jdigits_ge : forall B f j, j <= jdigits B j f.
Proof.
  intros B f. induction f as [|f IH]; intros j; cbn [jdigits].
  - lia.
  - destruct ((j <? jlen B) && jdigit (jbyte B j)).
    + specialize (IH (j + 1)). lia.
    + lia.
Qed.

Lemma jdigits_le : forall B f j, j <= jlen B -> jdigits B j f <= jlen B.
Proof.
  intros B f. induction f as [|f IH]; intros j Hj; cbn [jdigits].
  - lia.
  - destruct ((j <? jlen B) && jdigit (jbyte B j)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E _]. apply Z.ltb_lt in E. apply IH. lia.
    + lia.
Qed.

Lemma jstr_bnd : forall B i f j r, jstr B i j f = Some r ->
  exists jc, j <= jc < jlen B /\ r = (jc + 1, 1, i + 1, jc - i - 1).
Proof.
  intros B i f. induction f as [|f IH]; intros j r H; cbn [jstr] in H.
  - discriminate.
  - destruct (jlen B <=? j) eqn:E1; cbv beta iota in H; [discriminate|].
    apply Z.leb_gt in E1.
    destruct (jbyte B j =? 34) eqn:E2; cbv beta iota in H.
    + injection H; intros; subst. exists j. split; [lia|reflexivity].
    + destruct (jbyte B j <? 32) eqn:E3; cbv beta iota in H; [discriminate|].
      destruct (jbyte B j =? 92) eqn:E4; cbv beta iota in H.
      * destruct (jlen B <=? j + 1) eqn:E5; cbv beta iota in H; [discriminate|].
        destruct (negb (jesc (jbyte B (j + 1)))) eqn:E6; cbv beta iota in H; [discriminate|].
        destruct (jbyte B (j + 1) =? 117) eqn:E7; cbv beta iota in H.
        -- match type of H with context [if ?c then _ else _] => destruct c eqn:E8 end;
             cbv beta iota in H; [discriminate|].
           apply IH in H. destruct H as (jc & Hjc & ->). exists jc. split; [lia|reflexivity].
        -- apply IH in H. destruct H as (jc & Hjc & ->). exists jc. split; [lia|reflexivity].
      * apply IH in H. destruct H as (jc & Hjc & ->). exists jc. split; [lia|reflexivity].
Qed.

Lemma jlit_bnd : forall B i ws r, jlit B i ws = Some r ->
  exists n, 0 <= n <= jlen B - i /\ r = (i + n, 3, i, n).
Proof.
  intros B i ws. induction ws as [|w ws IH]; intros r H; cbn [jlit] in H.
  - discriminate.
  - match type of H with context [if ?c then _ else _] => destruct c eqn:E end; cbv beta iota in H.
    + injection H; intros; subst. apply andb_true_iff in E. destruct E as [E _]. apply Z.leb_le in E.
      exists (Z.of_nat (length w)). split; [lia|reflexivity].
    + apply IH. exact H.
Qed.

Lemma jdig_tail : forall B k r,
  (if jdig_at B k then Some (jdigits B k (length B)) else None) = Some r -> k <= r <= jlen B.
Proof.
  intros B k r H. destruct (jdig_at B k) eqn:E; cbv beta iota in H; [|discriminate].
  injection H; intros; subst. unfold jdig_at in E. apply andb_true_iff in E. destruct E as [E _].
  apply Z.ltb_lt in E. split; [apply jdigits_ge|apply jdigits_le; lia].
Qed.

Lemma jfrac_bnd : forall B j r, jfrac B j = Some r -> j <= jlen B -> j <= r <= jlen B.
Proof.
  intros B j r H Hj. unfold jfrac in H.
  destruct ((j <? jlen B) && (jbyte B j =? 46)) eqn:E; cbv beta iota in H.
  - apply jdig_tail in H. lia.
  - injection H; intros; subst. lia.
Qed.

Lemma jexp_bnd : forall B j r, jexp B j = Some r -> j <= jlen B -> j <= r <= jlen B.
Proof.
  intros B j r H Hj. unfold jexp in H.
  destruct ((j <? jlen B) && ((jbyte B j =? 101) || (jbyte B j =? 69))) eqn:E; cbv beta iota zeta in H.
  - apply jdig_tail in H. revert H.
    match goal with |- context [if ?c then _ else _] => destruct c end; intro H; lia.
  - injection H; intros; subst. lia.
Qed.

Lemma jnum_tail : forall B i j0 r,
  (if negb (jdig_at B j0) then None else
   match jfrac B (if jbyte B j0 =? 48 then j0 + 1 else jdigits B j0 (length B)) with
   | None => None
   | Some j2 => match jexp B j2 with None => None | Some j3 => Some (j3, 2, i, j3 - i) end
   end) = Some r -> i <= j0 -> exists j3, i <= j3 <= jlen B /\ r = (j3, 2, i, j3 - i).
Proof.
  intros B i j0 r H Hi.
  destruct (negb (jdig_at B j0)) eqn:E0; cbv beta iota in H; [discriminate|].
  apply negb_false_iff in E0. unfold jdig_at in E0. apply andb_true_iff in E0. destruct E0 as [E0 _].
  apply Z.ltb_lt in E0.
  assert (Hj1 : j0 <= (if jbyte B j0 =? 48 then j0 + 1 else jdigits B j0 (length B)) <= jlen B).
  { destruct (jbyte B j0 =? 48); [lia|split; [apply jdigits_ge|apply jdigits_le; lia]]. }
  destruct (jfrac B (if jbyte B j0 =? 48 then j0 + 1 else jdigits B j0 (length B))) as [j2|] eqn:E2;
    cbv beta iota in H; [|discriminate].
  pose proof (jfrac_bnd B _ j2 E2) as F2. specialize (F2 ltac:(lia)).
  destruct (jexp B j2) as [j3|] eqn:E3; cbv beta iota in H; [|discriminate].
  pose proof (jexp_bnd B j2 j3 E3) as F3. specialize (F3 ltac:(lia)).
  injection H; intros; subst. exists j3. split; [lia|reflexivity].
Qed.

Lemma jnum_bnd : forall B i r, jnum B i = Some r ->
  exists j3, i <= j3 <= jlen B /\ r = (j3, 2, i, j3 - i).
Proof.
  intros B i r H. unfold jnum in H. cbv zeta in H.
  apply (jnum_tail B i (if jbyte B i =? 45 then i + 1 else i) r H).
  destruct (jbyte B i =? 45); lia.
Qed.

Lemma jscalar_bnd : forall B i j k s l, jscalar B i = Some (j, k, s, l) -> 0 <= i ->
  0 <= s /\ 0 <= l /\ s + l <= jlen B /\ 0 <= j.
Proof.
  intros B i j k s l H Hi. unfold jscalar in H.
  destruct (jlen B <=? i) eqn:E1; cbv beta iota in H; [discriminate|].
  destruct (jbyte B i =? 34) eqn:E2; cbv beta iota in H.
  - apply jstr_bnd in H. destruct H as (jc & Hjc & Heq). injection Heq; intros; subst. lia.
  - destruct (jlit B i jlit_words) as [t|] eqn:E3; cbv beta iota in H.
    + injection H; intros; subst. apply jlit_bnd in E3. destruct E3 as (n & Hn & Heq).
      injection Heq; intros; subst. lia.
    + apply jnum_bnd in H. destruct H as (j3 & Hj3 & Heq). injection Heq; intros; subst. lia.
Qed.

Lemma set_nth_forall : forall (P : tokv -> Prop) k o t, Forall P o -> P t -> Forall P (set_nth k o t).
Proof.
  intros P k o. revert k. induction o as [|x o IH]; intros k t Ho Ht; destruct k as [|k]; cbn [set_nth].
  - constructor.
  - constructor.
  - inversion Ho; subst. constructor; assumption.
  - inversion Ho; subst. constructor; [assumption|]. apply IH; assumption.
Qed.

Lemma jobj_empty_inb : forall B, Forall (tok_inb B) jobj_empty.
Proof.
  intros B. apply Forall_forall. intros x Hx. unfold jobj_empty in Hx. apply repeat_spec in Hx. subst.
  left. reflexivity.
Qed.

Lemma json_pairs_inb : forall B f i cur r c, json_pairs B i cur f = Some (r, c) -> 0 <= i ->
  Forall (tok_inb B) cur -> 0 <= r /\ Forall (tok_inb B) c.
Proof.
  intros B f. induction f as [|f IH]; intros i cur r c H Hi Hc; cbn [json_pairs] in H; cbv zeta in H.
  - discriminate.
  - destruct (jscalar B i) as [[[[j kk] ks] kl]|] eqn:E1; cbv beta iota in H; [|discriminate].
    pose proof (jscalar_bnd B i j kk ks kl E1 Hi) as (_ & _ & _ & Hj).
    destruct (negb (kk =? 1)) eqn:E2; cbv beta iota in H; [discriminate|].
    destruct (negb (at_byte B (json_ws B j) 58)) eqn:E3; cbv beta iota in H; [discriminate|].
    pose proof (json_ws_ge B j) as W1.
    pose proof (json_ws_ge B (json_ws B j + 1)) as W2.
    destruct (jscalar B (json_ws B (json_ws B j + 1))) as [[[[j2 vk] vs] vl]|] eqn:E4;
      cbv beta iota in H; [|discriminate].
    pose proof (jscalar_bnd B (json_ws B (json_ws B j + 1)) j2 vk vs vl E4 ltac:(lia)) as (Hvs & Hvl & Hvb & Hj2).
    pose proof (json_ws_ge B j2) as W3.
    pose proof (json_ws_ge B (json_ws B j2 + 1)) as W4.
    assert (Hv : tok_inb B (vk, vs, vl)) by (right; cbn [fst snd]; lia).
    destruct (slot_of B (kk, ks, kl)) as [k|] eqn:E5; cbv beta iota in H.
    + destruct (tv_kind (nth k cur tok_none) =? 0) eqn:E6; cbv beta iota in H; [|discriminate].
      pose proof (set_nth_forall (tok_inb B) k cur (vk, vs, vl) Hc Hv) as Hc'.
      destruct (at_byte B (json_ws B j2) 44) eqn:E7; cbv beta iota in H.
      * exact (IH _ _ _ _ H ltac:(lia) Hc').
      * destruct (at_byte B (json_ws B j2) 125) eqn:E8; cbv beta iota in H; [|discriminate].
        injection H; intros; subst. split; [lia|exact Hc'].
    + destruct (at_byte B (json_ws B j2) 44) eqn:E7; cbv beta iota in H.
      * exact (IH _ _ _ _ H ltac:(lia) Hc).
      * destruct (at_byte B (json_ws B j2) 125) eqn:E8; cbv beta iota in H; [|discriminate].
        injection H; intros; subst. split; [lia|exact Hc].
Qed.

Lemma json_obj1_inb : forall B i1 i2 cur,
  (if at_byte B i1 125 then Some (i1 + 1, jobj_empty) else json_pairs B i1 jobj_empty (length B)) = Some (i2, cur) ->
  0 <= i1 -> 0 <= i2 /\ Forall (tok_inb B) cur.
Proof.
  intros B i1 i2 cur H Hi.
  destruct (at_byte B i1 125); cbv beta iota in H.
  - injection H; intros; subst. split; [lia|apply jobj_empty_inb].
  - exact (json_pairs_inb B (length B) i1 jobj_empty i2 cur H Hi (jobj_empty_inb B)).
Qed.

Lemma json_objs_inb : forall B f i count max acc r os,
  json_objs B i count max acc f = Some (r, os) -> 0 <= i -> Forall (Forall (tok_inb B)) acc ->
  Forall (Forall (tok_inb B)) os.
Proof.
  intros B f. induction f as [|f IH]; intros i count max acc r os H Hi Ha; cbn [json_objs] in H; cbv zeta in H.
  - discriminate.
  - destruct (negb (at_byte B i 123)) eqn:E1; cbv beta iota in H; [discriminate|].
    pose proof (json_ws_ge B (i + 1)) as W1.
    match type of H with
    | context [match ?x with _ => _ end] => destruct x as [[i2 cur]|] eqn:E2
    end; cbv beta iota in H; [|discriminate].
    pose proof (json_obj1_inb B _ i2 cur E2) as F. specialize (F ltac:(lia)). destruct F as [Hi2 Hcur].
    pose proof (json_ws_ge B i2) as W2.
    pose proof (json_ws_ge B (json_ws B i2 + 1)) as W3.
    assert (Ha' : Forall (Forall (tok_inb B)) (if count <? max then acc ++ [cur] else acc)).
    { destruct (count <? max).
      - apply Forall_app. split; [exact Ha|constructor; [exact Hcur|constructor]].
      - exact Ha. }
    destruct (at_byte B (json_ws B i2) 44) eqn:E3; cbv beta iota in H.
    + exact (IH _ _ _ _ _ _ H ltac:(lia) Ha').
    + destruct (at_byte B (json_ws B i2) 93) eqn:E4; cbv beta iota in H; [|discriminate].
      destruct (json_ws B (json_ws B i2 + 1) =? jlen B) eqn:E5; cbv beta iota in H; [|discriminate].
      injection H; intros; subst. exact Ha'.
Qed.

Theorem json_read_inb : forall B max c os, json_read B max = Some (c, os) -> Forall (Forall (tok_inb B)) os.
Proof.
  intros B max c os H. unfold json_read in H. cbv zeta in H.
  destruct (negb (at_byte B (json_ws B 0) 91)) eqn:E1; cbv beta iota in H; [discriminate|].
  pose proof (json_ws_ge B 0) as W0.
  pose proof (json_ws_ge B (json_ws B 0 + 1)) as W1.
  destruct (at_byte B (json_ws B (json_ws B 0 + 1)) 93) eqn:E2; cbv beta iota in H.
  - destruct (json_ws B (json_ws B (json_ws B 0 + 1) + 1) =? jlen B) eqn:E3; cbv beta iota in H; [|discriminate].
    injection H; intros; subst. constructor.
  - exact (json_objs_inb B _ _ _ _ _ _ _ H ltac:(lia) (Forall_nil _)).
Qed.
