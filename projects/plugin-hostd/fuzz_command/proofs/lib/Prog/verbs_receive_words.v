From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strspn_c strcspn_c strtok_r_c.
Import ListNotations.
Open Scope Z_scope.

Definition sepl : list byte := map (Z_to_bv 8) [32; 9].

Lemma in_set_sepl : forall b : byte, in_set sepl b = is_sep b.
Proof.
  intros b. unfold in_set, sepl, is_sep. cbn [map existsb].
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), orb_false_r. reflexivity.
Qed.

Lemma cset_sepl : forall b : byte, existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned b)) sepl = is_sep b.
Proof. exact in_set_sepl. Qed.

Lemma words_acc_nosep : forall w cur rest, Forall (fun b => is_sep b = false) w ->
  words_acc cur (w ++ rest) = words_acc (cur ++ w) rest.
Proof.
  induction w as [|x w IH]; intros cur rest H; cbn [app]; [rewrite app_nil_r; reflexivity|].
  apply Forall_cons_iff in H. destruct H as [Hx Hw]. cbn [words_acc]. rewrite Hx.
  rewrite IH by exact Hw. rewrite <- app_assoc. reflexivity.
Qed.

Lemma words_acc_seps : forall s rest, Forall (fun b => is_sep b = true) s ->
  words_acc [] (s ++ rest) = words_acc [] rest.
Proof.
  induction s as [|x s IH]; intros rest H; cbn [app]; [reflexivity|].
  apply Forall_cons_iff in H. destruct H as [Hx Hs]. cbn [words_acc]. rewrite Hx. apply IH. exact Hs.
Qed.

Lemma spn_prefix : forall s, Forall (fun b => is_sep b = true) (firstn (spn_len sepl s) s).
Proof.
  induction s as [|x s IH]; [constructor|]. cbn [spn_len]. rewrite in_set_sepl.
  destruct (is_sep x) eqn:E; cbn [firstn]; [constructor; assumption | constructor].
Qed.

Lemma spn_stop : forall s, (spn_len sepl s < length s)%nat ->
  exists x r, skipn (spn_len sepl s) s = x :: r /\ is_sep x = false.
Proof.
  induction s as [|x s IH]; cbn [length spn_len]; [lia|]. rewrite in_set_sepl.
  destruct (is_sep x) eqn:E; intros H.
  - cbn [skipn]. apply IH. lia.
  - exists x, s. split; [reflexivity | exact E].
Qed.

Lemma spn_le : forall s, (spn_len sepl s <= length s)%nat.
Proof.
  induction s as [|x s IH]; cbn [length spn_len]; [lia|]. destruct (in_set sepl x); lia.
Qed.

Lemma cspn_prefix : forall s, Forall (fun b => is_sep b = false) (firstn (cspn_len sepl s) s).
Proof.
  induction s as [|x s IH]; [constructor|]. cbn [cspn_len]. rewrite cset_sepl.
  destruct (is_sep x) eqn:E; cbn [firstn]; [constructor | constructor; assumption].
Qed.

Lemma cspn_stop : forall s, (cspn_len sepl s < length s)%nat ->
  exists x r, skipn (cspn_len sepl s) s = x :: r /\ is_sep x = true.
Proof.
  induction s as [|x s IH]; cbn [length cspn_len]; [lia|]. rewrite cset_sepl.
  destruct (is_sep x) eqn:E; intros H.
  - exists x, s. split; [reflexivity | exact E].
  - cbn [skipn]. apply IH. lia.
Qed.

Lemma cspn_le : forall s, (cspn_len sepl s <= length s)%nat.
Proof.
  induction s as [|x s IH]; cbn [length cspn_len]; [lia|]. destruct (existsb _ _); lia.
Qed.

Lemma cspn_pos : forall x r, is_sep x = false -> (1 <= cspn_len sepl (x :: r))%nat.
Proof. intros x r H. cbn [cspn_len]. rewrite cset_sepl, H. lia. Qed.

Definition tok_word (s : list byte) : list byte :=
  firstn (tok_j sepl s - tok_i sepl s) (skipn (tok_i sepl s) s).

Definition tok_rest (s : list byte) : list byte := skipn (S (tok_j sepl s)) s.

Lemma tok_i_le_j : forall s, (tok_i sepl s <= tok_j sepl s)%nat.
Proof. intros s. unfold tok_j. lia. Qed.

Lemma tok_j_le : forall s, (tok_j sepl s <= length s)%nat.
Proof.
  intros s. unfold tok_j, tok_i. pose proof (cspn_le (skipn (spn_len sepl s) s)) as H.
  rewrite length_skipn in H. pose proof (spn_le s). lia.
Qed.

Lemma words_none : forall s, tok_i sepl s = length s -> words s = [].
Proof.
  intros s H. unfold words, tok_i in *. rewrite <- (firstn_skipn (spn_len sepl s) s).
  rewrite words_acc_seps by apply spn_prefix. rewrite H, skipn_all. reflexivity.
Qed.

Lemma words_step : forall s, (tok_i sepl s < length s)%nat ->
  words s = tok_word s :: words (tok_rest s) /\ tok_word s <> [] /\ (tok_i sepl s < tok_j sepl s)%nat.
Proof.
  intros s H. unfold words, tok_word, tok_rest, tok_j. set (i := tok_i sepl s) in *.
  set (u := skipn i s). set (c := cspn_len sepl u).
  destruct (spn_stop s H) as (x & r & Eu & Hx). change (skipn (spn_len sepl s) s) with u in Eu.
  assert (C1 : (1 <= c)%nat) by (unfold c; rewrite Eu; apply cspn_pos; exact Hx).
  replace (i + c - i)%nat with c by lia.
  assert (Es : s = firstn i s ++ firstn c u ++ skipn c u)
    by (rewrite firstn_skipn; unfold u; rewrite firstn_skipn; reflexivity).
  assert (NW : firstn c u <> []).
  { rewrite Eu. destruct c as [|c]; [lia|]. discriminate. }
  split; [|split; [exact NW | lia]].
  rewrite Es at 1. rewrite words_acc_seps by apply spn_prefix.
  rewrite words_acc_nosep by apply cspn_prefix. cbn [app].
  assert (Er : skipn (S (i + c)) s = skipn (S c) u)
    by (unfold u; rewrite skipn_skipn; f_equal; lia).
  rewrite Er.
  destruct (Nat.lt_ge_cases c (length u)) as [Lt|Ge].
  - destruct (cspn_stop u Lt) as (y & r' & Ey & Hy). fold c in Ey.
    rewrite Ey. cbn [words_acc]. rewrite Hy.
    destruct (firstn c u) as [|z zs] eqn:Ef; [congruence|].
    f_equal. replace (skipn (S c) u) with r'; [reflexivity|].
    replace (S c) with (1 + c)%nat by lia. rewrite <- skipn_skipn, Ey. reflexivity.
  - rewrite skipn_all2 by exact Ge. rewrite skipn_all2 by lia. cbn [words_acc].
    destruct (firstn c u) as [|z zs] eqn:Ef; [congruence|]. reflexivity.
Qed.

Lemma tok_word_nosep : forall s, Forall (fun b => is_sep b = false) (tok_word s).
Proof.
  intros s. unfold tok_word, tok_j. replace (tok_i sepl s + cspn_len sepl (skipn (tok_i sepl s) s) - tok_i sepl s)%nat
    with (cspn_len sepl (skipn (tok_i sepl s) s)) by lia. apply cspn_prefix.
Qed.

Lemma in_firstn_l : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma in_skipn_l : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma in_tok_word : forall s b, In b (tok_word s) -> In b s.
Proof. intros s b H. unfold tok_word in H. apply in_firstn_l, in_skipn_l in H. exact H. Qed.

Lemma in_tok_rest : forall s b, In b (tok_rest s) -> In b s.
Proof. intros s b H. unfold tok_rest in H. apply in_skipn_l in H. exact H. Qed.
