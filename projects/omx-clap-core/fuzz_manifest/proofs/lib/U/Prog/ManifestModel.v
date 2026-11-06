From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zl_eqb a' b'
  | _, _ => false
  end.

Lemma zl_eqb_eq : forall a b, zl_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; split; intro H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - inversion H; subst. rewrite Z.eqb_refl. cbn. apply IH. reflexivity.
Qed.

Fixpoint count_while (f : Z -> bool) (l : list Z) : nat :=
  match l with
  | [] => O
  | x :: l' => if f x then S (count_while f l') else O
  end.

Fixpoint find_idx (f : Z -> bool) (l : list Z) : option nat :=
  match l with
  | [] => None
  | x :: l' => if f x then Some O else option_map S (find_idx f l')
  end.

Definition is_alnum (c : Z) : bool :=
  ((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).

Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).

Definition name_char (c : Z) : bool :=
  is_alnum c || (c =? 95) || (c =? 45) || (c =? 58) || (c =? 37) || (c =? 92) || (128 <=? c).

Definition plain_ok (c : Z) : bool := is_alnum c || (c =? 95) || (c =? 45) || (c =? 46) || (c =? 58).

Definition plain_name (bs : list Z) : bool :=
  match bs with
  | [] => false
  | _ => negb (last bs 0 =? 46) && forallb plain_ok bs
  end.

Definition byte_at (t : list Z) (i : nat) : Z := nth i t 0.

Definition token_at (t pre loc : list Z) (j : nat) : bool :=
  let e := (j + length pre + 1 + length loc)%nat in
  (e <=? length t)%nat
  && zl_eqb (firstn (length pre) (skipn j t)) pre
  && (byte_at t (j + length pre) =? 58)
  && zl_eqb (firstn (length loc) (skipn (j + length pre + 1) t)) loc
  && match j with
     | O => true
     | S j' => negb (name_char (byte_at t j')) && negb (byte_at t j' =? 46)
     end
  && negb (name_char (byte_at t e)).

Definition token (t pre loc : list Z) : bool := existsb (token_at t pre loc) (seq 0 (S (length t))).

Definition whole_at (t u : list Z) (j : nat) : bool := zl_eqb (firstn (length u + 2) (skipn j t)) (60 :: u ++ [62]).

Definition whole (t u : list Z) : bool := existsb (whole_at t u) (seq 0 (S (length t))).

Definition prefix_lc : list Z := [112; 114; 101; 102; 105; 120].

Fixpoint ci_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => ((x =? y) || (x =? y - 32)) && ci_eqb a' b'
  | _, _ => false
  end.

Definition head (t : list Z) (i : nat) : option nat :=
  if (byte_at t i =? 64) && zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc then Some (i + 7)%nat
  else if ci_eqb (firstn 6 (skipn i t)) prefix_lc
          && match i with O => true | S i' => is_space (byte_at t i') end
       then Some (i + 6)%nat
       else None.

Definition name_ok (c : Z) : bool := negb (c =? 0) && negb (c =? 58) && negb (is_space c).

Inductive decl_r := DNone | DCut | DFound (name nl ns nl2 close : nat).

Definition decl (t : list Z) (i : nat) : decl_r :=
  match head t i with
  | None => DNone
  | Some p0 =>
      if negb (is_space (byte_at t p0)) then DNone else
      let p1 := (p0 + count_while is_space (skipn p0 t))%nat in
      let p2 := (p1 + count_while name_ok (skipn p1 t))%nat in
      if negb (byte_at t p2 =? 58) then DNone else
      let p3 := (S p2 + count_while is_space (skipn (S p2) t))%nat in
      if negb (byte_at t p3 =? 60) then DNone else
      match find_idx (fun c => c =? 62) (skipn (S p3) t) with
      | None => DCut
      | Some o => DFound p1 (p2 - p1) (S p3) o (S p3 + o)
      end
  end.

Definition matches (t u : list Z) (ns nl2 : nat) : bool :=
  (nl2 <? length u)%nat && zl_eqb (firstn nl2 (skipn ns t)) (firstn nl2 u) && plain_name (skipn nl2 u).

Fixpoint scan (t u : list Z) (i d fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if (length t <=? i)%nat then 0 else
      match decl t i with
      | DNone => scan t u (S i) d fuel'
      | DCut => 0
      | DFound name nl ns nl2 close =>
          if matches t u ns nl2 then
            if (16 <? S d)%nat then 1
            else if token t (firstn nl (skipn name t)) (skipn nl2 u) then 1
            else scan t u (S close) (S d) fuel'
          else scan t u (S close) d fuel'
      end
  end.

Fixpoint readings (t u : list Z) (i d fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      if (length t <=? i)%nat then O else
      match decl t i with
      | DNone => readings t u (S i) d fuel'
      | DCut => O
      | DFound name nl ns nl2 close =>
          if matches t u ns nl2 then
            if (16 <? S d)%nat then O
            else if token t (firstn nl (skipn name t)) (skipn nl2 u) then 1%nat
            else S (readings t u (S close) (S d) fuel')
          else readings t u (S close) d fuel'
      end
  end.

Definition names (t u : list Z) : Z :=
  if (length u =? 0)%nat then 0
  else if whole t u then 1
  else scan t u 0 0 (S (length t)).

Definition nreadings (t u : list Z) : nat :=
  if (length u =? 0)%nat then O
  else if whole t u then O
  else readings t u 0 0 (S (length t)).

Definition no_zero (l : list Z) : Prop := Forall (fun c => 0 < c < 256) l.

Definition tail_lv2 : list Z :=
  [10; 32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10].

Definition txt_whole (u : list Z) : list Z := 60 :: u ++ 62 :: tail_lv2.
Definition txt_wholex (u : list Z) : list Z := 60 :: u ++ 88 :: 62 :: tail_lv2.
Definition txt_t1 (u : list Z) (k : nat) : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60] ++ firstn k u ++ [62; 32; 46; 10; 112; 58]
  ++ skipn k u ++ tail_lv2.
Definition txt_t2 (u : list Z) (k : nat) : list Z :=
  [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60] ++ firstn k u ++ [62; 10; 112; 58] ++ skipn k u ++ tail_lv2.
Definition txt_t3 (u : list Z) (k : nat) : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60] ++ firstn k u ++ [62; 32; 46; 10; 58] ++ skipn k u
  ++ tail_lv2.
Definition txt_t1x (u : list Z) (k : nat) : list Z :=
  [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60] ++ firstn k u ++ [62; 32; 46; 10; 112; 58]
  ++ skipn k u ++ 88 :: tail_lv2.

Lemma rt_empty : forall u, names [] u = 0.
Proof.
  intros u. unfold names. destruct (length u =? 0)%nat; [reflexivity|].
  unfold whole. cbn. unfold whole_at. cbn.
  destruct (length u + 2)%nat eqn:E; [lia|]. cbn. reflexivity.
Qed.

Lemma skipn_app_len : forall (a b : list Z) m, skipn (length a + m) (a ++ b) = skipn m b.
Proof. induction a as [|x a IH]; intros b m; cbn; [reflexivity|apply IH]. Qed.

Lemma firstn_app_len : forall (a b : list Z), firstn (length a) (a ++ b) = a.
Proof. induction a as [|x a IH]; intros b; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma byte_at_app_len : forall (a b : list Z) m, byte_at (a ++ b) (length a + m) = byte_at b m.
Proof. unfold byte_at. induction a as [|x a IH]; intros b m; cbn; [reflexivity|apply IH]. Qed.

Lemma zl_eqb_refl : forall a, zl_eqb a a = true.
Proof. intros a. apply zl_eqb_eq. reflexivity. Qed.

Lemma find_idx_app_none : forall f (a b : list Z), forallb (fun c => negb (f c)) a = true ->
  find_idx f (a ++ b) = option_map (Nat.add (length a)) (find_idx f b).
Proof.
  intros f. induction a as [|x a IH]; intros b H; cbn in *.
  - destruct (find_idx f b); reflexivity.
  - apply andb_true_iff in H as [H1 H2]. destruct (f x); [discriminate|].
    rewrite IH by exact H2. destruct (find_idx f b); reflexivity.
Qed.

Lemma names_whole : forall t u, (length u <> 0)%nat -> whole t u = true -> names t u = 1.
Proof.
  intros t u Hu Hw. unfold names. destruct (length u =? 0)%nat eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - rewrite Hw. reflexivity.
Qed.

Lemma rt_whole : forall u, (length u <> 0)%nat -> names (txt_whole u) u = 1.
Proof.
  intros u Hu. apply names_whole; [exact Hu|].
  unfold whole. cbn [seq existsb]. apply orb_true_iff. left.
  unfold whole_at, txt_whole. cbn [skipn].
  replace (length u + 2)%nat with (S (length u + 1)) by lia. cbn [firstn].
  rewrite firstn_app_2. cbn [firstn]. apply zl_eqb_refl.
Qed.

Lemma names_first_decl : forall t u name nl ns nl2 close,
  (length u <> 0)%nat -> (length t <> 0)%nat ->
  decl t 0 = DFound name nl ns nl2 close -> matches t u ns nl2 = true ->
  token t (firstn nl (skipn name t)) (skipn nl2 u) = true -> names t u = 1.
Proof.
  intros t u name nl ns nl2 close Hu Ht Hd Hm Htk. unfold names.
  destruct (length u =? 0)%nat eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  destruct (whole t u); [reflexivity|].
  cbn [scan]. destruct (length t <=? 0)%nat eqn:E2; [apply Nat.leb_le in E2; lia|].
  rewrite Hd, Hm, Htk. reflexivity.
Qed.

Ltac len_simpl := repeat (first [rewrite length_app | progress (cbn [length])]).

Lemma token_at_mid : forall A c pre loc d B,
  name_char c = false -> (c =? 46) = false -> name_char d = false ->
  token_at (A ++ c :: pre ++ 58 :: loc ++ d :: B) pre loc (S (length A)) = true.
Proof.
  intros A c pre loc d B Hc Hc2 Hd.
  set (t := A ++ c :: pre ++ 58 :: loc ++ d :: B).
  assert (Hl : length t = (length A + 1 + length pre + 1 + length loc + 1 + length B)%nat).
  { subst t. len_simpl. lia. }
  assert (S1 : skipn (S (length A)) t = pre ++ 58 :: loc ++ d :: B).
  { subst t. replace (S (length A)) with (length A + 1)%nat by lia. rewrite skipn_app_len. reflexivity. }
  assert (S2 : skipn (S (length A) + length pre + 1) t = loc ++ d :: B).
  { subst t. replace (S (length A) + length pre + 1)%nat with (length A + S (length pre + 1))%nat by lia.
    rewrite skipn_app_len. cbn [skipn]. rewrite skipn_app_len. reflexivity. }
  assert (B0 : byte_at t (length A) = c).
  { subst t. replace (length A) with (length A + 0)%nat at 1 by lia. rewrite byte_at_app_len. reflexivity. }
  assert (B1 : byte_at t (S (length A) + length pre) = 58).
  { subst t. replace (S (length A) + length pre)%nat with (length A + S (length pre + 0))%nat by lia.
    rewrite byte_at_app_len. unfold byte_at. cbn [nth]. fold (byte_at (pre ++ 58 :: loc ++ d :: B) (length pre + 0)).
    rewrite byte_at_app_len. reflexivity. }
  assert (B2 : byte_at t (S (length A) + length pre + 1 + length loc) = d).
  { subst t.
    replace (S (length A) + length pre + 1 + length loc)%nat
      with (length A + S (length pre + S (length loc + 0)))%nat by lia.
    rewrite byte_at_app_len. unfold byte_at. cbn [nth].
    fold (byte_at (pre ++ 58 :: loc ++ d :: B) (length pre + S (length loc + 0))).
    rewrite byte_at_app_len. unfold byte_at. cbn [nth].
    fold (byte_at (loc ++ d :: B) (length loc + 0)). rewrite byte_at_app_len. reflexivity. }
  unfold token_at. rewrite S1, S2, B0, B1, B2, firstn_app_len, firstn_app_len, !zl_eqb_refl, Hc, Hc2, Hd.
  assert (He : (S (length A) + length pre + 1 + length loc <=? length t)%nat = true).
  { apply Nat.leb_le. rewrite Hl. lia. }
  rewrite He. reflexivity.
Qed.

Definition tl_lv2 : list Z := [32; 32; 32; 32; 97; 32; 108; 118; 50; 58; 80; 108; 117; 103; 105; 110; 32; 46; 10].

Lemma token_in : forall t pre loc j, (j <= length t)%nat -> token_at t pre loc j = true -> token t pre loc = true.
Proof.
  intros t pre loc j Hj H. unfold token. apply existsb_exists. exists j. split; [apply in_seq; lia|exact H].
Qed.

Lemma matches_split : forall (P M : list Z) u k,
  (k < length u)%nat -> plain_name (skipn k u) = true ->
  matches (P ++ firstn k u ++ M) u (length P) k = true.
Proof.
  intros P M u k Hk Hp. unfold matches.
  assert (Hl : length (firstn k u) = k) by (rewrite length_firstn; lia).
  assert (Hs : skipn (length P) (P ++ firstn k u ++ M) = firstn k u ++ M).
  { replace (length P) with (length P + 0)%nat by lia. rewrite skipn_app_len. reflexivity. }
  pose proof (firstn_app_len (firstn k u) M) as F. rewrite Hl in F.
  rewrite Hs, F, zl_eqb_refl, Hp.
  apply Nat.ltb_lt in Hk. rewrite Hk. reflexivity.
Qed.

Lemma rt_t1 : forall u k, (k < length u)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn k u) = true -> plain_name (skipn k u) = true ->
  names (txt_t1 u k) u = 1.
Proof.
  intros u k Hk Hg Hp.
  assert (Hl : length (firstn k u) = k) by (rewrite length_firstn; lia).
  assert (Hd : decl (txt_t1 u k) 0 = DFound 8 1 12 k (12 + k)).
  { unfold decl, txt_t1. cbn. rewrite find_idx_app_none by exact Hg. rewrite Hl. cbn. f_equal; lia. }
  set (A := [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60] ++ firstn k u ++ [62; 32; 46]).
  assert (HT : txt_t1 u k = A ++ 10 :: [112] ++ 58 :: skipn k u ++ 10 :: tl_lv2).
  { unfold txt_t1, A, tail_lv2, tl_lv2. rewrite <- !app_assoc. reflexivity. }
  apply (names_first_decl _ _ 8 1 12 k (12 + k)); [lia| |exact Hd| |].
  - unfold txt_t1. len_simpl. lia.
  - exact (matches_split [64; 112; 114; 101; 102; 105; 120; 32; 112; 58; 32; 60]
             ([62; 32; 46; 10; 112; 58] ++ skipn k u ++ tail_lv2) u k Hk Hp).
  - assert (H8 : firstn 1 (skipn 8 (txt_t1 u k)) = [112]) by reflexivity. rewrite H8.
    apply (token_in _ _ _ (S (length A))).
    + rewrite HT. len_simpl. lia.
    + rewrite HT. apply token_at_mid; reflexivity.
Qed.

Lemma rt_t2 : forall u k, (k < length u)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn k u) = true -> plain_name (skipn k u) = true ->
  names (txt_t2 u k) u = 1.
Proof.
  intros u k Hk Hg Hp.
  assert (Hl : length (firstn k u) = k) by (rewrite length_firstn; lia).
  assert (Hd : decl (txt_t2 u k) 0 = DFound 7 1 11 k (11 + k)).
  { unfold decl, txt_t2. cbn. rewrite find_idx_app_none by exact Hg. rewrite Hl. cbn. f_equal; lia. }
  set (A := [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60] ++ firstn k u ++ [62]).
  assert (HT : txt_t2 u k = A ++ 10 :: [112] ++ 58 :: skipn k u ++ 10 :: tl_lv2).
  { unfold txt_t2, A, tail_lv2, tl_lv2. rewrite <- !app_assoc. reflexivity. }
  apply (names_first_decl _ _ 7 1 11 k (11 + k)); [lia| |exact Hd| |].
  - unfold txt_t2. len_simpl. lia.
  - exact (matches_split [80; 82; 69; 70; 73; 88; 32; 112; 58; 32; 60]
             ([62; 10; 112; 58] ++ skipn k u ++ tail_lv2) u k Hk Hp).
  - assert (H7 : firstn 1 (skipn 7 (txt_t2 u k)) = [112]) by reflexivity. rewrite H7.
    apply (token_in _ _ _ (S (length A))).
    + rewrite HT. len_simpl. lia.
    + rewrite HT. apply token_at_mid; reflexivity.
Qed.

Lemma rt_t3 : forall u k, (k < length u)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn k u) = true -> plain_name (skipn k u) = true ->
  names (txt_t3 u k) u = 1.
Proof.
  intros u k Hk Hg Hp.
  assert (Hl : length (firstn k u) = k) by (rewrite length_firstn; lia).
  assert (Hd : decl (txt_t3 u k) 0 = DFound 8 0 11 k (11 + k)).
  { unfold decl, txt_t3. cbn. rewrite find_idx_app_none by exact Hg. rewrite Hl. cbn. f_equal; lia. }
  set (A := [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60] ++ firstn k u ++ [62; 32; 46]).
  assert (HT : txt_t3 u k = A ++ 10 :: [] ++ 58 :: skipn k u ++ 10 :: tl_lv2).
  { unfold txt_t3, A, tail_lv2, tl_lv2. rewrite <- !app_assoc. reflexivity. }
  apply (names_first_decl _ _ 8 0 11 k (11 + k)); [lia| |exact Hd| |].
  - unfold txt_t3. len_simpl. lia.
  - exact (matches_split [64; 112; 114; 101; 102; 105; 120; 32; 58; 32; 60]
             ([62; 32; 46; 10; 58] ++ skipn k u ++ tail_lv2) u k Hk Hp).
  - assert (H8 : firstn 0 (skipn 8 (txt_t3 u k)) = []) by reflexivity. rewrite H8.
    apply (token_in _ _ _ (S (length A))).
    + rewrite HT. len_simpl. lia.
    + rewrite HT. apply token_at_mid; reflexivity.
Qed.
