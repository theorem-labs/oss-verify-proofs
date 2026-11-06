From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel.
Import ListNotations.
Local Open Scope Z_scope.

Lemma nth_skipn0 : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros k j; destruct k as [|k]; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma byte_at_skipn : forall t k j, byte_at (skipn k t) j = byte_at t (k + j).
Proof. intros. unfold byte_at. apply nth_skipn0. Qed.

Lemma byte_at_ge : forall t k, (length t <= k)%nat -> byte_at t k = 0.
Proof. intros t k H. unfold byte_at. apply nth_overflow. exact H. Qed.

Lemma byte_at_nz_lt : forall t k, byte_at t k <> 0 -> (k < length t)%nat.
Proof. intros t k H. destruct (Nat.lt_ge_cases k (length t)); [exact H0|]. rewrite byte_at_ge in H by exact H0. lia. Qed.

Lemma find_idx_some : forall f l o, find_idx f l = Some o ->
  (o < length l)%nat /\ f (nth o l 0) = true /\ forall j, (j < o)%nat -> f (nth j l 0) = false.
Proof.
  intros f l. induction l as [|x l IH]; intros o H; cbn in H; [discriminate|].
  destruct (f x) eqn:Ex.
  - inversion H; subst. cbn. split; [lia|]. split; [exact Ex|]. intros j Hj; lia.
  - destruct (find_idx f l) as [o'|] eqn:E; cbn in H; [|discriminate]. inversion H; subst.
    destruct (IH o' eq_refl) as (A & B & C). cbn. split; [lia|]. split; [exact B|].
    intros j Hj. destruct j; [exact Ex|]. apply C. lia.
Qed.

Lemma find_idx_none : forall f l, find_idx f l = None -> forall j, (j < length l)%nat -> f (nth j l 0) = false.
Proof.
  intros f l. induction l as [|x l IH]; intros H j Hj; cbn in *; [lia|].
  destruct (f x) eqn:Ex; [discriminate|].
  destruct (find_idx f l) eqn:E; cbn in H; [discriminate|].
  destruct j; [exact Ex|]. apply IH; [reflexivity|lia].
Qed.

Inductive sres := SCont (i d : nat) | SRet (r : Z).

Definition sstep (t u : list Z) (i d : nat) : sres :=
  match decl t i with
  | DNone => SCont i d
  | DCut => SRet 0
  | DFound name nl ns nl2 close =>
      if matches t u ns nl2 then
        if (16 <? S d)%nat then SRet 1
        else if token t (firstn nl (skipn name t)) (skipn nl2 u) then SRet 1
        else SCont close (S d)
      else SCont close d
  end.

Lemma scan_step : forall t u i d f, (i < length t)%nat ->
  scan t u i d (S f) = match sstep t u i d with SCont i' d' => scan t u (S i') d' f | SRet r => r end.
Proof.
  intros t u i d f Hi. cbn [scan]. destruct (length t <=? i)%nat eqn:E; [apply Nat.leb_le in E; lia|].
  unfold sstep. destruct (decl t i); try reflexivity.
  destruct (matches t u ns nl2); [|reflexivity].
  destruct (16 <? S d)%nat; [reflexivity|]. destruct (token _ _ _); reflexivity.
Qed.

Lemma scan_end : forall t u i d f, (length t <= i)%nat -> scan t u i d (S f) = 0.
Proof.
  intros t u i d f Hi. cbn [scan]. destruct (length t <=? i)%nat eqn:E; [reflexivity|].
  apply Nat.leb_gt in E. lia.
Qed.

Lemma decl_found : forall t i name nl ns nl2 close, decl t i = DFound name nl ns nl2 close ->
  (name + nl < ns)%nat /\ (i < ns)%nat /\ close = (ns + nl2)%nat /\ (close < length t)%nat /\ byte_at t close = 62.
Proof.
  intros t i name nl ns nl2 close H. unfold decl in H. cbv zeta in H.
  destruct (head t i) as [p0|] eqn:Hh; [|discriminate].
  assert (Hp0 : (i < p0)%nat).
  { unfold head in Hh. repeat match type of Hh with context [if ?c then _ else _] => destruct c end;
    inversion Hh; lia. }
  destruct (negb (is_space (byte_at t p0))); [discriminate|].
  destruct (negb (byte_at t _ =? 58)); [discriminate|].
  destruct (negb (byte_at t _ =? 60)); [discriminate|].
  match type of H with context [find_idx ?f ?l] => destruct (find_idx f l) as [o|] eqn:Ef end; [|discriminate].
  injection H as E1 E2 E3 E4 E5. subst. apply find_idx_some in Ef as (A & B & _).
  rewrite length_skipn in A. apply Z.eqb_eq in B. rewrite nth_skipn0 in B.
  cbn [skipn] in A, B |- *.
  split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. exact B.
Qed.

Lemma sstep_cont : forall t u i d i' d', (i < length t)%nat -> (d <= 16)%nat ->
  sstep t u i d = SCont i' d' -> (i <= i' < length t)%nat /\ (d' <= 16)%nat.
Proof.
  intros t u i d i' d' Hi Hd H. unfold sstep in H.
  destruct (decl t i) as [| |name nl ns nl2 close] eqn:Hdc.
  - inversion H; subst. lia.
  - discriminate.
  - apply decl_found in Hdc as (A & B & C & D & _).
    destruct (matches t u ns nl2).
    + destruct (16 <? S d)%nat eqn:E; [discriminate|]. apply Nat.ltb_ge in E.
      destruct (token _ _ _); [discriminate|]. inversion H; subst. lia.
    + inversion H; subst. lia.
Qed.

Lemma firstn_noz : forall (x u : list Z), Forall (fun c => c <> 0) u ->
  firstn (length u) (x ++ [0]) = u <-> firstn (length u) x = u.
Proof.
  intros x u Hu. destruct (Nat.le_gt_cases (length u) (length x)) as [Hl|Hl].
  - rewrite firstn_app. replace (length u - length x)%nat with O by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
  - rewrite firstn_app, (firstn_all2 x) by lia.
    replace (length u - length x)%nat with (S (length u - length x - 1)) by lia. cbn [firstn].
    split; intro H.
    + exfalso. assert (In 0 u) as Hin by (rewrite <- H; apply in_or_app; right; left; reflexivity).
      rewrite Forall_forall in Hu. exact (Hu 0 Hin eq_refl).
    + exfalso. apply (f_equal (@length Z)) in H. lia.
Qed.

Lemma firstn_snoc : forall (u s : list Z) b, b <> 0 ->
  firstn (length u + 1) s = u ++ [b] <-> firstn (length u) s = u /\ nth (length u) s 0 = b.
Proof.
  induction u as [|c u IH]; intros s b Hb; destruct s as [|y s]; cbn.
  - split; [discriminate|]. intros [_ H]. congruence.
  - split; [intro H; injection H as H; auto|]. intros [_ H]; subst; reflexivity.
  - split; [discriminate|]. intros [H _]; discriminate.
  - split.
    + intro H. injection H as H1 H2. apply IH in H2 as [H3 H4]; [|exact Hb]. rewrite H1, H3. auto.
    + intros [H1 H2]. injection H1 as H3 H4. f_equal; [exact H3|]. apply IH; [exact Hb|]. auto.
Qed.

Lemma firstn_cons_app : forall (s u : list Z) a b, b <> 0 ->
  firstn (length u + 2) s = a :: u ++ [b] <->
  nth 0 s 0 = a /\ firstn (length u) (skipn 1 s) = u /\ nth (S (length u)) s 0 = b.
Proof.
  intros s u a b Hb. destruct s as [|x s].
  - rewrite firstn_nil. cbn [nth]. split; [discriminate|]. intros (_ & _ & H). congruence.
  - replace (length u + 2)%nat with (S (length u + 1)) by lia. cbn [firstn nth skipn].
    rewrite <- (firstn_snoc u s b Hb). split.
    + intro H. injection H as H1 H2. auto.
    + intros (H1 & H2). subst. rewrite H2. reflexivity.
Qed.

Lemma whole_at_spec : forall t u k, whole_at t u k = true <->
  byte_at t k = 60 /\ firstn (length u) (skipn (S k) t) = u /\ byte_at t (S k + length u) = 62.
Proof.
  intros t u k. unfold whole_at. rewrite zl_eqb_eq, firstn_cons_app by lia.
  unfold byte_at. rewrite !nth_skipn0, skipn_skipn. rewrite Nat.add_0_r.
  replace (1 + k)%nat with (S k) by lia. replace (k + S (length u))%nat with (S k + length u)%nat by lia.
  reflexivity.
Qed.

Lemma whole_at_not_lt : forall t u k, byte_at t k <> 60 -> whole_at t u k = false.
Proof.
  intros t u k H. destruct (whole_at t u k) eqn:E; [|reflexivity]. apply whole_at_spec in E. tauto.
Qed.

Lemma whole_true_of : forall t u k, (k <= length t)%nat -> whole_at t u k = true -> whole t u = true.
Proof. intros t u k Hk H. unfold whole. apply existsb_exists. exists k. split; [apply in_seq; lia|exact H]. Qed.

Lemma whole_false_of : forall t u, (forall k, (k <= length t)%nat -> whole_at t u k = false) -> whole t u = false.
Proof.
  intros t u H. unfold whole. destruct (existsb _ _) eqn:E; [|reflexivity].
  apply existsb_exists in E as (k & Hk & Hw). apply in_seq in Hk. rewrite H in Hw by lia. discriminate.
Qed.

Lemma token_at_long : forall t pre loc j, token_at t pre loc j = true -> (j + length pre + 1 + length loc <= length t)%nat.
Proof.
  intros t pre loc j H. unfold token_at in H. apply andb_true_iff in H as [H _].
  repeat (apply andb_true_iff in H as [H _]). apply Nat.leb_le in H. exact H.
Qed.

Lemma token_false_of : forall t pre loc n,
  (forall j, (j < n)%nat -> token_at t pre loc j = false) -> (length t < n + length pre + 1 + length loc)%nat ->
  token t pre loc = false.
Proof.
  intros t pre loc n H Hn. unfold token. destruct (existsb _ _) eqn:E; [|reflexivity].
  apply existsb_exists in E as (j & Hj & Hw).
  destruct (Nat.lt_ge_cases j n) as [Hl|Hl]; [rewrite H in Hw by exact Hl; discriminate|].
  apply token_at_long in Hw. lia.
Qed.

Lemma token_true_of : forall t pre loc j, token_at t pre loc j = true -> token t pre loc = true.
Proof.
  intros t pre loc j H. pose proof (token_at_long _ _ _ _ H) as L. apply (token_in _ _ _ j); [lia|exact H].
Qed.
