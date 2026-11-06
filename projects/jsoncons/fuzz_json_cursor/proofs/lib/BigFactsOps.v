(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import BigModel BigFactsBase.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition wf (s : sto) : Prop :=
  words_ok (s_words s) /\ (size s <= capacity s)%nat /\ (s_alloc s = false -> s_cap s = inlined_capacity).

Definition reduced_ws (ws : words) : Prop := ws = [] \/ last ws 0 <> 0.
Definition reduced (s : sto) : Prop := reduced_ws (s_words s).

Lemma wf_empty : wf sto_empty.
Proof. unfold wf, sto_empty, size, capacity, inlined_capacity; simpl. split. constructor. split. lia. auto. Qed.
Lemma wf_of_word w : wordZ w -> wf (sto_of_word w).
Proof. unfold wf, sto_of_word, size, capacity, inlined_capacity; simpl. intros. destruct (Z.eqb_spec w 0); simpl.
  split. constructor. split. lia. auto. split. constructor. auto. constructor. split. lia. auto. Qed.
Lemma reduced_empty : reduced sto_empty. Proof. left; reflexivity. Qed.
Lemma reduced_of_word w : reduced (sto_of_word w).
Proof. unfold reduced, reduced_ws, sto_of_word; simpl. destruct (Z.eqb_spec w 0); simpl; auto. Qed.
Lemma val_of_word w : val (s_words (sto_of_word w)) = w.
Proof. unfold sto_of_word. cbn [s_words]. destruct (Z.eqb_spec w 0). subst; reflexivity. rewrite val_cons, val_nil. lia. Qed.
Lemma size_of_word w : size (sto_of_word w) = if w =? 0 then 0%nat else 1%nat.
Proof. unfold sto_of_word, size; simpl. destruct (w =? 0); reflexivity. Qed.

Lemma wf_set_neg s b : wf s -> wf (set_neg s b).
Proof. unfold wf, set_neg, size, capacity; simpl; tauto. Qed.
Lemma wf_set_words s ws : wf s -> words_ok ws -> (length ws <= capacity s)%nat -> wf (set_words s ws).
Proof. unfold wf, set_words, size, capacity; simpl. intuition. Qed.
Lemma reduced_set_neg s b : reduced s -> reduced (set_neg s b). Proof. unfold reduced; simpl; auto. Qed.

Lemma last_nth ws : ws <> [] -> last ws 0 = nth_w ws (length ws - 1).
Proof. induction ws as [|a ws IH]; intros. congruence. destruct ws as [|b ws']. reflexivity.
  simpl length. replace (S (S (length ws')) - 1)%nat with (S (length ws')) by lia.
  unfold nth_w. simpl nth. change (last (b::ws') 0 = nth_w (b::ws') (length ws')). rewrite IH by congruence. simpl length. f_equal. lia. Qed.
Lemma reduced_ws_top ws : reduced_ws ws -> ws <> [] -> nth_w ws (length ws - 1) <> 0.
Proof. intros [->|H] Hn. congruence. rewrite <- last_nth; auto. Qed.
Lemma reduced_ws_intro ws : (ws <> [] -> nth_w ws (length ws - 1) <> 0) -> reduced_ws ws.
Proof. intros. destruct ws. left; auto. right. rewrite last_nth. apply H. congruence. congruence. Qed.

Lemma reduced_val_lower ws : words_ok ws -> reduced_ws ws -> ws <> [] -> W.M ^ (Z.of_nat (length ws) - 1) <= val ws.
Proof. intros. rewrite val_removelast by auto. pose proof (reduced_ws_top ws H0 H1). rewrite <- last_nth in H2 by auto.
  assert (wordZ (last ws 0)). { rewrite last_nth by auto. apply words_ok_nth; auto. }
  assert (words_ok (removelast ws)). { rewrite (app_removelast_last 0 H1) in H. apply words_ok_app_inv in H. tauto. }
  pose proof (val_nonneg _ H4). unfold wordZ in H3. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (length ws) - 1) M_pos). nia. Qed.
Lemma reduced_val_zero ws : words_ok ws -> reduced_ws ws -> val ws = 0 -> ws = [].
Proof. intros. destruct (list_eq_dec Z.eq_dec ws []); auto. exfalso.
  pose proof (reduced_val_lower ws H H0 n). assert (0 < W.M ^ (Z.of_nat (length ws) - 1)). { apply Z.pow_pos_nonneg. apply M_pos. destruct ws. congruence. simpl length. lia. } lia. Qed.
Lemma size_le_of_val ws k : words_ok ws -> reduced_ws ws -> val ws < W.M ^ (Z.of_nat k) -> (length ws <= k)%nat.
Proof. intros. destruct (list_eq_dec Z.eq_dec ws []). subst; simpl; lia.
  pose proof (reduced_val_lower ws H H0 n).
  destruct (Nat.le_gt_cases (length ws) k); auto. exfalso.
  assert (W.M ^ Z.of_nat k <= W.M ^ (Z.of_nat (length ws) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia. Qed.
Lemma size_ge_of_val ws k : words_ok ws -> W.M ^ (Z.of_nat k) <= val ws -> (k < length ws)%nat.
Proof. intros. pose proof (val_bound ws H). destruct (Nat.lt_ge_cases k (length ws)); auto. exfalso.
  assert (W.M ^ Z.of_nat (length ws) <= W.M ^ Z.of_nat k). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia. Qed.

Lemma top_word_of_val ws k d : words_ok ws -> reduced_ws ws -> 1 <= d < W.M ->
  d * W.M ^ (Z.of_nat k) <= val ws < (d + 1) * W.M ^ (Z.of_nat k) ->
  length ws = S k /\ nth_w ws k = d.
Proof. intros Hw Hr Hd [Hlo Hhi]. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat k) M_pos) as Pk.
  assert (L1: (k < length ws)%nat). { apply size_ge_of_val; auto. nia. }
  assert (L2: (length ws <= S k)%nat). { apply size_le_of_val; auto. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof M_pos. nia. }
  assert (L: length ws = S k) by lia. split; auto.
  pose proof (val_single_nth ws k L1) as E.
  assert (Sk: skipn (S k) ws = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
  rewrite Sk, val_nil, Z.mul_0_r, Z.add_0_r in E.
  pose proof (val_bound (firstn k ws) (words_ok_firstn k ws Hw)) as B0. rewrite length_firstn, Nat.min_l in B0 by lia.
  pose proof (words_ok_nth ws k Hw) as Wk. unfold wordZ in Wk.
  set (w := nth_w ws k) in *. set (V0 := val (firstn k ws)) in *. set (P := W.M ^ Z.of_nat k) in *.
  assert (~ w <= d - 1). { intro. assert (P * w <= P * (d - 1)) by nia. nia. }
  assert (~ d + 1 <= w). { intro. assert (P * (d + 1) <= P * w) by nia. nia. }
  lia. Qed.

Definition ev_ok (B : Z) (e : event) : Prop :=
  match e with EAlloc _ b _ => 0 <= b <= B | _ => True end.
Fixpoint nallocs (l : list event) : nat :=
  match l with [] => O | EAlloc _ _ _ :: t => S (nallocs t) | _ :: t => nallocs t end.
Lemma nallocs_app a b : nallocs (a ++ b) = (nallocs a + nallocs b)%nat.
Proof. induction a as [|e a IH]; simpl; auto. destruct e; simpl; rewrite IH; auto. Qed.

Definition post {A} (m : M A) (s0 : st) (P : A -> Prop) (K : nat) (B : Z) : Prop :=
  P (fst (m s0)) /\
  exists l, st_evs (snd (m s0)) = rev l ++ st_evs s0 /\ Forall (ev_ok B) l /\ (nallocs l <= K)%nat
            /\ (st_next s0 <= st_next (snd (m s0)))%nat.
Definition mspec {A} (m : M A) (P : A -> Prop) (K : nat) (B : Z) : Prop := forall s0, post m s0 P K B.

Lemma mspec_ret {A} (a : A) (P : A -> Prop) K B : P a -> mspec (ret a) P K B.
Proof. intros H s0. unfold post, ret; simpl. split; auto. exists []. simpl. repeat split; auto; try lia. Qed.
Lemma mspec_emit_free blk n P K B : P tt -> mspec (emit (EFree blk n)) P K B.
Proof. intros H s0. unfold post, emit; simpl. split; auto. exists [EFree blk n]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_emit_throw e P K B : P tt -> mspec (emit (EThrow e)) P K B.
Proof. intros H s0. unfold post, emit; simpl. split; auto. exists [EThrow e]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_emit_catch P K B : P tt -> mspec (emit ECatch) P K B.
Proof. intros H s0. unfold post, emit; simpl. split; auto. exists [ECatch]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_alloc n w B : 0 <= n <= B -> mspec (alloc n w) (fun _ => True) 1 B.
Proof. intros H s0. unfold post, alloc, bind, fresh, emit, ret; simpl. split; auto.
  exists [EAlloc (st_next s0) n w]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_bind {A B'} (m : M A) (k : A -> M B') P Q K1 K2 B :
  mspec m P K1 B -> (forall a, P a -> mspec (k a) Q K2 B) -> mspec (bind m k) Q (K1 + K2) B.
Proof. intros Hm Hk s0. unfold post, bind. specialize (Hm s0). unfold post in Hm.
  destruct (m s0) as [a s1]. simpl in Hm. destruct Hm as [Pa (l1 & E1 & F1 & N1 & X1)].
  specialize (Hk a Pa s1). unfold post in Hk. destruct (k a s1) as [b s2]. simpl in *.
  destruct Hk as [Qb (l2 & E2 & F2 & N2 & X2)]. split; auto. exists (l1 ++ l2).
  rewrite E2, E1, rev_app_distr, <- app_assoc. repeat split; auto. apply Forall_app; auto. rewrite nallocs_app; lia. lia. Qed.
Lemma mspec_weaken {A} (m : M A) (P Q : A -> Prop) K K' B B' :
  mspec m P K B -> (forall a, P a -> Q a) -> (K <= K')%nat -> B <= B' -> mspec m Q K' B'.
Proof. intros Hm HPQ HK HB s0. specialize (Hm s0). unfold post in *. destruct (m s0) as [a s1]; simpl in *.
  destruct Hm as [Pa (l & E & F & N & X)]. split; auto. exists l; repeat split; auto.
  eapply Forall_impl. 2: exact F. intros e. destruct e; simpl; auto; lia. lia. Qed.

Lemma mspec_if {A} (b : bool) (m1 m2 : M A) P K B :
  (b = true -> mspec m1 P K B) -> (b = false -> mspec m2 P K B) -> mspec (if b then m1 else m2) P K B.
Proof. destruct b; auto. Qed.

Lemma mspec_conj {A} (m : M A) (P Q : A -> Prop) K B :
  mspec m P K B -> (forall s0, Q (fst (m s0))) -> mspec m (fun a => P a /\ Q a) K B.
Proof. intros Hm HQ s0. specialize (Hm s0). specialize (HQ s0). unfold post in *. destruct (m s0); simpl in *. tauto. Qed.

Lemma mspec_bind' {A B'} (m : M A) (k : A -> M B') P Q K1 K B :
  mspec m P K1 B -> (forall a, P a -> mspec (k a) Q (K - K1) B) -> (K1 <= K)%nat -> mspec (bind m k) Q K B.
Proof. intros. replace K with (K1 + (K - K1))%nat by lia. eapply mspec_bind; eauto. Qed.

Ltac mstep L := eapply mspec_bind'; [ apply L | intros | simpl; lia ].

Lemma round_up_gt n : (n < round_up n)%nat.
Proof. unfold round_up. pose proof (Nat.mod_upper_bound n 8). lia. Qed.
Lemma round_up_le n : (round_up n <= n + 8)%nat.
Proof. unfold round_up. lia. Qed.
Lemma round_up_mult8 n : (round_up n mod 8 = 0)%nat.
Proof. unfold round_up. rewrite (Nat.div_mod_eq n 8) at 1. pose proof (Nat.mod_upper_bound n 8).
  replace (8 * (n / 8) + n mod 8 + (8 - n mod 8))%nat with ((n / 8 + 1) * 8)%nat by lia. apply Nat.Div0.mod_mul. Qed.
Lemma round_up_eq n : round_up n = (8 * (n / 8 + 1))%nat.
Proof. unfold round_up. pose proof (Nat.div_mod_eq n 8). pose proof (Nat.mod_upper_bound n 8). lia. Qed.
Lemma round_up_mono a b : (a <= b -> round_up a <= round_up b)%nat.
Proof. intros. rewrite !round_up_eq. pose proof (Nat.Div0.div_le_mono a b 8 H). lia. Qed.

Definition BB (N : nat) : Z := 8 * Z.of_nat (round_up N).

Definition okN (N : nat) (s : sto) : Prop := wf s /\ (capacity s <= round_up N)%nat.

Lemma okN_wf N s : okN N s -> wf s. Proof. intros [H _]; auto. Qed.
Lemma okN_size N s : okN N s -> (size s <= round_up N)%nat.
Proof. intros [[_ [H _]] H']. lia. Qed.
Lemma okN_words N s : okN N s -> words_ok (s_words s). Proof. intros [[H _] _]; auto. Qed.
Lemma okN_empty N : okN N sto_empty.
Proof. split. apply wf_empty. unfold capacity, sto_empty, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma okN_of_word N w : wordZ w -> okN N (sto_of_word w).
Proof. intros. split. apply wf_of_word; auto. unfold capacity, sto_of_word, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma okN_set_neg N s b : okN N s -> okN N (set_neg s b).
Proof. intros [H1 H2]. split. apply wf_set_neg; auto. unfold capacity, set_neg in *; simpl in *; auto. Qed.
Lemma okN_set_words N s ws : okN N s -> words_ok ws -> (length ws <= capacity s)%nat -> okN N (set_words s ws).
Proof. intros [H1 H2] Hw Hl. split. apply wf_set_words; auto. unfold capacity, set_words in *; simpl in *; auto. Qed.
Lemma capacity_set_words s ws : capacity (set_words s ws) = capacity s. Proof. reflexivity. Qed.
Lemma capacity_set_neg s b : capacity (set_neg s b) = capacity s. Proof. reflexivity. Qed.
Lemma size_set_words s ws : size (set_words s ws) = length ws. Proof. reflexivity. Qed.
Lemma size_set_neg s b : size (set_neg s b) = size s. Proof. reflexivity. Qed.

Lemma reserve_mspec N s n : okN N s -> (n <= N)%nat ->
  mspec (reserve s n)
    (fun s' => okN N s' /\ s_words s' = s_words s /\ s_neg s' = s_neg s /\ (n <= capacity s')%nat /\ (capacity s <= capacity s')%nat)
    1 (BB N).
Proof.
  intros Hok Hn. unfold reserve. destruct (Nat.ltb_spec (capacity s) n).
  2:{ apply mspec_ret. repeat split; auto; try lia. all: destruct Hok as [[? [? ?]] ?]; auto. }
  eapply mspec_bind'. apply mspec_alloc. unfold BB. split. lia. apply Z.mul_le_mono_nonneg_l. lia. apply Nat2Z.inj_le. apply round_up_mono; auto.
  2: lia. intros blk _. simpl.
  eapply mspec_bind' with (P := fun _ => True) (K1 := 0%nat). destruct (s_alloc s). apply mspec_emit_free; auto. apply mspec_ret; auto. 2: lia.
  intros u _. apply mspec_ret. destruct Hok as [[Hw [Hsz Hcap]] Hc].
  unfold okN, wf, capacity, size in *; simpl in *. pose proof (round_up_gt n). pose proof (round_up_mono n N Hn).
  repeat split; auto; try lia. all: try (intros; congruence).
Qed.

Lemma resize_words_eq n (ws : words) :
  (if (n <=? length ws)%nat then firstn n ws else ws ++ zeros (n - length ws)) = firstn n ws ++ zeros (n - length ws).
Proof. destruct (Nat.leb_spec n (length ws)).
  replace (n - length ws)%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity.
  rewrite firstn_all2 by lia. reflexivity. Qed.

Lemma resize_mspec N s n : okN N s -> (n <= N)%nat ->
  mspec (resize s n)
    (fun s' => okN N s' /\ s_words s' = firstn n (s_words s) ++ zeros (n - size s) /\ size s' = n /\ s_neg s' = s_neg s
               /\ (capacity s <= capacity s')%nat)
    1 (BB N).
Proof.
  intros Hok Hn. unfold resize. eapply mspec_bind'. apply reserve_mspec; eauto. 2: lia.
  intros s1 (Hok1 & Hw1 & Hneg1 & Hc1 & Hc2). unfold size. rewrite resize_words_eq. rewrite Hw1.
  assert (Hlen: length (firstn n (s_words s) ++ zeros (n - length (s_words s))) = n).
  { rewrite length_app, length_firstn, zeros_length. lia. }
  apply mspec_ret. split. apply okN_set_words; auto. apply words_ok_app. apply words_ok_firstn. apply (okN_words N); auto. apply words_ok_zeros.
  rewrite Hlen; lia.
  cbn [s_words set_words s_neg]. repeat split; auto.
Qed.

Lemma removelast_firstn (ws : words) : removelast ws = firstn (length ws - 1) ws.
Proof. induction ws as [|a ws IH]. reflexivity. destruct ws as [|b ws']. reflexivity.
  simpl length. change (removelast (a :: b :: ws')) with (a :: removelast (b :: ws')). rewrite IH.
  simpl length. replace (S (S (length ws')) - 1)%nat with (S (S (length ws') - 1))%nat by lia. reflexivity. Qed.

Lemma reduce_loop_prefix fuel ws : exists m, (m <= length ws)%nat /\ reduce_loop fuel ws = firstn m ws.
Proof. revert ws; induction fuel as [|f IH]; intros ws; simpl.
  exists (length ws). split. lia. rewrite firstn_all; auto.
  destruct ws as [|w t]. exists 0%nat. simpl. split; auto.
  destruct (Z.eqb_spec (last (w :: t) 0) 0).
  - destruct (IH (removelast (w :: t))) as (m & Hm & E). rewrite E. rewrite removelast_firstn in *.
    rewrite length_firstn in Hm. exists m. split. simpl length in *. lia. rewrite firstn_firstn. f_equal. simpl length in *. lia.
  - exists (length (w :: t)). split. lia. rewrite firstn_all. reflexivity. Qed.

Lemma reduce_loop_val fuel ws : val (reduce_loop fuel ws) = val ws.
Proof. revert ws; induction fuel as [|f IH]; intros ws; simpl. auto.
  destruct ws as [|w t]. auto. destruct (Z.eqb_spec (last (w :: t) 0) 0).
  rewrite IH. rewrite (val_removelast (w :: t)) by congruence. rewrite e. lia. auto. Qed.

Lemma reduce_loop_reduced fuel ws : (length ws <= fuel)%nat -> reduced_ws (reduce_loop fuel ws).
Proof. revert ws; induction fuel as [|f IH]; intros ws Hl; simpl.
  destruct ws. left; auto. simpl in Hl; lia.
  destruct ws as [|w t]. left; auto. destruct (Z.eqb_spec (last (w :: t) 0) 0).
  apply IH. rewrite removelast_firstn, length_firstn. simpl length in *. lia.
  right. auto. Qed.

Lemma reduce_loop_id fuel ws : reduced_ws ws -> reduce_loop fuel ws = ws.
Proof. intros [->|H]; destruct fuel; simpl; auto. destruct ws; auto. destruct (Z.eqb_spec (last (z :: ws) 0) 0); auto. congruence. Qed.

Lemma reduce_loop_length fuel ws : (length (reduce_loop fuel ws) <= length ws)%nat.
Proof. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E, length_firstn. lia. Qed.

Lemma reduce_loop_words_ok fuel ws : words_ok ws -> words_ok (reduce_loop fuel ws).
Proof. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E. apply words_ok_firstn. Qed.

Lemma reduce_loop_nth fuel ws i : (i < length (reduce_loop fuel ws))%nat -> nth_w (reduce_loop fuel ws) i = nth_w ws i.
Proof. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E. rewrite length_firstn. intros.
  unfold nth_w. rewrite <- (firstn_skipn m ws) at 2. rewrite app_nth1. auto. rewrite length_firstn. lia. Qed.

Lemma reduce_words s : s_words (reduce s) = reduce_loop (size s) (s_words s). Proof. reflexivity. Qed.
Lemma reduce_alloc s : s_alloc (reduce s) = s_alloc s. Proof. reflexivity. Qed.
Lemma reduce_cap s : s_cap (reduce s) = s_cap s. Proof. reflexivity. Qed.
Lemma reduce_blk s : s_blk (reduce s) = s_blk s. Proof. reflexivity. Qed.
Lemma capacity_reduce s : capacity (reduce s) = capacity s. Proof. reflexivity. Qed.
Lemma reduce_neg s : s_neg (reduce s) = if (size (reduce s) =? 0)%nat then false else s_neg s.
Proof. reflexivity. Qed.
Lemma reduce_val s : val (s_words (reduce s)) = val (s_words s).
Proof. rewrite reduce_words. apply reduce_loop_val. Qed.
Lemma reduce_reduced s : reduced (reduce s).
Proof. unfold reduced. rewrite reduce_words. apply reduce_loop_reduced. unfold size; lia. Qed.
Lemma reduce_size_le s : (size (reduce s) <= size s)%nat.
Proof. unfold size at 1. rewrite reduce_words. apply reduce_loop_length. Qed.
Lemma reduce_okN N s : okN N s -> okN N (reduce s).
Proof. intros [[Hw [Hs Hc]] Hcap]. pose proof (reduce_size_le s). split. split. rewrite reduce_words. apply reduce_loop_words_ok; auto.
  rewrite capacity_reduce. split. lia. rewrite reduce_alloc, reduce_cap. auto. rewrite capacity_reduce. auto. Qed.
Lemma reduce_id s : reduced s -> s_neg s = false \/ (0 < size s)%nat -> reduce s = s.
Proof. intros Hr Hn. unfold reduce. rewrite (reduce_loop_id _ _ Hr). destruct s as [al ng ws cp bk]; simpl in *.
  f_equal. unfold size in Hn; simpl in Hn. destruct (Nat.eqb_spec (length ws) 0); auto. destruct Hn; auto. lia. Qed.

Lemma reduce_nil_iff s : words_ok (s_words s) -> (s_words (reduce s) = [] <-> val (s_words s) = 0).
Proof. intros Hw. split. intros E. rewrite <- reduce_val, E. reflexivity.
  intros V. apply reduced_val_zero. rewrite reduce_words. apply reduce_loop_words_ok; auto. apply reduce_reduced. rewrite reduce_val; auto. Qed.

Lemma copy_mspec N src : okN N src ->
  mspec (copy src) (fun s' => okN N s' /\ s_words s' = s_words src /\ s_neg s' = s_neg src /\ s_alloc s' = s_alloc src
                             /\ capacity s' = capacity src) 1 (BB N).
Proof.
  intros Hok. unfold copy. destruct (s_alloc src) eqn:A.
  - eapply mspec_bind'. apply mspec_alloc. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold capacity in Hcap. rewrite A in Hcap. unfold BB. split. lia. nia.
    2: lia. intros blk _. apply mspec_ret. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold okN, wf, capacity, size in *; simpl in *. rewrite A in *.
    repeat split; auto; try (intros; congruence).
  - apply mspec_ret. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold okN, wf, capacity, size in *; simpl in *. rewrite A in *.
    repeat split; auto; try lia. all: try (rewrite (Hc eq_refl) in Hs; auto).
Qed.

Lemma assign_mspec N dst src : okN N dst -> okN N src -> (size src <= N)%nat ->
  mspec (assign dst src) (fun s' => okN N s' /\ s_words s' = s_words src /\ size s' = size src
                                   /\ s_neg s' = (if (0 <? size src)%nat then s_neg src else s_neg dst)
                                   /\ (capacity dst <= capacity s')%nat) 1 (BB N).
Proof.
  intros Hd Hs Hn. unfold assign. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
  intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1). apply mspec_ret. destruct (Nat.ltb_spec 0 (size src)).
  - pose proof (okN_words N src Hs) as Hws. destruct Hok1 as [[Hw [Hsz Hc]] Hcap]. clear Hd Hs.
    unfold okN, wf, size, capacity in *. cbn [s_words s_neg s_alloc s_cap] in *. repeat split; auto; try lia.
  - assert (E: s_words src = []). { destruct (s_words src) eqn:E; auto. unfold size in H; rewrite E in H; simpl in H; lia. }
    assert (E1: s_words s1 = []). { apply length_zero_iff_nil. unfold size in *. lia. }
    split. auto. rewrite E1, E. unfold size. rewrite E1, E. repeat split; auto.
Qed.

Lemma destroy_mspec s (P : unit -> Prop) B : P tt -> mspec (destroy s) P 0 B.
Proof. intros. unfold destroy. destruct (s_alloc s). apply mspec_emit_free; auto. apply mspec_ret; auto. Qed.

Lemma firstn_S_nth (ws : words) i : (i < length ws)%nat -> firstn (S i) ws = firstn i ws ++ [nth_w ws i].
Proof. revert i; induction ws as [|w ws IH]; intros [|i] H; simpl in *; try lia; auto.
  unfold nth_w. simpl. f_equal. specialize (IH i). unfold nth_w in IH. rewrite <- IH by lia. reflexivity. Qed.
Lemma val_firstn_S (ws : words) i : (i < length ws)%nat ->
  val (firstn (S i) ws) = val (firstn i ws) + nth_w ws i * W.M ^ Z.of_nat i.
Proof. intros. rewrite firstn_S_nth by auto. rewrite val_app, val_cons, val_nil, length_firstn, Nat.min_l by lia. lia. Qed.
Lemma firstn_upd_le (ws : words) i j v : (j <= i)%nat -> firstn j (upd ws i v) = firstn j ws.
Proof. revert i j; induction ws as [|w ws IH]; intros [|i] [|j] H; simpl; auto; try lia. rewrite IH; auto; lia. Qed.
Lemma val_firstn_all (ws : words) : val (firstn (length ws) ws) = val ws.
Proof. rewrite firstn_all; auto. Qed.

Lemma mul_loop_inv y orig : wordZ y -> words_ok orig ->
  forall f i dig carry ws,
  words_ok ws -> wordZ carry -> length ws = length orig -> (i + f < length orig)%nat ->
  (forall k, (i <= k)%nat -> nth_w ws k = nth_w orig k) -> dig = nth_w orig i ->
  val (firstn i ws) + carry * W.M ^ Z.of_nat i = y * val (firstn i orig) ->
  let (ws', c') := mul_loop f i dig carry y ws in
  words_ok ws' /\ wordZ c' /\ length ws' = length orig /\
  (forall k, (i + f <= k)%nat -> nth_w ws' k = nth_w orig k) /\
  val (firstn (i + f) ws') + c' * W.M ^ Z.of_nat (i + f) = y * val (firstn (i + f) orig).
Proof.
  intros Hy Ho. induction f as [|f IH]; intros i dig carry ws Hw Hc Hl Hf Hk Hd Hv.
  - simpl. rewrite Nat.add_0_r. repeat split; auto; unfold wordZ in *; try lia.
  - cbn [mul_loop]. pose proof (words_ok_nth orig i Ho) as Hdig. rewrite <- Hd in Hdig.
    pose proof (DDproduct_correct dig y Hdig Hy) as HP. pose proof (DDproduct_hi_bound dig y Hdig Hy) as Hhb.
    destruct (DDproduct dig y) as [hi lo]. simpl in Hhb. destruct HP as (Whi & Wlo & EP).
    set (wi := W.add lo carry). set (ws1 := upd ws i wi).
    pose proof (add_carry lo carry Wlo Hc) as AC. fold wi in AC.
    set (c1 := W.b2z (W.ltu wi lo)) in *.
    assert (Hc1: 0 <= c1 <= 1) by (apply b2z_range).
    assert (Ecarry: W.add hi c1 = hi + c1). { apply add_small; auto. unfold wordZ; rewrite M_val; lia. unfold wordZ in *; lia. }
    specialize (IH (S i) (nth_w ws1 (S i)) (W.add hi c1) ws1).
    replace (i + S f)%nat with (S i + f)%nat by lia.
    destruct (mul_loop f (S i) (nth_w ws1 (S i)) (W.add hi c1) y ws1) as [ws' c'].
    apply IH; clear IH.
    + unfold ws1. apply upd_words_ok; auto. apply add_range.
    + rewrite Ecarry. unfold wordZ in *; lia.
    + unfold ws1. rewrite upd_length; auto.
    + lia.
    + intros k Hk2. unfold ws1. rewrite upd_nth_other by lia. apply Hk. lia.
    + unfold ws1. rewrite upd_nth_other by lia. apply Hk. lia.
    + rewrite val_firstn_S. 2: unfold ws1; rewrite upd_length; lia.
      rewrite val_firstn_S by lia. unfold ws1 at 1. rewrite firstn_upd_le by lia. unfold ws1. rewrite upd_nth_same by lia.
      rewrite Ecarry. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite <- Hd. nia.
Qed.

Lemma mul_word_mspec N s y : okN N s -> wordZ y -> (S (size s) <= N)%nat ->
  mspec (mul_word s y)
    (fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) * y /\ (size s' <= S (size s))%nat
               /\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
    1 (BB N).
Proof.
  intros Hok Hy Hn. unfold mul_word. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
  intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
  assert (Horig: s_words s1 = s_words s ++ [0]).
  { rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
  pose proof (okN_words N s1 Hok1) as Wo. pose proof (okN_words N s Hok) as Ws.
  set (orig := s_words s1) in *. set (len0 := size s) in *.
  assert (Hlen: length orig = S len0). { subst orig len0. unfold size in Hsz1. exact Hsz1. }
  assert (Hdig: nth_w (s_words s) 0 = nth_w orig 0).
  { rewrite Horig. destruct (s_words s). reflexivity. reflexivity. }
  pose proof (mul_loop_inv y orig Hy Wo len0 0 (nth_w (s_words s) 0) 0 orig Wo) as INV.
  destruct (mul_loop len0 0 (nth_w (s_words s) 0) 0 y orig) as [ws' c'] eqn:EL.
  assert (INV' : words_ok ws' /\ wordZ c' /\ length ws' = length orig /\
          (forall k, (len0 <= k)%nat -> nth_w ws' k = nth_w orig k) /\
          val (firstn len0 ws') + c' * W.M ^ Z.of_nat len0 = y * val (firstn len0 orig)).
  { apply INV; auto. unfold wordZ; rewrite M_val; lia. lia. simpl. lia. }
  clear INV. destruct INV' as (W' & Wc' & L' & K' & V').
  apply mspec_ret.
  assert (Vfin: val (upd ws' len0 c') = val (s_words s) * y).
  { rewrite val_upd by lia. rewrite (K' len0) by lia.
    assert (Ho0: nth_w orig len0 = 0). { rewrite Horig. rewrite nth_w_app_r. unfold len0, size. rewrite Nat.sub_diag. reflexivity. unfold len0, size; lia. }
    rewrite Ho0. pose proof (val_single_nth ws' len0) as VS. rewrite VS by lia. rewrite (K' len0) by lia. rewrite Ho0.
    assert (SK: skipn (S len0) ws' = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
    rewrite SK, val_nil.
    assert (Fo: firstn len0 orig = s_words s). { rewrite Horig. rewrite firstn_app. unfold len0, size. rewrite Nat.sub_diag, firstn_O, firstn_all, app_nil_r. reflexivity. }
    rewrite Fo in V'. nia. }
  assert (Hok2: okN N (set_words s1 (upd ws' len0 c'))).
  { apply okN_set_words; auto. apply upd_words_ok; auto. rewrite upd_length, L', Hlen. destruct Hok1 as [[_ [Hs _]] _]. unfold size in Hs. rewrite <- Hsz1. exact Hs. }
  split. apply reduce_okN; auto.
  split. apply reduce_reduced.
  split. rewrite reduce_val. cbn [s_words set_words]. exact Vfin.
  split. pose proof (reduce_size_le (set_words s1 (upd ws' len0 c'))) as RS. rewrite size_set_words, upd_length, L', Hlen in RS. exact RS.
  split. rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
  rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.

Lemma skipn_nth_ext (a b : words) i : length a = length b -> (forall k, (i <= k)%nat -> nth_w a k = nth_w b k) -> skipn i a = skipn i b.
Proof. intros Hl Hk. apply (nth_ext _ _ 0 0). rewrite !length_skipn; lia.
  intros n Hn. rewrite !nth_skipn. apply Hk. lia. Qed.

Lemma add_carry_loop_inv y orig n : words_ok orig -> length orig = n -> nth_w orig (n - 1) = 0 -> (1 <= n)%nat ->
  forall f i carry ws, (i + f = n)%nat -> (1 <= i)%nat -> words_ok ws -> length ws = n -> 0 <= carry <= 1 ->
  (carry <> 0 -> (i < n)%nat) ->
  (forall k, (i <= k)%nat -> nth_w ws k = nth_w orig k) ->
  val (firstn i ws) + carry * W.M ^ Z.of_nat i = val (firstn i orig) + y ->
  let ws' := add_carry_loop f i n carry ws in
  words_ok ws' /\ length ws' = n /\ val ws' = val orig + y.
Proof.
  intros Ho Hlo Htop Hn1. induction f as [|f IH]; intros i carry ws Hif Hi Hw Hl Hc Hcn Hk Hv; cbn [add_carry_loop].
  - assert (carry = 0). { destruct (Z.eq_dec carry 0); auto. specialize (Hcn n0). lia. } subst carry.
    assert (i = n) by lia. subst i. repeat split; auto.
    rewrite !firstn_all2 in Hv by lia. lia.
  - destruct (Nat.ltb_spec i n); cbn [andb].
    2:{ exfalso. lia. }
    destruct (Z.eqb_spec carry 0); cbn [negb].
    + subst carry. repeat split; auto.
      rewrite (val_firstn_skipn i ws), (val_firstn_skipn i orig). rewrite !length_firstn, Hl, Hlo.
      rewrite (skipn_nth_ext ws orig i) by (auto; lia). lia.
    + assert (carry = 1) by lia. subst carry.
      pose proof (words_ok_nth ws i Hw) as Wi.
      assert (W1: wordZ 1) by (unfold wordZ; rewrite M_val; lia).
      pose proof (add_carry' (nth_w ws i) 1 Wi W1) as AC.
      set (d := W.add (nth_w ws i) 1) in *. set (c' := W.b2z (W.ltu d 1)) in *.
      pose proof (b2z_range (W.ltu d 1)) as Rc'. fold c' in Rc'.
      apply IH; clear IH.
      * lia. * lia.
      * apply upd_words_ok; auto. apply add_range.
      * rewrite upd_length; auto.
      * lia.
      * intros Hc'. destruct (Nat.eq_dec (S i) n); try lia. exfalso.
        assert (Hz: nth_w ws i = 0). { rewrite Hk by lia. replace i with (n - 1)%nat by lia. exact Htop. }
        rewrite Hz in AC. unfold c' in *. unfold W.b2z, W.ltu in *. destruct (Z.ltb_spec d 1); try lia.
        pose proof (add_range (nth_w ws i) 1). fold d in H1. unfold wordZ in H1. rewrite M_val in *. lia.
      * intros k Hk2. rewrite upd_nth_other by lia. apply Hk; lia.
      * rewrite val_firstn_S by (rewrite upd_length; lia). rewrite firstn_upd_le by lia. rewrite upd_nth_same by lia.
        rewrite val_firstn_S by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        rewrite <- (Hk i) by lia. nia.
Qed.

Lemma add_word_mspec N s y : okN N s -> wordZ y -> (S (size s) <= N)%nat ->
  mspec (add_word s y)
    (fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) + y /\ (size s' <= S (size s))%nat
               /\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
    1 (BB N).
Proof.
  intros Hok Hy Hn. unfold add_word. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
  intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
  assert (Horig: s_words s1 = s_words s ++ [0]).
  { rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
  pose proof (okN_words N s1 Hok1) as Wo. pose proof (okN_words N s Hok) as Ws.
  set (orig := s_words s1) in *. set (n := size s1) in *.
  assert (Hlen: length orig = n) by reflexivity.
  assert (Htop: nth_w orig (n - 1) = 0).
  { unfold n, size. fold orig. rewrite Horig, length_app. simpl length. rewrite nth_w_app_r by lia.
    replace (length (s_words s) + 1 - 1 - length (s_words s))%nat with 0%nat by lia. reflexivity. }
  pose proof (words_ok_nth orig 0 Wo) as W0.
  assert (E0: W.add (nth_w orig 0) 0 = nth_w orig 0). { rewrite add_small. lia. auto. unfold wordZ; rewrite M_val; lia. unfold wordZ in *; lia. }
  rewrite E0. replace (W.ltu (nth_w orig 0) 0) with false.
  2:{ unfold W.ltu. destruct (Z.ltb_spec (nth_w orig 0) 0); auto. unfold wordZ in W0; lia. }
  cbn [W.b2z].
  pose proof (add_carry (nth_w orig 0) y W0 Hy) as AC.
  set (w0 := W.add (nth_w orig 0) y) in *.
  set (c := if W.ltu w0 (nth_w orig 0) then 1 else 0).
  assert (Ec: c = W.b2z (W.ltu w0 (nth_w orig 0))) by reflexivity.
  pose proof (b2z_range (W.ltu w0 (nth_w orig 0))) as Rc. rewrite <- Ec in Rc, AC.
  pose proof (add_carry_loop_inv y orig n Wo Hlen Htop ltac:(lia) (n - 1) 1 c (upd orig 0 w0)) as INV.
  assert (INV': let ws' := add_carry_loop (n - 1) 1 n c (upd orig 0 w0) in words_ok ws' /\ length ws' = n /\ val ws' = val orig + y).
  { apply INV; clear INV; try lia.
    - apply upd_words_ok; auto. apply add_range.
    - rewrite upd_length; auto.
    - intros Hc0. destruct (Nat.eq_dec n 1); try lia. exfalso.
      assert (Hz: nth_w orig 0 = 0). { replace 0%nat with (n - 1)%nat by lia. exact Htop. }
      pose proof (add_range (nth_w orig 0) y) as AR. fold w0 in AR. unfold wordZ in AR.
      rewrite Hz in AC. unfold c in Hc0, AC. unfold W.ltu in *. rewrite Hz in *. destruct (Z.ltb_spec w0 0); try lia.
    - intros k Hk. rewrite upd_nth_other by lia. auto.
    - rewrite val_firstn_S by (rewrite upd_length; lia). rewrite val_firstn_S by lia. cbn [firstn]. rewrite val_nil, upd_nth_same by lia.
      simpl Z.of_nat. rewrite Z.pow_0_r, Z.pow_1_r. lia. }
  clear INV. cbv zeta in INV'. destruct INV' as (W' & L' & V').
  set (ws2 := add_carry_loop (n - 1) 1 n c (upd orig 0 w0)) in *.
  assert (Hok2: okN N (set_words s1 ws2)).
  { apply okN_set_words; auto. rewrite L'. destruct Hok1 as [[_ [Hs _]] _]. exact Hs. }
  apply mspec_ret.
  split. apply reduce_okN; auto.
  split. apply reduce_reduced.
  split. rewrite reduce_val. cbn [s_words set_words]. rewrite V'. fold orig. rewrite Horig, val_app, val_cons, val_nil. lia.
  split. pose proof (reduce_size_le (set_words s1 ws2)) as RS. rewrite size_set_words, L' in RS. lia.
  split. rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
  rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.

Lemma land_high_low k a b : 0 <= k -> 0 <= a -> 0 <= b < 2^k -> Z.land (a * 2^k) b = 0.
Proof.
  intros Hk Ha Hb. apply Z.bits_inj_0. intros n.
  destruct (Z_lt_le_dec n 0). rewrite Z.testbit_neg_r; auto.
  rewrite Z.land_spec. destruct (Z_lt_le_dec n k).
  - rewrite Z.mul_pow2_bits_low; auto.
  - destruct (Z.eq_dec b 0). subst. rewrite Z.bits_0. apply andb_false_r.
    rewrite (Z.bits_above_log2 b). apply andb_false_r. lia. apply Z.lt_le_trans with k. apply Z.log2_lt_pow2; lia. lia.
Qed.
Lemma lor_high_low k a b : 0 <= k -> 0 <= a -> 0 <= b < 2^k -> Z.lor (a * 2^k) b = a * 2^k + b.
Proof. intros. rewrite <- Z.lxor_lor by (apply land_high_low; auto). symmetry. apply Z.add_nocarry_lxor. apply land_high_low; auto. Qed.

Lemma testbit_high y n : 0 <= n -> 0 <= y < 2 ^ (n + 1) -> (Z.testbit y n = true <-> 2 ^ n <= y).
Proof.
  intros Hn Hy. rewrite Z.testbit_true by auto.
  assert (Hq: 0 <= y / 2 ^ n < 2). { split. apply Z.div_pos. lia. apply Z.pow_pos_nonneg; lia.
    apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia. rewrite Z.pow_add_r in Hy by lia. change (2^1) with 2 in Hy. lia. }
  pose proof (Z.pow_pos_nonneg 2 n).
  split; intros H1.
  - assert (y / 2 ^ n = 1). { rewrite Z.mod_small in H1 by lia. auto. }
    pose proof (Z.mul_div_le y (2^n)). lia.
  - rewrite Z.mod_small by lia. pose proof (Z.div_le_lower_bound y (2^n) 1). lia.
Qed.

Lemma land_l_bit y : wordZ y -> (W.land y W.l_bit =? 0) = (y <? 2^63).
Proof.
  intros Hy. unfold W.land. rewrite l_bit_val. change 9223372036854775808 with (2^63).
  unfold wordZ in Hy. rewrite M_val in Hy. change 18446744073709551616 with (2^(63+1)) in Hy.
  pose proof (testbit_high y 63 ltac:(lia) Hy) as TB.
  assert (E: Z.land y (2^63) = if Z.testbit y 63 then 2^63 else 0).
  { apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 m). subst. destruct (Z.testbit y 63). rewrite Z.pow2_bits_true by lia. reflexivity. rewrite Z.bits_0. reflexivity.
    rewrite andb_false_r. destruct (Z.testbit y 63). rewrite Z.pow2_bits_false by lia. reflexivity. rewrite Z.bits_0. reflexivity. }
  rewrite E. destruct (Z.testbit y 63).
  - destruct TB as [TB1 _]. specialize (TB1 eq_refl). pose proof (Z.pow_pos_nonneg 2 63).
    destruct (Z.ltb_spec y (2^63)); destruct (Z.eqb_spec (2^63) 0); auto; lia.
  - rewrite Z.eqb_refl. destruct (Z.ltb_spec y (2^63)); auto. exfalso. destruct TB as [_ TB2]. specialize (TB2 ltac:(lia)). congruence.
Qed.

Lemma norm_count_spec : forall f y x, wordZ y -> y <> 0 -> 2^63 <= y * 2 ^ (Z.of_nat f) -> 0 <= x ->
  let x' := norm_count f y x in x <= x' <= x + Z.of_nat f /\ 2^63 <= y * 2 ^ (x' - x) < 2^64.
Proof.
  induction f as [|f IH]; intros y x Hy Hnz Hf Hx; cbn [norm_count].
  - simpl in Hf. replace (x - x) with 0 by lia. rewrite Z.pow_0_r. unfold wordZ in Hy; rewrite M_val in Hy. change 18446744073709551616 with (2^64) in Hy. lia.
  - rewrite land_l_bit by auto. destruct (Z.ltb_spec y (2^63)).
    + assert (Hs: W.shl y 1 = y * 2). { unfold W.shl. change (2^1) with 2. apply wrap_id. unfold wordZ; rewrite M_val. change 18446744073709551616 with (2^64). lia. }
      rewrite Hs. specialize (IH (y * 2) (x + 1)).
      assert (wordZ (y * 2)). { unfold wordZ; rewrite M_val; change 18446744073709551616 with (2^64); unfold wordZ in Hy; lia. }
      assert (2 ^ 63 <= y * 2 * 2 ^ Z.of_nat f). { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. lia. }
      specialize (IH H0 ltac:(lia) H1 ltac:(lia)). cbv zeta in IH.
      set (x' := norm_count f (y * 2) (x + 1)) in *.
      replace (x' - x) with (1 + (x' - (x + 1))) by lia. rewrite Z.pow_add_r by lia. change (2^1) with 2. rewrite Nat2Z.inj_succ. lia.
    + replace (x - x) with 0 by lia. rewrite Z.pow_0_r. unfold wordZ in Hy; rewrite M_val in Hy. change 18446744073709551616 with (2^64) in Hy. lia.
Qed.

Corollary norm_count_64 y : wordZ y -> y <> 0 ->
  let x := norm_count NORM_FUEL y 0 in 0 <= x <= 63 /\ 2^63 <= y * 2 ^ x < 2^64.
Proof.
  intros Hy Hnz. unfold NORM_FUEL. pose proof (norm_count_spec 64 y 0 Hy Hnz) as H.
  assert (H0: 2 ^ 63 <= y * 2 ^ Z.of_nat 64). { simpl Z.of_nat. unfold wordZ in Hy. assert (1 <= y) by lia.
    assert (2^63 <= 2^64) by (apply Z.pow_le_mono_r; lia). nia. }
  specialize (H H0 ltac:(lia)). cbv zeta in H. rewrite Z.sub_0_r in H. simpl Z.of_nat in H.
  cbv zeta. set (x := norm_count 64 y 0) in *. destruct H as [H1 H2].
  assert (x <> 64). { intro e. rewrite e in H2. unfold wordZ in Hy. assert (1 <= y) by lia. pose proof (Z.pow_pos_nonneg 2 64). nia. }
  split. lia. exact H2.
Qed.

Section ShlFacts.
  Variable k : Z.
  Hypothesis Hk : 0 < k < 64.
  Let k1 := 64 - k.
  Let mask := W.sub (W.shl 1 k) 1.

  Lemma pow_k_pos : 0 < 2 ^ k. Proof. apply Z.pow_pos_nonneg; lia. Qed.
  Lemma pow_k1_pos : 0 < 2 ^ k1. Proof. apply Z.pow_pos_nonneg; lia. Qed.
  Lemma M_split : W.M = 2 ^ k1 * 2 ^ k.
  Proof. rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
  Lemma pow_k_lt_M : 2 ^ k < W.M.
  Proof. rewrite M_val. change 18446744073709551616 with (2^64). apply Z.pow_lt_mono_r; lia. Qed.

  Lemma mask_eq : mask = 2 ^ k - 1.
  Proof. unfold mask. unfold W.shl. rewrite Z.mul_1_l. rewrite wrap_id. 2:{ unfold wordZ. pose proof pow_k_pos. pose proof pow_k_lt_M. lia. }
    apply sub_small. unfold wordZ; pose proof pow_k_pos; pose proof pow_k_lt_M; lia. unfold wordZ; rewrite M_val; lia. pose proof pow_k_pos; lia. Qed.

  Lemma shl_decomp a : wordZ a ->
    W.shl a k = (a mod 2 ^ k1) * 2 ^ k /\ a * 2 ^ k = W.shl a k + W.M * (a / 2 ^ k1) /\ 0 <= a / 2 ^ k1 < 2 ^ k.
  Proof.
    intros Ha. unfold W.shl, W.wrap. rewrite M_split. pose proof pow_k_pos. pose proof pow_k1_pos.
    rewrite Z.mul_mod_distr_r by lia.
    split. reflexivity. split. rewrite (Z_div_mod_eq_full a (2 ^ k1)) at 1. nia.
    split. apply Z.div_pos; unfold wordZ in Ha; lia. apply Z.div_lt_upper_bound. lia. rewrite <- M_split. unfold wordZ in Ha; lia.
  Qed.

  Lemma hi_part b : wordZ b -> W.land (W.shr b k1) mask = b / 2 ^ k1.
  Proof.
    intros Hb. rewrite mask_eq. unfold W.land, W.shr. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
    rewrite Z.land_ones by lia. apply Z.mod_small. destruct (shl_decomp b Hb) as (_ & _ & H). exact H.
  Qed.

  Definition shlG (orig : words) (j : nat) : Z :=
    let wi := W.shl (nth_w orig j) k in
    if (0 <? j)%nat then W.lor wi (W.land (W.shr (nth_w orig (j - 1)) k1) mask) else wi.

  Lemma shlG_val orig j : words_ok orig ->
    shlG orig j = W.shl (nth_w orig j) k + (if (0 <? j)%nat then nth_w orig (j - 1) / 2 ^ k1 else 0)
    /\ wordZ (shlG orig j).
  Proof.
    intros Ho. unfold shlG. pose proof (words_ok_nth orig j Ho) as Wj. pose proof (words_ok_nth orig (j-1) Ho) as Wj1.
    destruct (shl_decomp _ Wj) as (E1 & E2 & R1). destruct (shl_decomp _ Wj1) as (_ & _ & R2).
    destruct (Nat.ltb_spec 0 j).
    - rewrite hi_part by auto. unfold W.lor. rewrite E1. rewrite lor_high_low; try lia. 2:{ apply Z.mod_pos_bound. apply pow_k1_pos. }
      split. reflexivity. unfold wordZ. rewrite M_split. pose proof (Z.mod_pos_bound (nth_w orig j) (2^k1) pow_k1_pos). nia.
    - split. lia. apply shl_range.
  Qed.

  Lemma shl_loop_pointwise orig : words_ok orig -> forall f ws,
    length ws = length orig -> (f <= length orig)%nat -> (forall j, (j < f)%nat -> nth_w ws j = nth_w orig j) ->
    let r := shl_loop f k k1 mask ws in
    length r = length orig /\ (forall j, (f <= j)%nat -> nth_w r j = nth_w ws j) /\ (forall j, (j < f)%nat -> nth_w r j = shlG orig j).
  Proof.
    intros Ho. induction f as [|i IH]; intros ws Hl Hf Hagree; cbn [shl_loop].
    - repeat split; auto. intros; lia.
    - set (wi := if (0 <? i)%nat then W.lor (W.shl (nth_w ws i) k) (W.land (W.shr (nth_w ws (i - 1)) k1) mask) else W.shl (nth_w ws i) k).
      assert (Ewi: wi = shlG orig i). { unfold wi, shlG. rewrite !Hagree by lia. reflexivity. }
      specialize (IH (upd ws i wi)). cbv zeta in IH.
      destruct IH as (L & A & B). rewrite upd_length; auto. lia. intros j Hj. rewrite upd_nth_other by lia. apply Hagree; lia.
      repeat split. exact L.
      + intros j Hj. rewrite A by lia. rewrite upd_nth_other by lia. reflexivity.
      + intros j Hj. destruct (Nat.eq_dec j i). subst j. rewrite A by lia. rewrite upd_nth_same by lia. exact Ewi. apply B. lia.
  Qed.

  Lemma shl_val_prefix orig r : words_ok orig -> length r = length orig ->
    (forall j, (j < length orig)%nat -> nth_w r j = shlG orig j) ->
    forall m, (1 <= m <= length orig)%nat ->
    val (firstn m r) = 2 ^ k * val (firstn m orig) - W.M ^ Z.of_nat m * (nth_w orig (m - 1) / 2 ^ k1).
  Proof.
    intros Ho Hl Hr. induction m as [|m IH]; intros Hm. lia.
    destruct (Nat.eq_dec m 0).
    - subst m. rewrite !val_firstn_S by lia. cbn [firstn]. rewrite !val_nil. simpl Z.of_nat. rewrite Z.pow_0_r, Z.pow_1_r. simpl Nat.sub.
      rewrite Hr by lia. destruct (shlG_val orig 0 Ho) as [E _]. rewrite E. cbn [Nat.ltb Nat.leb].
      destruct (shl_decomp (nth_w orig 0) (words_ok_nth orig 0 Ho)) as (_ & E2 & _). lia.
    - rewrite !val_firstn_S by lia. rewrite IH by lia. rewrite Hr by lia.
      destruct (shlG_val orig m Ho) as [E _]. rewrite E. destruct (Nat.ltb_spec 0 m). 2: lia.
      destruct (shl_decomp (nth_w orig m) (words_ok_nth orig m Ho)) as (_ & E2 & _).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. replace (S m - 1)%nat with m by lia.
      nia.
  Qed.
End ShlFacts.

Ltac splits := repeat match goal with |- _ /\ _ => split end.

Lemma shl_bits_mspec N s k : okN N s -> 0 <= k < 64 -> (S (size s) <= N)%nat ->
  mspec (shl_bits s k)
    (fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) * 2 ^ k /\ (size s' <= S (size s))%nat
               /\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
    2 (BB N).
Proof.
  intros Hok Hk Hn. unfold shl_bits.
  replace (Z.to_nat (k / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity). cbn [Nat.eqb negb].
  eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = (s, k, size s)). reflexivity. 2: lia.
  intros sq ->. destruct (Z.eqb_spec k 0).
  - subst k. cbn [negb]. eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = s); reflexivity. 2: lia.
    intros s1 ->. apply mspec_ret. rewrite Z.pow_0_r, Z.mul_1_r. pose proof (reduce_size_le s).
    splits. apply reduce_okN; auto. apply reduce_reduced. apply reduce_val. lia. apply reduce_neg. rewrite capacity_reduce; lia.
  - cbn [negb]. eapply mspec_bind' with (K1 := 1%nat). 3: lia. 2:{ intros s2 Hs2. apply mspec_ret. exact Hs2. }
    eapply mspec_bind' with (K1 := 1%nat). apply resize_mspec; eauto. 2: lia.
    intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
    assert (Horig: s_words s1 = s_words s ++ [0]).
    { rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
    pose proof (okN_words N s1 Hok1) as Wo.
    assert (Lo: length (s_words s1) = size s1) by reflexivity.
    rewrite Horig in Wo, Lo |- *. set (orig := s_words s ++ [0]) in *.
    assert (Ln: length orig = S (length (s_words s))). { subst orig. rewrite length_app. simpl. lia. }
    assert (Hk' : 0 < k < 64) by lia.
    pose proof (shl_loop_pointwise k orig Wo (size s1) orig eq_refl ltac:(lia) ltac:(auto)) as PW. cbv zeta in PW.
    destruct PW as (L & A & B).
    set (r := shl_loop (size s1) k (64 - k) (W.sub (W.shl 1 k) 1) orig) in *.
    assert (B' : forall j0, (j0 < length orig)%nat -> nth_w r j0 = shlG k orig j0). { intros j0 Hj0. apply B. lia. }
    assert (Wr: words_ok r).
    { unfold words_ok. apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx. destruct Hx as (j & Hj & <-).
      fold (nth_w r j). rewrite B' by lia. apply (shlG_val k Hk' orig j Wo). }
    assert (Vr: val r = val (s_words s) * 2 ^ k).
    { pose proof (shl_val_prefix k Hk' orig r Wo L B' (length orig) ltac:(lia)) as VP.
      rewrite (firstn_all2 r) in VP by lia. rewrite (firstn_all2 orig) in VP by lia. rewrite VP.
      replace (nth_w orig (length orig - 1)) with 0.
      2:{ rewrite Ln. subst orig. rewrite nth_w_app_r by (simpl; lia). replace (S (length (s_words s)) - 1 - length (s_words s))%nat with 0%nat by lia. reflexivity. }
      rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). subst orig; rewrite val_app, val_cons, val_nil. lia. }
    apply mspec_ret.
    assert (Hok2: okN N (set_words s1 r)). { apply okN_set_words; auto. rewrite L, Lo. destruct Hok1 as [[_ [Hs _]] _]. exact Hs. }
    pose proof (reduce_size_le (set_words s1 r)) as RS. rewrite size_set_words, L in RS.
    splits. apply reduce_okN; auto. apply reduce_reduced. rewrite reduce_val. exact Vr.
    lia.
    rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
    rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.

Lemma shr_loop_length f i n k k1 mask ws : length (shr_loop f i n k k1 mask ws) = length ws.
Proof. revert i ws; induction f; intros; cbn [shr_loop]; auto. rewrite IHf, upd_length; auto. Qed.
Lemma shr_loop_words_ok f i n k k1 mask ws : 0 <= k -> words_ok ws -> words_ok (shr_loop f i n k k1 mask ws).
Proof. revert i ws; induction f; intros; cbn [shr_loop]; auto. apply IHf; auto. apply upd_words_ok; auto.
  destruct (Nat.ltb i n). apply lor_range. apply shr_range; auto. apply words_ok_nth; auto. apply shl_range. apply shr_range; auto. apply words_ok_nth; auto. Qed.

Lemma shr_bits_mspec N s k : okN N s -> 0 < k < 64 ->
  mspec (shr_bits s k)
    (fun s' => okN N s' /\ reduced s' /\ (size s' <= size s)%nat /\ (capacity s <= capacity s')%nat) 1 (BB N).
Proof.
  intros Hok Hk. unfold shr_bits.
  replace (Z.to_nat (k / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity). cbn [Nat.ltb Nat.leb andb].
  destruct (size s) as [|n0] eqn:Hsz; cbn [Nat.leb].
  - eapply mspec_weaken. apply resize_mspec; eauto. lia. 2: lia. 2: lia.
    intros s1 (Hok1 & Hw1 & Hsz1 & _ & Hc1). assert (s_words s1 = []) by (apply length_zero_iff_nil; auto).
    splits; auto. unfold reduced; rewrite H; left; auto. lia.
  - eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = (s, k)); reflexivity. 2: lia.
    intros sk ->. apply mspec_ret.
    set (r := shr_loop _ _ _ _ _ _ _).
    assert (Lr: length r = size s). { subst r. rewrite shr_loop_length. reflexivity. }
    assert (Hok2: okN N (set_words s r)). { apply okN_set_words; auto. apply shr_loop_words_ok. lia. apply (okN_words N); auto.
      rewrite Lr. destruct Hok as [[_ [Hs _]] _]; auto. }
    pose proof (reduce_size_le (set_words s r)) as RS. rewrite size_set_words, Lr in RS.
    splits. apply reduce_okN; auto. apply reduce_reduced. lia. rewrite capacity_reduce, capacity_set_words. lia.
Qed.

Definition cmp3 (a b : Z) : Z := match a ?= b with Lt => -1 | Eq => 0 | Gt => 1 end.

Lemma compare_loop_spec xs ys : words_ok xs -> words_ok ys -> forall n, (n <= length xs)%nat -> (n <= length ys)%nat ->
  compare_loop n xs ys = cmp3 (val (firstn n xs)) (val (firstn n ys)).
Proof.
  intros Wx Wy. induction n as [|i IH]; intros Hx Hy; cbn [compare_loop].
  - cbn. reflexivity.
  - rewrite !val_firstn_S by lia.
    pose proof (val_bound (firstn i xs) (words_ok_firstn i xs Wx)) as Bx. pose proof (val_bound (firstn i ys) (words_ok_firstn i ys Wy)) as By.
    rewrite !length_firstn, !Nat.min_l in Bx, By by lia.
    pose proof (words_ok_nth xs i Wx) as Wxi. pose proof (words_ok_nth ys i Wy) as Wyi. unfold wordZ in *.
    set (P := W.M ^ Z.of_nat i) in *. set (a := nth_w xs i) in *. set (b := nth_w ys i) in *.
    destruct (Z.ltb_spec b a).
    + unfold cmp3. assert (a * P >= (b + 1) * P) by nia. rewrite (proj2 (Z.compare_gt_iff _ _)). reflexivity. nia.
    + destruct (Z.ltb_spec a b).
      * unfold cmp3. assert ((a + 1) * P <= b * P) by nia. rewrite (proj2 (Z.compare_lt_iff _ _)). reflexivity. nia.
      * assert (a = b) by lia. rewrite IH by lia. rewrite H1. unfold cmp3.
        destruct (Z.compare_spec (val (firstn i xs)) (val (firstn i ys)));
        [ rewrite (proj2 (Z.compare_eq_iff _ _)) by lia | rewrite (proj2 (Z.compare_lt_iff _ _)) by lia | rewrite (proj2 (Z.compare_gt_iff _ _)) by lia ]; reflexivity.
Qed.

Lemma cmp3_lt a b : a < b -> cmp3 a b = -1.
Proof. intros. unfold cmp3. rewrite (proj2 (Z.compare_lt_iff _ _)); auto. Qed.
Lemma cmp3_gt a b : b < a -> cmp3 a b = 1.
Proof. intros. unfold cmp3. rewrite (proj2 (Z.compare_gt_iff _ _)); auto; lia. Qed.
Lemma cmp3_eq a b : a = b -> cmp3 a b = 0.
Proof. intros. unfold cmp3. rewrite (proj2 (Z.compare_eq_iff _ _)); auto. Qed.

Lemma compare_nonneg x y : words_ok (s_words x) -> words_ok (s_words y) -> reduced x -> reduced y ->
  s_neg x = false -> s_neg y = false ->
  compare x y = cmp3 (val (s_words x)) (val (s_words y)).
Proof.
  intros Wx Wy Rx Ry Nx Ny. unfold compare. rewrite Nx, Ny. cbn [Bool.eqb negb].
  assert (Sx: size x = length (s_words x)) by reflexivity. assert (Sy: size y = length (s_words y)) by reflexivity.
  pose proof (val_bound _ Wx) as Bx. pose proof (val_bound _ Wy) as By.
  assert (Zx: size x = 0%nat -> val (s_words x) = 0). { intros E. rewrite Sx in E. apply length_zero_iff_nil in E. rewrite E. reflexivity. }
  assert (Zy: size y = 0%nat -> val (s_words y) = 0). { intros E. rewrite Sy in E. apply length_zero_iff_nil in E. rewrite E. reflexivity. }
  assert (Lx: size x <> 0%nat -> W.M ^ (Z.of_nat (size x) - 1) <= val (s_words x)).
  { intros E. rewrite Sx. apply reduced_val_lower; auto. intro E'. rewrite Sx, E' in E. simpl in E. lia. }
  assert (Ly: size y <> 0%nat -> W.M ^ (Z.of_nat (size y) - 1) <= val (s_words y)).
  { intros E. rewrite Sy. apply reduced_val_lower; auto. intro E'. rewrite Sy, E' in E. simpl in E. lia. }
  rewrite <- Sx in Bx. rewrite <- Sy in By.
  destruct (Nat.eqb_spec (size x) 0) as [Ex|Ex]; destruct (Nat.eqb_spec (size y) 0) as [Ey|Ey]; cbn [andb].
  - rewrite Zx, Zy by auto. reflexivity.
  - destruct (Nat.ltb_spec (size x) (size y)); try lia. rewrite Zx by auto. symmetry. apply cmp3_lt.
    specialize (Ly Ey). pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (size y) - 1) M_pos). lia.
  - destruct (Nat.ltb_spec (size x) (size y)); try lia. destruct (Nat.ltb_spec (size y) (size x)); try lia.
    rewrite Zy by auto. symmetry. apply cmp3_gt.
    specialize (Lx Ex). pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (size x) - 1) M_pos). lia.
  - destruct (Nat.ltb_spec (size x) (size y)).
    + symmetry. apply cmp3_lt. specialize (Ly Ey).
      assert (W.M ^ Z.of_nat (size x) <= W.M ^ (Z.of_nat (size y) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia.
    + destruct (Nat.ltb_spec (size y) (size x)).
      * symmetry. apply cmp3_gt. specialize (Lx Ex).
        assert (W.M ^ Z.of_nat (size y) <= W.M ^ (Z.of_nat (size x) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia.
      * assert (E: size x = size y) by lia. rewrite compare_loop_spec by (auto; lia).
        rewrite Sx, firstn_all. rewrite Sx, E, Sy, firstn_all in *. reflexivity.
Qed.

Lemma cmp3_lt_iff a b : cmp3 a b <? 0 = (a <? b).
Proof. unfold cmp3. destruct (Z.compare_spec a b); destruct (Z.ltb_spec a b); simpl; auto; lia. Qed.
Lemma cmp3_nonneg_iff a b : (cmp3 a b <? 0) = false <-> b <= a.
Proof. rewrite cmp3_lt_iff. destruct (Z.ltb_spec a b); split; intros; auto; try lia; try congruence. Qed.

Lemma top_word_range ws k lo hi : words_ok ws -> reduced_ws ws -> 1 <= lo -> lo <= hi -> hi <= W.M ->
  lo * W.M ^ (Z.of_nat k) <= val ws < hi * W.M ^ (Z.of_nat k) ->
  length ws = S k /\ lo <= nth_w ws k < hi.
Proof. intros Hw Hr Hlo Hlh Hhi [H1 H2]. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat k) M_pos) as Pk.
  assert (L1: (k < length ws)%nat). { apply size_ge_of_val; auto. nia. }
  assert (L2: (length ws <= S k)%nat). { apply size_le_of_val; auto. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia. }
  assert (L: length ws = S k) by lia. split; auto.
  pose proof (val_single_nth ws k L1) as E.
  assert (Sk: skipn (S k) ws = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
  rewrite Sk, val_nil, Z.mul_0_r, Z.add_0_r in E.
  pose proof (val_bound (firstn k ws) (words_ok_firstn k ws Hw)) as B0. rewrite length_firstn, Nat.min_l in B0 by lia.
  pose proof (words_ok_nth ws k Hw) as Wk. unfold wordZ in Wk.
  set (w := nth_w ws k) in *. set (V0 := val (firstn k ws)) in *. set (P := W.M ^ Z.of_nat k) in *.
  assert (~ w <= lo - 1). { intro. assert (P * w <= P * (lo - 1)) by nia. nia. }
  assert (~ hi <= w). { intro. assert (P * hi <= P * w) by nia. nia. }
  lia. Qed.
