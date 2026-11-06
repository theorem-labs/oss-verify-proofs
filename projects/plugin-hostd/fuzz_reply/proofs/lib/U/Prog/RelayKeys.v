From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayModel.
Import ListNotations.
Open Scope Z_scope.

Fixpoint set_nth {A : Type} (n : nat) (y : A) (l : list A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => y :: t
  | h :: t, S n' => h :: set_nth n' y t
  end.

Definition swap_remove {A : Type} (d : A) (n : nat) (l : list A) : list A :=
  firstn (length l - 1) (set_nth n (last l d) l).

Lemma set_nth_app_left : forall {A} (a : list A) b n y,
  (n < length a)%nat -> set_nth n y (a ++ b) = set_nth n y a ++ b.
Proof.
  induction a as [|h t IH]; intros b n y Hn; cbn in *; [lia|].
  destruct n; [reflexivity|]. cbn. f_equal. apply IH. lia.
Qed.

Lemma set_nth_middle : forall {A} (a b : list A) x y,
  set_nth (length a) y (a ++ x :: b) = a ++ y :: b.
Proof.
  induction a as [|h t IH]; intros; cbn; [reflexivity|]. f_equal. apply IH.
Qed.

Lemma swap_remove_last : forall {A} (d : A) a x,
  swap_remove d (length a) (a ++ [x]) = a.
Proof.
  intros A d a x. unfold swap_remove.
  rewrite last_last, set_nth_middle, length_app. cbn [length].
  replace (length a + 1 - 1)%nat with (length a) by lia.
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
Qed.

Lemma swap_remove_mid : forall {A} (d : A) a x b z,
  swap_remove d (length a) (a ++ x :: b ++ [z]) = a ++ z :: b.
Proof.
  intros A d a x b z. unfold swap_remove.
  replace (a ++ x :: b ++ [z]) with ((a ++ x :: b) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  rewrite last_last.
  rewrite set_nth_app_left by (rewrite length_app; cbn; lia).
  rewrite set_nth_middle.
  replace (length ((a ++ x :: b) ++ [z]) - 1)%nat with (length (a ++ z :: b))
    by (rewrite !length_app; cbn; lia).
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
Qed.

Lemma swap_remove_perm : forall {A} (d : A) a x b,
  Permutation (a ++ x :: b) (x :: swap_remove d (length a) (a ++ x :: b)).
Proof.
  intros A d a x b.
  induction b as [|z b' _] using rev_ind.
  - rewrite swap_remove_last. apply Permutation_sym, Permutation_cons_append.
  - rewrite swap_remove_mid.
    eapply perm_trans; [apply Permutation_sym, Permutation_middle|].
    apply perm_skip. apply Permutation_app_head.
    apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma length_swap_remove : forall {A} (d : A) a x b,
  length (swap_remove d (length a) (a ++ x :: b)) = (length a + length b)%nat.
Proof.
  intros A d a x b. induction b as [|z b' _] using rev_ind.
  - rewrite swap_remove_last. cbn. lia.
  - rewrite swap_remove_mid. rewrite !length_app. cbn. lia.
Qed.

Lemma nth_swap_remove_lt : forall {A} (d : A) a x b i,
  (i < length a)%nat -> nth i (swap_remove d (length a) (a ++ x :: b)) d = nth i (a ++ x :: b) d.
Proof.
  intros A d a x b i Hi.
  rewrite (app_nth1 a (x :: b) d Hi).
  induction b as [|z b' _] using rev_ind.
  - rewrite swap_remove_last. reflexivity.
  - rewrite swap_remove_mid. apply app_nth1. exact Hi.
Qed.

Definition key_eqb (a b : list Z) : bool := list_eqb a b.

Lemma key_eqb_spec : forall a b, key_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold key_eqb, list_eqb.
  destruct (list_eq_dec Z.eq_dec a b); split; congruence.
Qed.

Lemma list_eqb_refl : forall a, list_eqb a a = true.
Proof. intros a. apply (key_eqb_spec a a). reflexivity. Qed.

Lemma list_eqb_true : forall a b, list_eqb a b = true -> a = b.
Proof. intros a b H. apply (key_eqb_spec a b). exact H. Qed.

Fixpoint index_of (x : list Z) (H : list (list Z)) : option nat :=
  match H with
  | [] => None
  | y :: H' => if key_eqb y x then Some O else option_map S (index_of x H')
  end.

Definition seen_arr (H : list (list Z)) (l : list Z) : list (list Z) :=
  match gesture l with
  | Some (GBegin, x) => match index_of x H with Some _ => H | None => H ++ [x] end
  | Some (GEnd, x) => match index_of x H with Some n => swap_remove [] n H | None => H end
  | None => H
  end.

Lemma index_of_some : forall x H n, index_of x H = Some n ->
  exists a b, H = a ++ x :: b /\ length a = n.
Proof.
  intros x H. induction H as [|y H IH]; intros n E; cbn in E; [discriminate|].
  destruct (key_eqb y x) eqn:Ey.
  - apply key_eqb_spec in Ey. subst y. injection E as <-.
    exists [], H. split; reflexivity.
  - destruct (index_of x H) as [m|] eqn:Em; cbn in E; [|discriminate].
    injection E as <-.
    destruct (IH m eq_refl) as (a & b & -> & <-).
    exists (y :: a), b. split; reflexivity.
Qed.

Lemma index_of_none : forall x H, index_of x H = None -> ~ In x H.
Proof.
  intros x H. induction H as [|y H IH]; intros E; [intros []|].
  cbn in E. destruct (key_eqb y x) eqn:Ey; [discriminate|].
  destruct (index_of x H) eqn:Ei; cbn in E; [discriminate|].
  intros [Hy|Hy].
  - subst y. rewrite (proj2 (key_eqb_spec x x) eq_refl) in Ey. discriminate.
  - exact (IH eq_refl Hy).
Qed.

Definition same_set (A B : list (list Z)) : Prop := forall y, In y A <-> In y B.

Lemma upd_in_begin : forall G x y,
  In y (if existsb (list_eqb x) G then G else G ++ [x]) <-> In y G \/ y = x.
Proof.
  intros G x y. destruct (existsb (list_eqb x) G) eqn:E.
  - apply existsb_exists in E. destruct E as (z & Hz & Ez).
    apply list_eqb_true in Ez. subst z.
    split; [intros Hy; left; exact Hy|intros [Hy|Hy]; [exact Hy|subst y; exact Hz]].
  - rewrite in_app_iff. cbn [In].
    split.
    + intros [Hy|[Hy|[]]]; [left; exact Hy|right; symmetry; exact Hy].
    + intros [Hy|Hy]; [left; exact Hy|right; left; symmetry; exact Hy].
Qed.

Lemma upd_in_end : forall G x y,
  In y (filter (fun z => negb (list_eqb x z)) G) <-> In y G /\ y <> x.
Proof.
  intros G x y. rewrite filter_In. split.
  - intros [Hy Hn]. split; [exact Hy|]. intros Hyx. subst y.
    rewrite list_eqb_refl in Hn. discriminate.
  - intros [Hy Hn]. split; [exact Hy|].
    destruct (list_eqb x y) eqn:E; [|reflexivity].
    apply list_eqb_true in E. congruence.
Qed.

Theorem seen_arr_ok : forall H G l,
  NoDup H -> same_set H G ->
  NoDup (seen_arr H l) /\ same_set (seen_arr H l) (upd G l).
Proof.
  intros H G l Hnd Hs. unfold seen_arr, upd.
  destruct (gesture l) as [[[|] x]|]; cbv beta iota.
  - destruct (index_of x H) as [n|] eqn:E.
    + split; [exact Hnd|]. intros y. rewrite upd_in_begin, <- (Hs y). split.
      * intros Hy. left. exact Hy.
      * intros [Hy|Hy]; [exact Hy|]. subst y.
        destruct (index_of_some x H n E) as (a & b & HH & _). rewrite HH.
        apply in_or_app. right. left. reflexivity.
    + split.
      * eapply Permutation_NoDup; [apply Permutation_cons_append|].
        constructor; [exact (index_of_none x H E)|exact Hnd].
      * intros y. rewrite in_app_iff, upd_in_begin, <- (Hs y). cbn [In].
        split.
        -- intros [Hy|[Hy|[]]]; [left; exact Hy|right; symmetry; exact Hy].
        -- intros [Hy|Hy]; [left; exact Hy|right; left; symmetry; exact Hy].
  - destruct (index_of x H) as [n|] eqn:E.
    + destruct (index_of_some x H n E) as (a & b & HH & Ha). subst H n.
      pose proof (swap_remove_perm [] a x b) as Hp.
      assert (Hnd' : NoDup (x :: swap_remove [] (length a) (a ++ x :: b))).
      { eapply Permutation_NoDup; [exact Hp|exact Hnd]. }
      inversion Hnd' as [|? ? Hx Hnd2].
      split; [exact Hnd2|].
      intros y. rewrite upd_in_end, <- (Hs y). split.
      * intros Hy. split.
        -- apply (Permutation_in _ (Permutation_sym Hp)). right. exact Hy.
        -- intros Hyx. subst y. contradiction.
      * intros [Hy Hn]. apply (Permutation_in _ Hp) in Hy.
        destruct Hy as [Hy|Hy]; [congruence|exact Hy].
    + split; [exact Hnd|]. intros y. rewrite upd_in_end, <- (Hs y). split.
      * intros Hy. split; [exact Hy|]. intros Hyx. subst y. exact (index_of_none x H E Hy).
      * intros [Hy _]. exact Hy.
  - split; [exact Hnd|exact Hs].
Qed.

Definition has_prefix (pre x : list Z) : bool := list_eqb (firstn (length pre) x) pre.

Fixpoint gei_loop (fuel : nat) (pre : list Z) (n : nat) (H : list (list Z))
  : list (list Z) * list (list Z) :=
  match fuel with
  | O => ([], H)
  | S f =>
      if Nat.ltb n (length H) then
        if has_prefix pre (nth n H []) then
          let '(E, H') := gei_loop f pre n (swap_remove [] n H) in (nth n H [] :: E, H')
        else gei_loop f pre (S n) H
      else ([], H)
  end.

Definition gei (pre : list Z) (H : list (list Z)) : list (list Z) * list (list Z) :=
  gei_loop (length H) pre 0 H.

Lemma all_before : forall pre n H,
  (length H <= n)%nat ->
  (forall i, (i < n)%nat -> (i < length H)%nat -> has_prefix pre (nth i H []) = false) ->
  Forall (fun x => has_prefix pre x = false) H.
Proof.
  intros pre n H Hn Hpre. apply Forall_forall. intros y Hy.
  apply (In_nth H y []) in Hy. destruct Hy as (i & Hi & <-).
  apply Hpre; lia.
Qed.

Lemma gei_loop_ok : forall fuel pre n H,
  (length H - n <= fuel)%nat ->
  (forall i, (i < n)%nat -> (i < length H)%nat -> has_prefix pre (nth i H []) = false) ->
  let '(E, H') := gei_loop fuel pre n H in
  Permutation (E ++ H') H /\ Forall (fun x => has_prefix pre x = true) E
  /\ Forall (fun x => has_prefix pre x = false) H'.
Proof.
  induction fuel as [|f IH]; intros pre n H Hf Hpre; cbn [gei_loop].
  - split; [apply Permutation_refl|]. split; [constructor|].
    apply (all_before pre n); [lia|exact Hpre].
  - destruct (Nat.ltb_spec n (length H)) as [Hn|Hn].
    + destruct (nth_split H [] Hn) as (a & b & HH & Ha).
      set (x := nth n H []) in *. clearbody x. subst H n.
      rewrite length_app in Hf. cbn [length] in Hf.
      destruct (has_prefix pre x) eqn:Ep.
      * pose proof (IH pre (length a) (swap_remove [] (length a) (a ++ x :: b))) as IHn.
        rewrite length_swap_remove in IHn.
        specialize (IHn ltac:(lia)).
        assert (Hpre' : forall i, (i < length a)%nat ->
                   (i < length a + length b)%nat ->
                   has_prefix pre (nth i (swap_remove [] (length a) (a ++ x :: b)) []) = false).
        { intros i Hi _. rewrite nth_swap_remove_lt by exact Hi.
          apply Hpre; [exact Hi|rewrite length_app; cbn [length]; lia]. }
        specialize (IHn Hpre').
        destruct (gei_loop f pre (length a) (swap_remove [] (length a) (a ++ x :: b))) as [E H'].
        destruct IHn as (Hp & HE & HH').
        split; [|split; [constructor; [exact Ep|exact HE]|exact HH']].
        cbn [app].
        eapply perm_trans; [apply perm_skip, Hp|].
        apply Permutation_sym, swap_remove_perm.
      * pose proof (IH pre (S (length a)) (a ++ x :: b)) as IHn.
        specialize (IHn ltac:(rewrite length_app; cbn [length]; lia)).
        apply IHn.
        intros i Hi Hi2. destruct (Nat.eq_dec i (length a)) as [->|Hne].
        -- rewrite nth_middle. exact Ep.
        -- apply Hpre; lia.
    + split; [apply Permutation_refl|]. split; [constructor|].
      apply (all_before pre n); [lia|exact Hpre].
Qed.

Theorem gei_ok : forall pre H,
  NoDup H ->
  let '(E, H') := gei pre H in
  NoDup E /\ NoDup H' /\ Permutation (E ++ H') H /\
  same_set E (filter (has_prefix pre) H) /\
  same_set H' (filter (fun x => negb (has_prefix pre x)) H).
Proof.
  intros pre H Hnd. unfold gei.
  assert (H0 : forall i, (i < 0)%nat -> (i < length H)%nat -> has_prefix pre (nth i H []) = false)
    by (intros i Hi; exfalso; lia).
  pose proof (gei_loop_ok (length H) pre 0 H ltac:(lia) H0) as G.
  destruct (gei_loop (length H) pre 0 H) as [E H'].
  destruct G as (Hp & HE & HH').
  rewrite Forall_forall in HE, HH'.
  assert (Hnd2 : NoDup (E ++ H')) by (eapply Permutation_NoDup; [apply Permutation_sym, Hp|exact Hnd]).
  split; [eapply NoDup_app_remove_r; exact Hnd2|].
  split; [eapply NoDup_app_remove_l; exact Hnd2|].
  split; [exact Hp|].
  split.
  - intros y. rewrite filter_In. split.
    + intros Hy. split.
      * apply (Permutation_in _ Hp). apply in_or_app. left. exact Hy.
      * apply HE, Hy.
    + intros [Hy Hpy]. apply (Permutation_in _ (Permutation_sym Hp)) in Hy.
      apply in_app_or in Hy. destruct Hy as [Hy|Hy]; [exact Hy|].
      rewrite (HH' y Hy) in Hpy. discriminate.
  - intros y. rewrite filter_In. split.
    + intros Hy. split.
      * apply (Permutation_in _ Hp). apply in_or_app. right. exact Hy.
      * rewrite (HH' y Hy). reflexivity.
    + intros [Hy Hpy]. apply (Permutation_in _ (Permutation_sym Hp)) in Hy.
      apply in_app_or in Hy. destruct Hy as [Hy|Hy]; [|exact Hy].
      rewrite (HE y Hy) in Hpy. discriminate.
Qed.
