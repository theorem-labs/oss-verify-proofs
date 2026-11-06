(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope nat_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lexlt (u v : list Z) : Prop :=
  match u, v with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: u', b :: v' => (a < b)%Z \/ (a = b /\ lexlt u' v')
  end.
Definition lexle (u v : list Z) : Prop := lexlt u v \/ u = v.

Lemma lexlt_irrefl : forall u, ~ lexlt u u.
Proof. induction u as [|a u IH]; cbn; [tauto|]. intros [H|[_ H]]; [lia|exact (IH H)]. Qed.

Lemma lexlt_trans : forall u v w, lexlt u v -> lexlt v w -> lexlt u w.
Proof.
  induction u as [|a u IH]; intros [|b v] [|c w]; cbn; try tauto.
  intros [H1|[-> H1]] [H2|[-> H2]]; try (left; lia). right; split; [reflexivity|eauto].
Qed.

Lemma lexlt_total : forall u v, length u = length v -> lexlt u v \/ u = v \/ lexlt v u.
Proof.
  induction u as [|a u IH]; intros [|b v] Hl; cbn in *; try lia; [tauto|].
  destruct (Z.lt_trichotomy a b) as [H|[->|H]]; [left; left; exact H| |right; right; left; exact H].
  destruct (IH v ltac:(lia)) as [H|[->|H]]; [left; right; auto|right; left; reflexivity|right; right; right; auto].
Qed.

Lemma lexle_trans : forall u v w, lexle u v -> lexle v w -> lexle u w.
Proof.
  intros u v w [A| ->] [B| ->]; unfold lexle; eauto using lexlt_trans.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma lexlt_not_le : forall u v, lexlt u v -> ~ lexle v u.
Proof. intros u v A [B|E]; [exact (lexlt_irrefl _ (lexlt_trans _ _ _ A B))|subst; exact (lexlt_irrefl _ A)]. Qed.

Lemma lexle_total : forall u v, length u = length v -> lexle u v \/ lexlt v u.
Proof. intros u v H. destruct (lexlt_total u v H) as [A|[A|A]]; unfold lexle; tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lexlt_app_single : forall u v a b, length u = length v -> lexlt u v -> lexlt (u ++ [a]) (v ++ [b]).
Proof.
  induction u as [|x u IH]; intros [|y v] a b Hl H; cbn in *; try lia; try tauto.
  destruct H as [H|[-> H]]; [left; exact H|right; split; [reflexivity|apply IH; [lia|exact H]]].
Qed.

Lemma lexlt_app_single_inv : forall u v a b, length u = length v ->
  lexlt (u ++ [a]) (v ++ [b]) -> lexlt u v \/ (u = v /\ (a < b)%Z).
Proof.
  induction u as [|x u IH]; intros [|y v] a b Hl H; cbn in *; try lia.
  - destruct H as [H|[_ H]]; [right; auto|destruct H].
  - destruct H as [H|[-> H]]; [left; left; exact H|].
    destruct (IH v a b ltac:(lia) H) as [A|[-> A]]; [left; right; auto|right; auto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_cons_nth : forall (l : list Z) p, p < length l -> skipn p l = nth p l 0%Z :: skipn (S p) l.
Proof.
  induction l as [|a l IH]; intros [|p] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma firstn_S_snoc : forall (l : list Z) p, p < length l -> firstn (S p) l = firstn p l ++ [nth p l 0%Z].
Proof.
  induction l as [|a l IH]; intros [|p] H; cbn in *; try lia; [reflexivity|]. rewrite (IH p) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rotl (u : list Z) : list Z := match u with [] => [] | a :: u' => u' ++ [a] end.
Definition rotr (u : list Z) : list Z := match rev u with [] => [] | a :: r => a :: rev r end.

Lemma rotr_rotl : forall u, rotr (rotl u) = u.
Proof. intros [|a u]; [reflexivity|]. unfold rotl, rotr. rewrite rev_app_distr. cbn. rewrite rev_involutive. reflexivity. Qed.
Lemma rotl_rotr : forall u, rotl (rotr u) = u.
Proof.
  intros u. unfold rotr. destruct (rev u) as [|a r] eqn:E.
  - destruct u; [reflexivity|]. cbn in E. destruct (rev u); discriminate.
  - cbn. rewrite <- (rev_involutive u), E. reflexivity.
Qed.
Lemma rotl_length : forall u, length (rotl u) = length u.
Proof. intros [|a u]; [reflexivity|]. cbn. rewrite length_app. cbn. lia. Qed.
Lemma hd_rotr_last : forall u, u <> [] -> hd 0%Z (rotr u) = last u 0%Z.
Proof.
  intros u Hu. unfold rotr. destruct (rev u) as [|a r] eqn:E.
  - destruct u; [congruence|]. cbn in E. destruct (rev u); discriminate.
  - cbn. rewrite <- (rev_involutive u), E. cbn. rewrite last_last. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cnt (P : nat -> bool) (m : nat) : nat := length (filter P (seq 0 m)).

Lemma cnt_S : forall P m, cnt P (S m) = cnt P m + (if P m then 1 else 0).
Proof.
  intros P m. unfold cnt. rewrite seq_S, filter_app, length_app. cbn. destruct (P m); cbn; lia.
Qed.
Lemma cnt_0 : forall P, cnt P 0 = 0. Proof. reflexivity. Qed.

Lemma cnt_le : forall P m, cnt P m <= m.
Proof. intros P m; induction m as [|m IH]; [reflexivity|]. rewrite cnt_S. destruct (P m); lia. Qed.

Lemma cnt_mono : forall (P Q : nat -> bool) m, (forall k, k < m -> P k = true -> Q k = true) -> cnt P m <= cnt Q m.
Proof.
  intros P Q m H; induction m as [|m IH]; [reflexivity|]. rewrite !cnt_S.
  specialize (IH ltac:(intros; apply H; [lia|assumption])).
  destruct (P m) eqn:EP; [rewrite (H m ltac:(lia) EP); lia|]. destruct (Q m); lia.
Qed.

Lemma cnt_ext : forall (P Q : nat -> bool) m, (forall k, k < m -> P k = Q k) -> cnt P m = cnt Q m.
Proof.
  intros P Q m H. apply Nat.le_antisymm; apply cnt_mono; intros k Hk E; [rewrite <- H|rewrite H]; auto.
Qed.

Lemma cnt_true : forall m, cnt (fun _ => true) m = m.
Proof. induction m as [|m IH]; [reflexivity|rewrite cnt_S; cbn; lia]. Qed.

Lemma cnt_all : forall P m, (forall k, k < m -> P k = true) -> cnt P m = m.
Proof.
  intros P m H. apply Nat.le_antisymm; [apply cnt_le|]. rewrite <- (cnt_true m) at 1. apply cnt_mono. auto.
Qed.

Lemma cnt_none : forall P m, (forall k, k < m -> P k = false) -> cnt P m = 0.
Proof.
  intros P m H. induction m as [|m IH]; [reflexivity|]. rewrite cnt_S, (H m) by lia. rewrite IH; [lia|]. intros; apply H; lia.
Qed.

Lemma cnt_split : forall (P Q : nat -> bool) m, (forall k, k < m -> P k = true -> Q k = true -> False) ->
  cnt (fun k => P k || Q k) m = cnt P m + cnt Q m.
Proof.
  intros P Q m H; induction m as [|m IH]; [reflexivity|]. rewrite !cnt_S.
  rewrite (IH ltac:(intros; eapply H; [| eassumption | eassumption]; lia)).
  destruct (P m) eqn:EP, (Q m) eqn:EQ; cbn; try lia. exfalso; eapply (H m); [lia|exact EP|exact EQ].
Qed.

Lemma cnt_le_mono_m : forall P m m', m <= m' -> cnt P m <= cnt P m'.
Proof. intros P m m' H. induction H; [lia|]. rewrite cnt_S. destruct (P m0); lia. Qed.

(* [comment removed for export] *)
Lemma cnt_single : forall m x, x < m -> cnt (fun r => r =? x) m = 1.
Proof.
  intros m x Hx. induction m as [|m IH]; [lia|]. rewrite cnt_S.
  destruct (Nat.eqb_spec m x).
  - subst. rewrite cnt_none; [reflexivity|]. intros k Hk. apply Nat.eqb_neq. lia.
  - rewrite IH by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma cnt_down_closed : forall (P : nat -> bool) m,
  (forall k k', k' <= k -> k < m -> P k = true -> P k' = true) ->
  forall r, r < m -> (P r = true <-> r < cnt P m).
Proof.
  intros P m H. induction m as [|m IH]; intros r Hr; [lia|].
  rewrite cnt_S.
  assert (IH' : forall r, r < m -> P r = true <-> r < cnt P m).
  { apply IH. intros k k' A B C. apply (H k k'); [exact A|lia|exact C]. }
  destruct (P m) eqn:EP.
  - assert (ALL : forall k, k < m -> P k = true) by (intros k Hk; apply (H m k); [lia|lia|exact EP]).
    rewrite (cnt_all P m ALL). split; intros; [lia|]. destruct (Nat.eq_dec r m); [subst; exact EP|apply ALL; lia].
  - destruct (Nat.eq_dec r m).
    + subst. rewrite EP. split; [discriminate|]. pose proof (cnt_le P m). lia.
    + rewrite Nat.add_0_r. apply IH'. lia.
Qed.

(* [comment removed for export] *)
Lemma cnt_inj_le : forall m (P Q : nat -> bool) (f : nat -> nat) m',
  (forall k, k < m -> P k = true -> f k < m' /\ Q (f k) = true) ->
  (forall k k', k < m -> k' < m -> P k = true -> P k' = true -> f k = f k' -> k = k') ->
  cnt P m <= cnt Q m'.
Proof.
  induction m as [|m IH]; intros P Q f m' Hf Hinj; [apply Nat.le_0_l|].
  rewrite cnt_S. destruct (P m) eqn:EP.
  - destruct (Hf m ltac:(lia) EP) as [Fm QF].
    set (Q' := fun r => Q r && negb (r =? f m)).
    assert (E : cnt Q m' = cnt Q' m' + 1).
    { transitivity (cnt (fun r => Q' r || (r =? f m)) m').
      - apply cnt_ext. intros k Hk. unfold Q'. destruct (Nat.eqb_spec k (f m)); [subst; rewrite QF; reflexivity|].
        destruct (Q k); reflexivity.
      - rewrite cnt_split; [rewrite cnt_single by exact Fm; reflexivity|].
        intros k Hk A B. unfold Q' in A. rewrite B in A. cbn in A. rewrite andb_false_r in A. discriminate. }
    rewrite E. enough (cnt P m <= cnt Q' m') by lia.
    apply (IH P Q' f m').
    + intros k Hk Pk. destruct (Hf k ltac:(lia) Pk) as [A B]. split; [exact A|]. unfold Q'. rewrite B. cbn.
      destruct (Nat.eqb_spec (f k) (f m)); [|reflexivity]. exfalso.
      assert (k = m) by (apply Hinj; try lia; assumption). lia.
    + intros; apply Hinj; try lia; assumption.
  - rewrite Nat.add_0_r. apply (IH P Q f m'); intros; [apply Hf|apply Hinj]; try lia; assumption.
Qed.

Lemma nth_map_seq : forall (A : Type) (f : nat -> A) (d : A) m s k, k < m -> nth k (map f (seq s m)) d = f (s + k).
Proof.
  intros A f d m. induction m as [|m IH]; intros s k Hk; [lia|].
  cbn. destruct k as [|k]; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Section Block.
  Variable t : list Z.
  Let n := length t.
  Hypothesis Hn : 0 < n.

  Definition rot (p : nat) : list Z := skipn p t ++ firstn p t.

  Lemma rot_length : forall p, p <= n -> length (rot p) = n.
  Proof. intros p Hp. unfold rot. rewrite length_app, length_skipn, length_firstn. unfold n in *. lia. Qed.

  (* [comment removed for export] *)
  Definition nxt (p : nat) : nat := if S p <? n then S p else 0.
  Definition prv (p : nat) : nat := if p =? 0 then n - 1 else p - 1.

  Lemma nxt_lt : forall p, p < n -> nxt p < n. Proof. intros; unfold nxt; destruct (Nat.ltb_spec (S p) n); lia. Qed.
  Lemma prv_lt : forall p, p < n -> prv p < n. Proof. intros; unfold prv; destruct (Nat.eqb_spec p 0); lia. Qed.
  Lemma prv_nxt : forall p, p < n -> prv (nxt p) = p.
  Proof.
    intros p Hp; unfold prv, nxt. destruct (Nat.ltb_spec (S p) n).
    - cbn. lia.
    - rewrite Nat.eqb_refl. lia.
  Qed.
  Lemma nxt_prv : forall p, p < n -> nxt (prv p) = p.
  Proof.
    intros p Hp; unfold prv, nxt. destruct (Nat.eqb_spec p 0).
    - subst. destruct (Nat.ltb_spec (S (n - 1)) n); lia.
    - destruct (Nat.ltb_spec (S (p - 1)) n); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rotl_skipn_firstn : forall (l : list Z) p, p < length l ->
    rotl (skipn p l ++ firstn p l) = skipn (S p) l ++ firstn (S p) l.
  Proof.
    intros l p Hp. rewrite (skipn_cons_nth l p Hp). cbn [rotl app].
    rewrite (firstn_S_snoc l p Hp), app_assoc. reflexivity.
  Qed.

  Lemma rot_nxt : forall p, p < n -> rot (nxt p) = rotl (rot p).
  Proof.
    intros p Hp. unfold rot, nxt. unfold n in *.
    rewrite (rotl_skipn_firstn t p Hp).
    destruct (Nat.ltb_spec (S p) (length t)); [reflexivity|].
    assert (E : S p = length t) by lia. rewrite E, skipn_all, firstn_all. cbn. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma rot_0 : rot 0 = t.
  Proof. unfold rot. cbn. apply app_nil_r. Qed.

  Lemma rot_hd : forall p, p < n -> hd 0%Z (rot p) = nth p t 0%Z.
  Proof. intros p Hp. unfold rot. unfold n in Hp. rewrite (skipn_cons_nth t p Hp). reflexivity. Qed.

  Lemma rot_prv : forall p, p < n -> rot (prv p) = rotr (rot p).
  Proof.
    intros p Hp. rewrite <- (nxt_prv p Hp) at 2. rewrite rot_nxt by (apply prv_lt; exact Hp).
    rewrite rotr_rotl. reflexivity.
  Qed.

  Lemma rot_nonnil : forall p, p <= n -> rot p <> [].
  Proof. intros p Hp E. pose proof (rot_length p Hp). rewrite E in H. cbn in H. lia. Qed.

  (* [comment removed for export] *)
  Lemma rot_last : forall p, p < n -> last (rot p) 0%Z = nth (prv p) t 0%Z.
  Proof.
    intros p Hp. rewrite <- rot_hd by (apply prv_lt; exact Hp). rewrite rot_prv by exact Hp.
    symmetry. apply hd_rotr_last. apply rot_nonnil. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lexlt_rotr : forall u v, length u = length v -> u <> [] -> last u 0%Z = last v 0%Z ->
    (lexlt u v <-> lexlt (rotr u) (rotr v)).
  Proof.
    intros u v Hl Hu Hlast.
    assert (Hv : v <> []) by (intros ->; destruct u; [congruence|discriminate]).
    rewrite <- (rotl_rotr u) at 1. rewrite <- (rotl_rotr v) at 1.
    pose proof (hd_rotr_last u Hu) as Eu. pose proof (hd_rotr_last v Hv) as Ev.
    assert (Lu : length (rotr u) = length u) by (rewrite <- (rotl_rotr u) at 2; rewrite rotl_length; reflexivity).
    assert (Lv : length (rotr v) = length v) by (rewrite <- (rotl_rotr v) at 2; rewrite rotl_length; reflexivity).
    revert Eu Ev Lu Lv. generalize (rotr u) as u'. generalize (rotr v) as v'. intros v' u' Eu Ev Lu Lv.
    destruct u' as [|a u'']; [destruct u; [congruence|cbn in Lu; lia]|].
    destruct v' as [|b v'']; [destruct v; [congruence|cbn in Lv; lia]|].
    cbn in Eu, Ev. assert (ab : b = a) by congruence. rewrite ab in *. clear ab Ev. cbn [rotl].
    split.
    - intros H. destruct (lexlt_app_single_inv u'' v'' a a ltac:(cbn in Lu, Lv; lia) H) as [A|[_ A]]; [|lia].
      right; auto.
    - intros [A|[_ A]]; [lia|]. apply lexlt_app_single; [cbn in Lu, Lv; lia|exact A].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint lexltb (u v : list Z) : bool :=
    match u, v with
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: u', b :: v' => (a <? b)%Z || ((a =? b)%Z && lexltb u' v')
    end.
  Lemma lexltb_spec : forall u v, lexltb u v = true <-> lexlt u v.
  Proof.
    induction u as [|a u IH]; intros [|b v]; cbn; try (split; [discriminate|tauto]); [tauto|].
    rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.ltb_lt, Z.eqb_eq, IH. tauto.
  Qed.
  Lemma lexltb_false : forall u v, lexltb u v = false <-> ~ lexlt u v.
  Proof.
    intros u v. pose proof (lexltb_spec u v) as H. destruct (lexltb u v); split; intros A.
    - discriminate.
    - exfalso. apply A, H. reflexivity.
    - intros B. apply H in B. discriminate.
    - reflexivity.
  Qed.
  Definition lexleb (u v : list Z) : bool := negb (lexltb v u).
  Lemma lexleb_spec : forall u v, length u = length v -> (lexleb u v = true <-> lexle u v).
  Proof.
    intros u v Hl. unfold lexleb. rewrite Bool.negb_true_iff, lexltb_false. split.
    - intros H. destruct (lexle_total u v Hl); [assumption|contradiction].
    - intros H A. exact (lexlt_not_le _ _ A H).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Sorted.
    Variables pi rho : nat -> nat.          (* [comment removed for export] *)
    Hypothesis pi_lt : forall i, i < n -> pi i < n.
    Hypothesis rho_lt : forall p, p < n -> rho p < n.
    Hypothesis rho_pi : forall i, i < n -> rho (pi i) = i.
    Hypothesis pi_rho : forall p, p < n -> pi (rho p) = p.
    Hypothesis sorted : forall i j, i <= j -> j < n -> lexle (rot (pi i)) (rot (pi j)).

    Definition cls (i : nat) : list Z := rot (pi i).        (* [comment removed for export] *)
    Definition Fc (i : nat) : Z := nth (pi i) t 0%Z.        (* [comment removed for export] *)
    Definition Lc (i : nat) : Z := nth (prv (pi i)) t 0%Z.  (* [comment removed for export] *)
    Definition qrow (i : nat) : nat := rho (prv (pi i)).     (* [comment removed for export] *)
    Definition srow (i : nat) : nat := rho (nxt (pi i)).     (* [comment removed for export] *)

    Lemma cls_length : forall i, i < n -> length (cls i) = n.
    Proof. intros; unfold cls; apply rot_length. pose proof (pi_lt i H). lia. Qed.
    Lemma cls_hd : forall i, i < n -> hd 0%Z (cls i) = Fc i.
    Proof. intros; unfold cls, Fc; apply rot_hd; auto. Qed.
    Lemma cls_last : forall i, i < n -> last (cls i) 0%Z = Lc i.
    Proof. intros; unfold cls, Lc; apply rot_last; auto. Qed.
    Lemma cls_nonnil : forall i, i < n -> cls i <> [].
    Proof. intros; unfold cls; apply rot_nonnil. pose proof (pi_lt i H). lia. Qed.
    Lemma qrow_lt : forall i, i < n -> qrow i < n. Proof. intros; unfold qrow; auto using prv_lt. Qed.
    Lemma srow_lt : forall i, i < n -> srow i < n. Proof. intros; unfold srow; auto using nxt_lt. Qed.
    Lemma cls_qrow : forall i, i < n -> cls (qrow i) = rotr (cls i).
    Proof. intros i Hi; unfold cls, qrow. rewrite pi_rho by auto using prv_lt. apply rot_prv; auto. Qed.
    (* [comment removed for export] *)
    Lemma Fc_qrow : forall i, i < n -> Fc (qrow i) = Lc i.
    Proof. intros i Hi; unfold Fc, Lc, qrow. rewrite pi_rho by auto using prv_lt. reflexivity. Qed.
    Lemma Lc_srow : forall i, i < n -> Lc (srow i) = Fc i.
    Proof. intros i Hi; unfold Fc, Lc, srow. rewrite pi_rho by auto using nxt_lt. rewrite prv_nxt by auto. reflexivity. Qed.
    Lemma qrow_srow : forall i, i < n -> qrow (srow i) = i.
    Proof. intros i Hi; unfold qrow, srow. rewrite pi_rho by auto using nxt_lt. rewrite prv_nxt by auto. auto. Qed.
    Lemma srow_qrow : forall i, i < n -> srow (qrow i) = i.
    Proof. intros i Hi; unfold qrow, srow. rewrite pi_rho by auto using prv_lt. rewrite nxt_prv by auto. auto. Qed.

    (* [comment removed for export] *)
    Lemma sorted_lt : forall i j, i < n -> j < n -> lexlt (cls i) (cls j) -> i < j.
    Proof.
      intros i j Hi Hj H. destruct (Nat.lt_ge_cases i j) as [A|A]; [exact A|]. exfalso.
      exact (lexlt_not_le _ _ H (sorted j i A Hi)).
    Qed.

    (* [comment removed for export] *)
    Lemma qrow_lt_iff : forall i j, i < n -> j < n -> Lc j = Lc i ->
      (lexlt (cls j) (cls i) <-> lexlt (cls (qrow j)) (cls (qrow i))).
    Proof.
      intros i j Hi Hj HL. rewrite !cls_qrow by assumption. apply lexlt_rotr.
      - rewrite !cls_length; auto.
      - apply cls_nonnil; auto.
      - rewrite !cls_last; auto.
    Qed.
    Lemma qrow_eq_iff : forall i j, i < n -> j < n -> (cls j = cls i <-> cls (qrow j) = cls (qrow i)).
    Proof.
      intros i j Hi Hj. rewrite !cls_qrow by assumption. split; [intros ->; reflexivity|].
      intros E. rewrite <- (rotl_rotr (cls j)), <- (rotl_rotr (cls i)), E. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Definition Ccnt (c : Z) : nat := cnt (fun r => (Fc r <? c)%Z) n.            (* [comment removed for export] *)
    Definition occ (i : nat) : nat := cnt (fun j => (Lc j =? Lc i)%Z) i.         (* [comment removed for export] *)
    Definition LF (i : nat) : nat := Ccnt (Lc i) + occ i.

    (* [comment removed for export] *)
    Theorem LF_spec : forall i, i < n -> LF i < n /\ cls (LF i) = cls (qrow i).
    Proof.
      intros i Hi.
      set (X := cls (qrow i)). set (c := Lc i).
      assert (HX : hd 0%Z X = c) by (subst X c; rewrite cls_hd, Fc_qrow; auto using qrow_lt).
      assert (LX : length X = n) by (subst X; apply cls_length; auto using qrow_lt).
      (* [comment removed for export] *)
      set (Pa := fun r => lexltb (cls r) X). set (Pb := fun r => lexleb (cls r) X).
      set (a := cnt Pa n). set (b := cnt Pb n).
      (* [comment removed for export] *)
      assert (DA : forall r, r < n -> Pa r = ((Fc r <? c)%Z || ((Fc r =? c)%Z && lexltb (cls r) X))).
      { intros r Hr. subst Pa. cbn beta.
        destruct (cls r) as [|x u] eqn:Er; [exfalso; exact (cls_nonnil r Hr Er)|].
        destruct X as [|y v] eqn:EX; [cbn in LX; lia|]. cbn in HX. subst y.
        assert (Fx : Fc r = x) by (rewrite <- cls_hd, Er by assumption; reflexivity). rewrite Fx. cbn.
        destruct (Z.ltb_spec x c); cbn; [reflexivity|]. destruct (Z.eqb_spec x c); reflexivity. }
      assert (DB : forall r, r < n -> Pb r = ((Fc r <? c)%Z || ((Fc r =? c)%Z && lexleb (cls r) X))).
      { intros r Hr. subst Pb. unfold lexleb. cbn beta.
        destruct (cls r) as [|x u] eqn:Er; [exfalso; exact (cls_nonnil r Hr Er)|].
        destruct X as [|y v] eqn:EX; [cbn in LX; lia|]. cbn in HX. subst y.
        assert (Fx : Fc r = x) by (rewrite <- cls_hd, Er by assumption; reflexivity). rewrite Fx. cbn.
        destruct (Z.ltb_spec c x), (Z.ltb_spec x c), (Z.eqb_spec c x), (Z.eqb_spec x c); cbn; try lia; reflexivity. }
      (* [comment removed for export] *)
      assert (A : a <= LF i).
      { subst a. unfold LF. rewrite (cnt_ext Pa _ n DA), cnt_split.
        2: { intros k Hk P1 P2. apply Bool.andb_true_iff in P2. destruct P2 as [P2 _]. lia. }
        apply Nat.add_le_mono_l. unfold occ.
        apply (cnt_inj_le n _ _ srow i).
        - intros r Hr Pr. apply Bool.andb_true_iff in Pr. destruct Pr as [P1 P2].
          apply Z.eqb_eq in P1. apply lexltb_spec in P2.
          assert (Ls : Lc (srow r) = c) by (rewrite Lc_srow; auto).
          assert (LT : lexlt (cls (srow r)) (cls i)).
          { apply (qrow_lt_iff i (srow r) Hi (srow_lt r Hr)); [subst c; exact Ls|].
            rewrite qrow_srow by assumption. exact P2. }
          split; [exact (sorted_lt _ _ (srow_lt r Hr) Hi LT)|]. subst c. rewrite Ls. apply Z.eqb_refl.
        - intros k k' Hk Hk' _ _ E. rewrite <- (qrow_srow k Hk), <- (qrow_srow k' Hk'), E. reflexivity. }
      (* [comment removed for export] *)
      assert (B : LF i < b).
      { subst b. unfold LF. rewrite (cnt_ext Pb _ n DB), cnt_split.
        2: { intros k Hk P1 P2. apply Bool.andb_true_iff in P2. destruct P2 as [P2 _]. lia. }
        apply Nat.add_lt_mono_l. unfold occ.
        apply (Nat.lt_le_trans _ (cnt (fun j : nat => (Lc j =? Lc i)%Z) (S i))).
        { rewrite cnt_S, Z.eqb_refl. lia. }
        apply (cnt_inj_le (S i) _ _ qrow n).
        - intros j Hj Pj. apply Z.eqb_eq in Pj. assert (Hjn : j < n) by lia.
          split; [apply qrow_lt; exact Hjn|]. apply Bool.andb_true_iff. split.
          + rewrite Fc_qrow by exact Hjn. subst c. rewrite Pj. apply Z.eqb_refl.
          + apply lexleb_spec; [rewrite cls_length; auto using qrow_lt|].
            destruct (sorted j i ltac:(lia) Hi) as [LT|EQ].
            * left. subst X. apply (qrow_lt_iff i j Hi Hjn); [subst c; exact Pj|exact LT].
            * right. subst X. apply (qrow_eq_iff i j Hi Hjn). exact EQ.
        - intros k k' Hk Hk' _ _ E. rewrite <- (srow_qrow k), <- (srow_qrow k'), E by lia. reflexivity. }
      (* [comment removed for export] *)
      assert (Hb : b <= n) by (subst b; apply cnt_le).
      split; [lia|].
      assert (DCa : forall k k', k' <= k -> k < n -> Pa k = true -> Pa k' = true).
      { intros k k' H1 H2 H3. subst Pa. cbn beta in *. apply lexltb_spec. apply lexltb_spec in H3.
        destruct (sorted k' k H1 H2) as [LT| EQ]; [exact (lexlt_trans _ _ _ LT H3)|unfold cls in *; rewrite EQ; exact H3]. }
      assert (DCb : forall k k', k' <= k -> k < n -> Pb k = true -> Pb k' = true).
      { intros k k' H1 H2 H3. subst Pb. cbn beta in *.
        apply lexleb_spec; [rewrite cls_length; lia|]. apply lexleb_spec in H3; [|rewrite cls_length; lia].
        exact (lexle_trans _ _ _ (sorted k' k H1 H2) H3). }
      pose proof (cnt_down_closed Pa n DCa (LF i) ltac:(lia)) as [NA _].
      pose proof (cnt_down_closed Pb n DCb (LF i) ltac:(lia)) as [_ PB].
      specialize (PB B). subst Pb. cbn beta in PB. apply lexleb_spec in PB; [|rewrite cls_length; lia].
      destruct PB as [LT|EQ]; [|exact EQ].
      exfalso. assert (Pa (LF i) = true) by (subst Pa; apply lexltb_spec; exact LT).
      specialize (NA H). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma cntF_eq_cntL : forall c, cnt (fun r => (Fc r =? c)%Z) n = cnt (fun j => (Lc j =? c)%Z) n.
    Proof.
      intros c. apply Nat.le_antisymm.
      - apply (cnt_inj_le n _ _ srow n).
        + intros r Hr P. split; [auto using srow_lt|]. rewrite Lc_srow; auto.
        + intros k k' Hk Hk' _ _ E. rewrite <- (qrow_srow k), <- (qrow_srow k'), E by assumption. reflexivity.
      - apply (cnt_inj_le n _ _ qrow n).
        + intros r Hr P. split; [auto using qrow_lt|]. rewrite Fc_qrow; auto.
        + intros k k' Hk Hk' _ _ E. rewrite <- (srow_qrow k), <- (srow_qrow k'), E by assumption. reflexivity.
    Qed.

    Lemma occ_lt_total : forall i, i < n -> occ i < cnt (fun j => (Lc j =? Lc i)%Z) n.
    Proof.
      intros i Hi. unfold occ. apply (Nat.lt_le_trans _ (cnt (fun j => (Lc j =? Lc i)%Z) (S i))).
      - rewrite cnt_S, Z.eqb_refl. lia.
      - apply cnt_le_mono_m. lia.
    Qed.

    Lemma Ccnt_step : forall c c', (c < c')%Z -> Ccnt c + cnt (fun r => (Fc r =? c)%Z) n <= Ccnt c'.
    Proof.
      intros c c' H. unfold Ccnt. rewrite <- cnt_split.
      - apply cnt_mono. intros k Hk P. apply Bool.orb_true_iff in P. apply Z.ltb_lt.
        destruct P as [P|P]; [apply Z.ltb_lt in P|apply Z.eqb_eq in P]; lia.
      - intros k Hk P1 P2. apply Z.ltb_lt in P1. apply Z.eqb_eq in P2. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma LF_lt : forall i j, i < n -> j < n -> ((Lc i < Lc j)%Z \/ (Lc i = Lc j /\ i < j)) -> LF i < LF j.
    Proof.
      intros i j Hi Hj [H|[E H]]; unfold LF.
      - pose proof (occ_lt_total i Hi). rewrite <- cntF_eq_cntL in H0.
        pose proof (Ccnt_step _ _ H). lia.
      - rewrite E. apply Nat.add_lt_mono_l. unfold occ. rewrite E.
        apply (Nat.lt_le_trans _ (cnt (fun j0 => (Lc j0 =? Lc j)%Z) (S i))).
        + rewrite cnt_S, E, Z.eqb_refl. lia.
        + apply cnt_le_mono_m. lia.
    Qed.

    Lemma LF_inj : forall i j, i < n -> j < n -> LF i = LF j -> i = j.
    Proof.
      intros i j Hi Hj E.
      destruct (Z.lt_trichotomy (Lc i) (Lc j)) as [A|[A|A]].
      - pose proof (LF_lt i j Hi Hj (or_introl A)). lia.
      - destruct (Nat.lt_trichotomy i j) as [B|[B|B]]; [|exact B|].
        + pose proof (LF_lt i j Hi Hj (or_intror (conj A B))). lia.
        + pose proof (LF_lt j i Hj Hi (or_intror (conj (eq_sym A) B))). lia.
      - pose proof (LF_lt j i Hj Hi (or_introl A)). lia.
    Qed.

    Lemma LF_lt_n : forall i, i < n -> LF i < n.
    Proof. intros i Hi. exact (proj1 (LF_spec i Hi)). Qed.

    (* [comment removed for export] *)
    Lemma bounded_search : forall (f : nat -> nat) m r,
      (exists i, i < m /\ f i = r) \/ (forall i, i < m -> f i <> r).
    Proof.
      intros f m r. induction m as [|m [IH|IH]].
      - right. intros; lia.
      - left. cps_destruct IH as (i & A & B). exists i. split; [lia|exact B].
      - destruct (Nat.eq_dec (f m) r) as [E|NE].
        + left. exists m. split; [lia|exact E].
        + right. intros i Hi. destruct (Nat.eq_dec i m); [subst; exact NE|apply IH; lia].
    Qed.

    Lemma LF_surj : forall r, r < n -> exists i, i < n /\ LF i = r.
    Proof.
      intros r Hr. destruct (bounded_search LF n r) as [H|H]; [exact H|]. exfalso.
      assert (n <= cnt (fun k => negb (k =? r)) n).
      { rewrite <- (cnt_true n) at 1. apply (cnt_inj_le n _ _ LF n).
        - intros k Hk _. split; [apply LF_lt_n; exact Hk|]. apply Bool.negb_true_iff. apply Nat.eqb_neq. apply H. exact Hk.
        - intros k k' Hk Hk' _ _ E. exact (LF_inj k k' Hk Hk' E). }
      assert (cnt (fun k => negb (k =? r)) n + 1 = n); [|lia].
      rewrite <- (cnt_single n r Hr), Nat.add_comm, <- cnt_split.
      - apply cnt_all. intros k Hk. destruct (k =? r); reflexivity.
      - intros k Hk A B. rewrite A in B. discriminate.
    Qed.

    (* [comment removed for export] *)
    Definition FL (r : nat) : nat :=
      match find (fun i => LF i =? r) (seq 0 n) with Some i => i | None => 0 end.

    Lemma FL_spec : forall r, r < n -> FL r < n /\ LF (FL r) = r.
    Proof.
      intros r Hr. unfold FL.
      destruct (find (fun i => LF i =? r) (seq 0 n)) as [i|] eqn:E.
      - apply find_some in E. destruct E as [A B]. apply in_seq in A. apply Nat.eqb_eq in B. split; [lia|exact B].
      - exfalso. cps_destruct (LF_surj r Hr) as (i & A & B).
        pose proof (find_none _ _ E i ltac:(apply in_seq; lia)) as C. cbn in C. apply Nat.eqb_neq in C. congruence.
    Qed.

    Lemma FL_LF : forall i, i < n -> FL (LF i) = i.
    Proof.
      intros i Hi. destruct (FL_spec (LF i) (LF_lt_n i Hi)) as [A B]. exact (LF_inj _ _ A Hi B).
    Qed.

    Lemma LF_qrow_cls : forall i, i < n -> cls (LF i) = rotr (cls i).
    Proof. intros i Hi. rewrite (proj2 (LF_spec i Hi)). apply cls_qrow. exact Hi. Qed.

    (* [comment removed for export] *)
    Theorem FL_cls : forall r, r < n -> cls (FL r) = rotl (cls r).
    Proof.
      intros r Hr. destruct (FL_spec r Hr) as [A B].
      transitivity (rotl (rotr (cls (FL r)))); [symmetry; apply rotl_rotr|].
      f_equal. rewrite <- (LF_qrow_cls _ A), B. reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition origPtr : nat := rho 0.
    Definition walk (k : nat) : nat := Nat.iter k FL origPtr.

    Lemma origPtr_lt : origPtr < n. Proof. unfold origPtr. apply rho_lt. exact Hn. Qed.
    Lemma walk_lt : forall k, walk k < n.
    Proof. induction k as [|k IH]; [apply origPtr_lt|]. change (walk (S k)) with (FL (walk k)). apply (proj1 (FL_spec _ IH)). Qed.
    Lemma walk_cls : forall k, cls (walk k) = Nat.iter k rotl t.
    Proof.
      induction k as [|k IH].
      - cbn. unfold cls, origPtr. rewrite pi_rho by exact Hn. apply rot_0.
      - change (walk (S k)) with (FL (walk k)). rewrite FL_cls by apply walk_lt. rewrite IH. reflexivity.
    Qed.

    Lemma iter_rotl_rot : forall k, k < n -> Nat.iter k rotl t = rot k.
    Proof.
      induction k as [|k IH]; intros Hk; [symmetry; apply rot_0|].
      change (Nat.iter (S k) rotl t) with (rotl (Nat.iter k rotl t)). rewrite IH by lia.
      rewrite <- rot_nxt by lia. unfold nxt. destruct (Nat.ltb_spec (S k) n); [reflexivity|lia].
    Qed.
    (* [comment removed for export] *)

    (* [comment removed for export] *)

    Lemma walk_cls_rot : forall k, k < n -> cls (walk k) = rot k.
    Proof. intros k Hk. rewrite walk_cls. apply iter_rotl_rot. exact Hk. Qed.

    (* [comment removed for export] *)
    Theorem small_walk_char : forall k, k < n -> Fc (walk k) = nth k t 0%Z.
    Proof.
      intros k Hk. rewrite <- cls_hd by apply walk_lt. rewrite walk_cls_rot by exact Hk. apply rot_hd. exact Hk.
    Qed.
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Theorem fast_walk_char : forall k, 1 <= k <= n -> Lc (walk k) = nth (k - 1) t 0%Z.
    Proof.
      intros k Hk. rewrite <- cls_last by apply walk_lt.
      change (walk k) with (Nat.iter k FL origPtr). rewrite <- (Nat.succ_pred_pos k) by lia.
      change (Nat.iter (S (Nat.pred k)) FL origPtr) with (FL (walk (Nat.pred k))).
      rewrite FL_cls by apply walk_lt. rewrite walk_cls_rot by lia.
      rewrite <- rot_nxt by lia. rewrite rot_last by (apply nxt_lt; lia). rewrite prv_nxt by lia.
      f_equal. lia.
    Qed.
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    (* [comment removed for export] *)
  End Sorted.
End Block.
