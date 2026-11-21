(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.

Lemma zsum_app : forall l m, zsum (l ++ m) = zsum l + zsum m.
Proof. induction l; intros; cbn; rewrite ?IHl; lia. Qed.

Lemma zsum_perm : forall l m, Permutation l m -> zsum l = zsum m.
Proof. intros l m P. induction P; cbn; lia. Qed.

Lemma zsum_map_perm : forall {A} (f : A -> Z) l m, Permutation l m -> zsum (map f l) = zsum (map f m).
Proof. intros A f l m P. apply zsum_perm. apply Permutation_map. exact P. Qed.

Lemma zsum_nonneg : forall l, (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|x l IH]; intros H; cbn; [lia|]. assert (0 <= x) by (apply H; now left). assert (0 <= zsum l) by (apply IH; intros; apply H; now right). lia. Qed.

Lemma zsum_map_le : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. induction l as [|x l IH]; intros H; cbn; [lia|]. assert (f x <= g x) by (apply H; now left). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros; apply H; now right). lia. Qed.

Lemma zsum_map_ext : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. induction l as [|x l IH]; intros H; cbn; [lia|]. rewrite H by now left. rewrite IH by (intros; apply H; now right). lia. Qed.

Lemma zsum_map_mul : forall {A} (k : Z) (f : A -> Z) l, zsum (map (fun x => k * f x) l) = k * zsum (map f l).
Proof. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.

Lemma zsum_map_add : forall {A} (f g : A -> Z) l, zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.


Record ent : Type := E { ew : Z; ea : Z; ed : Z }.

Definition ccost (c : list ent) : Z := zsum (map (fun e => ew e * ed e) c).
Definition kraft (H : Z) (c : list ent) : Z := zsum (map (fun e => 2 ^ (H - ed e)) c).
Definition dep_ok (H : Z) (c : list ent) : Prop := forall e, In e c -> 0 <= ed e <= H.

Lemma ccost_cons : forall e c, ccost (e :: c) = ew e * ed e + ccost c.
Proof. reflexivity. Qed.
Lemma kraft_cons : forall H e c, kraft H (e :: c) = 2 ^ (H - ed e) + kraft H c.
Proof. reflexivity. Qed.
Lemma ccost_app : forall c c', ccost (c ++ c') = ccost c + ccost c'.
Proof. intros. unfold ccost. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma kraft_app : forall H c c', kraft H (c ++ c') = kraft H c + kraft H c'.
Proof. intros. unfold kraft. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma ccost_perm : forall c c', Permutation c c' -> ccost c = ccost c'.
Proof. intros. unfold ccost. apply zsum_map_perm. assumption. Qed.
Lemma kraft_perm : forall H c c', Permutation c c' -> kraft H c = kraft H c'.
Proof. intros. unfold kraft. apply zsum_map_perm. assumption. Qed.

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma kraft_nonneg : forall H c, dep_ok H c -> 0 <= kraft H c.
Proof.
  intros H c D. unfold kraft. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx.
  destruct Hx as (e & <- & He). pose proof (D e He). apply Z.pow_nonneg. lia.
Qed.


Lemma kraft_scale : forall H d c, (forall e, In e c -> ed e <= d) -> d <= H ->
  kraft H c = 2 ^ (H - d) * kraft d c.
Proof.
  intros H d c. induction c as [|e c IH]; intros Hd HdH; [unfold kraft; cbn; lia|].
  rewrite !kraft_cons. rewrite IH; [| intros; apply Hd; now right | lia].
  assert (ed e <= d) by (apply Hd; now left).
  replace (H - ed e) with ((H - d) + (d - ed e)) by lia.
  rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma deepest : forall c : list ent, c <> [] -> exists e, In e c /\ forall e', In e' c -> ed e' <= ed e.
Proof.
  induction c as [|x c IH]; intros Hn; [congruence|].
  destruct c as [|y c'].
  - exists x. split; [now left|]. intros e' [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as (e & He & Hmax).
    destruct (Z_le_gt_dec (ed x) (ed e)).
    + exists e. split; [now right|]. intros e' [<-|He']; [lia| apply Hmax; exact He'].
    + exists x. split; [now left|]. intros e' [<-|He']; [lia|]. specialize (Hmax e' He'). lia.
Qed.

Definition cnt (d : Z) (c : list ent) : Z := zsum (map (fun e => if ed e =? d then 1 else 0) c).

Lemma cnt_cons : forall d e c, cnt d (e :: c) = (if ed e =? d then 1 else 0) + cnt d c.
Proof. reflexivity. Qed.
Lemma cnt_nonneg : forall d c, 0 <= cnt d c.
Proof. intros. unfold cnt. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (e & <- & _). destruct (ed e =? d); lia. Qed.
Lemma cnt_perm : forall d c c', Permutation c c' -> cnt d c = cnt d c'.
Proof. intros. unfold cnt. apply zsum_map_perm. assumption. Qed.

Lemma cnt_pos_in : forall d c, 0 < cnt d c -> exists e c', Permutation c (e :: c') /\ ed e = d.
Proof.
  induction c as [|x c IH]; intros Hc; [unfold cnt in Hc; cbn in Hc; lia|].
  rewrite cnt_cons in Hc. destruct (Z.eqb_spec (ed x) d).
  - exists x, c. split; [apply Permutation_refl| assumption].
  - destruct (IH ltac:(lia)) as (e & c' & P & He). exists e, (x :: c'). split; [|exact He].
    rewrite P. apply perm_swap.
Qed.

Lemma cnt_in_pos : forall d c e, In e c -> ed e = d -> 0 < cnt d c.
Proof.
  induction c as [|x c IH]; intros e Hin He; [destruct Hin|].
  rewrite cnt_cons. pose proof (cnt_nonneg d c). destruct Hin as [<-|Hin].
  - rewrite (proj2 (Z.eqb_eq _ _) He). lia.
  - specialize (IH e Hin He). destruct (ed x =? d); lia.
Qed.

Lemma kraft_parity : forall d c, (forall e, In e c -> ed e <= d) ->
  exists M, kraft d c = cnt d c + 2 * M.
Proof.
  induction c as [|e c IH]; intros Hd.
  - exists 0. reflexivity.
  - destruct (IH ltac:(intros; apply Hd; now right)) as (M & HM).
    rewrite kraft_cons, cnt_cons, HM. assert (ed e <= d) by (apply Hd; now left).
    destruct (Z.eqb_spec (ed e) d).
    + exists M. rewrite e0, Z.sub_diag, Z.pow_0_r. lia.
    + exists (2 ^ (d - ed e - 1) + M). set (k := d - ed e - 1) in *. replace (d - ed e) with (1 + k) by lia.
      rewrite Z.pow_add_r by lia. replace (2 ^ 1) with 2 by reflexivity. lia.
Qed.

Lemma complete_two_deepest : forall H c e1 e2 r,
  Permutation c (e1 :: e2 :: r) -> dep_ok H c -> kraft H c = 2 ^ H ->
  exists d, 1 <= d <= H /\ (forall e, In e c -> ed e <= d) /\ 2 <= cnt d c.
Proof.
  intros H c e1 e2 r P D K.
  destruct (deepest c) as (em & Hem & Hmax).
  { intros ->. apply Permutation_nil in P. discriminate. }
  set (d := ed em) in *. exists d.
  pose proof (D em Hem) as Dm. fold d in Dm.
  assert (Hs : kraft H c = 2 ^ (H - d) * kraft d c) by (apply kraft_scale; [exact Hmax|lia]).
  destruct (kraft_parity d c Hmax) as (M & HM).
  pose proof (cnt_in_pos d c em Hem eq_refl) as Hc1.
  assert (Hd1 : 1 <= d).
  { destruct (Z_lt_le_dec d 1); [|lia]. exfalso.
    assert (d = 0) by lia.
    assert (E1 : forall e, In e c -> ed e = 0).
    { intros e He. pose proof (D e He). pose proof (Hmax e He). lia. }
    rewrite (kraft_perm _ _ _ P) in K. rewrite !kraft_cons in K.
    rewrite (E1 e1) in K by (eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto).
    rewrite (E1 e2) in K by (eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto).
    rewrite Z.sub_0_r in K.
    assert (0 <= kraft H r); [|lia].
    apply kraft_nonneg. intros e He. apply D. eapply Permutation_in; [apply Permutation_sym, P|]. cbn; auto. }
  split; [lia|]. split; [exact Hmax|].
  rewrite K in Hs. replace H with ((H - d) + d) in Hs at 1 by lia. rewrite Z.pow_add_r in Hs by lia.
  assert (E2 : 2 ^ d = kraft d c).
  { apply (Z.mul_reg_l _ _ (2 ^ (H - d))); [|exact Hs]. pose proof (pow2_pos (H - d)). lia. }
  rewrite HM in E2. replace d with (1 + (d - 1)) in E2 at 1 by lia. rewrite Z.pow_add_r in E2 by lia.
  replace (2 ^ 1) with 2 in E2 by reflexivity.
  assert (Z.Even (cnt d c)). { exists (2 ^ (d - 1) - M). lia. }
  destruct (Z_le_gt_dec 2 (cnt d c)); [assumption|]. exfalso.
  assert (cnt d c = 1) by lia. rewrite H1 in H0. destruct H0 as [k Hk]. lia.
Qed.



Definition setd (e : ent) (d : Z) : ent := E (ew e) (ea e) d.

Lemma code_merge : forall H c e1 e2 r,
  Permutation c (e1 :: e2 :: r) -> dep_ok H c -> kraft H c = 2 ^ H ->
  (forall e, In e r -> ew e1 <= ew e /\ ew e2 <= ew e) ->
  exists d r', 1 <= d <= H /\ Permutation (map ew r') (map ew r)
    /\ dep_ok H (E (ew e1 + ew e2) (ea e1) (d - 1) :: r')
    /\ kraft H (E (ew e1 + ew e2) (ea e1) (d - 1) :: r') = 2 ^ H
    /\ ccost (E (ew e1 + ew e2) (ea e1) (d - 1) :: r') + ew e1 + ew e2 <= ccost c.
Proof.
  intros H c e1 e2 r P D K Hmin.
  destruct (complete_two_deepest H c e1 e2 r P D K) as (d & Hd & Hmax & Hcnt).
  assert (S1 : exists r2, Permutation (map ew r2) (map ew r) /\ dep_ok H (setd e1 d :: setd e2 d :: r2)
            /\ kraft H (setd e1 d :: setd e2 d :: r2) = kraft H c
            /\ ccost (setd e1 d :: setd e2 d :: r2) <= ccost c).
  { pose proof (D e1 ltac:(eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto)) as De1.
    pose proof (D e2 ltac:(eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto)) as De2.
    pose proof (Hmax e1 ltac:(eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto)) as Me1.
    pose proof (Hmax e2 ltac:(eapply Permutation_in; [apply Permutation_sym, P|]; cbn; auto)) as Me2.
    assert (Dr : forall e, In e r -> 0 <= ed e <= H /\ ed e <= d).
    { intros e He. split; [apply D|apply Hmax]; eapply Permutation_in; try (apply Permutation_sym, P); cbn; auto. }
    rewrite (cnt_perm _ _ _ P), !cnt_cons in Hcnt.
    rewrite (kraft_perm _ _ _ P), (ccost_perm _ _ P). rewrite !kraft_cons, !ccost_cons.
    destruct (Z.eqb_spec (ed e1) d) as [E1|E1]; destruct (Z.eqb_spec (ed e2) d) as [E2|E2].
    - exists r. split; [apply Permutation_refl|]. split.
      { intros e [<-|[<-|He]]; cbn; try lia. apply Dr, He. }
      rewrite !kraft_cons, !ccost_cons. cbn. rewrite E1, E2. lia.
    -
      destruct (cnt_pos_in d r ltac:(lia)) as (p & r0 & Pr & Hp).
      exists (setd p (ed e2) :: r0). split.
      { cbn. rewrite (Permutation_map ew Pr). cbn. apply Permutation_refl. }
      pose proof (Dr p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto)) as Dp.
      pose proof (Hmin p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto)) as Mp.
      split.
      { intros e [<-|[<-|[<-|He]]]; cbn; try lia. apply Dr. eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto. }
      rewrite (kraft_perm _ _ _ Pr), (ccost_perm _ _ Pr). rewrite !kraft_cons, !ccost_cons. cbn.
      rewrite Hp, E1. split; [lia|].
      assert (0 <= (ew p - ew e2) * (d - ed e2)) by (apply Z.mul_nonneg_nonneg; lia). nia.
    - destruct (cnt_pos_in d r ltac:(lia)) as (p & r0 & Pr & Hp).
      exists (setd p (ed e1) :: r0). split.
      { cbn. rewrite (Permutation_map ew Pr). cbn. apply Permutation_refl. }
      pose proof (Dr p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto)) as Dp.
      pose proof (Hmin p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto)) as Mp.
      split.
      { intros e [<-|[<-|[<-|He]]]; cbn; try lia. apply Dr. eapply Permutation_in; [apply Permutation_sym, Pr|]; cbn; auto. }
      rewrite (kraft_perm _ _ _ Pr), (ccost_perm _ _ Pr). rewrite !kraft_cons, !ccost_cons. cbn.
      rewrite Hp, E2. split; [lia|].
      assert (0 <= (ew p - ew e1) * (d - ed e1)) by (apply Z.mul_nonneg_nonneg; lia). nia.
    -
      destruct (cnt_pos_in d r ltac:(lia)) as (p & r0 & Pr & Hp).
      rewrite (cnt_perm _ _ _ Pr), cnt_cons, (proj2 (Z.eqb_eq _ _) Hp) in Hcnt.
      destruct (cnt_pos_in d r0 ltac:(lia)) as (q & r1 & Pr0 & Hq).
      exists (setd p (ed e1) :: setd q (ed e2) :: r1). split.
      { cbn. rewrite (Permutation_map ew Pr). cbn. rewrite (Permutation_map ew Pr0). cbn. apply Permutation_refl. }
      assert (Pr' : Permutation r (p :: q :: r1)) by (rewrite Pr, Pr0; apply Permutation_refl).
      pose proof (Dr p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr'|]; cbn; auto)) as Dp.
      pose proof (Hmin p ltac:(eapply Permutation_in; [apply Permutation_sym, Pr'|]; cbn; auto)) as Mp.
      pose proof (Dr q ltac:(eapply Permutation_in; [apply Permutation_sym, Pr'|]; cbn; auto)) as Dq.
      pose proof (Hmin q ltac:(eapply Permutation_in; [apply Permutation_sym, Pr'|]; cbn; auto)) as Mq.
      split.
      { intros e [<-|[<-|[<-|[<-|He]]]]; cbn; try lia. apply Dr. eapply Permutation_in; [apply Permutation_sym, Pr'|]; cbn; auto. }
      rewrite (kraft_perm _ _ _ Pr'), (ccost_perm _ _ Pr'). rewrite !kraft_cons, !ccost_cons. cbn.
      rewrite Hp, Hq. split; [lia|].
      assert (0 <= (ew p - ew e1) * (d - ed e1)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (0 <= (ew q - ew e2) * (d - ed e2)) by (apply Z.mul_nonneg_nonneg; lia). nia. }
  destruct S1 as (r2 & P2 & D2 & K2 & C2).
  exists d, r2. split; [exact Hd|]. split; [exact P2|].
  rewrite !kraft_cons, !ccost_cons in *. cbn in *.
  split.
  { intros e [<-|He]; cbn; [lia|]. apply D2. cbn. auto. }
  split.
  - rewrite <- K, <- K2. replace (H - (d - 1)) with (1 + (H - d)) by lia. rewrite Z.pow_add_r by lia.
    replace (2 ^ 1) with 2 by reflexivity. lia.
  - nia.
Qed.


Definition dominated (c c' : list ent) : Prop :=
  Forall2 (fun e e' => ew e' = ew e /\ ea e' = ea e /\ 0 <= ed e' <= ed e) c c'.

Lemma dominated_refl : forall c, (forall e, In e c -> 0 <= ed e) -> dominated c c.
Proof. induction c; intros; constructor; [|apply IHc; intros; apply H; now right]. pose proof (H a (or_introl eq_refl)). lia. Qed.

Lemma dominated_trans : forall c1 c2 c3, dominated c1 c2 -> dominated c2 c3 -> dominated c1 c3.
Proof.
  intros c1 c2 c3 A. revert c3. induction A; intros c3 B; inversion B; subst; constructor.
  - lia. - apply IHA. assumption.
Qed.

Lemma dominated_cost : forall c c', dominated c c' -> (forall e, In e c -> 0 <= ew e) -> ccost c' <= ccost c.
Proof.
  intros c c' A. induction A; intros W; [unfold ccost; cbn; lia|]. rewrite !ccost_cons.
  assert (0 <= ew x) by (apply W; now left).
  assert (ccost l' <= ccost l) by (apply IHA; intros; apply W; now right). nia.
Qed.

Lemma dominated_map_w : forall c c', dominated c c' -> map ew c' = map ew c.
Proof. intros c c' A. induction A; cbn; [reflexivity|]. destruct H as (-> & _). rewrite IHA. reflexivity. Qed.
Lemma dominated_len : forall c c', dominated c c' -> Forall2 (fun e e' => ed e' <= ed e) c c'.
Proof. intros c c' A. induction A; constructor; [lia| assumption]. Qed.

Lemma lower_one : forall c d, 0 < cnt d c -> 1 <= d -> (forall e, In e c -> 0 <= ed e) ->
  exists c', dominated c c' /\ (forall H, kraft H c' = kraft H c - 2 ^ (H - d) + 2 ^ (H - (d - 1)))
    /\ zsum (map ed c') = zsum (map ed c) - 1 /\ (forall e', In e' c' -> exists e, In e c /\ ed e' <= ed e).
Proof.
  induction c as [|x c IH]; intros d Hc Hd Hnn; [unfold cnt in Hc; cbn in Hc; lia|].
  rewrite cnt_cons in Hc. destruct (Z.eqb_spec (ed x) d).
  - exists (setd x (d - 1) :: c). split.
    { constructor. { cbn. lia. } apply dominated_refl. intros; apply Hnn; now right. }
    split. { intros H. rewrite !kraft_cons. cbn. rewrite e. lia. }
    split. { cbn. lia. }
    intros e' [<-|He']. { exists x. split; [now left| cbn; lia]. } exists e'. split; [now right|lia].
  - destruct (IH d ltac:(lia) Hd ltac:(intros; apply Hnn; now right)) as (c' & A & B & C & D').
    exists (x :: c'). split.
    { constructor; [|exact A]. pose proof (Hnn x (or_introl eq_refl)). lia. }
    split. { intros H. rewrite !kraft_cons, B. lia. }
    split. { cbn. lia. }
    intros e' [<-|He']. { exists x. split; [now left|lia]. }
    destruct (D' e' He') as (e0 & He0 & Hle). exists e0. split; [now right| exact Hle].
Qed.

Lemma kraft_dominate_aux : forall n c H, (Z.to_nat (zsum (map ed c)) <= n)%nat ->
  c <> [] -> dep_ok H c -> kraft H c <= 2 ^ H ->
  exists c', dominated c c' /\ dep_ok H c' /\ kraft H c' = 2 ^ H.
Proof.
  induction n as [|n IH]; intros c H Hn Hne D K.
  -
    assert (Z0 : zsum (map ed c) = 0).
    { pose proof (zsum_nonneg (map ed c)). assert (0 <= zsum (map ed c)); [|lia].
      apply H0. intros x Hx. apply in_map_iff in Hx. destruct Hx as (e & <- & He). pose proof (D e He). lia. }
    assert (A0 : forall e, In e c -> ed e = 0).
    { clear -D Z0. induction c as [|x c IHc]; intros e He; [destruct He|]. cbn in Z0.
      pose proof (D x (or_introl eq_refl)).
      assert (0 <= zsum (map ed c)).
      { apply zsum_nonneg. intros y Hy. apply in_map_iff in Hy. destruct Hy as (e' & <- & He'). pose proof (D e' (or_intror He')). lia. }
      destruct He as [<-|He]; [lia|]. apply IHc; [intros e2 He2; apply D; now right| lia | exact He]. }
    exists c. split; [apply dominated_refl; intros e He; pose proof (D e He); lia|]. split; [exact D|].
    destruct c as [|x [|y c]]; [congruence| |].
    + unfold kraft. cbn -[Z.pow Z.sub]. rewrite (A0 x) by now left. rewrite Z.sub_0_r. lia.
    + exfalso. rewrite !kraft_cons in K. rewrite (A0 x), (A0 y) in K by (cbn; auto). rewrite Z.sub_0_r in K.
      assert (0 <= kraft H c) by (apply kraft_nonneg; intros e He; apply D; cbn; auto).
      pose proof (pow2_pos H ltac:(pose proof (D x (or_introl eq_refl)); lia)). lia.
  - destruct (Z_le_gt_dec (2 ^ H) (kraft H c)) as [|LT].
    { exists c. split; [apply dominated_refl; intros e He; pose proof (D e He); lia|]. split; [exact D| lia]. }
    destruct (deepest c Hne) as (em & Hem & Hmax). set (d := ed em) in *.
    pose proof (D em Hem) as Dm. fold d in Dm.
    assert (Hs : kraft H c = 2 ^ (H - d) * kraft d c) by (apply kraft_scale; [exact Hmax|lia]).
    assert (Hd1 : 1 <= d).
    { destruct (Z_lt_le_dec d 1); [|lia]. exfalso. assert (d = 0) by lia.
      destruct c as [|x c']; [congruence|]. rewrite kraft_cons in LT.
      assert (ed x = 0). { pose proof (Hmax x (or_introl eq_refl)). pose proof (D x (or_introl eq_refl)). lia. }
      rewrite H1, Z.sub_0_r in LT.
      assert (0 <= kraft H c') by (apply kraft_nonneg; intros e He; apply D; cbn; auto). lia. }
    assert (LTd : kraft d c + 1 <= 2 ^ d).
    { assert (EH : 2 ^ H = 2 ^ (H - d) * 2 ^ d) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      rewrite EH, Hs in LT. pose proof (pow2_pos (H - d)). nia. }
    destruct (lower_one c d (cnt_in_pos d c em Hem eq_refl) Hd1 ltac:(intros e He; pose proof (D e He); lia))
      as (c' & A & B & C & D').
    assert (Hne' : c' <> []). { intros ->. inversion A. subst. congruence. }
    assert (Dc' : dep_ok H c').
    { intros e' He'. destruct (D' e' He') as (e & He & Hle). pose proof (D e He).
      pose proof (dominated_len _ _ A) as F2.
      split; [|lia].
      clear -A He'. induction A; [destruct He'|]. destruct He' as [<-|He']; [lia| apply IHA; exact He']. }
    assert (K' : kraft H c' <= 2 ^ H).
    { rewrite B. rewrite Hs.
      replace (H - (d - 1)) with (1 + (H - d)) by lia. rewrite Z.pow_add_r by lia. replace (2 ^ 1) with 2 by reflexivity.
      assert (EH : 2 ^ H = 2 ^ (H - d) * 2 ^ d) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      rewrite EH. pose proof (pow2_pos (H - d)). nia. }
    destruct (IH c' H ltac:(rewrite C; lia) Hne' Dc' K') as (c'' & A'' & D'' & K'').
    exists c''. split; [eapply dominated_trans; eassumption|]. split; assumption.
Qed.

Theorem kraft_dominate : forall H c, c <> [] -> dep_ok H c -> kraft H c <= 2 ^ H ->
  exists c', dominated c c' /\ dep_ok H c' /\ kraft H c' = 2 ^ H.
Proof. intros H c. apply (kraft_dominate_aux (Z.to_nat (zsum (map ed c)))). lia. Qed.


Inductive htree : Type := HL (w a : Z) | HN (l r : htree).

Fixpoint hw (t : htree) : Z := match t with HL w _ => w | HN l r => hw l + hw r end.
Fixpoint hcost (t : htree) : Z := match t with HL _ _ => 0 | HN l r => hcost l + hcost r + hw l + hw r end.
Fixpoint hheight (t : htree) : Z := match t with HL _ _ => 0 | HN l r => Z.max (hheight l) (hheight r) + 1 end.
Fixpoint hprof (d : Z) (t : htree) : list ent :=
  match t with HL w a => [E w a d] | HN l r => hprof (d + 1) l ++ hprof (d + 1) r end.
Fixpoint hwmin (lo : Z) (t : htree) : Prop := match t with HL w _ => lo <= w | HN l r => hwmin lo l /\ hwmin lo r end.

Lemma hheight_nonneg : forall t, 0 <= hheight t.
Proof. induction t; cbn; lia. Qed.


Lemma hw_prof : forall d t, zsum (map ew (hprof d t)) = hw t.
Proof. intros d t. revert d. induction t; intros d; cbn; [lia|]. rewrite map_app, zsum_app, IHt1, IHt2. reflexivity. Qed.

Lemma hwmin_hw : forall lo t, 0 <= lo -> hwmin lo t -> lo <= hw t.
Proof. induction t; cbn; intros; [lia|]. destruct H0. specialize (IHt1 H H0). specialize (IHt2 H H1). lia. Qed.

Lemma hwmin_prof : forall lo d t e, hwmin lo t -> In e (hprof d t) -> lo <= ew e.
Proof.
  intros lo d t. revert d. induction t; intros d e Hm Hin; cbn in *.
  - destruct Hin as [<-|[]]. cbn. exact Hm.
  - apply in_app_iff in Hin. destruct Hm, Hin; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma hcost_prof : forall d t, ccost (hprof d t) = hcost t + d * hw t.
Proof.
  intros d t. revert d. induction t; intros d; cbn [hprof hcost hw]; [unfold ccost; cbn -[Z.mul]; lia|].
  rewrite ccost_app, IHt1, IHt2. lia.
Qed.

Lemma hprof_dep : forall d t e, In e (hprof d t) -> d <= ed e <= d + hheight t.
Proof.
  intros d t. revert d. induction t; intros d e Hin; cbn in *.
  - destruct Hin as [<-|[]]. cbn. lia.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [apply IHt1 in Hin|apply IHt2 in Hin]; lia.
Qed.

Lemma hprof_nonnil : forall d t, hprof d t <> [].
Proof. intros d t. revert d. induction t; intros d; cbn; [discriminate|]. intros Happ. apply app_eq_nil in Happ. destruct Happ. eapply IHt1; eassumption. Qed.

Theorem kraft_hprof : forall H d t, 0 <= d -> d + hheight t <= H -> kraft H (hprof d t) = 2 ^ (H - d).
Proof.
  intros H d t. revert d. induction t; intros d Hd Hh; cbn [hheight hprof] in *.
  - unfold kraft. cbn -[Z.pow Z.sub]. lia.
  - pose proof (hheight_nonneg t1). pose proof (hheight_nonneg t2). rewrite kraft_app, IHt1, IHt2 by lia.
    replace (H - d) with (1 + (H - (d + 1))) by lia. rewrite Z.pow_add_r by lia. replace (2 ^ 1) with 2 by reflexivity. lia.
Qed.

Corollary tree_code_complete : forall t, dep_ok (hheight t) (hprof 0 t) /\ kraft (hheight t) (hprof 0 t) = 2 ^ hheight t.
Proof.
  intros t. split.
  - intros e He. pose proof (hprof_dep 0 t e He). lia.
  - rewrite kraft_hprof; [f_equal; lia| lia | lia].
Qed.

Fixpoint hsplit (d : Z) (t : htree) (w a dd : Z) (p q : ent) : option htree :=
  match t with
  | HL w' a' => if (w' =? w) && (a' =? a) && (d =? dd) then Some (HN (HL (ew p) (ea p)) (HL (ew q) (ea q))) else None
  | HN l r =>
      match hsplit (d + 1) l w a dd p q with
      | Some l' => Some (HN l' r)
      | None => match hsplit (d + 1) r w a dd p q with Some r' => Some (HN l r') | None => None end
      end
  end.







Inductive hstep : list htree -> list htree -> Prop :=
  | HStep : forall F t1 t2 R,
      Permutation F (t1 :: t2 :: R) ->
      (forall t, In t R -> hw t1 <= hw t /\ hw t2 <= hw t) ->
      hstep F (HN t1 t2 :: R).

Inductive hbuild : list htree -> htree -> Prop :=
  | HB_one : forall T, hbuild [T] T
  | HB_step : forall F F' T, hstep F F' -> hbuild F' T -> hbuild F T.

Definition is_leaf (t : htree) : Prop := match t with HL _ _ => True | HN _ _ => False end.
Definition leaf_forest (F : list htree) : Prop := forall t, In t F -> is_leaf t.

Lemma leaf_forest_cost : forall F, leaf_forest F -> zsum (map hcost F) = 0.
Proof.
  induction F as [|t F IH]; intros HF; cbn; [reflexivity|].
  rewrite IH by (intros u Hu; apply HF; now right).
  specialize (HF t (or_introl eq_refl)). destruct t; [cbn; lia| destruct HF].
Qed.

Lemma perm_map_cons_inv : forall {A B} (f : A -> B) l x m,
  Permutation (map f l) (x :: m) -> exists e l', Permutation l (e :: l') /\ f e = x /\ Permutation (map f l') m.
Proof.
  intros A B f l x m P.
  assert (Hin : In x (map f l)) by (apply (Permutation_in _ (Permutation_sym P)); now left).
  apply in_map_iff in Hin. destruct Hin as (e & He & Hin).
  apply in_split in Hin. destruct Hin as (l1 & l2 & ->).
  exists e, (l1 ++ l2). split; [apply Permutation_sym; apply Permutation_middle|]. split; [exact He|].
  apply Permutation_cons_inv with (a := x).
  rewrite <- P. rewrite <- He. change (f e :: map f (l1 ++ l2)) with (map f (e :: (l1 ++ l2))).
  apply Permutation_map. apply Permutation_middle.
Qed.

Lemma hbuild_perm : forall F F' T, Permutation F F' -> hbuild F T -> hbuild F' T.
Proof.
  intros F F' T P HB. destruct HB as [T|F F1 T HS HB].
  - apply Permutation_length_1_inv in P. subst. apply HB_one.
  - apply HB_step with F1; [|exact HB]. destruct HS as [F t1 t2 R PF Hmin].
    apply HStep; [|exact Hmin]. rewrite <- P. exact PF.
Qed.

Lemma hbuild_nonnil : forall F T, hbuild F T -> F <> [].
Proof. intros F T HB. destruct HB; [discriminate|]. destruct H. intros ->. apply Permutation_nil in H. discriminate. Qed.

Theorem huffman_optimal_code : forall F T, hbuild F T ->
  forall H c, dep_ok H c -> kraft H c = 2 ^ H -> Permutation (map ew c) (map hw F) ->
  hcost T <= zsum (map hcost F) + ccost c.
Proof.
  intros F T HB. induction HB as [T|F F' T HS HB IH]; intros H c D K P.
  - cbn in P. destruct c as [|e [|e' c']]; [apply Permutation_nil in P; discriminate| |].
    2:{ apply Permutation_length in P. cbn in P. lia. }
    cbn. pose proof (D e (or_introl eq_refl)).
    assert (ed e = 0).
    { destruct (Z.eq_dec (ed e) 0); [assumption|]. exfalso. rewrite kraft_cons in K. unfold kraft in K. cbn [zsum map] in K.
      assert (2 ^ (H - ed e) < 2 ^ H) by (apply Z.pow_lt_mono_r; lia). lia. }
    unfold ccost. cbn. rewrite H1. lia.
  - destruct HS as [F t1 t2 R PF Hmin].
    rewrite (Permutation_map hw PF) in P. cbn in P.
    destruct (perm_map_cons_inv ew c _ _ P) as (e1 & c1 & P1 & W1 & Q1).
    destruct (perm_map_cons_inv ew c1 _ _ Q1) as (e2 & cr & P2 & W2 & Q2).
    assert (Pc : Permutation c (e1 :: e2 :: cr)) by (rewrite P1, P2; apply Permutation_refl).
    assert (Hm : forall e, In e cr -> ew e1 <= ew e /\ ew e2 <= ew e).
    { intros e He. assert (Hin : In (ew e) (map hw R)) by (apply (Permutation_in _ Q2); apply in_map; exact He).
      apply in_map_iff in Hin. destruct Hin as (t & <- & Ht). rewrite W1, W2. apply Hmin. exact Ht. }
    destruct (code_merge H c e1 e2 cr Pc D K Hm) as (d & r' & Hd & Pr & D' & K' & C').
    specialize (IH H _ D' K').
    cbn [map zsum hcost ew] in IH. rewrite W1, W2 in IH. rewrite ccost_cons in IH. cbn [ew ed] in IH.
    assert (Pm : Permutation (hw t1 + hw t2 :: map ew r') (hw t1 + hw t2 :: map hw R)).
    { apply perm_skip. rewrite Pr. exact Q2. }
    specialize (IH Pm).
    rewrite (zsum_map_perm hcost _ _ PF). cbn. rewrite ccost_cons in C'. cbn [ew ed] in C'. rewrite W1, W2 in C'. lia.
Qed.

Theorem huffman_optimal : forall F T, hbuild F T -> leaf_forest F ->
  forall H c, dep_ok H c -> kraft H c = 2 ^ H -> Permutation (map ew c) (map hw F) ->
  hcost T <= ccost c.
Proof.
  intros F T HB HL H c D K P. pose proof (huffman_optimal_code F T HB H c D K P). rewrite leaf_forest_cost in H0 by exact HL. lia.
Qed.


Theorem huffman_optimal_kraft : forall F T, hbuild F T -> leaf_forest F ->
  forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
  Permutation (map ew c) (map hw F) -> hcost T <= ccost c.
Proof.
  intros F T HB HL H c D K Wnn P.
  assert (Hne : c <> []).
  { intros ->. cbn in P. apply Permutation_nil in P. apply (hbuild_nonnil _ _ HB). destruct F; [reflexivity| discriminate]. }
  destruct (kraft_dominate H c Hne D K) as (c' & A & D' & K').
  pose proof (dominated_cost _ _ A Wnn).
  pose proof (huffman_optimal F T HB HL H c' D' K' ltac:(rewrite (dominated_map_w _ _ A); exact P)). lia.
Qed.

Definition wa (e : ent) : Z * Z := (ew e, ea e).

Lemma hprof_wa : forall d t, map wa (hprof d t) = map wa (hprof 0 t).
Proof.
  intros d t. revert d. induction t; intros d; cbn; [reflexivity|].
  rewrite !map_app, (IHt1 (d + 1)), (IHt2 (d + 1)), (IHt1 1), (IHt2 1). reflexivity.
Qed.

Lemma hbuild_leaves : forall F T, hbuild F T ->
  Permutation (map wa (hprof 0 T)) (flat_map (fun t => map wa (hprof 0 t)) F).
Proof.
  intros F T HB. induction HB as [T|F F' T HS HB IH].
  - cbn. rewrite app_nil_r. apply Permutation_refl.
  - destruct HS as [F t1 t2 R PF Hmin]. rewrite IH. rewrite (Permutation_flat_map (fun t => map wa (hprof 0 t)) PF). cbn.
    rewrite map_app, (hprof_wa 1 t1), (hprof_wa 1 t2), app_assoc. apply Permutation_refl.
Qed.

Lemma leaf_forest_flat : forall F, leaf_forest F ->
  flat_map (fun t => map wa (hprof 0 t)) F = map (fun t => (hw t, match t with HL _ a => a | HN _ _ => 0 end)) F.
Proof.
  induction F as [|t F IH]; intros HF; cbn; [reflexivity|].
  rewrite IH by (intros u Hu; apply HF; now right).
  specialize (HF t (or_introl eq_refl)). destruct t; [reflexivity| destruct HF].
Qed.

Corollary hbuild_leaves_w : forall F T, hbuild F T -> leaf_forest F ->
  Permutation (map ew (hprof 0 T)) (map hw F).
Proof.
  intros F T HB HL.
  pose proof (Permutation_map fst (hbuild_leaves F T HB)) as P.
  rewrite (leaf_forest_flat F HL), !map_map in P. cbn in P. exact P.
Qed.

