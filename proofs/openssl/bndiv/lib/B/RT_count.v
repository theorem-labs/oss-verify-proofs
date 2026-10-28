(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout R_sizeclass RT_iface RT_state RT_refillst RT_refillwf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint idx_from (f : ckst -> bool) (st : list ckst) (k : nat) : list nat :=
  match st with
  | [] => []
  | s :: st' => if f s then k :: idx_from f st' (S k) else idx_from f st' (S k)
  end.

Lemma idx_from_len : forall f st k, length (idx_from f st k) = length (filter f st).
Proof.
  intros f st. induction st as [|s st IH]; intros k; cbn [idx_from filter]; [reflexivity|].
  destruct (f s); cbn [length]; rewrite IH; reflexivity.
Qed.

Lemma idx_from_in : forall f st k i, In i (idx_from f st k) -> (k <= i)%nat /\ exists s, nth_error st (i - k) = Some s /\ f s = true.
Proof.
  intros f st. induction st as [|s st IH]; intros k i H; cbn [idx_from] in H; [destruct H|].
  destruct (f s) eqn:E.
  - destruct H as [<-|H].
    + split; [lia|]. exists s. rewrite Nat.sub_diag. split; [reflexivity | exact E].
    + destruct (IH (S k) i H) as (X1 & s' & X2 & X3). split; [lia|]. exists s'.
      replace (i - k)%nat with (S (i - S k)) by lia. split; [exact X2 | exact X3].
  - destruct (IH (S k) i H) as (X1 & s' & X2 & X3). split; [lia|]. exists s'.
    replace (i - k)%nat with (S (i - S k)) by lia. split; [exact X2 | exact X3].
Qed.

Lemma idx_from_nodup : forall f st k, NoDup (idx_from f st k).
Proof.
  intros f st. induction st as [|s st IH]; intros k; cbn [idx_from]; [constructor|].
  destruct (f s); [|apply IH]. constructor; [|apply IH]. intros H. destruct (idx_from_in f st (S k) k H) as (X & _). lia.
Qed.

Lemma idx_in : forall f st i, In i (idx_from f st 0) -> exists s, nth_error st i = Some s /\ f s = true.
Proof. intros f st i H. destruct (idx_from_in f st 0 i H) as (_ & s & X1 & X2). rewrite Nat.sub_0_r in X1. exists s. split; assumption. Qed.

Lemma count_inj : forall {A} (g : nat -> A) (l : list nat) (L : list A), NoDup l ->
  (forall i j, In i l -> In j l -> g i = g j -> i = j) -> (forall i, In i l -> In (g i) L) -> (length l <= length L)%nat.
Proof.
  intros A g l L ND INJ INC. rewrite <- (length_map g l). apply NoDup_incl_length.
  - apply NoDup_map_NoDup_ForallPairs; [|exact ND]. intros x y Hx Hy E. exact (INJ x y Hx Hy E).
  - intros x Hx. apply in_map_iff in Hx as (i & <- & Hi). exact (INC i Hi).
Qed.

Fixpoint wsum {A} (w : A -> Z) (l : list A) : Z := match l with [] => 0 | x :: l' => w x + wsum w l' end.

Lemma wsum_app : forall {A} (w : A -> Z) l1 l2, wsum w (l1 ++ l2) = wsum w l1 + wsum w l2.
Proof. intros A w l1 l2. induction l1 as [|x l1 IH]; cbn [wsum app]; [lia | rewrite IH; lia]. Qed.

Lemma wsum_nonneg : forall {A} (w : A -> Z) l, (forall x, In x l -> 0 <= w x) -> 0 <= wsum w l.
Proof.
  intros A w l. induction l as [|x l IH]; intros H; cbn [wsum]; [lia|].
  pose proof (H x (in_eq x l)). assert (0 <= wsum w l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

(* [comment removed for export] *)
Lemma wsum_sub : forall {A} (w : A -> Z) (l L : list A), NoDup l -> incl l L -> (forall x, In x L -> 0 <= w x) -> wsum w l <= wsum w L.
Proof.
  intros A w l. induction l as [|x l IH]; intros L ND INC POS; cbn [wsum].
  - exact (wsum_nonneg w L POS).
  - destruct (in_split x L (INC x (in_eq x l))) as (l1 & l2 & ->).
    apply NoDup_cons_iff in ND as (NI & ND).
    assert (INC' : incl l (l1 ++ l2)).
    { intros y Hy. pose proof (INC y (in_cons x y l Hy)) as Y. apply in_app_or in Y as [Y|[Y|Y]].
      - apply in_or_app. left. exact Y.
      - subst y. contradiction.
      - apply in_or_app. right. exact Y. }
    assert (POS' : forall z, In z (l1 ++ l2) -> 0 <= w z).
    { intros z Hz. apply POS. apply in_app_or in Hz as [Hz|Hz]; apply in_or_app; [left; exact Hz | right; right; exact Hz]. }
    pose proof (IH (l1 ++ l2) ND INC' POS') as X. rewrite wsum_app in X |- *. cbn [wsum]. lia.
Qed.

Lemma wsum_const : forall {A} (k : Z) (l : list A), wsum (fun _ => k) l = k * Z.of_nat (length l).
Proof. intros A k l. induction l as [|x l IH]; cbn [wsum length]; [lia | rewrite IH; lia]. Qed.

Lemma wsum_le : forall {A} (w v : A -> Z) l, (forall x, In x l -> w x <= v x) -> wsum w l <= wsum v l.
Proof.
  intros A w v l. induction l as [|x l IH]; intros H; cbn [wsum]; [lia|].
  pose proof (H x (in_eq x l)). assert (wsum w l <= wsum v l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma wsum_map : forall {A B} (w : B -> Z) (g : A -> B) l, wsum w (map g l) = wsum (fun x => w (g x)) l.
Proof. intros A B w g l. induction l as [|x l IH]; cbn [wsum map]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma st_partition : forall st, length st =
  (length (filter is_idle st) + length (filter is_alloc st) + length (filter is_quar st) + length (filter is_batch st))%nat.
Proof. induction st as [|s st IH]; [reflexivity|]. destruct s; cbn [filter is_idle is_alloc is_quar is_batch length]; lia. Qed.

(* [comment removed for export] *)
Lemma qents_w1 : forall (l : list (Z * Z)), wsum (fun e => 4 * snd e + 32) l = 4 * fold_right (fun e acc => snd e + acc) 0 l + 32 * Z.of_nat (length l).
Proof. intros l. induction l as [|e l IH]; cbn [wsum fold_right length]; [lia | rewrite IH; lia]. Qed.

Lemma qents_w : forall bs : list batch, Forall (fun b => (length (snd b) <= 1021)%nat) bs ->
  wsum (fun e => 4 * snd e + 32) (flat_map snd bs) <= 4 * qsum bs + 32672 * Z.of_nat (length bs).
Proof.
  intros bs. induction bs as [|b bs IH]; intros H; cbn [flat_map qsum fold_right length wsum]; [lia|].
  apply Forall_cons_iff in H as (H1 & H2). rewrite wsum_app, qents_w1. fold (qsum bs). specialize (IH H2).
  unfold qn. lia.
Qed.

Lemma wsum_fr : forall (l : list (Z * Z)), wsum snd l = fold_right (fun e acc => snd e + acc) 0 l.
Proof. intros l. induction l as [|e l IH]; cbn [wsum fold_right]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma qsum_flat : forall bs : list batch, qsum bs = wsum snd (flat_map snd bs).
Proof.
  intros bs. induction bs as [|b bs IH]; cbn [qsum fold_right flat_map wsum]; [reflexivity|].
  rewrite wsum_app. fold (qsum bs). rewrite IH. f_equal. unfold qn. symmetry. apply wsum_fr.
Qed.

Lemma qsum_app : forall b1 b2, qsum (b1 ++ b2) = qsum b1 + qsum b2.
Proof.
  intros b1 b2. unfold qsum. rewrite fold_right_app.
  generalize (fold_right (fun b acc => qn b + acc) 0 b2) as z. intros z.
  induction b1 as [|b b1 IH]; cbn [fold_right]; lia.
Qed.

(* [comment removed for export] *)
Lemma cs_quar_bound : forall n, 1 <= n -> rz_size n + n <= 65536 -> ClassSize (ClassID (needed n)) <= 4 * n + 32.
Proof.
  intros n H1 H2.
  assert (Hrz : 16 <= rz_size n) by (unfold rz_size, rz_log; repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia).
  (* [comment removed for export] *)
  assert (H : allb (fun n => (65536 <? rz_size n + n) || (ClassSize (ClassID (needed n)) <=? 4 * n + 32)) 1 65536 = true)
    by (vm_cast_no_check (eq_refl true)).
  pose proof (allb_ok _ _ _ H n ltac:(lia)) as E. cbv beta in E. apply orb_true_iff in E as [E|E]; [apply Z.ltb_lt in E; lia|].
  apply Z.leb_le in E. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Count.
Variables (Σ : rtsA) (c : Z) (i0 : nat).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hca : ca Σ c = [].
Hypothesis Hcnt : forall i n, nth_error (r_st (pr Σ c)) i = Some (CkQuar n) -> i <> i0 ->
  In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n) (qents Σ).
#[local] Notation st := (r_st (pr Σ c)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation S := (ClassSize c).

Lemma cn_regwf : reg_wf c (pr Σ c).
Proof using HW0 Hc. clear - HW0 Hc. pose proof HW0 as (_ & HR & _). exact (proj1 HR c Hc). Qed.

(* [comment removed for export] *)
Lemma cn_fit : forall i n, nth_error st i = Some (CkAlloc n) \/ nth_error st i = Some (CkQuar n) ->
  1 <= n /\ rz_size n + n <= S /\ c = ClassID (needed n).
Proof using HW0 Hc.
  intros i n H. pose proof cn_regwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  destruct H as [H|H]; pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ H)) as X; exact X.
Qed.

Lemma cn_rz : forall n, 1 <= n -> 16 <= rz_size n.
Proof. intros n _. unfold rz_size, rz_log. repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia. Qed.

Lemma cn_idle : rf_nf (pr Σ c) < MaxCount c / 2 -> Z.of_nat (length (filter is_idle st)) <= 7.
Proof using HW0 Hc Hca.
  intros Hsl. pose proof HW0 as (_ & (_ & _ & _ & _ & R5 & _) & _). pose proof (MaxCount_half c Hc) as HN.
  rewrite <- (idx_from_len is_idle st 0).
  assert (X : (length (idx_from is_idle st 0) <= length (r_fl (pr Σ c)))%nat).
  { apply (count_inj Z.of_nat); [apply idx_from_nodup | intros i j _ _ E; lia |].
    intros i Hi. destruct (idx_in is_idle st i Hi) as (s & Hs & Hf). destruct s; try discriminate Hf.
    pose proof (R5 c i Hc Hs) as Y. rewrite Hca in Y. exact Y. }
  unfold rf_nf in Hsl. clear - X HN Hsl. lia.
Qed.

Lemma cn_alloc : Z.of_nat (length (filter is_alloc st)) <= LIVE_MAX.
Proof using HW0 Hc.
  pose proof HW0 as (_ & _ & (V1 & _ & _ & V4 & _) & _). pose proof (ClassSize_range c Hc) as ((CS1 & _) & _).
  rewrite <- (idx_from_len is_alloc st 0).
  set (nsz := fun i => match nth_error st i with Some (CkAlloc n) => n | _ => 0 end).
  assert (X : (length (idx_from is_alloc st 0) <= length (live Σ))%nat).
  { apply (count_inj (fun i => (p_ubeg SB c i (nsz i), nsz i))); [apply idx_from_nodup | |].
    - intros i j Hi Hj E. injection E as E1 E2.
      destruct (idx_in is_alloc st i Hi) as (s & Hs & Hf). destruct s as [|ni|ni|]; try discriminate Hf.
      destruct (idx_in is_alloc st j Hj) as (s' & Hs' & Hf'). destruct s' as [|nj|nj|]; try discriminate Hf'.
      unfold nsz in E1. rewrite Hs, Hs' in E1. pose proof (cn_fit i ni (or_introl Hs)) as (F1 & F2 & _).
      pose proof (cn_fit j nj (or_introl Hs')) as (G1 & G2 & _). pose proof (cn_rz ni F1). pose proof (cn_rz nj G1).
      unfold p_ubeg, p_abeg in E1.
      destruct (Nat.lt_total i j) as [Hlt|[Heq|Hlt]]; [|exact Heq|]; exfalso; clear - E1 F1 F2 G1 G2 H H0 Hlt CS1; nia.
    - intros i Hi. destruct (idx_in is_alloc st i Hi) as (s & Hs & Hf). destruct s as [|ni|ni|]; try discriminate Hf.
      unfold nsz. rewrite Hs. exact (V4 c i ni Hc Hs). }
  clear - X V1. lia.
Qed.

Lemma cn_batch : S * Z.of_nat (length (filter is_batch st)) <= 8192 * Z.of_nat (length (ql Σ ++ qg Σ)).
Proof using HW0 Hc.
  pose proof HW0 as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8) & _).
  rewrite <- (idx_from_len is_batch st 0).
  destruct (idx_from is_batch st 0) as [|i l] eqn:El; [cbn [length]; lia|].
  assert (H24 : c = 24).
  { destruct (idx_in is_batch st i ltac:(rewrite El; left; reflexivity)) as (s & Hs & Hf). destruct s; try discriminate Hf.
    exact (proj1 (Q8 c i Hc Hs)). }
  rewrite <- El.
  assert (ES : S = 8192) by (rewrite H24; reflexivity).
  assert (X : (length (idx_from is_batch st 0) <= length (map fst (ql Σ ++ qg Σ)))%nat).
  { apply (count_inj (fun i => p_abeg SB 24 i)); [apply idx_from_nodup | |].
    - intros i1 j1 _ _ E. unfold p_abeg in E. change (ClassSize 24) with 8192 in E. clear - E. lia.
    - intros i1 Hi. destruct (idx_in is_batch st i1 Hi) as (s & Hs & Hf). destruct s; try discriminate Hf.
      exact (proj2 (Q8 c i1 Hc Hs)). }
  rewrite length_map in X. rewrite ES. apply Z.mul_le_mono_nonneg_l; [clear; lia | apply Nat2Z.inj_le; exact X].
Qed.

(* [comment removed for export] *)
Lemma cn_qent_pos : forall e, In e (qents Σ) -> 1 <= snd e.
Proof using HW0.
  pose proof HW0 as (_ & _ & _ & (_ & _ & _ & SF & _) & (_ & _ & _ & _ & _ & Q6 & _) & _).
  intros e He. pose proof (proj1 (Forall_forall _ _) Q6 e He) as [(c' & i' & Hc' & Hq & _)|(s & Hs & _ & Hn & _)].
  - pose proof HW0 as (_ & (R1 & _) & _). pose proof (R1 c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hq)) as (X & _). exact X.
  - pose proof (proj1 (Forall_forall _ _) SF s Hs) as (X & _). clear - X Hn. lia.
Qed.

Lemma cn_qsum : 0 <= qsum (ql Σ ++ qg Σ).
Proof using HW0.
  rewrite qsum_flat. apply wsum_nonneg. intros e He. pose proof (cn_qent_pos e He) as Y. clear - Y. lia.
Qed.

Lemma cn_quar : S * Z.of_nat (length (filter is_quar st)) <= S + 4 * qsum (ql Σ ++ qg Σ) + 32672 * Z.of_nat (length (ql Σ ++ qg Σ)).
Proof using HW0 Hc Hcnt.
  pose proof HW0 as (_ & _ & _ & _ & (_ & _ & _ & _ & Q5 & _) & _).
  pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & _).
  rewrite <- (idx_from_len is_quar st 0).
  set (l := idx_from is_quar st 0).
  set (l' := filter (fun i => negb (Nat.eqb i i0)) l).
  assert (Hll : (length l <= length l' + 1)%nat).
  { unfold l'. assert (NDl : NoDup l) by apply idx_from_nodup. clear - NDl. induction l as [|x l IH]; cbn [filter length]; [lia|].
    apply NoDup_cons_iff in NDl as (NI & ND). specialize (IH ND). destruct (Nat.eqb_spec x i0) as [->|Hne]; cbn [negb length].
    - assert (E : filter (fun i => negb (Nat.eqb i i0)) l = l).
      { apply forallb_filter_id. apply forallb_forall. intros y Hy. destruct (Nat.eqb_spec y i0); [subst; contradiction | reflexivity]. }
      rewrite E. lia.
    - lia. }
  set (nsz := fun i => match nth_error st i with Some (CkQuar n) => n | _ => 0 end).
  set (g := fun i => (p_abeg SB c i + rz_size (nsz i) - 16, nsz i)).
  assert (INl' : forall i, In i l' -> exists n, nth_error st i = Some (CkQuar n) /\ i <> i0 /\ nsz i = n).
  { intros i Hi. unfold l' in Hi. apply filter_In in Hi as (Hi & Hne). destruct (idx_in is_quar st i Hi) as (s & Hs & Hf).
    destruct s as [| |n|]; try discriminate Hf. exists n. split; [exact Hs|]. split; [intros E; subst; rewrite Nat.eqb_refl in Hne; discriminate Hne|].
    unfold nsz. rewrite Hs. reflexivity. }
  assert (NDg : NoDup (map g l')).
  { apply NoDup_map_NoDup_ForallPairs; [|apply NoDup_filter; apply idx_from_nodup].
    intros i j Hi Hj E. destruct (INl' i Hi) as (ni & Hsi & _ & Ei). destruct (INl' j Hj) as (nj & Hsj & _ & Ej).
    unfold g in E. rewrite Ei, Ej in E. injection E as E1 E2.
    pose proof (cn_fit i ni (or_intror Hsi)) as (F1 & F2 & _). pose proof (cn_fit j nj (or_intror Hsj)) as (G1 & G2 & _).
    pose proof (cn_rz ni F1). pose proof (cn_rz nj G1). unfold p_abeg in E1.
    destruct (Nat.lt_total i j) as [Hlt|[Heq|Hlt]]; [|exact Heq|]; exfalso; clear - E1 F1 F2 G1 G2 H H0 Hlt CS1; nia. }
  assert (INC : incl (map g l') (qents Σ)).
  { intros e He. apply in_map_iff in He as (i & <- & Hi). destruct (INl' i Hi) as (n & Hs & Hne & En).
    unfold g. rewrite En. exact (Hcnt i n Hs Hne). }
  assert (POS : forall e, In e (qents Σ) -> 0 <= 4 * snd e + 32) by (intros e He; pose proof (cn_qent_pos e He) as Y; clear - Y; lia).
  pose proof (wsum_sub (fun e => 4 * snd e + 32) _ _ NDg INC POS) as W1.
  rewrite wsum_map in W1. cbv beta in W1.
  assert (W2 : wsum (fun _ => S) l' <= wsum (fun i => 4 * snd (g i) + 32) l').
  { apply wsum_le. intros i Hi. destruct (INl' i Hi) as (n & Hs & _ & En). unfold g. cbn [snd]. rewrite En.
    pose proof (cn_fit i n (or_intror Hs)) as (F1 & F2 & F3). pose proof (cn_rz n F1).
    rewrite F3 at 1. apply cs_quar_bound; [exact F1 | clear - F2 CS2; lia]. }
  rewrite wsum_const in W2.
  pose proof (qents_w (ql Σ ++ qg Σ) Q5) as W3. unfold qents in W1.
  clear - Hll W1 W2 W3 CS1. nia.
Qed.

Theorem carved_room_gen : refill_room Σ c.
Proof using HW0 Hc Hca Hcnt.
  intros Hsl. pose proof HW0 as (_ & _ & _ & _ & (Q1 & Q2 & _) & _). unfold qbytes, QMAX_L, QMAX_G in Q1, Q2.
  pose proof (cn_idle Hsl) as X1. pose proof cn_alloc as X2. pose proof cn_batch as X3. pose proof cn_quar as X4. pose proof cn_qsum as X5.
  pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & _).
  rewrite (st_partition st), !Nat2Z.inj_add.
  rewrite length_app, Nat2Z.inj_add in X3. rewrite qsum_app, length_app, Nat2Z.inj_add in X4. rewrite qsum_app in X5.
  assert (Y1 : S * Z.of_nat (length (filter is_idle st)) <= 7 * 65536) by (clear - X1 CS1 CS2; nia).
  assert (Y2 : S * Z.of_nat (length (filter is_alloc st)) <= 2048 * 65536) by (clear - X2 CS1 CS2; unfold LIVE_MAX in X2; nia).
  clear - Y1 Y2 X3 X4 X5 Q1 Q2 CS2. nia.
Qed.

End Count.

Theorem carved_room : forall Σ c, rt_wf Σ -> 1 <= c <= 31 -> ca Σ c = [] -> refill_room Σ c.
Proof.
  intros Σ c HW Hc Hca. apply (proj1 (rt_wf_split Σ)) in HW as (HW0 & RC1 & _).
  apply (carved_room_gen Σ c (length (r_st (pr Σ c))) HW0 Hc Hca). intros i n Hi _. exact (RC1 c i n Hc Hi).
Qed.
