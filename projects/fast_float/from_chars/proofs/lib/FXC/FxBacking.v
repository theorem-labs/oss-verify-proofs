(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition init_sp_ok (h : VmMaps) : Prop := (sp_window_lo <= bv_unsigned (vm_init_sp h))%Z.
Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => (if P lo then 1 else 0) + zcount P (lo + 1) k
  end.

Lemma zcount_nonneg : forall P lo n, 0 <= zcount P lo n.
Proof. intros P lo n. revert lo. induction n; intros lo; cbn; [lia|]. destruct (P lo); specialize (IHn (lo+1)); lia. Qed.

Lemma zcount_le_len : forall P lo n, zcount P lo n <= Z.of_nat n.
Proof.
  intros P lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. rewrite Nat2Z.inj_succ. destruct (P lo); specialize (IHn (lo+1)); lia.
Qed.

Lemma zcount_mono : forall P Q lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = true -> Q x = true) ->
  zcount P lo n <= zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n; intros lo H; [cbn; lia|].
  cbn [zcount]. rewrite Nat2Z.inj_succ in H.
  assert (IH := IHn (lo + 1) ltac:(intros x Hx; apply H; lia)).
  destruct (P lo) eqn:EP.
  - rewrite (H lo ltac:(lia) EP). lia.
  - destruct (Q lo); lia.
Qed.

Lemma zcount_ext : forall P Q lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = Q x) ->
  zcount P lo n = zcount Q lo n.
Proof.
  intros P Q lo n H.
  pose proof (zcount_mono P Q lo n ltac:(intros x Hx HP; rewrite <- (H x Hx); exact HP)).
  pose proof (zcount_mono Q P lo n ltac:(intros x Hx HQ; rewrite (H x Hx); exact HQ)). lia.
Qed.

(* [comment removed for export] *)
Lemma zcount_or_le : forall P Q lo n,
  zcount (fun x => P x || Q x) lo n <= zcount P lo n + zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [orb]; lia.
Qed.

Lemma zcount_and_split : forall P Q lo n,
  zcount P lo n = zcount (fun x => P x && Q x) lo n + zcount (fun x => P x && negb (Q x)) lo n.
Proof.
  intros P Q lo n. revert lo. induction n; intros lo; [cbn; lia|].
  cbn [zcount]. specialize (IHn (lo + 1)). destruct (P lo), (Q lo); cbn [andb negb]; lia.
Qed.

Lemma zcount_const_false : forall lo n, zcount (fun _ => false) lo n = 0.
Proof. intros lo n. revert lo. induction n; intros; cbn; [lia|]. rewrite IHn. lia. Qed.

Lemma zcount_const_true : forall lo n, zcount (fun _ => true) lo n = Z.of_nat n.
Proof. intros lo n. revert lo. induction n; intros; [cbn; lia|]. cbn [zcount]. rewrite Nat2Z.inj_succ, IHn. lia. Qed.

Lemma zcount_false : forall P lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = false) -> zcount P lo n = 0.
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => false) lo n H). apply zcount_const_false. Qed.

Lemma zcount_true : forall P lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = true) -> zcount P lo n = Z.of_nat n.
Proof. intros P lo n H. rewrite (zcount_ext P (fun _ => true) lo n H). apply zcount_const_true. Qed.

(* [comment removed for export] *)
Lemma zcount_split : forall P lo n1 n2,
  zcount P lo (n1 + n2) = zcount P lo n1 + zcount P (lo + Z.of_nat n1) n2.
Proof.
  intros P lo n1 n2. revert lo. induction n1; intros lo.
  - cbn [zcount Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [zcount Nat.add]. rewrite IHn1, Nat2Z.inj_succ.
    replace (lo + 1 + Z.of_nat n1) with (lo + Z.succ (Z.of_nat n1)) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition B (p : word * word) : Z := bv_unsigned (fst p).
Definition S (p : word * word) : Z := bv_unsigned (snd p).

Definition in_rng (lo hi x : Z) : bool := (lo <=? x) && (x <? hi).
Definition in_iv (p : word * word) (x : Z) : bool := in_rng (B p) (B p + S p) x.

Definition covered (C : list (word * word)) (x : Z) : bool := existsb (fun c => in_iv c x) C.

(* [comment removed for export] *)
Definition iv_count (P : Z -> bool) (p : word * word) : Z := zcount P (B p) (Z.to_nat (S p)).

(* [comment removed for export] *)
Definition iv_wf (p : word * word) : Prop := B p + S p <= 2 ^ 64.

Lemma B_range : forall p, 0 <= B p < 2 ^ 64.
Proof. intros p. unfold B. exact (bv_unsigned_in_range _ (fst p)). Qed.
Lemma S_range : forall p, 0 <= S p < 2 ^ 64.
Proof. intros p. unfold S. exact (bv_unsigned_in_range _ (snd p)). Qed.

Lemma fg_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn -[Z.add]; [lia|rewrite IH; lia]. Qed.

Lemma maps_subtract_app : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|rewrite IH, app_assoc; reflexivity]. Qed.

Lemma maps_subtract_all_app : forall C l1 l2,
  maps_subtract_all (l1 ++ l2) C = maps_subtract_all l1 C ++ maps_subtract_all l2 C.
Proof.
  induction C as [|[a n] C IH]; intros; cbn; [reflexivity|].
  rewrite maps_subtract_app. apply IH.
Qed.

Lemma maps_subtract_all_nil_l : forall C, maps_subtract_all [] C = [].
Proof. induction C as [|[a n] C IH]; cbn; [reflexivity|exact IH]. Qed.

Lemma maps_subtract_all_cons_l : forall p l C,
  maps_subtract_all (p :: l) C = maps_subtract_all [p] C ++ maps_subtract_all l C.
Proof. intros. change (p :: l) with ([p] ++ l). apply maps_subtract_all_app. Qed.

(* [comment removed for export] *)
Fixpoint sum_count (P : Z -> bool) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | q :: r => iv_count P q + sum_count P r
  end.

Lemma sum_count_app : forall P l1 l2, sum_count P (l1 ++ l2) = sum_count P l1 + sum_count P l2.
Proof. induction l1; intros; cbn -[Z.add]; [lia|rewrite IHl1; lia]. Qed.

Lemma sum_count_nonneg : forall P l, 0 <= sum_count P l.
Proof. induction l; cbn -[Z.add]; [lia|]. pose proof (zcount_nonneg P (B a) (Z.to_nat (S a))). unfold iv_count. lia. Qed.

Lemma sum_count_mono : forall P Q l,
  (forall x, P x = true -> Q x = true) -> sum_count P l <= sum_count Q l.
Proof.
  intros P Q l H. induction l; cbn -[Z.add]; [lia|].
  pose proof (zcount_mono P Q (B a) (Z.to_nat (S a)) ltac:(intros; auto)). unfold iv_count. lia.
Qed.

Lemma sum_count_ext : forall P Q l,
  (forall x, P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l; cbn -[Z.add]; [lia|].
  unfold iv_count. rewrite (zcount_ext P Q) by (intros; apply H). lia.
Qed.

Lemma sum_count_or_le : forall P Q l,
  sum_count (fun x => P x || Q x) l <= sum_count P l + sum_count Q l.
Proof.
  intros P Q l. induction l; cbn -[Z.add]; [lia|].
  pose proof (zcount_or_le P Q (B a) (Z.to_nat (S a))). unfold iv_count in *. lia.
Qed.

Lemma live_bytes_sum_count : forall l, live_bytes l = sum_count (fun _ => true) l.
Proof.
  induction l as [|[b s] l IH]; cbn -[Z.add]; [lia|].
  unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_const_true, IH.
  pose proof (bv_unsigned_in_range 64 s). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition ivs_wf (l : list (word * word)) : Prop := forall q, In q l -> iv_wf q.

Lemma ivs_wf_nil : ivs_wf [].
Proof. intros q []. Qed.
Lemma ivs_wf_cons : forall p l, iv_wf p -> ivs_wf l -> ivs_wf (p :: l).
Proof. intros p l Hp Hl q [<-|Hq]; auto. Qed.
Lemma ivs_wf_cons_inv : forall p l, ivs_wf (p :: l) -> iv_wf p /\ ivs_wf l.
Proof. intros p l H. split; [apply H; now left|intros q Hq; apply H; now right]. Qed.
Lemma ivs_wf_app : forall l1 l2, ivs_wf l1 -> ivs_wf l2 -> ivs_wf (l1 ++ l2).
Proof. intros l1 l2 H1 H2 q Hq. apply in_app_iff in Hq as [Hq|Hq]; auto. Qed.
Lemma ivs_wf_app_inv : forall l1 l2, ivs_wf (l1 ++ l2) -> ivs_wf l1 /\ ivs_wf l2.
Proof. intros l1 l2 H. split; intros q Hq; apply H; apply in_app_iff; auto. Qed.
Lemma ivs_wf_filter : forall f l, ivs_wf l -> ivs_wf (List.filter f l).
Proof. intros f l H q Hq. apply filter_In in Hq as [Hq _]. auto. Qed.
Lemma iv_wf_intro : forall (a n : word),
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> iv_wf (a, n).
Proof. intros a n H. exact H. Qed.

(* [comment removed for export] *)
Ltac in_rng_tf :=
  intros x Hx; unfold in_rng;
  first [ rewrite (proj2 (Z.leb_gt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r; reflexivity]
        | rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity]
        | rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; cbn [andb negb]; first [reflexivity | rewrite ?andb_true_r, ?andb_false_r; reflexivity] ].

Lemma count_outside_gen : forall P lo hi A Z_,
  0 <= Z_ -> lo <= hi ->
  zcount (fun x => P x && negb (in_rng lo hi x)) A (Z.to_nat Z_)
  = (if A <? lo then zcount P A (Z.to_nat (Z.min Z_ (lo - A))) else 0)
    + (if hi <? A + Z_ then zcount P (Z.max A hi) (Z.to_nat (A + Z_ - Z.max A hi)) else 0).
Proof.
  intros P lo hi A Z_ HZ Hlh.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er.
  - destruct (Z.le_gt_cases (lo - A) Z_) as [H1|H1]; [|lia].
    replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + (Z.to_nat (hi - lo) + Z.to_nat (A + Z_ - hi)))%nat by lia.
    rewrite !zcount_split.
    rewrite (zcount_ext _ P A) by in_rng_tf.
    rewrite (zcount_false _ (A + _)) by in_rng_tf.
    rewrite (zcount_ext _ P (A + _ + _)) by in_rng_tf.
    rewrite (Z.min_r Z_ (lo - A) H1), (Z.max_r A hi) by lia.
    rewrite !Z2Nat.id by lia.
    replace (A + (lo - A) + (hi - lo)) with hi by lia.
    replace (A + Z_ - hi) with (A + Z_ - hi) by lia. lia.
  - destruct (Z.le_gt_cases (A + Z_) lo) as [H1|H1].
    + rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.min_l Z_ (lo - A)) by lia. lia.
    + replace (Z.to_nat Z_) with (Z.to_nat (lo - A) + Z.to_nat (A + Z_ - lo))%nat by lia.
      rewrite zcount_split.
      rewrite (zcount_ext _ P A) by in_rng_tf.
      rewrite (zcount_false _ (A + _)) by in_rng_tf.
      rewrite (Z.min_r Z_ (lo - A)) by lia. lia.
  - destruct (Z.le_gt_cases hi A) as [H1|H1].
    + rewrite (zcount_ext _ P) by in_rng_tf. rewrite (Z.max_l A hi) by lia.
      replace (A + Z_ - A) with Z_ by lia. lia.
    + replace (Z.to_nat Z_) with (Z.to_nat (hi - A) + Z.to_nat (A + Z_ - hi))%nat by lia.
      rewrite zcount_split.
      rewrite (zcount_false _ A) by in_rng_tf.
      rewrite (zcount_ext _ P (A + _)) by in_rng_tf.
      rewrite (Z.max_r A hi) by lia. rewrite !Z2Nat.id by lia.
      replace (A + (hi - A)) with hi by lia. lia.
  - rewrite zcount_false by in_rng_tf. lia.
Qed.

Lemma count_inside : forall lo hi A Z_,
  0 <= Z_ -> lo <= hi ->
  zcount (in_rng lo hi) A (Z.to_nat Z_) <= hi - lo.
Proof.
  intros lo hi A Z_ HZ Hlh.
  pose proof (zcount_and_split (fun _ => true) (in_rng lo hi) A (Z.to_nat Z_)) as Hsplit.
  cbn [andb] in Hsplit. rewrite zcount_const_true, Z2Nat.id in Hsplit by lia.
  rewrite (zcount_ext (fun x => negb (in_rng lo hi x)) (fun x => true && negb (in_rng lo hi x))) in Hsplit by reflexivity.
  rewrite (count_outside_gen (fun _ => true) lo hi A Z_ HZ Hlh) in Hsplit.
  rewrite !zcount_const_true in Hsplit.
  rewrite (zcount_ext (fun x => in_rng lo hi x) (in_rng lo hi)) in Hsplit by reflexivity.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El, Er; rewrite ?Z2Nat.id in Hsplit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sem : forall a sz lo hi,
  iv_wf (a, sz) -> lo <= hi ->
  (forall q, In q (iv_subtract a sz lo hi) -> iv_wf q)
  /\ (forall P, sum_count P (iv_subtract a sz lo hi)
        = iv_count (fun x => P x && negb (in_rng lo hi x)) (a, sz))
  /\ (forall x, covered (iv_subtract a sz lo hi) x = in_iv (a, sz) x && negb (in_rng lo hi x)).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, iv_count, B, S in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  unfold bv_modulus in Ha, Hs.
  set (A := bv_unsigned a) in *. set (Z_ := bv_unsigned sz) in *.
  unfold iv_subtract. cbv zeta. fold A. fold Z_.
  destruct (A <? lo) eqn:El; destruct (hi <? A + Z_) eqn:Er;
    pose proof El as El'; pose proof Er as Er';
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in El', Er'; cbn [app].
  - (* [comment removed for export] *)
    assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
    assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
    assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[<-|[]]]; cbn [fst snd]; rewrite ?E1, ?E2, ?E3; lia.
    + intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. fold A. rewrite E1, E2, E3.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, E2, E3, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite orb_true_iff, !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    assert (E1 : bv_unsigned (Z_to_bv 64 (Z.min Z_ (lo - A))) = Z.min Z_ (lo - A)) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[]]; cbn [fst snd]; rewrite ?E1; lia.
    + intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. fold A. rewrite E1.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E1, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    assert (E2 : bv_unsigned (Z_to_bv 64 (Z.max A hi)) = Z.max A hi) by (apply fg_lit; lia).
    assert (E3 : bv_unsigned (Z_to_bv 64 (A + Z_ - Z.max A hi)) = A + Z_ - Z.max A hi) by (apply fg_lit; lia).
    split; [|split].
    + intros q [<-|[]]; cbn [fst snd]; rewrite ?E2, ?E3; lia.
    + intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd]. rewrite E2, E3.
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_. rewrite E2, E3, orb_false_r.
      apply Bool.eq_true_iff_eq.
      rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_le, !Z.ltb_lt, Z.leb_gt, Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    split; [|split].
    + intros q [].
    + intros P. cbn [sum_count]. unfold iv_count, B, S. cbn [fst snd].
      rewrite (count_outside_gen P lo hi A Z_) by lia. rewrite El, Er. lia.
    + intros x. unfold covered, in_iv, in_rng, B, S. cbn [existsb fst snd]. fold A. fold Z_.
      symmetry. apply andb_false_iff.
      destruct (Z.lt_ge_cases x A); [left|]. { apply andb_false_iff. left. apply Z.leb_gt. lia. }
      destruct (Z.lt_ge_cases x (A + Z_)); [right|left].
      { apply negb_false_iff. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maps_subtract_sem : forall l lo hi,
  ivs_wf l -> lo <= hi ->
  ivs_wf (maps_subtract l lo hi)
  /\ (forall P, sum_count P (maps_subtract l lo hi)
        = sum_count (fun x => P x && negb (in_rng lo hi x)) l)
  /\ (forall x, covered (maps_subtract l lo hi) x = covered l x && negb (in_rng lo hi x)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hwf Hlh.
  - cbn. split; [apply ivs_wf_nil|]. split; [reflexivity|]. intros; reflexivity.
  - apply ivs_wf_cons_inv in Hwf as [Ha Hl].
    destruct (IH lo hi Hl Hlh) as (W & Sm & Cv).
    destruct (iv_subtract_sem a sz lo hi Ha Hlh) as (W1 & Sm1 & Cv1).
    cbn [maps_subtract]. split; [|split].
    + apply ivs_wf_app; [intros q Hq; apply W1; exact Hq|exact W].
    + intros P. rewrite sum_count_app, Sm1, Sm. reflexivity.
    + intros x. unfold covered. rewrite existsb_app. fold (covered (iv_subtract a sz lo hi) x).
      fold (covered (maps_subtract l lo hi) x). fold (covered l x). rewrite Cv1, Cv.
      cbn [existsb]. fold (covered l x). destruct (in_iv (a, sz) x), (covered l x), (in_rng lo hi x); reflexivity.
Qed.

Lemma maps_subtract_wf : forall l lo hi, ivs_wf l -> lo <= hi -> ivs_wf (maps_subtract l lo hi).
Proof. intros. apply maps_subtract_sem; assumption. Qed.

Lemma covered_app : forall l1 l2 x, covered (l1 ++ l2) x = covered l1 x || covered l2 x.
Proof. intros. unfold covered. apply existsb_app. Qed.

Lemma maps_subtract_all_app_cuts : forall l C1 C2,
  maps_subtract_all l (C1 ++ C2) = maps_subtract_all (maps_subtract_all l C1) C2.
Proof. intros l C1; revert l; induction C1 as [|[a n] C1 IH]; intros; cbn; [reflexivity|apply IH]. Qed.

(* [comment removed for export] *)
Theorem live_msa : forall C l,
  ivs_wf l ->
  live_bytes (maps_subtract_all l C) = sum_count (fun x => negb (covered C x)) l
  /\ ivs_wf (maps_subtract_all l C).
Proof.
  induction C as [|[a n] C IH]; intros l Hwf.
  - cbn [maps_subtract_all covered existsb negb]. split; [apply live_bytes_sum_count|exact Hwf].
  - cbn [maps_subtract_all].
    pose proof (bv_unsigned_in_range 64 n) as Hn.
    destruct (maps_subtract_sem l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hwf ltac:(lia)) as (W & Sm & Cv).
    destruct (IH _ W) as [Hl Hw]. split; [|exact Hw].
    rewrite Hl, Sm. apply sum_count_ext. intros x.
    unfold covered at 2. cbn [existsb]. fold (covered C x). unfold in_iv, B, S. cbn [fst snd].
    destruct (covered C x), (in_rng _ _ x); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma m_vmmaps_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h. Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_with_vm_backing : forall l p m, m_vmmaps (with_vm_backing l p m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vm_backing : forall l p m, m_vm_lazy (with_vm_backing l p m) = l. Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vm_backing : forall l p m, m_vm_materialized (with_vm_backing l p m) = p.
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_forget_range : forall lo hi m,
  m_vm_lazy (vm_forget_range lo hi m) = maps_subtract (m_vm_lazy m) lo hi. Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_forget_range : forall lo hi m,
  m_vm_materialized (vm_forget_range lo hi m) = List.filter (page_outside_range lo hi) (m_vm_materialized m).
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy : forall a n m, m_vmmaps (vm_add_lazy a n m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vm_lazy_vm_add_lazy : forall a n m,
  m_vm_lazy (vm_add_lazy a n m) = lazy_interior a n ++ m_vm_lazy m. Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_add_lazy : forall a n m,
  m_vm_materialized (vm_add_lazy a n m) = m_vm_materialized m. Proof. reflexivity. Qed.

Ltac model_proj :=
  rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
          ?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
          ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps.

(* [comment removed for export] *)
Definition model_ivs_wf (m : Model) : Prop :=
  ivs_wf (vm_maps (m_vmmaps m)) /\ ivs_wf (vm_noaccess (m_vmmaps m)) /\ ivs_wf (m_vm_lazy m)
  /\ init_sp_ok (m_vmmaps m).  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition overlap_sum (l : list (word * word)) (lo hi : Z) : Z := sum_count (in_rng lo hi) l.

Lemma overlap_sum_app : forall l1 l2 lo hi,
  overlap_sum (l1 ++ l2) lo hi = overlap_sum l1 lo hi + overlap_sum l2 lo hi.
Proof. intros. apply sum_count_app. Qed.

Lemma overlap_sum_cons : forall p l lo hi,
  overlap_sum (p :: l) lo hi = iv_count (in_rng lo hi) p + overlap_sum l lo hi.
Proof. reflexivity. Qed.

Lemma overlap_sum_nil : forall lo hi, overlap_sum [] lo hi = 0.
Proof. reflexivity. Qed.

Lemma iv_count_in_rng_le : forall p lo hi, lo <= hi -> iv_count (in_rng lo hi) p <= hi - lo.
Proof. intros p lo hi H. unfold iv_count. apply count_inside; [pose proof (S_range p); lia|exact H]. Qed.

Lemma iv_count_in_rng_disjoint : forall p lo hi,
  (B p + S p <= lo \/ hi <= B p) -> iv_count (in_rng lo hi) p = 0.
Proof.
  intros p lo hi H. unfold iv_count. apply zcount_false. intros x Hx.
  pose proof (S_range p). rewrite Z2Nat.id in Hx by lia.
  unfold in_rng. apply andb_false_iff. destruct H; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_region_free : forall l (lo n : word),
  region_free l lo n = true ->
  overlap_sum l (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) = 0.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free] in H. apply andb_true_iff in H as [H1 H2].
  rewrite overlap_sum_cons, (IH _ _ H2), iv_count_in_rng_disjoint; [lia|].
  apply negb_true_iff in H1. unfold iv_overlap in H1. unfold B, S. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_single_le : forall p lo hi, lo <= hi -> overlap_sum [p] lo hi <= hi - lo.
Proof. intros. rewrite overlap_sum_cons, overlap_sum_nil. pose proof (iv_count_in_rng_le p lo hi H). lia. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_sem_maps : forall m,
  ivs_wf (vm_maps (m_vmmaps m)) ->
  vm_backing_used m
  = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m))
    + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof.
  intros m Wm. unfold vm_backing_used, vm_backed_maps.
  rewrite <- maps_subtract_all_app_cuts. rewrite (proj1 (live_msa _ _ Wm)). reflexivity.
Qed.
Lemma vm_backing_used_sem : forall m,
  model_ivs_wf m ->
  vm_backing_used m
  = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m))
    + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof. intros m (Wm & _). apply vm_backing_used_sem_maps; exact Wm. Qed.

Lemma filter_length_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. induction l; cbn; [lia|]. destruct (f a); cbn; lia. Qed.

(* [comment removed for export] *)
Theorem backing_forget_commit_le : forall m h' lo hi,
  model_ivs_wf m -> lo <= hi ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  vm_backing_used (vm_forget_range lo hi (with_vmmaps h' m))
  <= vm_backing_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi.
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_forget_range lo hi (with_vmmaps h' m))))).
  { model_proj. rewrite Hmaps. exact Wm. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  unfold overlap_sum.
  eapply Z.le_trans.
  { apply Z.add_le_mono_r.
    apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
    intros x. rewrite !covered_app, Cn, Cl.
    destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
  pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
                (vm_maps (m_vmmaps m))).
  unfold page_size in *. lia.
Qed.

(* [comment removed for export] *)
Theorem backing_mprotect_le : forall m h' lo hi,
  model_ivs_wf m -> lo <= hi ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  vm_backing_used (with_vmmaps h' m)
  <= vm_backing_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi.
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (with_vmmaps h' m)))).
  { model_proj. rewrite Hmaps. exact Wm. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  unfold overlap_sum.
  eapply Z.le_trans.
  { apply Z.add_le_mono_r.
    apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
    intros x. rewrite !covered_app, Cn.
    destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
  pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi)
                (vm_maps (m_vmmaps m))).
  unfold page_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_interior_aligned : forall (a n : word),
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hpos Hwf. unfold lazy_interior, page_size in *.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn.
  unfold bv_modulus in Ra, Rn.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Da.
  pose proof (Z.div_mod (bv_unsigned n) 4096 ltac:(lia)) as Dn.
  rewrite Ha in Da. rewrite Hn in Dn.
  set (qa := bv_unsigned a / 4096) in *. set (qn := bv_unsigned n / 4096) in *.
  assert (E1 : (bv_unsigned a + 4096 - 1) / 4096 * 4096 = bv_unsigned a).
  { rewrite Da. replace (4096 * qa + 0 + 4096 - 1) with (qa * 4096 + 4095) by lia.
    rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (E2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 = bv_unsigned a + bv_unsigned n).
  { rewrite Da, Dn. replace (4096 * qa + 0 + (4096 * qn + 0)) with ((qa + qn) * 4096) by lia.
    rewrite Z.div_mul by lia. lia. }
  cbv zeta. rewrite E1, E2.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  f_equal. f_equal.
  - apply bv_eq. rewrite fg_lit by lia. reflexivity.
  - apply bv_eq. rewrite fg_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem backing_recommit_lazy_le : forall m h' (a n : word),
  model_ivs_wf m ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  vm_backing_used (vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)))
  <= vm_backing_used m.
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
  assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))))).
  { model_proj. rewrite Hmaps. exact Wm. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna, Hli.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  apply Z.add_le_mono; [|unfold page_size; nia].
  apply sum_count_mono. intros x Hx.
  rewrite covered_app in Hx. rewrite covered_app in Hx. rewrite Cn, Cl in Hx. rewrite covered_app.
  revert Hx. unfold covered at 2. cbn [existsb]. unfold in_iv, B, S. cbn [fst snd]. fold lo. fold hi.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vm_limit_with_vmmaps : forall h m, vm_limit (m_vmmaps (with_vmmaps h m)) = vm_limit h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem mmap_fixed_rw_budget_ok_commit_intro : forall flags m (addr n : word),
  mmap_noreserve_b flags = false ->
  model_ivs_wf m ->
  vm_backing_used m
    + overlap_sum (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    <= vm_limit (m_vmmaps m) ->
  mmap_fixed_rw_budget_ok flags m addr n = true.
Proof.
  intros flags m addr n Hnr Hwf Hb.
  unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
  rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
  pose proof (bv_unsigned_in_range 64 n).
  pose proof (backing_forget_commit_le m (mmap_fixed_rw_next (m_vmmaps m) addr n)
                (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl).
  unfold mmap_fixed_rw_next in *. lia.
Qed.

(* [comment removed for export] *)
Theorem mmap_fixed_rw_budget_ok_recommit_intro : forall flags m (addr n : word),
  mmap_noreserve_b flags = true ->
  model_ivs_wf m ->
  bv_unsigned addr mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned addr + bv_unsigned n <= 2 ^ 64 ->
  vm_backing_used m <= vm_limit (m_vmmaps m) ->
  mmap_fixed_rw_budget_ok flags m addr n = true.
Proof.
  intros flags m addr n Hnr Hwf Hal Hnl Hpos Hend Hb.
  unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit, with_mmap_replacement, with_mmap_backing.
  rewrite Hnr. apply Z.leb_le. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit].
  pose proof (backing_recommit_lazy_le m (mmap_fixed_rw_next (m_vmmaps m) addr n) addr n
                Hwf Hal Hnl Hpos Hend eq_refl eq_refl).
  unfold mmap_fixed_rw_next in *. lia.
Qed.

(* [comment removed for export] *)
Theorem mprotect_budget_ok_intro_gen : forall m (addr n : word),
  model_ivs_wf m ->
  vm_backing_used m
    + overlap_sum (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hwf Hb.
  unfold mprotect_budget_ok, vm_backing_within_limit, mprotect_model_next.
  apply Z.leb_le. model_proj. cbn [vm_limit].
  pose proof (bv_unsigned_in_range 64 n).
  pose proof (backing_mprotect_le m
                (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)))
                (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hwf ltac:(lia) eq_refl eq_refl) as Hle.
  cbv zeta in Hle. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lazy_interior_wf : forall a n, bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> ivs_wf (lazy_interior a n).
Proof.
  intros a n H. unfold lazy_interior. cbv zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
  unfold page_size.
  set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096). set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096).
  assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
  { subst hi'. pose proof (Z.mul_div_le (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). lia. }
  assert (Hlo : 0 <= lo').
  { subst lo'. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. }
  destruct (lo' <? hi') eqn:E; [|apply ivs_wf_nil].
  apply Z.ltb_lt in E. apply ivs_wf_cons; [|apply ivs_wf_nil].
  unfold iv_wf, B, S. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.

Lemma model_ivs_wf_intro : forall m,
  ivs_wf (vm_maps (m_vmmaps m)) -> ivs_wf (vm_noaccess (m_vmmaps m)) -> ivs_wf (m_vm_lazy m) ->
  init_sp_ok (m_vmmaps m) -> model_ivs_wf m.
Proof. intros; repeat split; assumption. Qed.

Lemma model_ivs_wf_with_vmmaps : forall h m,
  model_ivs_wf m -> ivs_wf (vm_maps h) -> ivs_wf (vm_noaccess h) -> vm_init_sp h = vm_init_sp (m_vmmaps m) ->
  model_ivs_wf (with_vmmaps h m).
Proof. intros h m (_ & _ & Wl & Wsp) Hm Hn Hsp. unfold model_ivs_wf. model_proj. repeat split; try assumption. eapply init_sp_ok_same; eassumption. Qed.

Lemma model_ivs_wf_vm_forget_range : forall lo hi m,
  lo <= hi -> model_ivs_wf m -> model_ivs_wf (vm_forget_range lo hi m).
Proof.
  intros lo hi m Hlh (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. model_proj.
  repeat split; try assumption. apply maps_subtract_wf; assumption.
Qed.

Lemma model_ivs_wf_vm_add_lazy : forall a n m,
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf m -> model_ivs_wf (vm_add_lazy a n m).
Proof.
  intros a n m H (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. model_proj.
  repeat split; try assumption. apply ivs_wf_app; [apply lazy_interior_wf; exact H|exact Wl].
Qed.

Lemma model_ivs_wf_with_mmap_backing : forall flags a n m,
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf m -> model_ivs_wf (with_mmap_backing flags a n m).
Proof.
  intros flags a n m H Hwf. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); [apply model_ivs_wf_vm_add_lazy; assumption|exact Hwf].
Qed.

Lemma model_ivs_wf_with_mmap_replacement : forall flags a n m,
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf m -> model_ivs_wf (with_mmap_replacement flags a n m).
Proof.
  intros flags a n m H Hwf. unfold with_mmap_replacement.
  apply model_ivs_wf_with_mmap_backing; [exact H|].
  apply model_ivs_wf_vm_forget_range; [pose proof (bv_unsigned_in_range 64 n); lia|exact Hwf].
Qed.

(* [comment removed for export] *)
Lemma model_ivs_wf_init : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> model_ivs_wf (init_model reserved brk0 mbase sp lim inp).
Proof. intros. repeat split; try (intros q Hq; cbn in Hq; contradiction). apply init_sp_ok_init_model; assumption. Qed.
