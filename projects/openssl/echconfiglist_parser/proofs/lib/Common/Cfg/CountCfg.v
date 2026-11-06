(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Cnt.

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

Lemma cnt_live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn -[Z.add]; [lia|rewrite IH; lia]. Qed.

Lemma cnt_maps_subtract_app : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|rewrite IH, app_assoc; reflexivity]. Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sum_count_msa : forall C l P,
  ivs_wf l ->
  sum_count P (maps_subtract_all l C) = sum_count (fun x => P x && negb (covered C x)) l
  /\ ivs_wf (maps_subtract_all l C).
Proof.
  induction C as [|[a n] C IH]; intros l P Hwf.
  - cbn [maps_subtract_all covered existsb negb]. split; [|exact Hwf].
    apply sum_count_ext. intros x. rewrite andb_true_r. reflexivity.
  - cbn [maps_subtract_all].
    pose proof (bv_unsigned_in_range 64 n) as Hn.
    destruct (maps_subtract_sem l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hwf ltac:(lia)) as (W & Sm & Cv).
    destruct (IH _ P W) as [Hl Hw]. split; [|exact Hw].
    rewrite Hl, Sm. apply sum_count_ext. intros x.
    unfold covered at 2. cbn [existsb]. fold (covered C x). unfold in_iv, B, S. cbn [fst snd].
    destruct (P x), (covered C x), (in_rng _ _ x); reflexivity.
Qed.

Definition eu (maps na lazy : list (word * word)) : Z :=
  live_bytes (maps_subtract_all (maps_subtract_all maps na) lazy).

Lemma eager_used_eu : forall m,
  eager_used m = eu (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m).
Proof. reflexivity. Qed.

Definition eu_pred (na lazy : list (word * word)) (x : Z) : bool :=
  negb (covered lazy x) && negb (covered na x).

Theorem eu_sem : forall maps na lazy,
  ivs_wf maps -> eu maps na lazy = sum_count (eu_pred na lazy) maps.
Proof.
  intros maps na lazy Hwf. unfold eu.
  destruct (sum_count_msa na maps (fun x => negb (covered lazy x)) Hwf) as [E1 W1].
  destruct (live_msa lazy _ W1) as [E2 _]. rewrite E2, E1. reflexivity.
Qed.

Lemma iv_count_le_S : forall P p, iv_count P p <= S p.
Proof.
  intros P p. unfold iv_count. pose proof (zcount_le_len P (B p) (Z.to_nat (S p))) as H.
  pose proof (S_range p). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma iv_count_nonneg : forall P p, 0 <= iv_count P p.
Proof. intros P p. unfold iv_count. apply zcount_nonneg. Qed.

(* [comment removed for export] *)
Theorem eu_grant_le : forall maps na lazy lz p,
  ivs_wf (p :: maps) ->
  eu (p :: maps) na (lz ++ lazy) <= eu maps na lazy + S p.
Proof.
  intros maps na lazy lz p Hwf. pose proof (proj2 (ivs_wf_cons_inv _ _ Hwf)) as Hwf0.
  rewrite (eu_sem _ _ _ Hwf), (eu_sem _ _ _ Hwf0). cbn [sum_count].
  pose proof (iv_count_le_S (eu_pred na (lz ++ lazy)) p) as H1.
  pose proof (sum_count_mono (eu_pred na (lz ++ lazy)) (eu_pred na lazy) maps) as H2.
  assert (Hm : forall x, eu_pred na (lz ++ lazy) x = true -> eu_pred na lazy x = true).
  { intros x. unfold eu_pred. rewrite covered_app. destruct (covered lz x), (covered lazy x), (covered na x); cbn; congruence. }
  specialize (H2 Hm). lia.
Qed.

(* [comment removed for export] *)
Theorem eu_grant_nr_le : forall maps na lazy p,
  ivs_wf (p :: maps) ->
  eu (p :: maps) na (p :: lazy) <= eu maps na lazy.
Proof.
  intros maps na lazy p Hwf. pose proof (proj2 (ivs_wf_cons_inv _ _ Hwf)) as Hwf0.
  rewrite (eu_sem _ _ _ Hwf), (eu_sem _ _ _ Hwf0). cbn [sum_count].
  assert (H0 : iv_count (eu_pred na (p :: lazy)) p = 0).
  { unfold iv_count. apply zcount_false. intros x Hx. pose proof (S_range p) as HS.
    rewrite Z2Nat.id in Hx by lia. unfold eu_pred, covered. cbn [existsb].
    assert (E : in_iv p x = true).
    { unfold in_iv, in_rng. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite E. reflexivity. }
  pose proof (sum_count_mono (eu_pred na (p :: lazy)) (eu_pred na lazy) maps) as H2.
  assert (Hm : forall x, eu_pred na (p :: lazy) x = true -> eu_pred na lazy x = true).
  { intros x. unfold eu_pred, covered. cbn [existsb]. fold (covered lazy x).
    destruct (in_iv p x), (covered lazy x), (covered na x); cbn; congruence. }
  specialize (H2 Hm). lia.
Qed.

(* [comment removed for export] *)
Theorem eu_unmap_le : forall maps na lazy (a n : word),
  ivs_wf maps -> ivs_wf na -> ivs_wf lazy ->
  pw_disj maps -> In (a, n) maps ->
  let lo := bv_unsigned a in let hi := bv_unsigned a + bv_unsigned n in
  eu (map_remove maps a) (maps_subtract na lo hi) (maps_subtract lazy lo hi) <= eu maps na lazy.
Proof.
  intros maps na lazy a n Hwf Hwna Hwlz Hpw Hin lo hi.
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  assert (Hle : lo <= hi) by (unfold lo, hi; lia).
  assert (Hwf' : ivs_wf (map_remove maps a)) by (unfold map_remove; apply ivs_wf_filter; exact Hwf).
  rewrite (eu_sem _ _ _ Hwf'), (eu_sem _ _ _ Hwf).
  destruct (maps_subtract_sem na lo hi Hwna Hle) as (_ & _ & Cna).
  destruct (maps_subtract_sem lazy lo hi Hwlz Hle) as (_ & _ & Clz).
  set (P' := eu_pred (maps_subtract na lo hi) (maps_subtract lazy lo hi)).
  set (P := eu_pred na lazy).
  assert (Hout : forall x, in_rng lo hi x = false -> P' x = P x).
  { intros x Hx. unfold P', P, eu_pred. rewrite Cna, Clz, Hx. cbn [negb]. rewrite !andb_true_r. reflexivity. }
  assert (Hgen : forall l, (forall q, In q l -> In q maps) ->
            sum_count P' (map_remove l a) <= sum_count P l).
  { induction l as [|q l IH]; intros Hsub; [cbn; lia|].
    unfold map_remove in *. cbn [List.filter]. specialize (IH (fun q0 Hq0 => Hsub q0 (or_intror Hq0))).
    destruct (bv_eqb (fst q) a) eqn:E; cbn [negb sum_count].
    - pose proof (iv_count_nonneg P q). lia.
    - apply bv_eqb_false_iff in E.
      assert (Hne : q <> (a, n)) by (intros ->; apply E; reflexivity).
      pose proof (pw_disj_In maps q (a, n) Hpw (Hsub q (or_introl eq_refl)) Hin Hne) as Hd.
      assert (Eq : iv_count P' q = iv_count P q).
      { unfold iv_count. apply zcount_ext. intros x Hx. pose proof (S_range q) as HS.
        rewrite Z2Nat.id in Hx by lia. apply Hout.
        unfold in_rng. unfold e_disj, e_hi, e_lo, e_sz in Hd. cbn [fst snd] in Hd. unfold B, S in Hx.
        fold lo in Hd. apply andb_false_iff.
        destruct Hd as [Hd|Hd]; [left; apply Z.leb_gt; unfold lo in *; lia | right; apply Z.ltb_ge; unfold hi, lo in *; lia]. }
      rewrite Eq. lia. }
  exact (Hgen maps (fun q Hq => Hq)).
Qed.

(* [comment removed for export] *)
Lemma iv_count_in_rng_disjoint : forall p lo hi,
  (B p + S p <= lo \/ hi <= B p) -> iv_count (in_rng lo hi) p = 0.
Proof.
  intros p lo hi Hd. unfold iv_count. apply zcount_false. intros x Hx. pose proof (S_range p) as HS.
  rewrite Z2Nat.id in Hx by lia. unfold in_rng. apply andb_false_iff.
  destruct Hd as [Hd|Hd]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma iv_count_in_rng_le : forall p lo hi, lo <= hi -> iv_count (in_rng lo hi) p <= hi - lo.
Proof. intros p lo hi Hle. unfold iv_count. pose proof (S_range p). apply count_inside; lia. Qed.

Lemma overlap_contained : forall maps p0 lo hi,
  pw_disj maps -> In p0 maps -> lo < hi -> e_lo p0 <= lo -> hi <= e_hi p0 ->
  sum_count (in_rng lo hi) maps <= hi - lo.
Proof.
  induction maps as [|q maps IH]; intros p0 lo hi Hpw Hin Hlt H1 H2; [contradiction|].
  cbn [sum_count]. destruct Hpw as [Hq Hpw].
  assert (Hrest0 : forall l, Forall (e_disj p0) l -> sum_count (in_rng lo hi) l = 0).
  { induction l as [|r l IHl]; intros HF; [reflexivity|]. cbn [sum_count].
    inversion HF as [|? ? Hr HF']; subst. rewrite (IHl HF').
    rewrite iv_count_in_rng_disjoint; [reflexivity|].
    unfold e_disj, e_hi, e_lo, e_sz, B, S in *. lia. }
  destruct Hin as [-> | Hin].
  - rewrite (Hrest0 maps Hq). pose proof (iv_count_in_rng_le p0 lo hi ltac:(lia)). lia.
  - rewrite (iv_count_in_rng_disjoint q).
    + pose proof (IH p0 lo hi Hpw Hin Hlt H1 H2). lia.
    + pose proof (proj1 (Forall_forall _ _) Hq p0 Hin) as Hd.
      unfold e_disj, e_hi, e_lo, e_sz, B, S in *. lia.
Qed.

Theorem eu_commit_le : forall maps na lazy p0 lo hi,
  ivs_wf maps -> ivs_wf na -> ivs_wf lazy ->
  pw_disj maps -> In p0 maps -> lo < hi -> e_lo p0 <= lo -> hi <= e_hi p0 ->
  eu maps (maps_subtract na lo hi) (maps_subtract lazy lo hi) <= eu maps na lazy + (hi - lo).
Proof.
  intros maps na lazy p0 lo hi Hwf Hwna Hwlz Hpw Hin Hlt H1 H2.
  rewrite !(eu_sem _ _ _ Hwf).
  destruct (maps_subtract_sem na lo hi Hwna ltac:(lia)) as (_ & _ & Cna).
  destruct (maps_subtract_sem lazy lo hi Hwlz ltac:(lia)) as (_ & _ & Clz).
  pose proof (sum_count_mono (eu_pred (maps_subtract na lo hi) (maps_subtract lazy lo hi))
                (fun x => eu_pred na lazy x || in_rng lo hi x) maps) as Hm.
  assert (Himp : forall x, eu_pred (maps_subtract na lo hi) (maps_subtract lazy lo hi) x = true ->
                           eu_pred na lazy x || in_rng lo hi x = true).
  { intros x. unfold eu_pred. rewrite Cna, Clz.
    destruct (covered lazy x), (covered na x), (in_rng lo hi x); cbn; congruence. }
  specialize (Hm Himp).
  pose proof (sum_count_or_le (eu_pred na lazy) (in_rng lo hi) maps) as Hor.
  pose proof (overlap_contained maps p0 lo hi Hpw Hin Hlt H1 H2). lia.
Qed.

(* [comment removed for export] *)
Lemma ivs_wf_Forall : forall l, ivs_wf l <-> Forall (fun q => e_hi q <= 2 ^ 64) l.
Proof. intros l. unfold ivs_wf, iv_wf, B, S, e_hi, e_lo, e_sz. rewrite Forall_forall. reflexivity. Qed.

End Cnt.
