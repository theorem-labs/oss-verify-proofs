(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM.
Import ListNotations.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCGtU.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lexcmp (T : nat) (f g : nat -> Z) (k : nat) : option bool :=
  match T with
  | O => None
  | S T' => if f k =? g k then lexcmp T' f g (S k) else Some (g k <? f k)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition lexgtb (T : nat) (f g : nat -> Z) : bool :=
  match lexcmp T f g 0 with Some b => b | None => false end.

(* [comment removed for export] *)
Lemma lexcmp_S : forall T f g k, lexcmp (S T) f g k = (if f k =? g k then lexcmp T f g (S k) else Some (g k <? f k)).
Proof. reflexivity. Qed.

Lemma lexcmp_asym : forall T f g k, lexcmp T f g k = Some true -> lexcmp T g f k = Some false.
Proof.
  induction T as [|T IH]; intros f g k H; cbn in *; [discriminate|].
  destruct (Z.eqb_spec (f k) (g k)) as [E|E].
  - replace (g k =? f k) with true by (symmetry; apply Z.eqb_eq; congruence). apply IH. exact H.
  - replace (g k =? f k) with false by (symmetry; apply Z.eqb_neq; congruence).
    injection H as H. apply Z.ltb_lt in H. f_equal. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Definition lexleb (T : nat) (f g : nat -> Z) (k : nat) : bool :=
  match lexcmp T f g k with Some b => negb b | None => true end.

Lemma lexleb_trans : forall T f g h k, lexleb T f g k = true -> lexleb T g h k = true -> lexleb T f h k = true.
Proof.
  induction T as [|T IH]; intros f g h k; unfold lexleb; cbn; [reflexivity|].
  destruct (Z.eqb_spec (f k) (g k)) as [E1|E1]; destruct (Z.eqb_spec (g k) (h k)) as [E2|E2]; intros H1 H2.
  - replace (f k =? h k) with true by (symmetry; apply Z.eqb_eq; congruence). apply (IH f g h); assumption.
  - replace (f k =? h k) with false by (symmetry; apply Z.eqb_neq; congruence). rewrite E1. exact H2.
  - replace (f k =? h k) with false by (symmetry; apply Z.eqb_neq; congruence). rewrite <- E2. exact H1.
  - cbn in H1, H2. apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H1. apply Z.ltb_ge in H2.
    replace (f k =? h k) with false by (symmetry; apply Z.eqb_neq; lia). cbn. apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma lexgtb_false_leb : forall T f g, lexgtb T f g = false <-> lexleb T f g 0 = true.
Proof.
  intros. unfold lexgtb, lexleb. destruct (lexcmp T f g 0) as [b|]; [destruct b; cbn; split; congruence| split; reflexivity].
Qed.

Lemma lexgtb_asym : forall T f g, lexgtb T f g = true -> lexgtb T g f = false.
Proof.
  intros T f g H. unfold lexgtb in *. destruct (lexcmp T f g 0) as [b|] eqn:E; [|discriminate]. subst b.
  rewrite (lexcmp_asym T f g 0 E). reflexivity.
Qed.

Lemma lexgtb_le_trans : forall T f g h, lexgtb T f g = false -> lexgtb T g h = false -> lexgtb T f h = false.
Proof.
  intros T f g h H1 H2. apply (proj2 (lexgtb_false_leb T f h)).
  apply (lexleb_trans T f g h 0); apply (proj1 (lexgtb_false_leb _ _ _)); assumption.
Qed.

Lemma lexcmp_app : forall T1 T2 f g k,
  lexcmp (T1 + T2) f g k = match lexcmp T1 f g k with Some b => Some b | None => lexcmp T2 f g (k + T1)%nat end.
Proof.
  induction T1 as [|T1 IH]; intros T2 f g k; cbn; [now rewrite Nat.add_0_r|].
  destruct (f k =? g k); [|reflexivity]. rewrite IH. replace (S k + T1)%nat with (k + S T1)%nat by lia. reflexivity.
Qed.

Lemma lexcmp_ext : forall T f f' g g' k, (forall j, (j < T)%nat -> f (k + j)%nat = f' (k + j)%nat /\ g (k + j)%nat = g' (k + j)%nat) ->
  lexcmp T f g k = lexcmp T f' g' k.
Proof.
  induction T as [|T IH]; intros f f' g g' k H; cbn; [reflexivity|].
  destruct (H 0%nat ltac:(lia)) as [E1 E2]. rewrite Nat.add_0_r in E1, E2. rewrite E1, E2.
  destruct (f' k =? g' k); [|reflexivity]. apply IH. intros j Hj. replace (S k + j)%nat with (k + S j)%nat by lia. apply H. lia.
Qed.

Lemma lexcmp_reindex : forall T f g f' g' k s,
  (forall j, (j < T)%nat -> f (k + j)%nat = f' (s + j)%nat /\ g (k + j)%nat = g' (s + j)%nat) ->
  lexcmp T f g k = lexcmp T f' g' s.
Proof.
  induction T as [|T IH]; intros f g f' g' k s H; cbn; [reflexivity|].
  destruct (H 0%nat ltac:(lia)) as [E1 E2]. rewrite !Nat.add_0_r in E1, E2. rewrite E1, E2.
  destruct (f' s =? g' s); [|reflexivity]. apply IH. intros j Hj.
  replace (S k + j)%nat with (k + S j)%nat by lia. replace (S s + j)%nat with (s + S j)%nat by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GtU.
  Variables (a2 : zarr) (qoff n : Z).
  Hypothesis Hn : 34 <= n.
  (* [comment removed for export] *)
  Hypothesis Bov : forall z, n <= z < n + 34 -> rd8 a2 z = rd8 a2 (z - n).
  Hypothesis Qov : forall z, n <= z < n + 34 -> qrd a2 qoff z = qrd a2 qoff (z - n).

  (* [comment removed for export] *)
  Definition B (z : Z) : Z := rd8 a2 (z mod n).
  Definition Q (z : Z) : Z := qrd a2 qoff (z mod n).

  Lemma B_act : forall z, 0 <= z < n + 34 -> rd8 a2 z = B z.
  Proof.
    intros z Hz. unfold B. destruct (Z_lt_le_dec z n) as [L|L].
    - rewrite Z.mod_small by lia. reflexivity.
    - rewrite Bov by lia. f_equal. rewrite <- (Z_mod_plus_full z (-1) n). symmetry. apply Z.mod_small. lia.
  Qed.
  Lemma Q_act : forall z, 0 <= z < n + 34 -> qrd a2 qoff z = Q z.
  Proof.
    intros z Hz. unfold Q. destruct (Z_lt_le_dec z n) as [L|L].
    - rewrite Z.mod_small by lia. reflexivity.
    - rewrite Qov by lia. f_equal. rewrite <- (Z_mod_plus_full z (-1) n). symmetry. apply Z.mod_small. lia.
  Qed.
  Lemma B_shift : forall z e, B (z - n * e) = B z.
  Proof. intros. unfold B. f_equal. replace (z - n * e) with (z + (- e) * n) by lia. apply Z_mod_plus_full. Qed.
  Lemma Q_shift : forall z e, Q (z - n * e) = Q z.
  Proof. intros. unfold Q. f_equal. replace (z - n * e) with (z + (- e) * n) by lia. apply Z_mod_plus_full. Qed.

  (* [comment removed for export] *)
  Definition bstream (v : Z) : nat -> Z := fun t => B (v + Z.of_nat t).
  Definition qstream (v : Z) : nat -> Z := fun j => if Nat.even j then B (v + Z.of_nat (Nat.div2 j)) else Q (v + Z.of_nat (Nat.div2 j)).
  (* [comment removed for export] *)
  Definition kstream (i : Z) : nat -> Z := fun k => if (k <? 12)%nat then bstream i k else qstream (i + 12) (k - 12)%nat.

  (* [comment removed for export] *)
  Lemma gtu_pre_spec : forall m i1 i2 (k : nat),
    0 <= i1 -> i1 + Z.of_nat (k + m) <= n + 34 -> 0 <= i2 -> i2 + Z.of_nat (k + m) <= n + 34 ->
    let '(r, j1, j2) := gtu_pre m a2 (i1 + Z.of_nat k) (i2 + Z.of_nat k) in
    r = lexcmp m (bstream i1) (bstream i2) k /\ (r = None -> j1 = i1 + Z.of_nat (k + m) /\ j2 = i2 + Z.of_nat (k + m)).
  Proof.
    induction m as [|m IH]; intros i1 i2 k H1 H2 H3 H4; cbn [gtu_pre lexcmp].
    - split; [reflexivity| intros _; split; lia].
    - unfold bstream at 1 2. rewrite !B_act by lia.
      fold (bstream i1 k) (bstream i2 k).
      change (B (i1 + Z.of_nat k)) with (bstream i1 k). change (B (i2 + Z.of_nat k)) with (bstream i2 k).
      destruct (Z.eqb_spec (bstream i1 k) (bstream i2 k)) as [E|E].
      + cbn [negb]. specialize (IH i1 i2 (S k) H1 ltac:(lia) H3 ltac:(lia)).
        replace (i1 + Z.of_nat k + 1) with (i1 + Z.of_nat (S k)) by lia.
        replace (i2 + Z.of_nat k + 1) with (i2 + Z.of_nat (S k)) by lia.
        destruct (gtu_pre m a2 (i1 + Z.of_nat (S k)) (i2 + Z.of_nat (S k))) as [[r j1] j2].
        destruct IH as [A C]. split; [exact A|]. intros R. destruct (C R). split; lia.
      + cbn [negb]. split; [reflexivity| discriminate].
  Qed.

  Lemma qstream_even : forall v u, qstream v (2 * u) = B (v + Z.of_nat u).
  Proof. intros. unfold qstream. rewrite Nat.even_even, Nat.div2_double. reflexivity. Qed.
  Lemma qstream_odd : forall v u, qstream v (S (2 * u)) = Q (v + Z.of_nat u).
  Proof.
    intros. unfold qstream. replace (S (2 * u)) with (1 + 2 * u)%nat at 1 by lia. rewrite Nat.even_add_mul_2. cbn [Nat.even].
    rewrite Nat.div2_succ_double. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gtu_oct_spec : forall m i1 i2 v1 v2 e1 e2 (u : nat),
    i1 = v1 - n * e1 -> i2 = v2 - n * e2 ->
    0 <= i1 -> i1 + Z.of_nat (u + m) <= n + 34 -> 0 <= i2 -> i2 + Z.of_nat (u + m) <= n + 34 ->
    let '(r, j1, j2) := gtu_oct m a2 qoff (i1 + Z.of_nat u) (i2 + Z.of_nat u) in
    r = lexcmp (2 * m) (qstream v1) (qstream v2) (2 * u) /\ (r = None -> j1 = i1 + Z.of_nat (u + m) /\ j2 = i2 + Z.of_nat (u + m)).
  Proof.
    induction m as [|m IH]; intros i1 i2 v1 v2 e1 e2 u E1 E2 H1 H2 H3 H4.
    - cbn. split; [reflexivity| intros _; split; lia].
    - cbn [gtu_oct]. replace (2 * S m)%nat with (S (S (2 * m))) by lia. rewrite !lexcmp_S.
      rewrite !B_act by lia. rewrite !Q_act by lia.
      rewrite !qstream_even, !qstream_odd.
      replace (B (i1 + Z.of_nat u)) with (B (v1 + Z.of_nat u)) by (rewrite E1; replace (v1 - n * e1 + Z.of_nat u) with (v1 + Z.of_nat u - n * e1) by lia; symmetry; apply B_shift).
      replace (B (i2 + Z.of_nat u)) with (B (v2 + Z.of_nat u)) by (rewrite E2; replace (v2 - n * e2 + Z.of_nat u) with (v2 + Z.of_nat u - n * e2) by lia; symmetry; apply B_shift).
      replace (Q (i1 + Z.of_nat u)) with (Q (v1 + Z.of_nat u)) by (rewrite E1; replace (v1 - n * e1 + Z.of_nat u) with (v1 + Z.of_nat u - n * e1) by lia; symmetry; apply Q_shift).
      replace (Q (i2 + Z.of_nat u)) with (Q (v2 + Z.of_nat u)) by (rewrite E2; replace (v2 - n * e2 + Z.of_nat u) with (v2 + Z.of_nat u - n * e2) by lia; symmetry; apply Q_shift).
      destruct (Z.eqb_spec (B (v1 + Z.of_nat u)) (B (v2 + Z.of_nat u))) as [EB|EB]; cbn [negb].
      + destruct (Z.eqb_spec (Q (v1 + Z.of_nat u)) (Q (v2 + Z.of_nat u))) as [EQ|EQ]; cbn [negb].
        * specialize (IH i1 i2 v1 v2 e1 e2 (S u) E1 E2 H1 ltac:(lia) H3 ltac:(lia)).
          replace (i1 + Z.of_nat u + 1) with (i1 + Z.of_nat (S u)) by lia.
          replace (i2 + Z.of_nat u + 1) with (i2 + Z.of_nat (S u)) by lia.
          replace (S (S (2 * u))) with (2 * S u)%nat by lia.
          destruct (gtu_oct m a2 qoff (i1 + Z.of_nat (S u)) (i2 + Z.of_nat (S u))) as [[r j1] j2].
          destruct IH as [A C]. split; [exact A|]. intros R. destruct (C R). split; lia.
        * split; [reflexivity| discriminate].
      + split; [reflexivity| discriminate].
  Qed.

  (* [comment removed for export] *)

  Lemma qstream_shift : forall v (g j : nat), qstream (v + 8 * Z.of_nat g) j = qstream v (16 * g + j)%nat.
  Proof.
    intros v g j. unfold qstream. replace (16 * g + j)%nat with (j + 2 * (8 * g))%nat by lia.
    rewrite Nat.even_add_mul_2.
    assert (D : Nat.div2 (j + 2 * (8 * g)) = (Nat.div2 j + 8 * g)%nat).
    { destruct (Nat.Even_or_Odd j) as [[p ->]|[p ->]].
      - replace (2 * p + 2 * (8 * g))%nat with (2 * (p + 8 * g))%nat by lia. rewrite !Nat.div2_double. reflexivity.
      - replace (2 * p + 1 + 2 * (8 * g))%nat with (S (2 * (p + 8 * g)))%nat by lia. replace (2 * p + 1)%nat with (S (2 * p)) by lia.
        rewrite !Nat.div2_succ_double. reflexivity. }
    rewrite D. replace (v + Z.of_nat (Nat.div2 j + 8 * g)) with (v + 8 * Z.of_nat g + Z.of_nat (Nat.div2 j)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gtu_loop_spec : forall fuel (g : nat) i1 i2 v1 v2 e1 e2 k budget,
    0 <= k -> (Z.to_nat (k / 8) < fuel)%nat ->
    i1 = v1 + 8 * Z.of_nat g - n * e1 -> i2 = v2 + 8 * Z.of_nat g - n * e2 ->
    0 <= i1 -> i1 + 8 <= n + 34 -> 0 <= i2 -> i2 + 8 <= n + 34 ->
    let N := (Z.to_nat (k / 8) + 1)%nat in
    fst (gtu_loop fuel a2 qoff n i1 i2 k budget) =
      match lexcmp (16 * N) (qstream v1) (qstream v2) (16 * g) with Some b => b | None => false end /\
    budget - Z.of_nat N <= snd (gtu_loop fuel a2 qoff n i1 i2 k budget) <= budget.
  Proof.
    induction fuel as [|fuel IH]; intros g i1 i2 v1 v2 e1 e2 k budget Hk Hf E1 E2 H1 H2 H3 H4; [lia|].
    cbv zeta. cbn [gtu_loop].
    pose proof (gtu_oct_spec 8 i1 i2 (v1 + 8 * Z.of_nat g) (v2 + 8 * Z.of_nat g) e1 e2 0 ltac:(lia) ltac:(lia) H1 ltac:(cbn; lia) H3 ltac:(cbn; lia)) as OS.
    rewrite !Z.add_0_r in OS.
    destruct (gtu_oct 8 a2 qoff i1 i2) as [[r j1] j2]. destruct OS as [R J].
    rewrite (lexcmp_reindex _ _ _ (qstream v1) (qstream v2) _ (16 * g)) in R
      by (intros j Hj; rewrite Nat.add_0_l; split; apply qstream_shift).
    replace (16 * (Z.to_nat (k / 8) + 1))%nat with (16 + 16 * Z.to_nat (k / 8))%nat by lia.
    rewrite lexcmp_app. change (2 * 8)%nat with 16%nat in R. rewrite <- R.
    destruct r as [b|].
    - cbn [fst snd]. split; [reflexivity| lia].
    - destruct (J eq_refl) as [J1 J2]. cbn in J1, J2. subst j1 j2.
      destruct (Z.leb_spec 0 (k - 8)) as [K8|K8].
      + (* [comment removed for export] *)
        assert (EK : Z.to_nat (k / 8) = (Z.to_nat ((k - 8) / 8) + 1)%nat).
        { replace k with (k - 8 + 1 * 8) at 1 by lia. rewrite Z.div_add by lia.
          assert (0 <= (k - 8) / 8) by (apply Z.div_pos; lia). lia. }
        set (i1' := if n <=? i1 + 8 then i1 + 8 - n else i1 + 8).
        set (i2' := if n <=? i2 + 8 then i2 + 8 - n else i2 + 8).
        assert (X1 : exists e, i1' = v1 + 8 * Z.of_nat (S g) - n * e /\ 0 <= i1' /\ i1' + 8 <= n + 34).
        { subst i1'. destruct (Z.leb_spec n (i1 + 8)); [exists (e1 + 1)| exists e1]; split; lia. }
        assert (X2 : exists e, i2' = v2 + 8 * Z.of_nat (S g) - n * e /\ 0 <= i2' /\ i2' + 8 <= n + 34).
        { subst i2'. destruct (Z.leb_spec n (i2 + 8)); [exists (e2 + 1)| exists e2]; split; lia. }
        cps_destruct X1 as (f1 & F1 & F2 & F3). cps_destruct X2 as (f2 & G1 & G2 & G3).
        specialize (IH (S g) i1' i2' v1 v2 f1 f2 (k - 8) (budget - 1) ltac:(lia) ltac:(lia) F1 G1 F2 F3 G2 G3).
        cbv zeta in IH. rewrite EK. replace (16 * g + 16)%nat with (16 * S g)%nat by lia.
        destruct IH as [A Bd]. split; [exact A| lia].
      + (* [comment removed for export] *)
        assert (EK : Z.to_nat (k / 8) = 0%nat) by (rewrite Z.div_small by lia; reflexivity).
        rewrite EK. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Definition GT_N : nat := (Z.to_nat ((n + 8) / 8) + 1)%nat.
  Definition KEYLEN : nat := (12 + 16 * GT_N)%nat.

  Theorem mainGtU_spec : forall i1 i2 budget,
    0 <= i1 <= n + 14 -> 0 <= i2 <= n + 14 ->
    fst (mainGtU i1 i2 a2 qoff n budget) = lexgtb KEYLEN (kstream i1) (kstream i2) /\
    budget - Z.of_nat GT_N <= snd (mainGtU i1 i2 a2 qoff n budget) <= budget.
  Proof.
    intros i1 i2 budget H1 H2. unfold mainGtU, lexgtb, KEYLEN.
    pose proof (gtu_pre_spec 12 i1 i2 0 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as PS.
    rewrite !Z.add_0_r in PS.
    destruct (gtu_pre 12 a2 i1 i2) as [[r j1] j2]. destruct PS as [R J].
    rewrite lexcmp_app.
    rewrite (lexcmp_ext 12 (kstream i1) (bstream i1) (kstream i2) (bstream i2) 0)
      by (intros j Hj; unfold kstream; cbn [Nat.add]; replace (j <? 12)%nat with true by (symmetry; apply Nat.ltb_lt; lia); split; reflexivity).
    rewrite <- R. destruct r as [b|].
    - cbn [fst snd]. split; [reflexivity| unfold GT_N; lia].
    - destruct (J eq_refl) as [-> ->]. cbn [Nat.add].
      pose proof (gtu_loop_spec (S (S (Z.to_nat ((n + 8) / 8)))) 0 (i1 + 12) (i2 + 12) (i1 + 12) (i2 + 12) 0 0 (n + 8) budget
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as LS.
      cbv zeta in LS. replace (Z.of_nat 12) with 12 by reflexivity.
      rewrite (lexcmp_reindex (16 * GT_N) (kstream i1) (kstream i2) (qstream (i1 + 12)) (qstream (i2 + 12)) 12 (16 * 0))
        by (intros j Hj; unfold kstream; replace (12 + j <? 12)%nat with false by (symmetry; apply Nat.ltb_ge; lia);
            rewrite Nat.mul_0_r, Nat.add_0_l; replace (12 + j - 12)%nat with j by lia; split; reflexivity).
      unfold GT_N. exact LS.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End GtU.
End BzCGtU.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma mpart_lo_S : forall f a2 d med pp,
  mpart_lo (S f) a2 d med pp =
  (if mp_unHi pp <? mp_unLo pp then pp else
   let n := rd8 a2 (rd32 (mp_a1 pp) (mp_unLo pp) + d) - med in
   if n =? 0 then mpart_lo f a2 d med (MP (mswap (mp_a1 pp) (mp_unLo pp) (mp_ltLo pp)) (mp_unLo pp + 1) (mp_unHi pp) (mp_ltLo pp + 1) (mp_gtHi pp))
   else if 0 <? n then pp else mpart_lo f a2 d med (MP (mp_a1 pp) (mp_unLo pp + 1) (mp_unHi pp) (mp_ltLo pp) (mp_gtHi pp))).
Proof. reflexivity. Qed.
Lemma mpart_hi_S : forall f a2 d med pp,
  mpart_hi (S f) a2 d med pp =
  (if mp_unHi pp <? mp_unLo pp then pp else
   let n := rd8 a2 (rd32 (mp_a1 pp) (mp_unHi pp) + d) - med in
   if n =? 0 then mpart_hi f a2 d med (MP (mswap (mp_a1 pp) (mp_unHi pp) (mp_gtHi pp)) (mp_unLo pp) (mp_unHi pp - 1) (mp_ltLo pp) (mp_gtHi pp - 1))
   else if n <? 0 then pp else mpart_hi f a2 d med (MP (mp_a1 pp) (mp_unLo pp) (mp_unHi pp - 1) (mp_ltLo pp) (mp_gtHi pp))).
Proof. reflexivity. Qed.
Lemma mpart_loop_S : forall f sz a2 d med pp,
  mpart_loop (S f) sz a2 d med pp =
  (let p1 := mpart_lo (S sz) a2 d med pp in let p2 := mpart_hi (S sz) a2 d med p1 in
   if mp_unHi p2 <? mp_unLo p2 then p2
   else mpart_loop f sz a2 d med (MP (mswap (mp_a1 p2) (mp_unLo p2) (mp_unHi p2)) (mp_unLo p2 + 1) (mp_unHi p2 - 1) (mp_ltLo p2) (mp_gtHi p2))).
Proof. reflexivity. Qed.

Section MPart.
  Variables (a2 : zarr) (d med lo hi : Z).

  (* [comment removed for export] *)
  Fixpoint cnt (fm : zarr) (a : Z) (n : nat) : Z :=
    match n with
    | O => 0
    | S n' => (if rd8 a2 (rd32 fm a + d) =? med then 1 else 0) + cnt fm (a + 1) n'
    end.

  Lemma cnt_nonneg : forall n fm a, 0 <= cnt fm a n.
  Proof. induction n; intros; cbn; [lia|]. specialize (IHn fm (a+1)). destruct (_ =? _); lia. Qed.

  Lemma cnt_ext : forall n fm fm' a,
    (forall k, a <= k < a + Z.of_nat n -> rd32 fm' k = rd32 fm k) -> cnt fm' a n = cnt fm a n.
  Proof.
    induction n as [|n IH]; intros fm fm' a H; cbn; [reflexivity|].
    rewrite (H a) by lia. rewrite (IH fm fm' (a+1)); [reflexivity|]. intros k Hk. apply H. lia.
  Qed.

  Lemma cnt_head : forall n fm a, cnt fm a (S n) = (if rd8 a2 (rd32 fm a + d) =? med then 1 else 0) + cnt fm (a+1) n.
  Proof. reflexivity. Qed.

  Lemma cnt_snoc : forall n fm a, cnt fm a (S n) = cnt fm a n + (if rd8 a2 (rd32 fm (a + Z.of_nat n) + d) =? med then 1 else 0).
  Proof.
    induction n as [|n IH]; intros fm a.
    - cbn. replace (a + 0) with a by lia. lia.
    - rewrite cnt_head. rewrite (IH fm (a+1)). rewrite cnt_head.
      replace (a + 1 + Z.of_nat n) with (a + Z.of_nat (S n)) by lia. lia.
  Qed.

  Lemma cnt_pos_at : forall n fm a x, a <= x < a + Z.of_nat n -> rd8 a2 (rd32 fm x + d) = med -> 1 <= cnt fm a n.
  Proof.
    induction n as [|n IH]; intros fm a x Hx Hm; [lia|].
    rewrite cnt_head. pose proof (cnt_nonneg n fm (a+1)).
    destruct (Z.eq_dec x a) as [->|NE].
    - rewrite Hm, Z.eqb_refl. lia.
    - assert (1 <= cnt fm (a+1) n) by (apply (IH fm (a+1) x); lia). destruct (_ =? _); lia.
  Qed.

  (* [comment removed for export] *)
  Definition PI (p : mpart) : Prop :=
    lo <= mp_ltLo p /\ mp_ltLo p <= mp_unLo p /\ mp_unLo p <= mp_unHi p + 1 /\
    mp_unHi p <= mp_gtHi p /\ mp_gtHi p <= hi /\
    1 <= (mp_ltLo p - lo) + (hi - mp_gtHi p) + cnt (mp_a1 p) (mp_unLo p) (Z.to_nat (mp_unHi p - mp_unLo p + 1)).

  Definition key (fm : zarr) (i : Z) : Z := rd8 a2 (rd32 fm i + d).


  Lemma mq_lo_ok : forall f p,
    PI p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < f)%nat ->
    PI (mpart_lo f a2 d med p) /\ mp_unHi (mpart_lo f a2 d med p) = mp_unHi p /\ mp_gtHi (mpart_lo f a2 d med p) = mp_gtHi p /\
    mp_ltLo p <= mp_ltLo (mpart_lo f a2 d med p) /\ mp_unLo p <= mp_unLo (mpart_lo f a2 d med p) /\
    (mp_unHi (mpart_lo f a2 d med p) < mp_unLo (mpart_lo f a2 d med p) \/ med < key (mp_a1 (mpart_lo f a2 d med p)) (mp_unLo (mpart_lo f a2 d med p))).
  Proof.
    induction f as [|f IH]; intros p HP Hf; [lia|].
    rewrite mpart_lo_S. cbn zeta.
    destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE].
    { repeat split; try apply HP; first [lia | left; lia]. }
    cps_destruct HP as (A & B & C & D & E & F).
    assert (HN : Z.to_nat (mp_unHi p - mp_unLo p + 1) = S (Z.to_nat (mp_unHi p - (mp_unLo p + 1) + 1))) by lia.
    rewrite HN, cnt_head in F.
    destruct (Z.eqb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) - med) 0) as [EQ|NE].
    - match goal with |- PI (mpart_lo f a2 d med ?q) /\ _ => specialize (IH q) end.
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia |].
      { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
        rewrite (cnt_ext _ (mp_a1 p)).
        2:{ intros k Hk. unfold mswap. rewrite !rd32_wr32_other by lia. reflexivity. }
        replace (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) =? med) with true in F by (symmetry; apply Z.eqb_eq; lia). lia. }
      repeat split; try apply P1; try lia.
    - destruct (Z.ltb_spec 0 (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) - med)) as [GT|LE].
      + split. { unfold PI. repeat split; try lia. rewrite HN, cnt_head. exact F. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. right; unfold key; lia.
      + match goal with |- PI (mpart_lo f a2 d med ?q) /\ _ => specialize (IH q) end.
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia |].
        { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
          replace (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia). lia. }
        repeat split; try apply P1; try lia.
  Qed.

  Lemma mq_hi_ok : forall f p,
    PI p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < f)%nat ->
    (mp_unHi p < mp_unLo p \/ med < key (mp_a1 p) (mp_unLo p)) ->
    PI (mpart_hi f a2 d med p) /\ mp_unLo (mpart_hi f a2 d med p) = mp_unLo p /\ mp_ltLo (mpart_hi f a2 d med p) = mp_ltLo p /\
    mp_gtHi (mpart_hi f a2 d med p) <= mp_gtHi p /\ mp_unHi (mpart_hi f a2 d med p) <= mp_unHi p /\
    (mp_unHi (mpart_hi f a2 d med p) < mp_unLo (mpart_hi f a2 d med p) \/
     (key (mp_a1 (mpart_hi f a2 d med p)) (mp_unHi (mpart_hi f a2 d med p)) < med /\
      med < key (mp_a1 (mpart_hi f a2 d med p)) (mp_unLo (mpart_hi f a2 d med p)))).
  Proof.
    induction f as [|f IH]; intros p HP Hf HK; [lia|].
    rewrite mpart_hi_S. cbn zeta.
    destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE].
    { repeat split; try apply HP; first [lia | left; lia]. }
    destruct HK as [HK|HK]; [lia|].
    cps_destruct HP as (A & B & C & D & E & F).
    assert (HN : Z.to_nat (mp_unHi p - mp_unLo p + 1) = S (Z.to_nat (mp_unHi p - 1 - mp_unLo p + 1))) by lia.
    rewrite HN, cnt_snoc in F.
    replace (mp_unLo p + Z.of_nat (Z.to_nat (mp_unHi p - 1 - mp_unLo p + 1))) with (mp_unHi p) in F by lia.
    destruct (Z.eqb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) - med) 0) as [EQ|NE].
    - assert (NEQ : mp_unLo p <> mp_unHi p).
      { intros X. unfold key in HK. rewrite X in HK. lia. }
      match goal with |- PI (mpart_hi f a2 d med ?q) /\ _ => specialize (IH q) end.
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia | |].
      { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
        rewrite (cnt_ext _ (mp_a1 p)).
        2:{ intros k Hk. unfold mswap. rewrite !rd32_wr32_other by lia. reflexivity. }
        replace (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) =? med) with true in F by (symmetry; apply Z.eqb_eq; lia). lia. }
      { right. unfold key in *. unfold mswap. rewrite !rd32_wr32_other by lia. exact HK. }
      repeat split; try apply P1; try lia.
    - destruct (Z.ltb_spec (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) - med) 0) as [LTm|GEm].
      + split. { unfold PI. repeat split; try lia. rewrite HN, cnt_snoc.
                 replace (mp_unLo p + Z.of_nat (Z.to_nat (mp_unHi p - 1 - mp_unLo p + 1))) with (mp_unHi p) by lia. exact F. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. right; unfold key in *; lia.
      + match goal with |- PI (mpart_hi f a2 d med ?q) /\ _ => specialize (IH q) end.
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia | |].
        { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
          replace (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia). lia. }
        { right. exact HK. }
        repeat split; try apply P1; try lia.
  Qed.

  Lemma mq_loop_ok : forall f sz p,
    PI p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) <= sz)%nat -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < 2 * f)%nat ->
    PI (mpart_loop f sz a2 d med p) /\ mp_unLo (mpart_loop f sz a2 d med p) = mp_unHi (mpart_loop f sz a2 d med p) + 1 /\
    mp_ltLo p <= mp_ltLo (mpart_loop f sz a2 d med p) /\ mp_gtHi (mpart_loop f sz a2 d med p) <= mp_gtHi p.
  Proof.
    induction f as [|f IH]; intros sz p HP Hsz Hf; [lia|].
    rewrite mpart_loop_S. cbn zeta.
    cps_pose (mq_lo_ok (S sz) p HP ltac:(lia)) as (L1 & L2 & L3 & L5 & L6 & L4).
    set (p1 := mpart_lo (S sz) a2 d med p) in *.
    assert (S1 : (Z.to_nat (mp_unHi p1 - mp_unLo p1 + 1) < S sz)%nat).
    { cps_destruct L1 as (_ & _ & C1 & _). rewrite L2. cps_destruct HP as (_ & B0 & _). lia. }
    cps_pose (mq_hi_ok (S sz) p1 L1 S1 L4) as (M1 & M2 & M3 & M5 & M6 & M4).
    set (p2 := mpart_hi (S sz) a2 d med p1) in *.
    destruct (Z.ltb_spec (mp_unHi p2) (mp_unLo p2)) as [LT|GE].
    { split; [exact M1|]. cps_destruct M1 as (_ & _ & C2 & _). repeat split; lia. }
    destruct M4 as [M4|[K1 K2]]; [lia|].
    assert (NE : mp_unLo p2 < mp_unHi p2).
    { destruct (Z.eq_dec (mp_unLo p2) (mp_unHi p2)) as [X|X]; [|lia]. rewrite X in K2. lia. }
    cps_destruct M1 as (A & B & C & D & E & F).
    match goal with |- PI (mpart_loop f sz a2 d med ?q) /\ _ => specialize (IH sz q) end.
    cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
    cps_destruct IH as (P1 & P2 & P3 & P4); [| lia | lia |].
    { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
      assert (HN : Z.to_nat (mp_unHi p2 - mp_unLo p2 + 1) = S (S (Z.to_nat (mp_unHi p2 - 1 - (mp_unLo p2 + 1) + 1)))) by lia.
      rewrite HN, cnt_head, cnt_snoc in F.
      replace (mp_unLo p2 + 1 + Z.of_nat (Z.to_nat (mp_unHi p2 - 1 - (mp_unLo p2 + 1) + 1))) with (mp_unHi p2) in F by lia.
      unfold key in K1, K2.
      replace (rd8 a2 (rd32 (mp_a1 p2) (mp_unLo p2) + d) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia).
      replace (rd8 a2 (rd32 (mp_a1 p2) (mp_unHi p2) + d) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia).
      rewrite (cnt_ext _ (mp_a1 p2)); [lia|].
      intros k Hk. unfold mswap. rewrite !rd32_wr32_other by lia. reflexivity. }
    repeat split; try apply P1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mq_part : forall fm x,
    lo <= x <= hi -> med = key fm x ->
    let sz := Z.to_nat (hi - lo + 1) in
    let p := mpart_loop (S sz) sz a2 d med (MP fm lo hi lo hi) in
    lo <= mp_ltLo p /\ mp_ltLo p <= mp_unLo p /\ mp_unLo p = mp_unHi p + 1 /\ mp_unHi p <= mp_gtHi p /\ mp_gtHi p <= hi /\
    1 <= (mp_ltLo p - lo) + (hi - mp_gtHi p).
  Proof.
    intros fm x Hx Hm. cbn zeta.
    assert (P0 : PI (MP fm lo hi lo hi)).
    { unfold PI; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat split; try lia.
      pose proof (cnt_pos_at (Z.to_nat (hi - lo + 1)) fm lo x ltac:(lia) ltac:(unfold key in Hm; congruence)). lia. }
    cps_pose (mq_loop_ok (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (MP fm lo hi lo hi) P0
                  ltac:(cbn [mp_unLo mp_unHi]; lia) ltac:(cbn [mp_unLo mp_unHi]; lia)) as (P1 & P2 & P3 & P4).
    cbn [mp_ltLo mp_gtHi] in P3, P4.
    cps_destruct P1 as (A & B & C & D & E & F).
    replace (Z.to_nat (mp_unHi _ - mp_unLo _ + 1)) with 0%nat in F by lia. cbn [cnt] in F.
    repeat split; lia.
  Qed.
End MPart.
