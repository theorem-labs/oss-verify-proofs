(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Zbitwise.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section ParseString.
  Variable bs : list Z.

  Record PS (i j p d : Z) : Prop := {
    ps_closes : closes bs p j;
    ps_lo     : i + 1 <= p;
    ps_d      : 0 <= d <= p - (i + 1);
  }.

  Lemma PS_init : forall i j, closes bs (i + 1) j -> PS i j (i + 1) 0.
  Proof. intros i j H. constructor; [exact H|lia|lia]. Qed.

  Lemma PS_read : forall i j p d, PS i j p d -> 0 <= p /\ p <= j /\ j < blen bs /\ p + 11 < blen bs + 64.
  Proof. intros i j p d H. pose proof (closes_bounds _ _ _ (ps_closes _ _ _ _ H)). lia. Qed.

  Lemma PS_store : forall i j p d, PS i j p d -> 0 <= d /\ d + 4 <= (j - i) + 3.
  Proof.
    intros i j p d H. pose proof (closes_bounds _ _ _ (ps_closes _ _ _ _ H)). pose proof (ps_lo _ _ _ _ H). pose proof (ps_d _ _ _ _ H). lia.
  Qed.

  Lemma PS_quote : forall i j p d, PS i j p d -> B bs p = 34 -> p = j /\ 0 <= d <= j - i - 1.
  Proof.
    intros i j p d H Hq. pose proof (closes_quote_inv _ _ _ (ps_closes _ _ _ _ H) Hq). pose proof (ps_d _ _ _ _ H). lia.
  Qed.

  Lemma PS_ord : forall i j p d, PS i j p d -> B bs p <> 34 -> B bs p <> 92 -> PS i j (p + 1) (d + 1).
  Proof.
    intros i j p d H H1 H2. pose proof (ps_lo _ _ _ _ H). pose proof (ps_d _ _ _ _ H).
    constructor; [apply closes_ord_inv; [exact (ps_closes _ _ _ _ H)|exact H1|exact H2]|lia|lia].
  Qed.

  Lemma PS_esc : forall i j p d, PS i j p d -> B bs p = 92 -> PS i j (p + 2) (d + 1).
  Proof.
    intros i j p d H Hq. pose proof (ps_lo _ _ _ _ H). pose proof (ps_d _ _ _ _ H).
    constructor; [apply closes_esc_inv; [exact (ps_closes _ _ _ _ H)|exact Hq]|lia|lia].
  Qed.

  Definition not_qb (b : Z) : Prop := b <> 34 /\ b <> 92.

  Lemma PS_u : forall i j p d w, PS i j p d -> B bs p = 92 ->
    (forall t, 2 <= t < 6 -> not_qb (B bs (p + t))) -> 0 <= w <= 6 -> PS i j (p + 6) (d + w).
  Proof.
    intros i j p d w H Hq Hh Hw. pose proof (ps_lo _ _ _ _ H). pose proof (ps_d _ _ _ _ H).
    constructor; [apply closes_u_inv; [exact (ps_closes _ _ _ _ H)|exact Hq|exact Hh]|lia|lia].
  Qed.

  Lemma PS_u_store : forall i j p d, PS i j p d -> B bs p = 92 ->
    (forall t, 2 <= t < 6 -> not_qb (B bs (p + t))) -> d + 6 <= (j - i) - 1.
  Proof.
    intros i j p d H Hq Hh. pose proof (closes_u_le _ _ _ (ps_closes _ _ _ _ H) Hq Hh). pose proof (ps_d _ _ _ _ H). lia.
  Qed.

  Lemma PS_uu : forall i j p d w, PS i j p d -> B bs p = 92 ->
    (forall t, 2 <= t < 6 -> not_qb (B bs (p + t))) -> B bs (p + 6) = 92 ->
    (forall t, 8 <= t < 12 -> not_qb (B bs (p + t))) -> 0 <= w <= 12 -> PS i j (p + 12) (d + w).
  Proof.
    intros i j p d w H Hq Hh Hq2 Hh2 Hw. pose proof (ps_lo _ _ _ _ H). pose proof (ps_d _ _ _ _ H).
    pose proof (closes_u_inv _ _ _ (ps_closes _ _ _ _ H) Hq Hh) as H6.
    constructor; [|lia|lia].
    replace (p + 12) with ((p + 6) + 6) by lia. apply closes_u_inv; [exact H6|exact Hq2|].
    intros t Ht. replace (p + 6 + t) with (p + (t + 6)) by lia. apply Hh2. lia.
  Qed.

  Lemma PS_uu_store : forall i j p d, PS i j p d -> B bs p = 92 ->
    (forall t, 2 <= t < 6 -> not_qb (B bs (p + t))) -> B bs (p + 6) = 92 ->
    (forall t, 8 <= t < 12 -> not_qb (B bs (p + t))) -> d + 12 <= (j - i) - 1.
  Proof.
    intros i j p d H Hq Hh Hq2 Hh2.
    pose proof (PS_uu i j p d 0 H Hq Hh Hq2 Hh2 ltac:(lia)) as H12.
    pose proof (closes_bounds _ _ _ (ps_closes _ _ _ _ H12)). pose proof (ps_d _ _ _ _ H). lia.
  Qed.

  Lemma PS_measure : forall i j p d, PS i j p d -> 0 <= j - p.
  Proof. intros i j p d H. pose proof (closes_bounds _ _ _ (ps_closes _ _ _ _ H)). lia. Qed.
End ParseString.

Definition hextab_ok (T : Z -> Z) : Prop :=
  (forall x, 0 <= T x < 2 ^ 32) /\
  forall base b, (base = 630 \/ base = 420 \/ base = 210 \/ base = 0) -> (b = 34 \/ b = 92) -> T (base + b) = 4294967295.

Lemma lor_ge_l : forall a b, 0 <= b -> a <= Z.lor a b.
Proof. intros a b Hb. pose proof (Z.sub_lor_l_same_l b a) as E. pose proof (proj2 (Z.land_nonneg b (Z.lnot a)) (or_introl Hb)). lia. Qed.

Lemma lor_ge_r : forall a b, 0 <= a -> b <= Z.lor a b.
Proof. intros a b Ha. rewrite Z.lor_comm. apply lor_ge_l; exact Ha. Qed.

Lemma hex_guard : forall T b0 b1 b2 b3, hextab_ok T ->
  Z.lor (Z.lor (Z.lor (T (630 + b0)) (T (420 + b1))) (T (210 + b2))) (T (0 + b3)) <= 1114111 ->
  not_qb b0 /\ not_qb b1 /\ not_qb b2 /\ not_qb b3.
Proof.
  intros T b0 b1 b2 b3 [Hr Ht] Hle.
  pose proof (Hr (630 + b0)) as R0. pose proof (Hr (420 + b1)) as R1. pose proof (Hr (210 + b2)) as R2. pose proof (Hr (0 + b3)) as R3.
  set (v0 := T (630 + b0)) in *. set (v1 := T (420 + b1)) in *. set (v2 := T (210 + b2)) in *. set (v3 := T (0 + b3)) in *.
  assert (L01 : 0 <= Z.lor v0 v1) by (apply Z.lor_nonneg; lia).
  assert (L012 : 0 <= Z.lor (Z.lor v0 v1) v2) by (apply Z.lor_nonneg; lia).
  pose proof (lor_ge_l (Z.lor (Z.lor v0 v1) v2) v3 ltac:(lia)) as G3a. pose proof (lor_ge_r (Z.lor (Z.lor v0 v1) v2) v3 L012) as G3.
  pose proof (lor_ge_l (Z.lor v0 v1) v2 ltac:(lia)) as G2a. pose proof (lor_ge_r (Z.lor v0 v1) v2 L01) as G2.
  pose proof (lor_ge_l v0 v1 ltac:(lia)) as G0. pose proof (lor_ge_r v0 v1 ltac:(lia)) as G1.
  assert (V0 : v0 <= 1114111) by lia. assert (V1 : v1 <= 1114111) by lia. assert (V2 : v2 <= 1114111) by lia. assert (V3 : v3 <= 1114111) by lia.
  unfold not_qb.
  repeat split; intro E; subst;
    match goal with
    | _ : T (630 + _) <= _ |- _ => idtac
    | _ => idtac
    end.
  all: try (pose proof (Ht 630 34 ltac:(auto) ltac:(auto)); unfold v0 in V0; lia).
  all: try (pose proof (Ht 630 92 ltac:(auto) ltac:(auto)); unfold v0 in V0; lia).
  all: try (pose proof (Ht 420 34 ltac:(auto) ltac:(auto)); unfold v1 in V1; lia).
  all: try (pose proof (Ht 420 92 ltac:(auto) ltac:(auto)); unfold v1 in V1; lia).
  all: try (pose proof (Ht 210 34 ltac:(auto) ltac:(auto)); unfold v2 in V2; lia).
  all: try (pose proof (Ht 210 92 ltac:(auto) ltac:(auto)); unfold v2 in V2; lia).
  all: try (pose proof (Ht 0 34 ltac:(auto) ltac:(auto)); unfold v3 in V3; lia).
  all: try (pose proof (Ht 0 92 ltac:(auto) ltac:(auto)); unfold v3 in V3; lia).
Qed.

Section Runs.
  Variable get : Z -> Z.

  Definition nonstop (b : Z) : Prop := b <> 0 /\ b <> 32.
  Definition run (p0 p : Z) : Prop := forall q, p0 <= q < p -> nonstop (get q).

  Lemma run_refl : forall p, run p p.
  Proof. intros p q Hq. lia. Qed.

  Lemma run_step : forall p0 p, run p0 p -> nonstop (get p) -> run p0 (p + 1).
  Proof. intros p0 p H Hn q Hq. destruct (Z.eq_dec q p) as [->|]; [exact Hn|apply H; lia]. Qed.

  Lemma run_skip : forall p0 p m, run p0 p -> (forall t, 0 <= t < m -> nonstop (get (p + t))) -> run p0 (p + m).
  Proof.
    intros p0 p m H Hn q Hq. destruct (Z_lt_ge_dec q p) as [Hl|Hg]; [apply H; lia|].
    replace q with (p + (q - p)) by lia. apply Hn. lia.
  Qed.

  Lemma run_bound : forall p0 p e, run p0 p -> p0 <= e -> ~ nonstop (get e) -> p <= e.
  Proof. intros p0 p e H He Hs. destruct (Z_le_gt_dec p e); [assumption|]. exfalso. apply Hs. apply H. lia. Qed.

  Lemma digit_nonstop : forall b, 48 <= b <= 57 -> nonstop b.
  Proof. intros b H; unfold nonstop; lia. Qed.
  Lemma hinib3_nonstop : forall b, 48 <= b <= 63 -> nonstop b.
  Proof. intros b H; unfold nonstop; lia. Qed.
  Lemma numchar_nonstop : forall b, (48 <= b <= 57 \/ b = 43 \/ b = 45 \/ b = 46 \/ b = 69 \/ b = 101) -> nonstop b.
  Proof. intros b H; unfold nonstop; lia. Qed.
End Runs.

Lemma run_buf_bound : forall bs p0 p, run (B bs) p0 p -> p0 <= blen bs -> p <= blen bs.
Proof.
  intros bs p0 p H H0. apply (run_bound (B bs) p0 p (blen bs) H H0).
  rewrite B_pad by lia. unfold nonstop. lia.
Qed.

Definition C (bs : list Z) (i0 : Z) (q : Z) : Z :=
  if q <? blen bs - i0 then B bs (i0 + q) else 32.

Lemma run_copy_bound : forall bs i0 p0 p, run (C bs i0) p0 p -> p0 <= blen bs - i0 -> p <= blen bs - i0.
Proof.
  intros bs i0 p0 p H H0. apply (run_bound (C bs i0) p0 p (blen bs - i0) H H0).
  unfold C. rewrite (proj2 (Z.ltb_ge _ _)) by lia. unfold nonstop. lia.
Qed.
