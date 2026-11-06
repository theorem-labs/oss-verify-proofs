(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition ind (b : bool) : Z := if b then 1 else 0.

Lemma ind_range : forall b, 0 <= ind b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma inI_true : forall lo hi x, inI lo hi x = true <-> lo <= x < hi.
Proof. intros lo hi x. unfold inI. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inI_false : forall lo hi x, inI lo hi x = false <-> ~ (lo <= x < hi).
Proof. intros lo hi x. rewrite <- not_true_iff_false, inI_true. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sumr_add : forall f g k b, sumr (fun x => f x + g x) b k = sumr f b k + sumr g b k.
Proof. intros f g k. induction k as [|k IH]; intros b; cbn [sumr]; [reflexivity|]. rewrite IH. ring. Qed.

Lemma sumr_0 : forall k b, sumr (fun _ => 0) b k = 0.
Proof. intros k. induction k as [|k IH]; intros b; cbn [sumr]; [reflexivity|]. rewrite IH. ring. Qed.

Lemma Wt_add : forall ps f g, Wt ps (fun x => f x + g x) = Wt ps f + Wt ps g.
Proof. intros ps f g. induction ps as [|p ps IH]; [reflexivity|]. rewrite !Wt_cons, sumr_add, IH. ring. Qed.

Lemma Wt_0 : forall ps, Wt ps (fun _ => 0) = 0.
Proof. intros ps. induction ps as [|p ps IH]; [reflexivity|]. rewrite Wt_cons, sumr_0, IH. ring. Qed.

Lemma Wt_mono : forall ps f g, (forall x, f x <= g x) -> Wt ps f <= Wt ps g.
Proof.
  intros ps f g H. induction ps as [|p ps IH]; [rewrite !Wt_nil; lia|]. rewrite !Wt_cons.
  pose proof (sumr_le f g (Z.to_nat (bv_unsigned (snd p))) (bv_unsigned (fst p)) H). lia.
Qed.

Lemma Wt_if : forall ps (c : bool) f, Wt ps (fun x => if c then f x else 0) = if c then Wt ps f else 0.
Proof. intros ps [|] f; [reflexivity | exact (Wt_0 ps)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sumr_clip : forall f a n lo hi, 0 <= n ->
  (forall x, a <= x < a + n -> (x < lo \/ hi <= x) -> f x = 0) ->
  sumr f a (Z.to_nat n) =
  sumr f (Z.max a (Z.min lo (a + n))) (Z.to_nat (Z.max (Z.max a (Z.min lo (a + n))) (Z.min hi (a + n)) - Z.max a (Z.min lo (a + n)))).
Proof.
  intros f a n lo hi Hn H.
  set (c1 := Z.max a (Z.min lo (a + n))). set (c2 := Z.max c1 (Z.min hi (a + n))).
  rewrite (sumr3 f a n c1 c2) by (unfold c1, c2; lia).
  rewrite (sumr_zero f (Z.to_nat (c1 - a)) a) by (intros x Hx; rewrite Z2Nat.id in Hx by (unfold c1; lia); apply H; unfold c1 in *; lia).
  rewrite (sumr_zero f (Z.to_nat (a + n - c2)) c2) by (intros x Hx; rewrite Z2Nat.id in Hx by (unfold c2, c1; lia); apply H; unfold c2, c1 in *; lia).
  ring.
Qed.

Lemma sumr_support : forall f a n lo hi, 0 <= n -> lo <= hi -> (forall x, (x < lo \/ hi <= x) -> f x = 0) ->
  sumr f a (Z.to_nat n) = sumr (fun x => if inI a (a + n) x then f x else 0) lo (Z.to_nat (hi - lo)).
Proof.
  intros f a n lo hi Hn Hlh H.
  rewrite (sumr_clip f a n lo hi Hn) by (intros x _ Hx; exact (H x Hx)).
  replace (hi - lo) with (hi - lo) by ring.
  rewrite (sumr_clip (fun x => if inI a (a + n) x then f x else 0) lo (hi - lo) a (a + n)) by
    (first [lia | intros x _ Hx; replace (inI a (a + n) x) with false by (symmetry; apply inI_false; lia); reflexivity]).
  replace (lo + (hi - lo)) with hi by ring.
  destruct (Z_lt_le_dec (Z.max a lo) (Z.min (a + n) hi)) as [Hne|Hem].
  - replace (Z.max a (Z.min lo (a + n))) with (Z.max a lo) by lia.
    replace (Z.max lo (Z.min a hi)) with (Z.max a lo) by lia.
    replace (Z.max (Z.max a lo) (Z.min hi (a + n))) with (Z.min (a + n) hi) by lia.
    replace (Z.max (Z.max a lo) (Z.min (a + n) hi)) with (Z.min (a + n) hi) by lia.
    apply sumr_ext. intros x Hx. rewrite Z2Nat.id in Hx by lia.
    replace (inI a (a + n) x) with true by (symmetry; apply inI_true; lia). reflexivity.
  - replace (Z.to_nat (Z.max (Z.max a (Z.min lo (a + n))) (Z.min hi (a + n)) - Z.max a (Z.min lo (a + n)))) with 0%nat by lia.
    replace (Z.to_nat (Z.max (Z.max lo (Z.min a hi)) (Z.min (a + n) hi) - Z.max lo (Z.min a hi))) with 0%nat by lia.
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sumr_sub : forall f a n lo hi, (forall x, 0 <= f x) -> a <= lo -> lo <= hi -> hi <= a + n ->
  sumr f lo (Z.to_nat (hi - lo)) <= sumr f a (Z.to_nat n).
Proof.
  intros f a n lo hi Hf H1 H2 H3. rewrite (sumr3 f a n lo hi) by lia.
  pose proof (sumr_nonneg f (Z.to_nat (lo - a)) a Hf). pose proof (sumr_nonneg f (Z.to_nat (a + n - hi)) hi Hf). lia.
Qed.

Lemma sumr_ind_full : forall lo hi, lo <= hi -> sumr (fun x => ind (inI lo hi x)) lo (Z.to_nat (hi - lo)) = hi - lo.
Proof.
  intros lo hi H. rewrite (sumr_ext _ (fun _ => 1)) by (intros x Hx; rewrite Z2Nat.id in Hx by lia; replace (inI lo hi x) with true by (symmetry; apply inI_true; lia); reflexivity).
  rewrite sumr_one. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Wt_disj_le : forall ps f lo hi, pairwise edisj ps -> lo <= hi -> (forall x, 0 <= f x) ->
  (forall x, (x < lo \/ hi <= x) -> f x = 0) -> Wt ps f <= sumr f lo (Z.to_nat (hi - lo)).
Proof.
  induction ps as [|p ps IH]; intros f lo hi Hpw Hlh Hf Hs.
  - rewrite Wt_nil. exact (sumr_nonneg f _ lo Hf).
  - destruct Hpw as (Hp & Hpw). rewrite Wt_cons.
    set (A := bv_unsigned (fst p)). set (N := bv_unsigned (snd p)).
    set (g := fun x => if inI A (A + N) x then 0 else f x).
    assert (E : Wt ps f = Wt ps g).
    { apply Wt_ext. intros q x Hq Hx. unfold g. pose proof (Hp q Hq) as D. unfold edisj in D. apply iv_overlap_false in D.
      replace (inI A (A + N) x) with false by (symmetry; apply inI_false; unfold A, N in *; lia). reflexivity. }
    rewrite E. pose proof (IH g lo hi Hpw Hlh ltac:(intros x; unfold g; destruct (inI A (A + N) x); [lia | apply Hf])
                 ltac:(intros x Hx; unfold g; destruct (inI A (A + N) x); [reflexivity | exact (Hs x Hx)])) as IHg.
    rewrite (sumr_support f A N lo hi ltac:(pose proof (urange (snd p)); unfold N; lia) Hlh Hs).
    assert (S : sumr (fun x => if inI A (A + N) x then f x else 0) lo (Z.to_nat (hi - lo)) + sumr g lo (Z.to_nat (hi - lo)) =
                sumr f lo (Z.to_nat (hi - lo))).
    { rewrite <- sumr_add. apply sumr_ext. intros x _. unfold g. destruct (inI A (A + N) x); ring. }
    lia.
Qed.

Lemma Wt_cover : forall ps e f lo hi, In e ps -> (forall x, 0 <= f x) ->
  bv_unsigned (fst e) <= lo -> lo <= hi -> hi <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  sumr f lo (Z.to_nat (hi - lo)) <= Wt ps f.
Proof.
  induction ps as [|p ps IH]; intros e f lo hi Hin Hf H1 H2 H3; [destruct Hin|]. rewrite Wt_cons.
  pose proof (Wt_nonneg ps f Hf). pose proof (sumr_nonneg f (Z.to_nat (bv_unsigned (snd p))) (bv_unsigned (fst p)) Hf).
  destruct Hin as [->|Hin].
  - pose proof (sumr_sub f (bv_unsigned (fst e)) (bv_unsigned (snd e)) lo hi Hf H1 H2 H3). lia.
  - pose proof (IH e f lo hi Hin Hf H1 H2 H3). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint isum (g : nat -> region -> Z) (k : nat) (rs : list region) : Z :=
  match rs with [] => 0 | rg :: rs' => g k rg + isum g (S k) rs' end.

Lemma isum_nonneg : forall g rs k, (forall r rg, 0 <= g r rg) -> 0 <= isum g k rs.
Proof. intros g rs. induction rs as [|rg rs IH]; intros k H; cbn [isum]; [lia|]. pose proof (H k rg). pose proof (IH (S k) H). lia. Qed.

Lemma isum_mono : forall g h rs k, (forall r rg, g r rg <= h r rg) -> isum g k rs <= isum h k rs.
Proof. intros g h rs. induction rs as [|rg rs IH]; intros k H; cbn [isum]; [lia|]. pose proof (H k rg). pose proof (IH (S k) H). lia. Qed.

Lemma isum_mono' : forall g h rs k, (forall r rg, nth_error rs r = Some rg -> g (k + r)%nat rg <= h (k + r)%nat rg) -> isum g k rs <= isum h k rs.
Proof.
  intros g h rs. induction rs as [|rg rs IH]; intros k H; cbn [isum]; [lia|].
  pose proof (H 0%nat rg eq_refl) as E0. rewrite Nat.add_0_r in E0.
  pose proof (IH (S k) ltac:(intros r rg' E; rewrite Nat.add_succ_comm; exact (H (S r) rg' E))). lia.
Qed.

Lemma isum_ext : forall g h rs k, (forall r rg, nth_error rs r = Some rg -> g (k + r)%nat rg = h (k + r)%nat rg) -> isum g k rs = isum h k rs.
Proof.
  intros g h rs. induction rs as [|rg rs IH]; intros k H; cbn [isum]; [reflexivity|].
  pose proof (H 0%nat rg eq_refl) as E0. rewrite Nat.add_0_r in E0. rewrite E0. f_equal. apply IH. intros r rg' E. rewrite Nat.add_succ_comm. exact (H (S r) rg' E).
Qed.

Lemma isum_zero : forall g rs k, (forall r rg, nth_error rs r = Some rg -> g (k + r)%nat rg = 0) -> isum g k rs = 0.
Proof.
  intros g rs k H. rewrite (isum_ext g (fun _ _ => 0) rs k H). clear H. revert k.
  induction rs as [|rg rs IH]; intros k; cbn [isum]; [reflexivity|]. rewrite IH. ring.
Qed.

Lemma isum_term : forall g rs k r rg, (forall r rg, 0 <= g r rg) -> nth_error rs r = Some rg -> g (k + r)%nat rg <= isum g k rs.
Proof.
  intros g rs. induction rs as [|y rs IH]; intros k r rg Hg E; [destruct r; discriminate E|]. cbn [isum].
  pose proof (isum_nonneg g rs (S k) Hg). pose proof (Hg k y).
  destruct r as [|r]; cbn in E.
  - injection E as <-. rewrite Nat.add_0_r. lia.
  - pose proof (IH (S k) r rg Hg E). rewrite <- Nat.add_succ_comm. lia.
Qed.

(* [comment removed for export] *)
Lemma isum_le1 : forall g rs k, (forall r rg, nth_error rs r = Some rg -> 0 <= g (k + r)%nat rg <= 1) ->
  (forall r1 r2 rg1 rg2, r1 <> r2 -> nth_error rs r1 = Some rg1 -> nth_error rs r2 = Some rg2 ->
     g (k + r1)%nat rg1 = 0 \/ g (k + r2)%nat rg2 = 0) ->
  isum g k rs <= 1.
Proof.
  intros g rs. induction rs as [|rg rs IH]; intros k H1 H2; cbn [isum]; [lia|].
  pose proof (H1 0%nat rg eq_refl) as B0. rewrite Nat.add_0_r in B0.
  destruct (Z.eq_dec (g k rg) 0) as [Z0|NZ].
  - rewrite Z0. apply IH.
    + intros r rg' E. rewrite Nat.add_succ_comm. exact (H1 (S r) rg' E).
    + intros r1 r2 rg1 rg2 Hne E1 E2. rewrite !Nat.add_succ_comm.
      exact (H2 (S r1) (S r2) rg1 rg2 ltac:(congruence) E1 E2).
  - rewrite (isum_zero g rs (S k)); [lia|]. intros r rg' E. rewrite Nat.add_succ_comm.
    destruct (H2 0%nat (S r) rg rg' ltac:(discriminate) eq_refl E) as [E0|E0]; [rewrite Nat.add_0_r in E0; contradiction | exact E0].
Qed.

Lemma Wt_isum : forall ps h rs k, Wt ps (fun x => isum (fun r rg => h r rg x) k rs) = isum (fun r rg => Wt ps (h r rg)) k rs.
Proof.
  intros ps h rs. induction rs as [|rg rs IH]; intros k; cbn [isum]; [exact (Wt_0 ps)|].
  rewrite Wt_add, IH. reflexivity.
Qed.

Definition lsum (h : Z -> Z) (l : list Z) : Z := fold_right (fun o acc => h o + acc) 0 l.

Lemma lsum_nil : forall h, lsum h [] = 0.
Proof. reflexivity. Qed.
Lemma lsum_cons : forall h o l, lsum h (o :: l) = h o + lsum h l.
Proof. reflexivity. Qed.

Lemma lsum_zero : forall h l, (forall o, In o l -> h o = 0) -> lsum h l = 0.
Proof.
  intros h l. induction l as [|o l IH]; intros H; [reflexivity|]. rewrite lsum_cons.
  rewrite (H o (or_introl eq_refl)), IH by (intros o' Ho'; exact (H o' (or_intror Ho'))). ring.
Qed.

Lemma lsum_ge : forall h l c, (forall o, In o l -> c <= h o) -> c * Z.of_nat (length l) <= lsum h l.
Proof.
  intros h l c. induction l as [|o l IH]; intros H; [rewrite lsum_nil; cbn; lia|]. rewrite lsum_cons. cbn [length].
  pose proof (H o (or_introl eq_refl)). pose proof (IH (fun o' Ho' => H o' (or_intror Ho'))). lia.
Qed.

Lemma lsum_nonneg : forall h l, (forall o, 0 <= h o) -> 0 <= lsum h l.
Proof. intros h l H. induction l as [|o l IH]; [rewrite lsum_nil; lia|]. rewrite lsum_cons. pose proof (H o). lia. Qed.

Lemma lsum_le1 : forall h l, List.NoDup l -> (forall o, 0 <= h o <= 1) ->
  (forall o1 o2, In o1 l -> In o2 l -> o1 <> o2 -> h o1 = 0 \/ h o2 = 0) -> lsum h l <= 1.
Proof.
  intros h l. induction l as [|o l IH]; intros ND H1 H2; [rewrite lsum_nil; lia|]. rewrite lsum_cons.
  inversion ND as [|o' l' Hno Hnd]; subst.
  destruct (Z.eq_dec (h o) 0) as [Z0|NZ].
  - rewrite Z0. apply IH; [exact Hnd | exact H1|]. intros o1 o2 I1 I2 Hne. exact (H2 o1 o2 (or_intror I1) (or_intror I2) Hne).
  - rewrite (lsum_zero h l); [pose proof (H1 o); lia|]. intros o2 I2.
    destruct (H2 o o2 (or_introl eq_refl) (or_intror I2) ltac:(intros ->; exact (Hno I2))) as [E|E]; [contradiction | exact E].
Qed.

Lemma Wt_lsum : forall ps h l, Wt ps (fun x => lsum (fun o => h o x) l) = lsum (fun o => Wt ps (h o)) l.
Proof.
  intros ps h l. induction l as [|o l IH]; [exact (Wt_0 ps)|]. rewrite lsum_cons.
  rewrite <- IH. rewrite <- Wt_add. apply Wt_ext. intros p x _ _. rewrite lsum_cons. reflexivity.
Qed.
