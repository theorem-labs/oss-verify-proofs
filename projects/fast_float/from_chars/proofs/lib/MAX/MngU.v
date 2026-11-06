(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocInv.

Module MngLedger.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition w64' (z : Z) : word := Z_to_bv 64 z.

Lemma u_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma u_Z_to_bv : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

(* [comment removed for export] *)
Definition ecov (e : word * word) (a k : Z) : Prop :=
  bv_unsigned (fst e) <= a /\ a + k <= bv_unsigned (fst e) + bv_unsigned (snd e).

Definition edisj (e1 e2 : word * word) : Prop := iv_overlap (fst e1) (snd e1) (fst e2) (snd e2) = false.

Lemma iv_overlap_false : forall a1 n1 a2 n2,
  iv_overlap a1 n1 a2 n2 = false ->
  bv_unsigned a1 + bv_unsigned n1 <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned n2 <= bv_unsigned a1.
Proof.
  intros a1 n1 a2 n2 H. unfold iv_overlap in H. apply andb_false_iff in H as [H|H]; apply Z.ltb_ge in H; lia.
Qed.

(* [comment removed for export] *)
Lemma rf_disj : forall E lo n e b k, region_free E lo n = true -> In e E -> ecov e b k ->
  ranges_disjoint (bv_unsigned lo, bv_unsigned n) (b, k).
Proof.
  intros E lo n [a sz] b k Hf Hin (H1 & H2). pose proof (region_free_In E lo n a sz Hf Hin) as Ho.
  apply iv_overlap_false in Ho. unfold ranges_disjoint. cbn [fst snd] in *. lia.
Qed.

Lemma map_has_In : forall l a n, map_has l a n = true <-> In (a, n) l.
Proof.
  intros l a n. unfold map_has. rewrite existsb_exists. split.
  - intros ([x y] & Hin & E). apply andb_true_iff in E as [E1 E2]. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2.
    cbn [fst snd] in *. subst. exact Hin.
  - intros Hin. exists (a, n). split; [exact Hin|]. cbn [fst snd]. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma map_contains_In : forall l lo n, map_contains l lo n = true <-> exists e, In e l /\ ecov e (bv_unsigned lo) (bv_unsigned n).
Proof.
  intros l lo n. unfold map_contains. rewrite existsb_exists. unfold ecov. split.
  - intros (e & Hin & E). apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. exists e. auto.
  - intros (e & Hin & E1 & E2). exists e. split; [exact Hin|]. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma pairwise_filter : forall {A} (R : A -> A -> Prop) (f : A -> bool) l, pairwise R l -> pairwise R (List.filter f l).
Proof.
  intros A R f l. induction l as [|x t IH]; intros H; cbn; [exact I|]. destruct H as (Hx & Ht).
  destruct (f x); [split; [intros y Hy; apply filter_In in Hy as [Hy _]; exact (Hx y Hy) | exact (IH Ht)] | exact (IH Ht)].
Qed.

Lemma pairwise_In2 : forall {A} (R : A -> A -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
  intros A R l. induction l as [|z t IH]; intros x y H Hx Hy Hne; [destruct Hx|]. destruct H as (Hz & Ht).
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y Ht Hx Hy Hne).
Qed.

(* [comment removed for export] *)
Lemma entry_same_base : forall l e1 e2, pairwise edisj l -> (forall e, In e l -> 0 < bv_unsigned (snd e)) ->
  In e1 l -> In e2 l -> fst e1 = fst e2 -> e1 = e2.
Proof.
  intros l e1 e2 HP Hpos H1 H2 E. destruct (decide (e1 = e2)) as [->|Hne]; [reflexivity|]. exfalso.
  pose proof (Hpos e1 H1) as P1. pose proof (Hpos e2 H2) as P2.
  destruct (pairwise_In2 edisj l e1 e2 HP H1 H2 Hne) as [D|D]; unfold edisj in D; apply iv_overlap_false in D; rewrite E in D; lia.
Qed.

(* [comment removed for export] *)
Lemma covered_remove : forall l a e x k, In e l -> ecov e x k -> fst e <> a -> exists e', In e' (map_remove l a) /\ ecov e' x k.
Proof.
  intros l a e x k Hin Hc Hne. exists e. split; [|exact Hc]. unfold map_remove. apply filter_In. split; [exact Hin|].
  apply negb_true_iff. destruct (bv_eqb (fst e) a) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
Qed.

Lemma In_map_remove : forall l a e, In e (map_remove l a) -> In e l.
Proof. intros l a e H. unfold map_remove in H. apply filter_In in H as [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma ecov_subtract : forall l x k lo hi, 0 < k -> (x + k <= lo \/ hi <= x) -> 0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  (exists e, In e l /\ ecov e x k) -> exists e', In e' (maps_subtract l lo hi) /\ ecov e' x k.
Proof.
  intros l x k lo hi Hk Hd Hlo Hlh Hhi (e & Hin & Hc). induction l as [|[a sz] t IH]; [destruct Hin|].
  cbn [maps_subtract]. destruct Hin as [<-|Hin].
  - unfold ecov in Hc. cbn [fst snd] in Hc. pose proof (u_range a) as Ra. pose proof (u_range sz) as Rs.
    unfold iv_subtract. destruct Hd as [Hd|Hd].
    + assert (Hal : bv_unsigned a < lo) by lia.
      exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). split.
      * apply in_or_app. left. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _) Hal). left. reflexivity.
      * unfold ecov. cbn [fst snd]. rewrite u_Z_to_bv by lia. lia.
    + assert (Hhl : hi < bv_unsigned a + bv_unsigned sz) by lia.
      exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)). split.
      * apply in_or_app. left. apply in_or_app. right. rewrite (proj2 (Z.ltb_lt _ _) Hhl). left. reflexivity.
      * unfold ecov. cbn [fst snd]. rewrite !u_Z_to_bv by lia. lia.
  - destruct (IH Hin) as (e' & H1 & H2). exists e'. split; [apply in_or_app; right; exact H1 | exact H2].
Qed.
End MngLedger.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition Um (md : Model) : Z :=
  vm_backing_used md + 4096 * Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sumr (f : Z -> Z) (b : Z) (k : nat) : Z :=
  match k with O => 0 | S k' => f b + sumr f (b + 1) k' end.

Lemma sumr_split : forall f k1 b k2, sumr f b (k1 + k2) = sumr f b k1 + sumr f (b + Z.of_nat k1) k2.
Proof.
  intros f k1. induction k1 as [|k1 IH]; intros b k2; cbn [sumr Nat.add].
  - rewrite Z.add_0_r. ring.
  - rewrite IH. replace (b + 1 + Z.of_nat k1) with (b + Z.of_nat (S k1)) by lia. ring.
Qed.

Lemma sumr_ext : forall f g k b, (forall x, b <= x < b + Z.of_nat k -> f x = g x) -> sumr f b k = sumr g b k.
Proof.
  intros f g k. induction k as [|k IH]; intros b H; cbn [sumr]; [reflexivity|].
  rewrite (H b) by lia. rewrite (IH (b + 1)) by (intros x Hx; apply H; lia). reflexivity.
Qed.

Lemma sumr_le : forall f g k b, (forall x, f x <= g x) -> sumr f b k <= sumr g b k.
Proof. intros f g k. induction k as [|k IH]; intros b H; cbn [sumr]; [lia|]. pose proof (H b). pose proof (IH (b + 1) H). lia. Qed.

Lemma sumr_nonneg : forall f k b, (forall x, 0 <= f x) -> 0 <= sumr f b k.
Proof. intros f k. induction k as [|k IH]; intros b H; cbn [sumr]; [lia|]. pose proof (H b). pose proof (IH (b + 1) H). lia. Qed.

Lemma sumr_one : forall k b, sumr (fun _ => 1) b k = Z.of_nat k.
Proof. intros k. induction k as [|k IH]; intros b; cbn [sumr]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumr_zero : forall f k b, (forall x, b <= x < b + Z.of_nat k -> f x = 0) -> sumr f b k = 0.
Proof.
  intros f k b H. rewrite (sumr_ext f (fun _ => 0) k b H). clear H. revert b.
  induction k as [|k IH]; intros b; cbn [sumr]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sumr3 : forall f A S p1 p2, A <= p1 -> p1 <= p2 -> p2 <= A + S ->
  sumr f A (Z.to_nat S) = sumr f A (Z.to_nat (p1 - A)) + sumr f p1 (Z.to_nat (p2 - p1)) + sumr f p2 (Z.to_nat (A + S - p2)).
Proof.
  intros f A S p1 p2 H1 H2 H3.
  replace (Z.to_nat S) with (Z.to_nat (p1 - A) + (Z.to_nat (p2 - p1) + Z.to_nat (A + S - p2)))%nat by lia.
  rewrite !sumr_split. rewrite !Z2Nat.id by lia. replace (A + (p1 - A)) with p1 by ring. replace (p1 + (p2 - p1)) with p2 by ring. ring.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wt (ps : list (word * word)) (f : Z -> Z) : Z :=
  fold_right (fun p acc => sumr f (bv_unsigned (fst p)) (Z.to_nat (bv_unsigned (snd p))) + acc) 0 ps.

Lemma Wt_nil : forall f, Wt [] f = 0.
Proof. reflexivity. Qed.

Lemma Wt_cons : forall p ps f, Wt (p :: ps) f = sumr f (bv_unsigned (fst p)) (Z.to_nat (bv_unsigned (snd p))) + Wt ps f.
Proof. reflexivity. Qed.

Lemma Wt_app : forall l1 l2 f, Wt (l1 ++ l2) f = Wt l1 f + Wt l2 f.
Proof. intros l1 l2 f. induction l1 as [|p l1 IH]; cbn [app]; [rewrite Wt_nil; ring|]. rewrite !Wt_cons, IH. ring. Qed.

Lemma Wt_ext : forall ps f g, (forall p x, In p ps -> bv_unsigned (fst p) <= x < bv_unsigned (fst p) + bv_unsigned (snd p) -> f x = g x) ->
  Wt ps f = Wt ps g.
Proof.
  intros ps f g. induction ps as [|p ps IH]; intros H; [reflexivity|]. rewrite !Wt_cons.
  rewrite (sumr_ext f g) by (intros x Hx; apply (H p x (or_introl eq_refl)); pose proof (bv_unsigned_in_range _ (snd p)); lia).
  rewrite IH by (intros q x Hq Hx; exact (H q x (or_intror Hq) Hx)). reflexivity.
Qed.

Lemma Wt_nonneg : forall ps f, (forall x, 0 <= f x) -> 0 <= Wt ps f.
Proof. intros ps f Hf. induction ps as [|p ps IH]; [rewrite Wt_nil; lia|]. rewrite Wt_cons. pose proof (sumr_nonneg f (Z.to_nat (bv_unsigned (snd p))) (bv_unsigned (fst p)) Hf). lia. Qed.

Lemma Wt_filter : forall (P : word * word -> bool) ps f, (forall x, 0 <= f x) -> Wt (List.filter P ps) f <= Wt ps f.
Proof.
  intros P ps f Hf. induction ps as [|p ps IH]; [cbn; lia|]. cbn [List.filter]. rewrite Wt_cons.
  pose proof (sumr_nonneg f (Z.to_nat (bv_unsigned (snd p))) (bv_unsigned (fst p)) Hf).
  destruct (P p); [rewrite Wt_cons|]; lia.
Qed.

Lemma live_bytes_Wt : forall ps, live_bytes ps = Wt ps (fun _ => 1).
Proof.
  induction ps as [|[a sz] ps IH]; [reflexivity|]. cbn [live_bytes]. rewrite Wt_cons, IH, sumr_one. cbn [snd].
  pose proof (bv_unsigned_in_range _ sz). rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inI (lo hi x : Z) : bool := (lo <=? x) && (x <? hi).
Definition cutf (lo hi : Z) (f : Z -> Z) (x : Z) : Z := if inI lo hi x then 0 else f x.

Definition inrange (ps : list (word * word)) : Prop :=
  forall p, In p ps -> bv_unsigned (fst p) + bv_unsigned (snd p) <= 2^64.

Lemma u64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_small. exact Hz. Qed.

Lemma urange : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma iv_subtract_Wt : forall a sz lo hi f, 0 <= lo <= hi -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  Wt (iv_subtract a sz lo hi) f = sumr (cutf lo hi f) (bv_unsigned a) (Z.to_nat (bv_unsigned sz)).
Proof.
  intros a sz lo hi f Hlh Hr. unfold iv_subtract.
  set (A := bv_unsigned a) in *. set (S := bv_unsigned sz) in *.
  pose proof (urange a) as RA. pose proof (urange sz) as RS. fold A S in RA, RS.
  rewrite (sumr3 (cutf lo hi f) A S (Z.max A (Z.min lo (A + S))) (Z.max (Z.max A (Z.min lo (A + S))) (Z.min hi (A + S)))) by lia.
  destruct (A <? lo) eqn:E1; destruct (hi <? A + S) eqn:E2; apply Z.ltb_lt in E1 || apply Z.ltb_ge in E1;
    apply Z.ltb_lt in E2 || apply Z.ltb_ge in E2; cbn [app]; rewrite ?Wt_cons, ?Wt_nil; cbn [fst snd]; fold A S; rewrite ?u64 by lia.
  - (* [comment removed for export] *)
    replace (Z.max A (Z.min lo (A + S))) with lo by lia. replace (Z.max lo (Z.min hi (A + S))) with hi by lia.
    replace (Z.min S (lo - A)) with (lo - A) by lia. replace (Z.max A hi) with hi by lia.
    rewrite (sumr_zero (cutf lo hi f) (Z.to_nat (hi - lo)) lo)
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace ((lo <=? x) && (x <? hi)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); reflexivity).
    rewrite (sumr_ext (cutf lo hi f) f (Z.to_nat (lo - A)) A)
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace (x <? hi) with true by (symmetry; apply Z.ltb_lt; lia);
          replace (lo <=? x) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
    rewrite (sumr_ext (cutf lo hi f) f (Z.to_nat (A + S - hi)) hi)
      by (intros x Hx; unfold cutf, inI; replace (x <? hi) with false by (symmetry; apply Z.ltb_ge; lia); rewrite andb_false_r; reflexivity).
    repeat match goal with |- context [sumr ?f ?b (Z.to_nat 0)] => change (sumr f b (Z.to_nat 0)) with 0 end. ring.
  - (* [comment removed for export] *)
    replace (Z.max (Z.max A (Z.min lo (A + S))) (Z.min hi (A + S))) with (A + S) by lia.
    replace (Z.max A (Z.min lo (A + S))) with (A + Z.min S (lo - A)) by lia.
    rewrite (sumr_zero (cutf lo hi f) (Z.to_nat (A + S - (A + Z.min S (lo - A)))) (A + Z.min S (lo - A)))
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace ((lo <=? x) && (x <? hi)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); reflexivity).
    replace (A + S - (A + S)) with 0 by ring. cbn [Z.to_nat sumr].
    replace (A + Z.min S (lo - A) - A) with (Z.min S (lo - A)) by ring.
    rewrite (sumr_ext (cutf lo hi f) f (Z.to_nat (Z.min S (lo - A))) A)
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace (lo <=? x) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
    repeat match goal with |- context [sumr ?f ?b (Z.to_nat 0)] => change (sumr f b (Z.to_nat 0)) with 0 end. ring.
  - (* [comment removed for export] *)
    replace (Z.max A (Z.min lo (A + S))) with A by lia. replace (Z.max A (Z.min hi (A + S))) with (Z.max A hi) by lia.
    replace (A - A) with 0 by ring. cbn [Z.to_nat sumr].
    rewrite (sumr_zero (cutf lo hi f) (Z.to_nat (Z.max A hi - A)) A)
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace ((lo <=? x) && (x <? hi)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); reflexivity).
    rewrite (sumr_ext (cutf lo hi f) f (Z.to_nat (A + S - Z.max A hi)) (Z.max A hi))
      by (intros x Hx; unfold cutf, inI; replace (x <? hi) with false by (symmetry; apply Z.ltb_ge; lia); rewrite andb_false_r; reflexivity).
    repeat match goal with |- context [sumr ?f ?b (Z.to_nat 0)] => change (sumr f b (Z.to_nat 0)) with 0 end. ring.
  - (* [comment removed for export] *)
    replace (Z.max A (Z.min lo (A + S))) with A by lia. replace (Z.max A (Z.min hi (A + S))) with (A + S) by lia.
    replace (A - A) with 0 by ring. replace (A + S - (A + S)) with 0 by ring. cbn [Z.to_nat sumr].
    rewrite (sumr_zero (cutf lo hi f) (Z.to_nat (A + S - A)) A)
      by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold cutf, inI; replace ((lo <=? x) && (x <? hi)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); reflexivity).
    repeat match goal with |- context [sumr ?f ?b (Z.to_nat 0)] => change (sumr f b (Z.to_nat 0)) with 0 end. ring.
Qed.

Lemma iv_subtract_inrange : forall a sz lo hi, 0 <= lo -> bv_unsigned a + bv_unsigned sz <= 2^64 -> inrange (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlo Hr p Hp. unfold iv_subtract in Hp. pose proof (urange a). pose proof (urange sz).
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    apply Z.ltb_lt in E1 || apply Z.ltb_ge in E1; apply Z.ltb_lt in E2 || apply Z.ltb_ge in E2; cbn [app In] in Hp;
    repeat (destruct Hp as [<-|Hp]; [cbn [fst snd]; rewrite ?u64 by lia; lia|]); destruct Hp.
Qed.

Lemma inrange_app : forall l1 l2, inrange l1 -> inrange l2 -> inrange (l1 ++ l2).
Proof. intros l1 l2 H1 H2 p Hp. apply in_app_iff in Hp as [Hp|Hp]; [exact (H1 p Hp) | exact (H2 p Hp)]. Qed.

Lemma maps_subtract_inrange : forall ps lo hi, 0 <= lo -> inrange ps -> inrange (maps_subtract ps lo hi).
Proof.
  induction ps as [|[a sz] ps IH]; intros lo hi Hlo H; [intros p []|]. cbn [maps_subtract].
  apply inrange_app; [apply iv_subtract_inrange; [exact Hlo | exact (H (a, sz) (or_introl eq_refl))]|].
  apply IH; [exact Hlo|]. intros p Hp. exact (H p (or_intror Hp)).
Qed.

Lemma maps_subtract_Wt : forall ps lo hi f, 0 <= lo <= hi -> inrange ps -> Wt (maps_subtract ps lo hi) f = Wt ps (cutf lo hi f).
Proof.
  induction ps as [|[a sz] ps IH]; intros lo hi f Hlh H; [reflexivity|]. cbn [maps_subtract]. rewrite Wt_app, Wt_cons.
  rewrite iv_subtract_Wt by (first [exact Hlh | exact (H (a, sz) (or_introl eq_refl))]).
  rewrite IH by (first [exact Hlh | intros p Hp; exact (H p (or_intror Hp))]). reflexivity.
Qed.

Fixpoint cutall (C : list (word * word)) (f : Z -> Z) : Z -> Z :=
  match C with
  | [] => f
  | (c, k) :: rest => cutf (bv_unsigned c) (bv_unsigned c + bv_unsigned k) (cutall rest f)
  end.

Lemma msa_Wt : forall C ps f, inrange ps -> Wt (maps_subtract_all ps C) f = Wt ps (cutall C f).
Proof.
  induction C as [|[c k] C IH]; intros ps f H; [reflexivity|]. cbn [maps_subtract_all cutall].
  pose proof (urange c). pose proof (urange k).
  rewrite IH by (apply maps_subtract_inrange; [lia | exact H]).
  apply maps_subtract_Wt; [lia | exact H].
Qed.

Definition inC (C : list (word * word)) (x : Z) : bool := existsb (fun e => inI (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) x) C.

Lemma cutall_spec : forall C f x, cutall C f x = if inC C x then 0 else f x.
Proof.
  induction C as [|[c k] C IH]; intros f x; [reflexivity|]. cbn [cutall inC existsb fst snd]. unfold cutf at 1. rewrite IH.
  destruct (inI (bv_unsigned c) (bv_unsigned c + bv_unsigned k) x); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma inC_subtract : forall C lo hi x, 0 <= lo <= hi -> hi < 2^64 ->
  inC (maps_subtract C lo hi) x = inC C x && negb (inI lo hi x).
Proof.
  induction C as [|[c k] C IH]; intros lo hi x Hlh Hh; [reflexivity|]. cbn [maps_subtract]. unfold inC in *.
  rewrite existsb_app. rewrite IH by assumption. cbn [existsb fst snd].
  pose proof (urange c) as Rc. pose proof (urange k) as Rk.
  assert (Hp : existsb (fun e => inI (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) x) (iv_subtract c k lo hi) =
               inI (bv_unsigned c) (bv_unsigned c + bv_unsigned k) x && negb (inI lo hi x)).
  { unfold iv_subtract, inI.
    destruct (bv_unsigned c <? lo) eqn:E1; destruct (hi <? bv_unsigned c + bv_unsigned k) eqn:E2;
      apply Z.ltb_lt in E1 || apply Z.ltb_ge in E1; apply Z.ltb_lt in E2 || apply Z.ltb_ge in E2; cbn [app existsb fst snd];
      rewrite ?u64 by lia; rewrite ?orb_false_r;
      destruct (Z.leb_spec (bv_unsigned c) x); destruct (Z.ltb_spec x (bv_unsigned c + bv_unsigned k));
      destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x hi); cbn [andb orb negb];
      repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
      cbn [andb orb negb]; first [reflexivity | lia]. }
  rewrite Hp. destruct (inI (bv_unsigned c) (bv_unsigned c + bv_unsigned k) x); destruct (inI lo hi x);
    destruct (existsb _ C); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pairwise_In2 : forall {X} (R : X -> X -> Prop) l x y, MallocInv.pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|]. destruct H as (Hz & Hl).
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y Hl Hx Hy Hne).
Qed.

Lemma filter_length_le' : forall {X} (P : X -> bool) l, (length (List.filter P l) <= length l)%nat.
Proof. intros X P l. induction l as [|x l IH]; [cbn; lia|]. cbn [List.filter length]. destruct (P x); cbn [length]; lia. Qed.

Theorem backing_munmap_next : forall md A N,
  m_vm_lazy md = [] -> MallocInv.pairwise edisj (vm_maps (m_vmmaps md)) -> inrange (vm_maps (m_vmmaps md)) ->
  In (A, N) (vm_maps (m_vmmaps md)) -> bv_unsigned A + bv_unsigned N < 2^64 ->
  vm_backing_used (munmap_next A N md) <= vm_backing_used md.
Proof.
  intros md A N Hlz Hdj Hrg Hin HAN.
  unfold vm_backing_used, munmap_next, vm_forget_range, with_vm_backing, with_vmmaps, m_vm_lazy, m_vm_materialized, m_vmmaps in *.
  cbn [vmst_maps vmst_lazy vmst_materialized m_vm] in *. rewrite Hlz. cbn [maps_subtract maps_subtract_all].
  set (M := vm_maps (vmst_maps (m_vm md))) in *. set (C := vm_noaccess (vmst_maps (m_vm md))).
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess].
  pose proof (urange A) as RA. pose proof (urange N) as RN.
  assert (HM' : inrange (map_remove M A)).
  { intros p Hp. unfold map_remove in Hp. apply filter_In in Hp as (Hp & _). exact (Hrg p Hp). }
  rewrite !live_bytes_Wt. rewrite (msa_Wt _ _ _ HM'), (msa_Wt _ _ _ Hrg).
  assert (E : Wt (map_remove M A) (cutall (maps_subtract C (bv_unsigned A) (bv_unsigned A + bv_unsigned N)) (fun _ => 1)) =
              Wt (map_remove M A) (cutall C (fun _ => 1))).
  { apply Wt_ext. intros p x Hp Hx. unfold map_remove in Hp. apply filter_In in Hp as (Hp & Hne).
    rewrite !cutall_spec. rewrite inC_subtract by lia.
    assert (Hnx : inI (bv_unsigned A) (bv_unsigned A + bv_unsigned N) x = false).
    { assert (Hpn : p <> (A, N)) by (intros ->; cbn [fst] in Hne; unfold bv_eqb in Hne; rewrite Z.eqb_refl in Hne; discriminate).
      destruct (pairwise_In2 edisj M p (A, N) Hdj Hp Hin Hpn) as [D|D]; apply iv_overlap_false in D; cbn [fst snd] in D;
        unfold inI; destruct (Z.leb_spec (bv_unsigned A) x); destruct (Z.ltb_spec x (bv_unsigned A + bv_unsigned N)); cbn; try reflexivity; lia. }
    rewrite Hnx. cbn [negb]. rewrite andb_true_r. reflexivity. }
  rewrite E.
  pose proof (Wt_filter (fun p => negb (bv_eqb (fst p) A)) M (cutall C (fun _ => 1))) as F.
  assert (Hnn : forall x, 0 <= cutall C (fun _ => 1) x) by (intros x; rewrite cutall_spec; destruct (inC C x); lia).
  specialize (F Hnn). unfold map_remove.
  pose proof (filter_length_le' (page_outside_range (bv_unsigned A) (bv_unsigned A + bv_unsigned N)) (vmst_materialized (m_vm md))) as Lm.
  unfold page_size. unfold C in *. lia.
Qed.

Theorem U_munmap_next : forall md A N,
  m_vm_lazy md = [] -> MallocInv.pairwise edisj (vm_maps (m_vmmaps md)) -> inrange (vm_maps (m_vmmaps md)) ->
  In (A, N) (vm_maps (m_vmmaps md)) -> bv_unsigned A + bv_unsigned N < 2^64 ->
  Um (munmap_next A N md) <= Um md.
Proof.
  intros md A N Hlz Hdj Hrg Hin HAN. unfold Um.
  pose proof (backing_munmap_next md A N Hlz Hdj Hrg Hin HAN) as B.
  assert (L : (length (vm_reserved (m_vmmaps (munmap_next A N md)) ++ vm_maps (m_vmmaps (munmap_next A N md))) <=
               length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)))%nat).
  { unfold munmap_next, vm_forget_range, with_vm_backing, with_vmmaps, m_vmmaps. cbn [vmst_maps m_vm vm_reserved vm_maps].
    rewrite !length_app. unfold map_remove. pose proof (filter_length_le' (fun p : word * word => negb (bv_eqb (fst p) A)) (vm_maps (vmst_maps (m_vm md)))). lia. }
  lia.
Qed.
