(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint rangeZ (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S k => lo :: rangeZ (lo + 1) k end.

Lemma rangeZ_in lo n x : In x (rangeZ lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
  revert lo. induction n as [|n IH]; intros lo; [cbn; lia|].
  cbn [rangeZ In]. rewrite IH. lia.
Qed.

Lemma rangeZ_nodup lo n : NoDup (rangeZ lo n).
Proof.
  revert lo. induction n as [|n IH]; intros lo; cbn; constructor; [|apply IH].
  rewrite rangeZ_in. lia.
Qed.

Lemma lsum_zsum f lo n : lsum f (rangeZ lo n) = zsum f lo n.
Proof. revert lo. induction n as [|n IH]; intros lo; [reflexivity|]. cbn [rangeZ lsum]. rewrite IH, zsum_shift. reflexivity. Qed.

Lemma lsum_filter f (P : Z -> bool) l : lsum f (filter P l) = lsum (fun x => if P x then f x else 0) l.
Proof. induction l as [|x r IH]; cbn; [reflexivity|]. destruct (P x); cbn; rewrite IH; lia. Qed.

Lemma filter_nodup {A} (P : A -> bool) l : NoDup l -> NoDup (filter P l).
Proof. apply NoDup_filter. Qed.

Lemma lsum_ind2 (P : Z -> bool) f l a b :
  NoDup l -> In a l -> In b l -> a <> b -> P a = true -> P b = true ->
  (forall c, In c l -> P c = true -> c = a \/ c = b) ->
  lsum (fun c => if P c then f c else 0) l = f a + f b.
Proof.
  intros ND Ia Ib NE Pa Pb ONLY.
  destruct (lsum_in_split l a Ia ND) as (l1 & l2 & E & N1 & N2).
  rewrite E in *. rewrite lsum_app. cbn. rewrite Pa.
  assert (Ib' : In b (l1 ++ l2)).
  { apply in_app_or in Ib. apply in_or_app. destruct Ib as [|[|]]; [tauto|congruence|tauto]. }
  assert (ND' : NoDup (l1 ++ l2)) by (apply NoDup_remove_1 in ND; exact ND).
  destruct (lsum_in_split (l1 ++ l2) b Ib' ND') as (m1 & m2 & E2 & M1 & M2).
  assert (REST : forall c, In c (l1 ++ l2) -> c <> b -> (if P c then f c else 0) = 0).
  { intros c Ic Nc. destruct (P c) eqn:Pc; [|reflexivity]. exfalso.
    assert (In c (l1 ++ a :: l2)) by (apply in_app_or in Ic; apply in_or_app; cbn; tauto).
    destruct (ONLY c H Pc) as [->| ->]; [|congruence]. apply in_app_or in Ic. tauto. }
  assert (lsum (fun c : Z => if P c then f c else 0) (l1 ++ l2) = f b).
  { rewrite E2, lsum_app. cbn. rewrite Pb.
    rewrite (lsum_ext _ (fun _ => 0) m1) by (intros c Ic; apply REST; [rewrite E2; apply in_or_app; cbn; tauto| intros ->; tauto]).
    rewrite (lsum_ext _ (fun _ => 0) m2) by (intros c Ic; apply REST; [rewrite E2; apply in_or_app; cbn; tauto| intros ->; tauto]).
    rewrite !lsum_zero; lia. }
  rewrite lsum_app in H. lia.
Qed.

Lemma lsum_ind0 (P : Z -> bool) f l :
  (forall c, In c l -> P c = false) -> lsum (fun c => if P c then f c else 0) l = 0.
Proof. intros H. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros c Ic. rewrite (H c Ic). reflexivity. Qed.

Section GTree.
Variable g : gtree.
Hypothesis G : gtree_ok g.

Notation lo := (g_lo g).
Notation hi := (g_hi g).
Notation par := (g_par g).
Notation leaf := (g_leaf g).
Notation wt := (g_wt g).
Notation ext := (g_ext g).
Notation depth := (g_depth g).

Definition npos : nat := Z.to_nat (hi - lo + 1).
Definition allpos : list Z := rangeZ lo npos.
Definition nonroot : list Z := rangeZ (lo + 1) (Z.to_nat (hi - lo)).
Definition leaves : list Z := filter leaf allpos.
Definition internals : list Z := filter (fun p => negb (leaf p)) allpos.

Lemma lohi : lo < hi. Proof. exact (go_range g G). Qed.

Lemma allpos_in x : In x allpos <-> lo <= x <= hi.
Proof. unfold allpos, npos. rewrite rangeZ_in. pose proof lohi. rewrite Z2Nat.id by lia. lia. Qed.
Lemma nonroot_in x : In x nonroot <-> lo < x <= hi.
Proof. unfold nonroot. rewrite rangeZ_in. pose proof lohi. rewrite Z2Nat.id by lia. lia. Qed.
Lemma leaves_in x : In x leaves <-> (lo <= x <= hi /\ leaf x = true).
Proof. unfold leaves. rewrite filter_In, allpos_in. tauto. Qed.
Lemma internals_in x : In x internals <-> (lo <= x <= hi /\ leaf x = false).
Proof. unfold internals. rewrite filter_In, allpos_in. destruct (leaf x); cbn; intuition congruence. Qed.
Lemma allpos_nodup : NoDup allpos. Proof. apply rangeZ_nodup. Qed.
Lemma nonroot_nodup : NoDup nonroot. Proof. apply rangeZ_nodup. Qed.
Lemma leaves_nodup : NoDup leaves. Proof. apply filter_nodup, allpos_nodup. Qed.
Lemma internals_nodup : NoDup internals. Proof. apply filter_nodup, allpos_nodup. Qed.

Lemma depth_fuel_S f i : g_depth_fuel g (S f) i = if i <=? lo then 0 else 1 + g_depth_fuel g f (par i).
Proof. reflexivity. Qed.

Lemma depth_fuel_stable : forall f i, lo <= i <= hi -> (Z.to_nat (i - lo) <= f)%nat ->
  g_depth_fuel g f i = g_depth_fuel g (S f) i.
Proof.
  induction f as [|f IH]; intros i Hi Hf.
  - assert (i = lo) by lia. subst i. cbn. rewrite Z.leb_refl. reflexivity.
  - rewrite (depth_fuel_S (S f) i), (depth_fuel_S f i). destruct (Z.leb_spec i lo); [reflexivity|].
    pose proof (go_par_lt g G i ltac:(lia)). rewrite <- IH; [reflexivity|lia|lia].
Qed.

Lemma depth_fuel_stable' : forall f f' i, lo <= i <= hi -> (Z.to_nat (i - lo) <= f)%nat -> (f <= f')%nat ->
  g_depth_fuel g f i = g_depth_fuel g f' i.
Proof.
  intros f f' i Hi Hf Hff. induction Hff; [reflexivity|]. rewrite IHHff. apply depth_fuel_stable; [assumption|lia].
Qed.

Lemma depth_root : depth lo = 0.
Proof. unfold g_depth. pose proof lohi. destruct (Z.to_nat (hi - lo + 1)) eqn:E; cbn; [reflexivity|]. rewrite Z.leb_refl. reflexivity. Qed.

Lemma depth_step i : lo < i <= hi -> depth i = 1 + depth (par i).
Proof.
  intros Hi. unfold g_depth. pose proof (go_par_lt g G i Hi).
  destruct (Z.to_nat (hi - lo + 1)) as [|f] eqn:E; [lia|]. rewrite depth_fuel_S.
  destruct (Z.leb_spec i lo); [lia|]. f_equal.
  apply depth_fuel_stable'; lia.
Qed.

Lemma depth_nonneg i : lo <= i <= hi -> 0 <= depth i.
Proof.
  intros Hi. remember (Z.to_nat (i - lo)) as n eqn:E. revert i Hi E.
  induction n as [n IH] using lt_wf_ind; intros i Hi E.
  destruct (Z.eq_dec i lo) as [->|NE]; [rewrite depth_root; lia|].
  rewrite depth_step by lia. pose proof (go_par_lt g G i ltac:(lia)).
  assert (0 <= depth (par i)) by (apply (IH (Z.to_nat (par i - lo))); lia). lia.
Qed.

Lemma depth_pos i : lo < i <= hi -> 1 <= depth i.
Proof. intros. rewrite depth_step by lia. pose proof (go_par_lt g G i H). pose proof (depth_nonneg (par i) ltac:(lia)). lia. Qed.

Lemma depth_le i : lo <= i <= hi -> depth i <= i - lo.
Proof.
  intros Hi. remember (Z.to_nat (i - lo)) as n eqn:E. revert i Hi E.
  induction n as [n IH] using lt_wf_ind; intros i Hi E.
  destruct (Z.eq_dec i lo) as [->|NE]; [rewrite depth_root; lia|].
  rewrite depth_step by lia. pose proof (go_par_lt g G i ltac:(lia)).
  assert (depth (par i) <= par i - lo) by (apply (IH (Z.to_nat (par i - lo))); lia). lia.
Qed.

Lemma root_internal : leaf lo = false.
Proof.
  pose proof lohi. pose proof (go_par_lt g G (lo + 1) ltac:(lia)).
  replace lo with (par (lo + 1)) by lia. apply (go_par_int g G). lia.
Qed.

Lemma wt_nonneg i : lo <= i <= hi -> 0 <= wt i.
Proof.
  intros Hi. remember (Z.to_nat (hi - i)) as n eqn:E. revert i Hi E.
  induction n as [n IH] using lt_wf_ind; intros i Hi E.
  destruct (leaf i) eqn:L.
  - pose proof (go_wt_leaf g G i Hi L). lia.
  - destruct (go_two g G i Hi L) as (a & b & NE & Ha & Hb & Pa & Pb & _).
    pose proof (go_par_lt g G a Ha). pose proof (go_par_lt g G b Hb).
    rewrite (go_wt_sum g G i a b Hi L Ha Hb NE Pa Pb).
    assert (0 <= wt a) by (apply (IH (Z.to_nat (hi - a))); lia).
    assert (0 <= wt b) by (apply (IH (Z.to_nat (hi - b))); lia). lia.
Qed.

Lemma wt_child_le c : lo < c <= hi -> wt c <= wt (par c).
Proof.
  intros Hc. pose proof (go_par_lt g G c Hc) as P. pose proof (go_par_int g G c Hc) as I.
  destruct (go_two g G (par c) ltac:(unfold g_pos; lia) I) as (a & b & NE & Ha & Hb & Pa & Pb & ONLY).
  rewrite (go_wt_sum g G (par c) a b ltac:(unfold g_pos; lia) I Ha Hb NE Pa Pb).
  pose proof (wt_nonneg a ltac:(lia)). pose proof (wt_nonneg b ltac:(lia)).
  destruct (ONLY c Hc eq_refl) as [->| ->]; lia.
Qed.

Lemma ext_mono i x : lo < i <= hi -> lo < x <= hi -> ext i < ext x -> wt i <= wt x.
Proof.
  intros Hi Hx. remember (Z.to_nat (ext x)) as n eqn:E. revert x Hx E.
  induction n as [n IH] using lt_wf_ind; intros x Hx E LT.
  destruct (leaf x) eqn:Lx.
  - apply (go_greedy g G i x Hi Hx LT). left; exact Lx.
  - destruct (go_two g G x ltac:(unfold g_pos; lia) Lx) as (a & b & NE & Ha & Hb & Pa & Pb & _).
    rewrite (go_wt_sum g G x a b ltac:(unfold g_pos; lia) Lx Ha Hb NE Pa Pb).
    pose proof (wt_nonneg a ltac:(lia)). pose proof (wt_nonneg b ltac:(lia)).
    destruct (Z.eq_dec a i) as [->|NA]; [lia|]. destruct (Z.eq_dec b i) as [->|NB]; [lia|].
    destruct (Z_lt_le_dec (ext a) (ext i)) as [La|La].
    + enough (wt i <= wt x) by (rewrite (go_wt_sum g G x a b ltac:(unfold g_pos; lia) Lx Ha Hb NE Pa Pb) in H1; lia).
      apply (go_greedy g G i x Hi Hx LT). right. exists a. auto.
    +
      assert (ext i <> ext a) by (intros EQ; apply NA; symmetry; apply (go_ext_inj g G i a); auto).
      pose proof (go_ext_par g G a Ha ltac:(lia)). rewrite Pa in H2.
      pose proof (go_ext_nonneg g G a Ha).
      assert (wt i <= wt a) by (apply (IH (Z.to_nat (ext a))); lia). lia.
Qed.

Lemma regroup (f : Z -> Z) :
  lsum f nonroot = lsum (fun p => lsum (fun c => if par c =? p then f c else 0) nonroot) internals.
Proof.
  transitivity (lsum (fun c => lsum (fun p => if par c =? p then f c else 0) internals) nonroot).
  - apply lsum_ext. intros c Hc. apply nonroot_in in Hc.
    pose proof (go_par_lt g G c Hc). pose proof (go_par_int g G c Hc).
    assert (In (par c) internals) by (apply internals_in; lia || (split; [lia|assumption])).
    destruct (lsum_in_split internals (par c) H1 internals_nodup) as (l1 & l2 & E & N1 & N2).
    rewrite E, lsum_app. cbn. rewrite Z.eqb_refl.
    rewrite (lsum_ext _ (fun _ => 0) l1) by (intros p Hp; destruct (Z.eqb_spec (par c) p); [subst; tauto|reflexivity]).
    rewrite (lsum_ext _ (fun _ => 0) l2) by (intros p Hp; destruct (Z.eqb_spec (par c) p); [subst; tauto|reflexivity]).
    rewrite !lsum_zero; lia.
  -
    generalize internals nonroot. clear. intros L1 L2.
    induction L2 as [|c r IH]; cbn.
    + induction L1; cbn; lia.
    + rewrite IH. clear IH. induction L1 as [|p s IH]; cbn; [lia|]. rewrite <- IH. lia.
Qed.

Lemma children_sum (f : Z -> Z) p : lo <= p <= hi -> leaf p = false ->
  exists a b, a <> b /\ lo < a <= hi /\ lo < b <= hi /\ par a = p /\ par b = p /\
    lsum (fun c => if par c =? p then f c else 0) nonroot = f a + f b /\ wt p = wt a + wt b.
Proof.
  intros Hp L. destruct (go_two g G p Hp L) as (a & b & NE & Ha & Hb & Pa & Pb & ONLY).
  exists a, b. repeat (split; [assumption|]). split.
  - apply lsum_ind2; try assumption.
    + apply nonroot_nodup. + apply nonroot_in; lia. + apply nonroot_in; lia.
    + apply Z.eqb_eq; assumption. + apply Z.eqb_eq; assumption.
    + intros c Hc E. apply nonroot_in in Hc. apply Z.eqb_eq in E. apply ONLY; assumption.
  - apply (go_wt_sum g G p a b Hp L Ha Hb NE Pa Pb).
Qed.

Lemma lsum_nonroot_split (f : Z -> Z) :
  lsum f nonroot + f lo = lsum f leaves + lsum f internals.
Proof.
  unfold leaves, internals. rewrite !lsum_filter.
  rewrite <- lsum_add.
  rewrite (lsum_ext (fun x => (if leaf x then f x else 0) + (if negb (leaf x) then f x else 0)) f) by (intros x _; destruct (leaf x); cbn; lia).
  unfold allpos, nonroot, npos. pose proof lohi.
  replace (Z.to_nat (hi - lo + 1)) with (S (Z.to_nat (hi - lo))) by lia. cbn. lia.
Qed.

Theorem W_leaves : g_W g = lsum wt leaves.
Proof.
  unfold g_W.
  pose proof (lsum_nonroot_split wt).
  rewrite regroup in H.
  rewrite (lsum_ext (fun p => lsum (fun c => if par c =? p then wt c else 0) nonroot) wt internals) in H; [lia|].
  intros p Hp. apply internals_in in Hp. destruct Hp as [Hp L].
  destruct (children_sum wt p Hp L) as (a & b & _ & _ & _ & _ & _ & E & W). lia.
Qed.

Theorem kraft_eq D : (forall i, lo <= i <= hi -> leaf i = true -> depth i <= D) ->
  lsum (fun i => 2 ^ (D - depth i)) leaves = 2 ^ D.
Proof.
  intros HD.
  assert (HD' : forall i, lo <= i <= hi -> depth i <= D).
  { intros i Hi. destruct (leaf i) eqn:L; [apply HD; assumption|].
    remember (Z.to_nat (hi - i)) as n eqn:E. revert i Hi L E.
    induction n as [n IH] using lt_wf_ind; intros i Hi L E.
    destruct (go_two g G i Hi L) as (a & b & NE & Ha & Hb & Pa & Pb & _).
    pose proof (go_par_lt g G a Ha). pose proof (depth_step a Ha). rewrite Pa in H0.
    destruct (leaf a) eqn:La.
    - pose proof (HD a ltac:(lia) La). lia.
    - assert (depth a <= D) by (apply (IH (Z.to_nat (hi - a))); try lia; exact La). lia. }
  pose proof (lsum_nonroot_split (fun i => 2 ^ (D - depth i))). cbn in H.
  rewrite regroup in H. rewrite depth_root, Z.sub_0_r in H.
  rewrite (lsum_ext (fun p => lsum (fun c => if par c =? p then 2 ^ (D - depth c) else 0) nonroot) (fun p => 2 ^ (D - depth p)) internals) in H; [lia|].
  intros p Hp. apply internals_in in Hp. destruct Hp as [Hp L].
  destruct (children_sum (fun i => 2 ^ (D - depth i)) p Hp L) as (a & b & NE & Ha & Hb & Pa & Pb & E & _).
  rewrite E. rewrite (depth_step a Ha), (depth_step b Hb), Pa, Pb.
  pose proof (HD' a ltac:(lia)). rewrite (depth_step a Ha), Pa in H0.
  replace (D - depth p) with (Z.succ (D - (1 + depth p))) by lia. rewrite Z.pow_succ_r; lia.
Qed.

Theorem cost_internal : lsum (fun i => wt i * depth i) leaves = lsum wt internals.
Proof.
  pose proof (lsum_nonroot_split (fun i => wt i * depth i)). cbn in H.
  rewrite regroup, depth_root, Z.mul_0_r in H.
  rewrite (lsum_ext (fun p => lsum (fun c => if par c =? p then wt c * depth c else 0) nonroot) (fun p => wt p * depth p + wt p) internals) in H.
  - rewrite lsum_add in H. lia.
  - intros p Hp. apply internals_in in Hp. destruct Hp as [Hp L].
    destruct (children_sum (fun i => wt i * depth i) p Hp L) as (a & b & NE & Ha & Hb & Pa & Pb & E & W).
    rewrite E, (depth_step a Ha), (depth_step b Hb), Pa, Pb. lia.
Qed.

End GTree.
