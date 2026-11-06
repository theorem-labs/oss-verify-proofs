(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI07 YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section u.
Context {A : Type}.
Variable dflt : A.
Definition znth (l : list A) (i : Z) : A := nth (Z.to_nat i) l dflt.
Definition zupd (l : list A) (i : Z) (x : A) : list A := lset l (Z.to_nat i) x.
Lemma zupd_length : forall l i x, length (zupd l i x) = length l.
Proof. intros. unfold zupd. apply lset_length. Qed.
Lemma nth_lset : forall (l : list A) n x m,
nth m (lset l n x) dflt = if (Nat.eqb m n && Nat.ltb n (length l))%bool then x else nth m l dflt.
Proof.
induction l as [|y r IH]; intros [|n] x [|m]; cbn; try reflexivity.
- rewrite Bool.andb_false_r. reflexivity.
- rewrite IH. destruct (Nat.eqb m n); cbn; [|reflexivity].
destruct (length r) as [|k]; [destruct (Nat.ltb_spec n 0); [lia|reflexivity]|].
destruct (Nat.ltb_spec n (S k)), (Nat.leb_spec n k); try reflexivity; lia.
Qed.
Lemma znth_zupd : forall l i j x, 0 <= i -> 0 <= j ->
znth (zupd l i x) j = if (j =? i) && (i <? elen l) then x else znth l j.
Proof.
intros l i j x Hi Hj. unfold znth, zupd, elen. rewrite nth_lset.
destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat i)), (Z.eqb_spec j i); try lia;
destruct (Nat.ltb_spec (Z.to_nat i) (length l)), (Z.ltb_spec i (Z.of_nat (length l))); cbn [andb]; try reflexivity; lia.
Qed.
Definition eswap (l : list A) (i k : Z) : list A := zupd (zupd l i (znth l k)) k (znth l i).
Lemma eswap_length : forall l i k, length (eswap l i k) = length l.
Proof. intros. unfold eswap. rewrite !zupd_length. reflexivity. Qed.
Lemma znth_eswap : forall l i k j, 0 <= i < elen l -> 0 <= k < elen l -> 0 <= j ->
znth (eswap l i k) j = if j =? k then znth l i else if j =? i then znth l k else znth l j.
Proof.
intros l i k j Hi Hk Hj. unfold eswap. rewrite !znth_zupd by lia.
unfold elen in *. rewrite zupd_length.
destruct (Z.ltb_spec k (Z.of_nat (length l))), (Z.ltb_spec i (Z.of_nat (length l))); try lia.
rewrite !Bool.andb_true_r. destruct (Z.eqb_spec j k), (Z.eqb_spec j i); reflexivity.
Qed.

Lemma eswap_perm : forall l i k, 0 <= i < elen l -> 0 <= k < elen l -> Permutation l (eswap l i k).
Proof.
intros l i k Hi Hk. unfold elen in *.
destruct (Z.eq_dec i k) as [->|Hne].
{ unfold eswap, zupd, znth.
assert (E : forall l' n (y : A), nth_error l' n = Some y -> lset l' n y = l').
{ clear. induction l' as [|a r IH]; intros [|n] y H; cbn in *; try reflexivity; [congruence|]. rewrite (IH _ _ H). reflexivity. }
assert (Hn : nth_error l (Z.to_nat k) = Some (nth (Z.to_nat k) l dflt)) by (apply nth_error_nth'; lia).
rewrite (E l) by exact Hn. rewrite (E l) by exact Hn. apply Permutation_refl. }
apply (proj2 (Permutation_nth_error _ _)). split; [symmetry; apply eswap_length|].
exists (fun n => if Nat.eqb n (Z.to_nat k) then Z.to_nat i else if Nat.eqb n (Z.to_nat i) then Z.to_nat k else n).
split.
- intros x y. destruct (Nat.eqb_spec x (Z.to_nat k)), (Nat.eqb_spec y (Z.to_nat k)),
(Nat.eqb_spec x (Z.to_nat i)), (Nat.eqb_spec y (Z.to_nat i)); lia.
- intros n. unfold eswap, zupd, znth. rewrite !nth_error_lset, !lset_length.
destruct (Nat.eqb_spec n (Z.to_nat k)).
+ subst n. replace (Z.to_nat k <? length l)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
symmetry. apply nth_error_nth'. lia.
+ cbn [andb]. destruct (Nat.eqb_spec n (Z.to_nat i)); [|reflexivity].
subst n. replace (Z.to_nat i <? length l)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
symmetry. apply nth_error_nth'. lia.
Qed.
Definition zsub (l : list A) (lo hi : Z) : list A :=
firstn (Z.to_nat (hi - lo + 1)) (skipn (Z.to_nat lo) l).
Lemma zsub_length : forall l lo hi, 0 <= lo -> lo <= hi + 1 -> hi < elen l ->
length (zsub l lo hi) = Z.to_nat (hi - lo + 1).
Proof.
intros l lo hi Hlo Hle Hhi. unfold zsub, elen in *. rewrite length_firstn, length_skipn. lia.
Qed.
Lemma zsub_nth : forall l lo hi n, 0 <= lo -> (n < Z.to_nat (hi - lo + 1))%nat ->
nth n (zsub l lo hi) dflt = znth l (lo + Z.of_nat n).
Proof.
intros l lo hi n Hlo Hn. unfold zsub, znth. rewrite nth_firstn.
destruct (Nat.ltb_spec n (Z.to_nat (hi - lo + 1))); [|lia]. rewrite nth_skipn. f_equal. lia.
Qed.
Lemma zsub_In : forall l lo hi x, 0 <= lo -> hi < elen l ->
In x (zsub l lo hi) <-> exists j, lo <= j <= hi /\ znth l j = x.
Proof.
intros l lo hi x Hlo Hhi. split.
- intros Hin. apply In_nth with (d := dflt) in Hin as (n & Hn & <-).
assert (Hn' : (n < Z.to_nat (hi - lo + 1))%nat).
{ unfold zsub in Hn. rewrite length_firstn in Hn. lia. }
exists (lo + Z.of_nat n). split; [lia|]. symmetry. apply zsub_nth; assumption.
- intros (j & Hj & <-).
replace j with (lo + Z.of_nat (Z.to_nat (j - lo))) by lia. rewrite <- (zsub_nth l lo hi) by lia.
apply nth_In. rewrite zsub_length; unfold elen in *; lia.
Qed.
Lemma zsub_ext : forall l l' lo hi, length l' = length l -> 0 <= lo ->
(forall j, lo <= j <= hi -> znth l' j = znth l j) -> zsub l' lo hi = zsub l lo hi.
Proof.
intros l l' lo hi Hlen Hlo Hj.
apply (nth_ext _ _ dflt dflt).
- unfold zsub. rewrite !length_firstn, !length_skipn, Hlen. reflexivity.
- intros n Hn. unfold zsub in Hn. rewrite length_firstn, length_skipn in Hn.
rewrite !zsub_nth by lia. apply Hj. lia.
Qed.
Lemma znth_In : forall l j, 0 <= j < elen l -> In (znth l j) l.
Proof. intros l j Hj. unfold znth, elen in *. apply nth_In. lia. Qed.
End u.
Arguments znth {A} dflt l i.
Arguments zupd {A} l i x.
Arguments eswap {A} dflt l i k.
Arguments zsub {A} l lo hi.
Section w.
Context {A : Type}.
Variable dflt : A.
Variable P : A -> bool.
Definition smallb (l : list A) (j : Z) : bool := P (znth dflt l j).
Definition scan_up (l : list A) (i : Z) (n : nat) : option Z := ffirst (fun j => negb (smallb l j)) i n.
Definition scan_dn (l : list A) (k : Z) (n : nat) : option Z :=
match ffirst (fun t => smallb l (k - (t - 0))) 0 n with Some t => Some (k - t) | None => None end.
Lemma scan_up_spec : forall l i n j, scan_up l i n = Some j ->
i <= j < i + Z.of_nat n /\ smallb l j = false /\ (forall x, i <= x < j -> smallb l x = true).
Proof.
intros l i n j H. unfold scan_up in H. apply ffirst_Some in H as (H1 & H2 & H3).
split; [exact H1|]. split; [destruct (smallb l j); [discriminate|reflexivity]|].
intros x Hx. specialize (H3 x Hx). destruct (smallb l x); [reflexivity|discriminate].
Qed.
Lemma scan_up_exists : forall l i n x, i <= x < i + Z.of_nat n -> smallb l x = false ->
exists j, scan_up l i n = Some j /\ j <= x.
Proof.
intros l i n x Hx Hb. unfold scan_up. apply ffirst_exists with (i := x); [exact Hx|]. rewrite Hb. reflexivity.
Qed.
Lemma scan_dn_spec : forall l k n j, scan_dn l k n = Some j ->
k - Z.of_nat n < j <= k /\ smallb l j = true /\ (forall x, j < x <= k -> smallb l x = false).
Proof.
intros l k n j H. unfold scan_dn in H.
destruct (ffirst _ 0 n) as [t|] eqn:E; [|discriminate]. injection H as <-.
apply ffirst_Some in E as (H1 & H2 & H3). rewrite Z.sub_0_r in H2.
split; [lia|]. split; [exact H2|].
intros x Hx. specialize (H3 (k - x) ltac:(lia)). rewrite Z.sub_0_r in H3.
replace (k - (k - x)) with x in H3 by lia. destruct (smallb l x); [discriminate|reflexivity].
Qed.
Lemma scan_dn_exists : forall l k n x, k - Z.of_nat n < x <= k -> smallb l x = true ->
exists j, scan_dn l k n = Some j /\ x <= j.
Proof.
intros l k n x Hx Hs. unfold scan_dn.
destruct (ffirst_exists (fun t => smallb l (k - (t - 0))) n 0 (k - x)) as (t & E & Ht); [lia| |].
- rewrite Z.sub_0_r. replace (k - (k - x)) with x by lia. exact Hs.
- rewrite E. exists (k - t). split; [reflexivity| lia].
Qed.
Inductive pstate := PRun (l : list A) (i k : Z) | PDone (l : list A) (i : Z).
Definition part_round (lo hi : Z) (l : list A) (i k : Z) : option pstate :=
match scan_up l i (Z.to_nat (hi - i + 1)), scan_dn l k (Z.to_nat (k - lo + 1)) with
| Some i', Some k' => if k' <=? i' then Some (PDone l i') else Some (PRun (eswap dflt l i' k') i' k')
| _, _ => None
end.
Fixpoint part_loop (lo hi : Z) (l : list A) (i k : Z) (fuel : nat) : option (list A * Z) :=
match fuel with
| O => None
| S f => match part_round lo hi l i k with
| Some (PDone l' i') => Some (l', i')
| Some (PRun l' i' k') => part_loop lo hi l' i' k' f
| None => None
end
end.
Definition partition (lo hi : Z) (l : list A) : option (list A * Z) :=
part_loop lo hi l lo hi (S (Z.to_nat (2 * (hi - lo) + 2))).
Definition pinv (lo hi : Z) (l0 l : list A) (i k : Z) : Prop :=
lo <= i <= k /\ k <= hi /\ 0 <= lo /\ hi < elen l0 /\ length l = length l0 /\
Permutation l0 l /\
(forall j, 0 <= j -> (j < lo \/ hi < j) -> znth dflt l j = znth dflt l0 j) /\
(forall j, lo <= j < i -> smallb l j = true) /\
(forall j, k < j <= hi -> smallb l j = false) /\
(exists x, i <= x <= hi /\ smallb l x = false) /\
(exists y, lo <= y <= k /\ smallb l y = true).
Definition part_meas (l : list A) (i k : Z) : Z :=
2 * (k - i) + (if smallb l i then 0 else 1) + (if smallb l k then 1 else 0).
Definition pdone (lo hi : Z) (l0 l : list A) (i : Z) : Prop :=
lo + 1 <= i <= hi /\ length l = length l0 /\ Permutation l0 l /\
(forall j, 0 <= j -> (j < lo \/ hi < j) -> znth dflt l j = znth dflt l0 j) /\
(forall j, lo <= j < i -> smallb l j = true) /\
(forall j, i <= j <= hi -> smallb l j = false).
Lemma smallb_eswap : forall l i k j, 0 <= i < elen l -> 0 <= k < elen l -> 0 <= j ->
smallb (eswap dflt l i k) j = if j =? k then smallb l i else if j =? i then smallb l k else smallb l j.
Proof.
intros l i k j Hi Hk Hj. unfold smallb. rewrite znth_eswap by assumption.
destruct (j =? k), (j =? i); reflexivity.
Qed.
Theorem part_round_spec : forall lo hi l0 l i k, pinv lo hi l0 l i k ->
exists i' k',
scan_up l i (Z.to_nat (hi - i + 1)) = Some i' /\ scan_dn l k (Z.to_nat (k - lo + 1)) = Some k' /\
i <= i' <= hi /\ lo <= k' <= k /\ smallb l i' = false /\ smallb l k' = true /\
(forall x, i <= x < i' -> smallb l x = true) /\ (forall x, k' < x <= k -> smallb l x = false) /\
((k' <= i' /\ part_round lo hi l i k = Some (PDone l i') /\ k' = i' - 1 /\ pdone lo hi l0 l i') \/
(i' < k' /\ part_round lo hi l i k = Some (PRun (eswap dflt l i' k') i' k') /\
pinv lo hi l0 (eswap dflt l i' k') i' k' /\
0 <= part_meas (eswap dflt l i' k') i' k' < part_meas l i k)).
Proof.
intros lo hi l0 l i k INV.
destruct INV as (Hik & Hkhi & Hlo & Hhi & Hlen & HP & Hout & Hsm & Hbg & (x & Hx & Hxb) & (y & Hy & Hys)).
destruct (scan_up_exists l i (Z.to_nat (hi - i + 1)) x ltac:(lia) Hxb) as (i' & Ei & Hi'x).
destruct (scan_up_spec l i _ i' Ei) as (Hi'1 & Hi'2 & Hi'3).
destruct (scan_dn_exists l k (Z.to_nat (k - lo + 1)) y ltac:(lia) Hys) as (k' & Ek & Hk'y).
destruct (scan_dn_spec l k _ k' Ek) as (Hk'1 & Hk'2 & Hk'3).
exists i', k'. split; [exact Ei|]. split; [exact Ek|].
split; [lia|]. split; [lia|]. split; [exact Hi'2|]. split; [exact Hk'2|]. split; [exact Hi'3|]. split; [exact Hk'3|].
unfold part_round. rewrite Ei, Ek.
destruct (Z.leb_spec k' i') as [Hle|Hlt].
- left. split; [exact Hle|]. split; [reflexivity|].
assert (Hk'i' : k' = i' - 1).
{ destruct (Z.eq_dec k' i') as [E|NE]; [rewrite E in Hk'2; congruence|].
destruct (Z_lt_le_dec (k' + 1) i') as [Hgap|]; [|lia]. exfalso.
assert (S1 : smallb l (k' + 1) = true) by (destruct (Z_lt_le_dec (k' + 1) i); [apply Hsm; lia| apply Hi'3; lia]).
assert (S2 : smallb l (k' + 1) = false) by (destruct (Z_lt_le_dec k (k' + 1)); [apply Hbg; lia| apply Hk'3; lia]).
congruence. }
split; [exact Hk'i'|].
unfold pdone. split; [lia|]. split; [exact Hlen|]. split; [exact HP|]. split; [exact Hout|]. split.
+ intros j Hj. destruct (Z_lt_le_dec j i); [apply Hsm; lia| apply Hi'3; lia].
+ intros j Hj. destruct (Z.eq_dec j i') as [->|]; [exact Hi'2|].
destruct (Z_lt_le_dec k j); [apply Hbg; lia| apply Hk'3; lia].
- right. split; [exact Hlt|]. split; [reflexivity|].
assert (Hi'r : 0 <= i' < elen l) by (unfold elen in *; lia).
assert (Hk'r : 0 <= k' < elen l) by (unfold elen in *; lia).
assert (SW : forall j, 0 <= j -> smallb (eswap dflt l i' k') j = if j =? k' then false else if j =? i' then true else smallb l j).
{ intros j Hj. rewrite smallb_eswap by assumption. rewrite Hi'2, Hk'2. reflexivity. }
split.
+ unfold pinv. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite eswap_length; exact Hlen|].
split; [apply (Permutation_trans HP); apply eswap_perm; assumption|].
split.
{ intros j Hj Hjo. rewrite znth_eswap by lia.
destruct (Z.eqb_spec j k'); [lia|]. destruct (Z.eqb_spec j i'); [lia|]. apply Hout; assumption. }
split.
{ intros j Hj. rewrite SW by lia. destruct (Z.eqb_spec j k'); [lia|]. destruct (Z.eqb_spec j i'); [lia|].
destruct (Z_lt_le_dec j i); [apply Hsm; lia| apply Hi'3; lia]. }
split.
{ intros j Hj. rewrite SW by lia. destruct (Z.eqb_spec j k'); [lia|]. destruct (Z.eqb_spec j i'); [lia|].
destruct (Z_lt_le_dec k j); [apply Hbg; lia| apply Hk'3; lia]. }
split.
{ exists k'. split; [lia|]. rewrite SW by lia. rewrite Z.eqb_refl. reflexivity. }
{ exists i'. split; [lia|]. rewrite SW by lia. destruct (Z.eqb_spec i' k'); [lia|]. rewrite Z.eqb_refl. reflexivity. }
+ unfold part_meas. rewrite !SW by lia. rewrite Z.eqb_refl.
destruct (Z.eqb_spec i' k'); [lia|]. rewrite Z.eqb_refl.
destruct (smallb l i) eqn:Si, (smallb l k) eqn:Sk; try lia.
assert (i' <> i) by (intros ->; congruence). assert (k' <> k) by (intros ->; congruence). lia.
Qed.
Lemma pinv_meas_bound : forall lo hi l0 l i k, pinv lo hi l0 l i k -> 0 <= part_meas l i k <= 2 * (hi - lo) + 2.
Proof.
intros lo hi l0 l i k (Hik & Hkhi & _). unfold part_meas. destruct (smallb l i), (smallb l k); lia.
Qed.

Lemma pinv_init : forall lo hi l, 0 <= lo -> lo <= hi -> hi < elen l ->
(exists x, lo <= x <= hi /\ smallb l x = false) -> (exists y, lo <= y <= hi /\ smallb l y = true) ->
pinv lo hi l l lo hi.
Proof.
intros lo hi l Hlo Hle Hhi Hx Hy. unfold pinv.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split; [intros; reflexivity|]. split; [intros; lia|]. split; [intros; lia|]. split; [exact Hx| exact Hy].
Qed.





End w.
Arguments smallb {A} dflt P l j.
Arguments scan_up {A} dflt P l i n.
Arguments scan_dn {A} dflt P l k n.
Arguments part_round {A} dflt P lo hi l i k.
Arguments part_loop {A} dflt P lo hi l i k fuel.
Arguments partition {A} dflt P lo hi l.
Arguments pinv {A} dflt P lo hi l0 l i k.
Arguments pdone {A} dflt P lo hi l0 l i.
Arguments part_meas {A} dflt P l i k.
Fixpoint sumZ {B : Type} (f : B -> Z) (l : list B) : Z :=
match l with [] => 0 | x :: r => f x + sumZ f r end.
Lemma sumZ_app : forall {B} (f : B -> Z) l1 l2, sumZ f (l1 ++ l2) = sumZ f l1 + sumZ f l2.
Proof. intros B f l1 l2. induction l1 as [|x r IH]; cbn; [lia|]. rewrite IH. lia. Qed.


Lemma sumZ_all_one : forall {B} (f : B -> Z) l, (forall x, In x l -> 1 <= f x) ->
Z.of_nat (length l) <= sumZ f l /\ (sumZ f l = Z.of_nat (length l) -> forall x, In x l -> f x = 1).
Proof.
intros B f l H. induction l as [|a r IH]; cbn [sumZ length]; [split; [lia| intros _ x []]|].
assert (Ha : 1 <= f a) by (apply H; left; reflexivity).
destruct IH as [IH1 IH2]; [intros; apply H; right; assumption|].
split; [lia|]. intros Hs x [<-|Hx]; [lia|]. apply IH2; [lia| exact Hx].
Qed.
Section z.
Context {A : Type}.
Variable dflt : A.
Record anode := mkN {
n_lo : Z; n_hi : Z; n_leaf : bool; n_col : Z;
n_k0 : option Z; n_k1 : option Z; n_par : Z; n_depth : Z; n_seg : list A }.
Definition dnode : anode := mkN 0 0 true 0 None None 0 0 [].
Definition nsize (nd : anode) : Z := n_hi nd - n_lo nd + 1.
Record cstate := mkC { c_E : list A; c_ns : list anode; c_q : Z }.
Definition node (ns : list anode) (j : Z) : anode := znth dnode ns j.
Definition leaves (ns : list anode) : list anode := filter n_leaf ns.
Definition nleaves (ns : list anode) : Z := elen (leaves ns).
Definition cinit (E : list A) : cstate :=
mkC E [mkN 0 (elen E - 1) true 0 None None 0 0 E] 0.
Definition cskip (st : cstate) : cstate := mkC (c_E st) (c_ns st) (c_q st + 1).
Definition csplit (st : cstate) (E' : list A) (i : Z) : cstate :=
let ns := c_ns st in let q := c_q st in let p := node ns q in
let m := elen ns in let L := nleaves ns in
let p' := mkN (n_lo p) (n_hi p) false (n_col p) (Some m) (Some (m + 1)) (n_par p) (n_depth p) (n_seg p) in
let kid0 := mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) (zsub E' (n_lo p) (i - 1)) in
let kid1 := mkN i (n_hi p) true L None None q (n_depth p + 1) (zsub E' i (n_hi p)) in
mkC E' (zupd ns q p' ++ [kid0; kid1]) (q + 1).
Definition cinv (cnt : Z) (E0 : list A) (st : cstate) : Prop :=
let E := c_E st in let ns := c_ns st in let q := c_q st in let L := nleaves ns in
(1 <= L /\ elen ns = 2 * L - 1 /\ 0 <= q <= elen ns /\ elen E = cnt /\ Permutation E0 E) /\
(forall j, 0 <= j < elen ns -> let nd := node ns j in
0 <= n_lo nd <= n_hi nd /\ n_hi nd < cnt /\ 0 <= n_depth nd /\ n_depth nd + 1 <= L /\ 0 <= n_col nd < L) /\
(forall j, 0 <= j < q -> n_leaf (node ns j) = true -> n_lo (node ns j) = n_hi (node ns j)) /\
(forall j, q <= j < elen ns -> n_leaf (node ns j) = true) /\
(forall j, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
exists c, j < c /\ c + 1 < elen ns /\ n_k0 (node ns j) = Some c /\ n_k1 (node ns j) = Some (c + 1) /\
n_depth (node ns c) = n_depth (node ns j) + 1 /\ n_depth (node ns (c + 1)) = n_depth (node ns j) + 1 /\
n_lo (node ns c) = n_lo (node ns j) /\ n_hi (node ns (c + 1)) = n_hi (node ns j) /\
n_hi (node ns c) + 1 = n_lo (node ns (c + 1)) /\ n_par (node ns c) = j /\ n_par (node ns (c + 1)) = j) /\
(forall j j', 0 <= j < elen ns -> 0 <= j' < elen ns -> j <> j' ->
n_leaf (node ns j) = true -> n_leaf (node ns j') = true ->
n_hi (node ns j) < n_lo (node ns j') \/ n_hi (node ns j') < n_lo (node ns j)) /\
sumZ nsize (leaves ns) = cnt /\
(forall j, q <= j < elen ns -> zsub E (n_lo (node ns j)) (n_hi (node ns j)) = n_seg (node ns j)) /\
n_depth (node ns 0) = 0 /\
(forall j, 1 <= j < elen ns -> let pj := n_par (node ns j) in
0 <= pj < j /\ n_leaf (node ns pj) = false /\ (n_k0 (node ns pj) = Some j \/ n_k1 (node ns pj) = Some j) /\
n_depth (node ns j) = n_depth (node ns pj) + 1).
Lemma node_app_l : forall ns l j, 0 <= j < elen ns -> node (ns ++ l) j = node ns j.
Proof. intros ns l j Hj. unfold node, znth, elen in *. apply app_nth1. lia. Qed.
Lemma node_app_r : forall ns l j, elen ns <= j -> node (ns ++ l) j = node l (j - elen ns).
Proof. intros ns l j Hj. unfold node, znth, elen in *. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma node_zupd : forall ns q x j, 0 <= q -> 0 <= j -> node (zupd ns q x) j = if (j =? q) && (q <? elen ns) then x else node ns j.
Proof. intros. unfold node. apply znth_zupd; assumption. Qed.
Lemma leaves_app : forall l1 l2, leaves (l1 ++ l2) = leaves l1 ++ leaves l2.
Proof. intros. unfold leaves. apply filter_app. Qed.

Lemma leaves_lset_perm : forall ns n x y, nth_error ns n = Some x -> n_leaf x = true -> n_leaf y = false ->
Permutation (leaves ns) (x :: leaves (lset ns n y)).
Proof.
induction ns as [|a r IH]; intros [|n] x y H Hx Hy; cbn in *; try discriminate.
- injection H as ->. rewrite Hx, Hy. apply Permutation_refl.
- specialize (IH n x y H Hx Hy). destruct (n_leaf a); [|exact IH].
apply (Permutation_trans (perm_skip a IH)). apply perm_swap.
Qed.
Lemma In_leaves : forall ns x, In x (leaves ns) <-> In x ns /\ n_leaf x = true.
Proof. intros. unfold leaves. apply filter_In. Qed.
Lemma In_node : forall ns x, In x ns <-> exists j, 0 <= j < elen ns /\ node ns j = x.
Proof.
intros ns x. split.
- intros H. apply In_nth with (d := dnode) in H as (n & Hn & <-). exists (Z.of_nat n).
unfold node, znth, elen. rewrite Nat2Z.id. split; [lia| reflexivity].
- intros (j & Hj & <-). apply znth_In. exact Hj.
Qed.
Fixpoint tree_ok (ns : list anode) (j : Z) (h : nat) {struct h} : Prop :=
match h with
| O => False
| S h' => 0 <= j < elen ns /\
(n_leaf (node ns j) = false ->
(forall c, n_k0 (node ns j) = Some c -> tree_ok ns c h') /\
(forall c, n_k1 (node ns j) = Some c -> tree_ok ns c h'))
end.

Lemma tree_ok_node : forall ns j h, tree_ok ns j h -> 0 <= j < elen ns /\ (1 <= h)%nat.
Proof. intros ns j [|h] HT; [destruct HT|]. destruct HT as [Hj _]. split; [exact Hj| lia]. Qed.

Definition tinv (Lb : Z) (ns : list anode) : Prop :=
forall j, 0 <= j < elen ns ->
0 <= n_depth (node ns j) /\ n_depth (node ns j) + 1 <= Lb /\
(n_leaf (node ns j) = false ->
(forall c, n_k0 (node ns j) = Some c -> 0 <= c < elen ns /\ n_depth (node ns c) = n_depth (node ns j) + 1) /\
(forall c, n_k1 (node ns j) = Some c -> 0 <= c < elen ns /\ n_depth (node ns c) = n_depth (node ns j) + 1)).
Theorem tinv_tree_ok : forall Lb ns j, tinv Lb ns -> 0 <= j < elen ns ->
tree_ok ns j (Z.to_nat (Lb - n_depth (node ns j))).
Proof.
intros Lb ns j TI. remember (Z.to_nat (Lb - n_depth (node ns j))) as h eqn:Eh. revert j Eh.
induction h as [|h IH]; intros j Eh Hj.
- destruct (TI j Hj) as (D0 & D1 & _). lia.
- split; [exact Hj|]. intros Hl. destruct (TI j Hj) as (D0 & D1 & K). destruct (K Hl) as [K0 K1].
split; intros c Hc; [destruct (K0 c Hc) as [Hc' Hd]| destruct (K1 c Hc) as [Hc' Hd]]; apply IH; lia.
Qed.
Corollary tinv_root_ok : forall Lb ns, tinv Lb ns -> 0 < elen ns -> n_depth (node ns 0) = 0 -> tree_ok ns 0 (Z.to_nat Lb).
Proof.
intros Lb ns TI Hne Hd0. pose proof (tinv_tree_ok Lb ns 0 TI ltac:(lia)) as HT. rewrite Hd0, Z.sub_0_r in HT. exact HT.
Qed.
Section a0.
Variables (cnt : Z) (E0 : list A) (st : cstate).
Hypothesis INV : cinv cnt E0 st.
Let E := c_E st. Let ns := c_ns st. Let q := c_q st. Let L := nleaves ns.
Lemma cinv_counts : 1 <= L /\ elen ns = 2 * L - 1 /\ 0 <= q <= elen ns /\ elen E = cnt /\ Permutation E0 E.
Proof. destruct INV as (C1 & _). exact C1. Qed.
Lemma cinv_node : forall j, 0 <= j < elen ns -> let nd := node ns j in
0 <= n_lo nd <= n_hi nd /\ n_hi nd < cnt /\ 0 <= n_depth nd /\ n_depth nd + 1 <= L /\ 0 <= n_col nd < L.
Proof. destruct INV as (_ & C2 & _). exact C2. Qed.
Theorem cinv_progress : L < cnt -> q < elen ns.
Proof.
subst L q ns E. intros HL. destruct INV as ((C1a & C1b & C1c & _) & C2 & C3a & C3b & C4 & C5a & C5b & C6 & _).
destruct (Z_lt_le_dec (c_q st) (elen (c_ns st))) as [Hlt|Hge]; [exact Hlt|]. exfalso.
pose proof (sumZ_all_one nsize (leaves (c_ns st))) as [S1 S2].
{ intros x Hx. apply In_leaves in Hx as [Hin Hleaf]. apply In_node in Hin as (j & Hj & <-).
pose proof (C2 j Hj) as (H1 & _). unfold nsize. lia. }
assert (Hall : forall x, In x (leaves (c_ns st)) -> nsize x = 1).
{ intros x Hx. apply In_leaves in Hx as [Hin Hleaf]. apply In_node in Hin as (j & Hj & <-).
unfold nsize. rewrite (C3a j) by (try assumption; lia). lia. }
assert (Hs : sumZ nsize (leaves (c_ns st)) = nleaves (c_ns st)).
{ unfold nleaves, elen. clear - Hall. induction (leaves (c_ns st)) as [|x r IH]; cbn [sumZ length]; [reflexivity|].
rewrite Hall by (left; reflexivity). rewrite IH by (intros; apply Hall; right; assumption). lia. }
lia.
Qed.
Theorem cinv_tinv : tinv L ns.
Proof.
subst L q ns E. destruct INV as (_ & C2 & _ & _ & C4 & _). intros j Hj.
pose proof (C2 j Hj) as (_ & _ & D0 & D1 & _). split; [exact D0|]. split; [exact D1|].
intros Hl. destruct (C4 j Hj Hl) as (c & Hc1 & Hc2 & K0 & K1 & Hd0 & Hd1 & _). rewrite K0, K1.
split; intros c' Hc'; injection Hc' as <-; split; lia.
Qed.
Corollary cinv_root_ok : tree_ok ns 0 (Z.to_nat L).
Proof.
pose proof cinv_counts as (C1a & C1b & _).
apply tinv_root_ok; [apply cinv_tinv| subst ns; lia|].
subst L q ns E. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & R & _). exact R.
Qed.
Lemma cinv_kids : forall j, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
exists c, n_k0 (node ns j) = Some c /\ n_k1 (node ns j) = Some (c + 1) /\ j < c /\ c + 1 < elen ns.
Proof.
intros j Hj Hl. destruct INV as (_ & _ & _ & _ & C4 & _). destruct (C4 j Hj Hl) as (c & H1 & H2 & K0 & K1 & _).
exists c. auto.
Qed.
Lemma cinv_seg : forall j, q <= j < elen ns -> zsub E (n_lo (node ns j)) (n_hi (node ns j)) = n_seg (node ns j).
Proof. destruct INV as (_ & _ & _ & _ & _ & _ & _ & C6 & _). exact C6. Qed.
Lemma cinv_unprocessed_leaf : forall j, q <= j < elen ns -> n_leaf (node ns j) = true.
Proof. destruct INV as (_ & _ & _ & C3b & _). exact C3b. Qed.
End a0.
Theorem cinit_inv : forall E, 1 <= elen E -> cinv (elen E) E (cinit E).
Proof.
intros E HE. unfold cinv, cinit. cbn [c_E c_ns c_q].
set (r := mkN 0 (elen E - 1) true 0 None None 0 0 E).
assert (Hn : forall j, 0 <= j < 1 -> node [r] j = r).
{ intros j Hj. unfold node, znth. replace (Z.to_nat j) with 0%nat by lia. reflexivity. }
assert (HL : nleaves [r] = 1) by reflexivity. rewrite HL.
assert (Hlen : elen [r] = 1) by reflexivity. rewrite Hlen.
split; [split; [lia|]; split; [reflexivity|]; split; [lia|]; split; [reflexivity| apply Permutation_refl]|].
split; [intros j Hj; rewrite Hn by lia; cbn [r n_lo n_hi n_depth n_col]; lia|].
split; [intros j Hj; lia|].
split; [intros j Hj; rewrite Hn by lia; reflexivity|].
split; [intros j Hj; rewrite Hn by lia; cbn; discriminate|].
split; [intros j j_ Hj Hj_; lia|].
split; [cbn [leaves filter r n_leaf sumZ]; unfold nsize; cbn [r n_hi n_lo]; lia|].
split.
{ intros j Hj. rewrite Hn by lia. cbn [r n_lo n_hi n_seg]. unfold zsub.
rewrite Z.sub_0_r. replace (elen E - 1 + 1) with (elen E) by lia.
unfold elen. rewrite Nat2Z.id. cbn [Z.to_nat skipn]. apply firstn_all. }
split; [rewrite Hn by lia; reflexivity|]. intros j Hj. lia.
Qed.
Lemma sumZ_perm : forall {B} (f : B -> Z) l l', Permutation l l' -> sumZ f l = sumZ f l'.
Proof. intros B f l l' HP. induction HP; cbn; lia. Qed.
Theorem cskip_inv : forall cnt E0 st, cinv cnt E0 st -> c_q st < elen (c_ns st) ->
n_lo (node (c_ns st) (c_q st)) = n_hi (node (c_ns st) (c_q st)) -> cinv cnt E0 (cskip st).
Proof.
intros cnt E0 [E ns q] INV Hq Hsing. unfold cinv, cskip in *. cbn [c_E c_ns c_q] in *.
destruct INV as ((C1a & C1b & C1c & C1d & C1e) & C2 & C3a & C3b & C4 & C5a & C5b & C6 & C7).
split; [repeat split; auto; lia|]. split; [exact C2|].
split; [intros j Hj Hl; destruct (Z.eq_dec j q) as [->|]; [exact Hsing| apply C3a; [lia| exact Hl]]|].
split; [intros j Hj; apply C3b; lia|]. split; [exact C4|]. split; [exact C5a|]. split; [exact C5b|].
split; [intros j Hj; apply C6; lia| exact C7].
Qed.
Theorem csplit_inv : forall cnt E0 st (P : A -> bool) E' i,
cinv cnt E0 st -> c_q st < elen (c_ns st) ->
let p := node (c_ns st) (c_q st) in
n_lo p < n_hi p -> pdone dflt P (n_lo p) (n_hi p) (c_E st) E' i ->
cinv cnt E0 (csplit st E' i) /\ nleaves (c_ns (csplit st E' i)) = nleaves (c_ns st) + 1 /\
elen (c_ns (csplit st E' i)) = elen (c_ns st) + 2.
Proof.
intros cnt E0 [E ns q] P E' i INV Hq p Hlt PD. unfold cinv in INV. cbn [c_E c_ns c_q] in Hq, p, PD, INV.
unfold csplit. cbn [c_E c_ns c_q]. fold p.
destruct INV as ((C1a & C1b & C1c & C1d & C1e) & C2 & C3a & C3b & C4 & C5a & C5b & C6 & C7).
destruct PD as (Pi & Plen & Pperm & Pout & Psm & Pbg).
set (m := elen ns) in *. set (L := nleaves ns) in *.
set (p' := mkN (n_lo p) (n_hi p) false (n_col p) (Some m) (Some (m + 1)) (n_par p) (n_depth p) (n_seg p)).
set (kid0 := mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) (zsub E' (n_lo p) (i - 1))).
set (kid1 := mkN i (n_hi p) true L None None q (n_depth p + 1) (zsub E' i (n_hi p))).
set (ns' := zupd ns q p' ++ [kid0; kid1]).
pose proof (C2 q ltac:(lia)) as Cq. fold p in Cq. cbn beta in Cq. destruct Cq as (Cq1 & Cq2 & Cq3 & Cq4 & Cq5).
pose proof (C3b q ltac:(lia)) as Hleaf. fold p in Hleaf.
assert (Hlen' : elen ns' = m + 2).
{ unfold ns', elen. rewrite length_app, zupd_length. cbn [length]. unfold m, elen. lia. }
assert (NDo : forall j, 0 <= j < m -> j <> q -> node ns' j = node ns j).
{ intros j Hj Hne. unfold ns'. rewrite node_app_l by (unfold elen; rewrite zupd_length; unfold m, elen in Hj; lia).
rewrite node_zupd by lia. destruct (Z.eqb_spec j q); [lia|]. reflexivity. }
assert (NDq : node ns' q = p').
{ unfold ns'. rewrite node_app_l by (unfold elen; rewrite zupd_length; unfold m, elen in Hq; lia).
rewrite node_zupd by lia. rewrite Z.eqb_refl. fold m. destruct (Z.ltb_spec q m); [reflexivity| lia]. }
assert (Hzl : elen (zupd ns q p') = m) by (unfold elen; rewrite zupd_length; reflexivity).
assert (ND0 : node ns' m = kid0).
{ unfold ns'. rewrite node_app_r by lia. rewrite Hzl, Z.sub_diag. reflexivity. }
assert (ND1 : node ns' (m + 1) = kid1).
{ unfold ns'. rewrite node_app_r by lia. rewrite Hzl. replace (m + 1 - m) with 1 by lia. reflexivity. }
assert (Hp : nth_error ns (Z.to_nat q) = Some p) by (unfold p, node, znth; apply nth_error_nth'; unfold m, elen in Hq; lia).
pose proof (leaves_lset_perm ns (Z.to_nat q) p p' Hp Hleaf eq_refl) as HPl.
assert (Hleaves : leaves ns' = leaves (zupd ns q p') ++ [kid0; kid1]) by (unfold ns'; rewrite leaves_app; reflexivity).
assert (HL' : nleaves ns' = L + 1).
{ unfold nleaves. rewrite Hleaves. unfold elen. rewrite length_app. cbn [length].
unfold L, nleaves, elen. rewrite (Permutation_length HPl). cbn [length]. unfold zupd. lia. }
assert (HS' : sumZ nsize (leaves ns') = cnt).
{ rewrite Hleaves, sumZ_app. rewrite (sumZ_perm nsize _ _ HPl) in C5b. cbn [sumZ] in C5b |- *.
unfold zupd. unfold nsize at 2 3. cbn [kid0 kid1 n_hi n_lo]. unfold nsize at 1 in C5b. lia. }
assert (LF : forall j, 0 <= j < m + 2 -> n_leaf (node ns' j) = true ->
(j < m /\ j <> q /\ node ns' j = node ns j /\ n_leaf (node ns j) = true) \/ j = m \/ j = m + 1).
{ intros j Hj Hl. destruct (Z.eq_dec j q) as [->|Hne]; [rewrite NDq in Hl; discriminate|].
destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- left. rewrite (NDo j) in Hl |- * by lia. auto.
- right. lia. }
split; [| split; [exact HL'| exact Hlen']].
unfold cinv. cbn [c_E c_ns c_q]. fold ns'. rewrite HL', Hlen'.
split.
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold elen in *; rewrite Plen; exact C1d|].
apply (Permutation_trans C1e Pperm). }
split.
{ intros j Hj. destruct (Z.eq_dec j q) as [->|Hne]; [rewrite NDq; cbn [p' n_lo n_hi n_depth n_col]; lia|].
destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- rewrite NDo by lia. pose proof (C2 j ltac:(lia)) as Cj. cbn beta in Cj. lia.
- destruct (Z.eq_dec j m) as [->|Hne2]; [rewrite ND0; cbn [kid0 n_lo n_hi n_depth n_col]; lia|].
replace j with (m + 1) by lia. rewrite ND1; cbn [kid1 n_lo n_hi n_depth n_col]. lia. }
split.
{ intros j Hj Hl. destruct (Z.eq_dec j q) as [->|Hne]; [rewrite NDq in Hl; discriminate|].
rewrite NDo in Hl |- * by lia. apply C3a; [lia| exact Hl]. }
split.
{ intros j Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm]; [rewrite NDo by lia; apply C3b; lia|].
destruct (Z.eq_dec j m) as [->|Hne2]; [rewrite ND0; reflexivity|]. replace j with (m + 1) by lia. rewrite ND1. reflexivity. }
split.
{ intros j Hj Hl. destruct (Z.eq_dec j q) as [->|Hne].
- exists m. rewrite NDq, ND0, ND1. cbn [p' kid0 kid1 n_k0 n_k1 n_depth n_lo n_hi n_par]. repeat split; lia.
- destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
+ rewrite NDo in Hl |- * by lia. destruct (C4 j ltac:(lia) Hl) as (c & Hc1 & Hc2 & K0 & K1 & D0 & D1 & R0 & R1 & R2 & Q0 & Q1).
exists c. split; [lia|]. split; [lia|]. split; [exact K0|]. split; [exact K1|].
assert (Ec : forall c', 0 <= c' < m -> n_depth (node ns' c') = n_depth (node ns c') /\
n_lo (node ns' c') = n_lo (node ns c') /\ n_hi (node ns' c') = n_hi (node ns c') /\ n_par (node ns' c') = n_par (node ns c')).
{ intros c' Hc'. destruct (Z.eq_dec c' q) as [->|]; [rewrite NDq; cbn [p' n_depth n_lo n_hi n_par]; fold p; auto|].
rewrite NDo by lia. auto. }
destruct (Ec c ltac:(lia)) as (-> & -> & -> & ->). destruct (Ec (c + 1) ltac:(lia)) as (-> & -> & -> & ->).
repeat split; assumption.
+ exfalso. destruct (Z.eq_dec j m) as [->|]; [rewrite ND0 in Hl; discriminate|].
replace j with (m + 1) in Hl by lia. rewrite ND1 in Hl. discriminate. }
split.
{ intros j j' Hj Hj' Hne Hl Hl'.
assert (OLD : forall a, 0 <= a < m -> a <> q -> n_leaf (node ns a) = true ->
n_hi (node ns a) < n_lo p \/ n_hi p < n_lo (node ns a)).
{ intros a Ha Hane Hla. apply (C5a a q); try assumption; lia. }
destruct (LF j Hj Hl) as [(Hjm & Hjq & Ej & Lj)|[->| ->]]; destruct (LF j' Hj' Hl') as [(Hjm' & Hjq' & Ej' & Lj')|[->| ->]];
rewrite ?Ej, ?Ej', ?ND0, ?ND1; cbn [kid0 kid1 n_lo n_hi]; try lia.
- apply C5a; assumption || lia.
- destruct (OLD j ltac:(lia) Hjq Lj); lia.
- destruct (OLD j ltac:(lia) Hjq Lj); lia.
- destruct (OLD j' ltac:(lia) Hjq' Lj'); lia.
- destruct (OLD j' ltac:(lia) Hjq' Lj'); lia. }
split; [exact HS'|].
split.
{ intros j Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- assert (Hjq : j <> q) by lia. rewrite NDo by lia.
pose proof (C3b j ltac:(lia)) as Lj. pose proof (C5a j q ltac:(lia) ltac:(lia) Hjq Lj Hleaf) as Hdisj. fold p in Hdisj.
rewrite <- (C6 j) by lia. apply (zsub_ext dflt); [exact Plen| pose proof (C2 j ltac:(lia)); cbn beta in *; lia|].
intros x Hx. apply Pout; [pose proof (C2 j ltac:(lia)); cbn beta in *; lia| lia].
- destruct (Z.eq_dec j m) as [->|]; [rewrite ND0; reflexivity|]. replace j with (m + 1) by lia. rewrite ND1. reflexivity. }
{ destruct C7 as [C7 C8]. split.
- destruct (Z.eq_dec q 0) as [->|]; [rewrite NDq; cbn [p' n_depth]; fold p; exact C7| rewrite NDo by lia; exact C7].
- intros j Hj.
destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
+ destruct (C8 j ltac:(lia)) as (P1 & P2 & P3 & P4).
assert (Hpj : n_par (node ns' j) = n_par (node ns j) /\ n_depth (node ns' j) = n_depth (node ns j)).
{ destruct (Z.eq_dec j q) as [->|]; [rewrite NDq; cbn [p' n_par n_depth]; fold p; auto| rewrite NDo by lia; auto]. }
destruct Hpj as [-> ->]. set (pj := n_par (node ns j)) in *.
destruct (Z.eq_dec pj q) as [Epj|Hne].
* exfalso. rewrite Epj in P2. fold p in P2. rewrite Hleaf in P2. discriminate.
* rewrite (NDo pj) by lia. auto.
+ cbn zeta. assert (Hk : node ns' j = kid0 \/ node ns' j = kid1).
{ destruct (Z.eq_dec j m) as [->|]; [left; exact ND0| right]. replace j with (m + 1) by lia. exact ND1. }
assert (Hpar : n_par (node ns' j) = q /\ n_depth (node ns' j) = n_depth p + 1) by (destruct Hk as [-> | ->]; split; reflexivity).
destruct Hpar as [-> ->]. rewrite NDq. cbn [p' n_leaf n_k0 n_k1 n_depth]. fold p.
split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
destruct (Z.eq_dec j m) as [->|]; [left; reflexivity| right]. f_equal. lia. }
Qed.
Definition par_ok (ns : list anode) : Prop :=
n_depth (node ns 0) = 0 /\
(forall j, 1 <= j < elen ns ->
0 <= n_par (node ns j) < j /\ n_leaf (node ns (n_par (node ns j))) = false /\
(n_k0 (node ns (n_par (node ns j))) = Some j \/ n_k1 (node ns (n_par (node ns j))) = Some j) /\
n_depth (node ns j) = n_depth (node ns (n_par (node ns j))) + 1) /\
(forall j c, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
(n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> j < c < elen ns /\ n_par (node ns c) = j) /\
(forall j c, 0 <= j < elen ns -> n_leaf (node ns j) = false -> n_k0 (node ns j) = Some c -> n_k1 (node ns j) <> Some c).
Lemma cinv_par_ok : forall cnt E0 st, cinv cnt E0 st -> par_ok (c_ns st).
Proof.
intros cnt E0 st INV. destruct INV as ((C1a & C1b & _) & C2 & _ & _ & C4 & _ & _ & _ & C7 & C8).
split; [exact C7|]. split; [exact C8|]. split.
- intros j c Hj Hl Hc. destruct (C4 j Hj Hl) as (c' & H1 & H2 & K0 & K1 & _ & _ & _ & _ & _ & Q0 & Q1).
rewrite K0, K1 in Hc. destruct Hc as [Hc|Hc]; injection Hc as <-; (split; [lia| assumption]).
- intros j c Hj Hl. destruct (C4 j Hj Hl) as (c' & _ & _ & K0 & K1 & _). rewrite K0, K1. intros E E'. injection E. injection E'. lia.
Qed.
Fixpoint up (ns : list anode) (x : Z) (t : nat) : Z :=
match t with O => x | S t' => up ns (n_par (node ns x)) t' end.
Definition depth (ns : list anode) (x : Z) : Z := n_depth (node ns x).
Definition ancb (ns : list anode) (j x : Z) : bool :=
(depth ns j <=? depth ns x) && (up ns x (Z.to_nat (depth ns x - depth ns j)) =? j).
Definition desc (ns : list anode) (j : Z) : list Z := filter (ancb ns j) (zseq 0 (elen ns)).
Definition odesc (ns : list anode) (o : option Z) : list Z := match o with Some c => desc ns c | None => [] end.
Section c0.
Variable ns : list anode.
Hypothesis PO : par_ok ns.
Lemma depth_pos : forall x, 1 <= x < elen ns -> 1 <= depth ns x /\ 0 <= depth ns (n_par (node ns x)).
Proof.
intros x. remember (Z.to_nat x) as n eqn:En. revert x En.
induction n as [n IH] using lt_wf_ind. intros x En Hx.
destruct PO as (P0 & P1 & _). destruct (P1 x Hx) as (Q1 & Q2 & Q3 & Q4). unfold depth in *.
destruct (Z.eq_dec (n_par (node ns x)) 0) as [E|NE]; [rewrite E in *; rewrite P0 in *; lia|].
destruct (IH (Z.to_nat (n_par (node ns x))) ltac:(lia) (n_par (node ns x)) eq_refl ltac:(lia)). lia.
Qed.
Lemma depth_nonneg : forall x, 0 <= x < elen ns -> 0 <= depth ns x.
Proof.
intros x Hx. destruct (Z.eq_dec x 0) as [->|]; [destruct PO as (P0 & _); unfold depth; rewrite P0; lia|].
destruct (depth_pos x ltac:(lia)). lia.
Qed.
Lemma depth_zero : forall x, 0 <= x < elen ns -> depth ns x = 0 -> x = 0.
Proof. intros x Hx Hd. destruct (Z.eq_dec x 0) as [->|]; [reflexivity|]. destruct (depth_pos x ltac:(lia)). lia. Qed.
Lemma up_spec : forall t x, 0 <= x < elen ns -> Z.of_nat t <= depth ns x ->
0 <= up ns x t < elen ns /\ depth ns (up ns x t) = depth ns x - Z.of_nat t.
Proof.
induction t as [|t IH]; intros x Hx Ht; cbn [up]; [lia|].
assert (Hx1 : 1 <= x) by (destruct (Z.eq_dec x 0) as [->|]; [destruct PO as (P0 & _); unfold depth in Ht; rewrite P0 in Ht; lia| lia]).
destruct PO as (P0 & P1 & _). destruct (P1 x ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
destruct (IH (n_par (node ns x)) ltac:(lia)) as [R1 R2]; [unfold depth in *; lia|].
split; [exact R1|]. unfold depth in *. rewrite R2. lia.
Qed.
Lemma up_add : forall a b x, up ns x (a + b) = up ns (up ns x a) b.
Proof. induction a as [|a IH]; intros b x; cbn [up Nat.add]; [reflexivity|]. apply IH. Qed.
Lemma ancb_true : forall j x,
ancb ns j x = true <-> depth ns j <= depth ns x /\ up ns x (Z.to_nat (depth ns x - depth ns j)) = j.
Proof. intros j x. unfold ancb. rewrite Bool.andb_true_iff, Z.leb_le, Z.eqb_eq. reflexivity. Qed.
Lemma ancb_refl : forall j, ancb ns j j = true.
Proof. intros j. apply ancb_true. rewrite Z.sub_diag. cbn. split; [lia| reflexivity]. Qed.
Lemma In_desc : forall j x, In x (desc ns j) <-> 0 <= x < elen ns /\ ancb ns j x = true.
Proof. intros j x. unfold desc. rewrite filter_In, In_zseq. rewrite Z.add_0_l. reflexivity. Qed.
Lemma desc_NoDup : forall j, NoDup (desc ns j).
Proof. intros. unfold desc. apply NoDup_filter. apply zseq_NoDup. Qed.
Lemma desc_self : forall j, 0 <= j < elen ns -> In j (desc ns j).
Proof. intros j Hj. apply In_desc. split; [exact Hj| apply ancb_refl]. Qed.
Lemma ancb_depth : forall j x, 0 <= x < elen ns -> ancb ns j x = true -> x <> j -> depth ns j < depth ns x.
Proof.
intros j x Hx Ha Hne. apply ancb_true in Ha as [Hd Hup].
destruct (Z.eq_dec (depth ns j) (depth ns x)) as [E|]; [|lia]. exfalso. rewrite E, Z.sub_diag in Hup. cbn in Hup. congruence.
Qed.
Lemma ancb_down : forall j x, 0 <= j < elen ns -> 0 <= x < elen ns -> ancb ns j x = true -> x <> j ->
n_leaf (node ns j) = false /\
exists c, (n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) /\ ancb ns c x = true.
Proof.
intros j x Hj Hx Ha Hne. pose proof (ancb_depth j x Hx Ha Hne) as Hlt. apply ancb_true in Ha as [Hd Hup].
pose proof (depth_nonneg x Hx) as Dx. pose proof (depth_nonneg j Hj) as Dj.
set (t := Z.to_nat (depth ns x - depth ns j - 1)).
destruct (up_spec t x Hx ltac:(lia)) as [U1 U2]. set (c := up ns x t) in *.
assert (Hcj : n_par (node ns c) = j).
{ replace (Z.to_nat (depth ns x - depth ns j)) with (t + 1)%nat in Hup by lia. rewrite up_add in Hup. exact Hup. }
destruct PO as (P0 & P1 & _).
assert (Hc1 : 1 <= c).
{ destruct (Z.eq_dec c 0) as [E0|]; [| lia]. exfalso. assert (D0 : depth ns c = 0) by (unfold depth; rewrite E0; exact P0). lia. }
destruct (P1 c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). rewrite Hcj in Q2, Q3, Q4.
split; [exact Q2|]. exists c. split; [exact Q3|]. apply ancb_true. unfold depth in *. split; [lia|].
replace (Z.to_nat (n_depth (node ns x) - n_depth (node ns c))) with t by lia. reflexivity.
Qed.
Lemma ancb_up : forall j c x, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
(n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> 0 <= x < elen ns -> ancb ns c x = true -> ancb ns j x = true.
Proof.
intros j c x Hj Hl Hc Hx Ha. destruct PO as (P0 & P1 & P2 & _). destruct (P2 j c Hj Hl Hc) as (Hc' & Hpc).
destruct (P1 c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). rewrite Hpc in Q4.
apply ancb_true in Ha as [Hd Hup]. apply ancb_true. unfold depth in *. split; [lia|].
replace (Z.to_nat (n_depth (node ns x) - n_depth (node ns j))) with (Z.to_nat (n_depth (node ns x) - n_depth (node ns c)) + 1)%nat by lia.
rewrite up_add, Hup. cbn. exact Hpc.
Qed.
Lemma ancb_disj : forall j c c' x, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
(n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> (n_k0 (node ns j) = Some c' \/ n_k1 (node ns j) = Some c') ->
ancb ns c x = true -> ancb ns c' x = true -> c = c'.
Proof.
intros j c c' x Hj Hl Hc Hc' Ha Ha'. destruct PO as (P0 & P1 & P2 & _).
destruct (P2 j c Hj Hl Hc) as (R1 & R2). destruct (P2 j c' Hj Hl Hc') as (R1' & R2').
destruct (P1 c ltac:(lia)) as (_ & _ & _ & D). destruct (P1 c' ltac:(lia)) as (_ & _ & _ & D').
rewrite R2 in D. rewrite R2' in D'.
apply ancb_true in Ha as [_ U]. apply ancb_true in Ha' as [_ U']. unfold depth in *.
rewrite D in U. rewrite D' in U'. congruence.
Qed.
Theorem desc_leaf : forall j, 0 <= j < elen ns -> n_leaf (node ns j) = true -> desc ns j = [j].
Proof.
intros j Hj Hl.
assert (H1 : forall x, In x (desc ns j) -> x = j).
{ intros x Hx. apply In_desc in Hx as [Hx Ha]. destruct (Z.eq_dec x j) as [->|Hne]; [reflexivity|].
destruct (ancb_down j x Hj Hx Ha Hne) as [Hl' _]. congruence. }
pose proof (desc_self j Hj) as Hin. pose proof (desc_NoDup j) as Hnd.
destruct (desc ns j) as [|a [|b r]]; [destruct Hin| |].
- f_equal. apply H1. left. reflexivity.
- exfalso. assert (a = j) by (apply H1; left; reflexivity). assert (b = j) by (apply H1; right; left; reflexivity).
subst. inversion Hnd as [|? ? Hn]. apply Hn. left. reflexivity.
Qed.
Theorem desc_split : forall j, 0 <= j < elen ns -> n_leaf (node ns j) = false ->
Permutation (desc ns j) (j :: odesc ns (n_k0 (node ns j)) ++ odesc ns (n_k1 (node ns j))).
Proof.
intros j Hj Hl. destruct PO as (P0 & P1 & P2 & P3).
assert (KIn : forall o x, (o = n_k0 (node ns j) \/ o = n_k1 (node ns j)) ->
In x (odesc ns o) <-> exists c, o = Some c /\ 0 <= x < elen ns /\ ancb ns c x = true).
{ intros o x Ho. destruct o as [c|]; cbn [odesc].
- rewrite In_desc. split; [intros [Hx Ha]; exists c; auto| intros (c' & E & Hx & Ha); injection E as ->; auto].
- split; [intros []| intros (c & E & _); discriminate]. }
apply NoDup_Permutation.
- apply desc_NoDup.
- constructor.
+ rewrite in_app_iff. intros [H|H];
[destruct (proj1 (KIn _ j ltac:(left; reflexivity)) H) as (c & E & Hx & Ha)
|destruct (proj1 (KIn _ j ltac:(right; reflexivity)) H) as (c & E & Hx & Ha)];
(destruct (P2 j c Hj Hl ltac:(rewrite <- E; auto)) as (R1 & R2);
destruct (P1 c ltac:(lia)) as (_ & _ & _ & D); rewrite R2 in D;
apply ancb_true in Ha as [Hd _]; unfold depth in *; lia).
+ apply NoDup_app.
* destruct (n_k0 (node ns j)); [apply desc_NoDup| constructor].
* destruct (n_k1 (node ns j)); [apply desc_NoDup| constructor].
* intros x H0 H1.
destruct (proj1 (KIn _ x ltac:(left; reflexivity)) H0) as (c & E & Hx & Ha).
destruct (proj1 (KIn _ x ltac:(right; reflexivity)) H1) as (c' & E' & _ & Ha').
pose proof (ancb_disj j c c' x Hj Hl ltac:(rewrite <- E; auto) ltac:(rewrite <- E'; auto) Ha Ha') as Ecc.
apply (P3 j c Hj Hl ltac:(rewrite <- E; reflexivity)). congruence.
- intros x. rewrite In_desc. cbn [In]. rewrite in_app_iff. split.
+ intros [Hx Ha]. destruct (Z.eq_dec x j) as [->|Hne]; [left; reflexivity| right].
destruct (ancb_down j x Hj Hx Ha Hne) as (_ & c & Hc & Hac).
destruct Hc as [Hc|Hc]; [left; apply (KIn _ x ltac:(left; reflexivity))| right; apply (KIn _ x ltac:(right; reflexivity))];
exists c; auto.
+ intros [<-|[H|H]]; [split; [exact Hj| apply ancb_refl]| |];
[destruct (proj1 (KIn _ x ltac:(left; reflexivity)) H) as (c & E & Hx & Ha)
|destruct (proj1 (KIn _ x ltac:(right; reflexivity)) H) as (c & E & Hx & Ha)];
(split; [exact Hx|]; apply (ancb_up j c x Hj Hl); auto; rewrite <- E; auto).
Qed.
Theorem desc_root : desc ns 0 = zseq 0 (elen ns).
Proof.
unfold desc. apply forallb_filter_id. apply forallb_forall. intros x Hx. apply In_zseq in Hx.
apply ancb_true. destruct PO as (P0 & _).
assert (D0 : depth ns 0 = 0) by (unfold depth; exact P0). rewrite D0, Z.sub_0_r.
pose proof (depth_nonneg x ltac:(lia)) as Dx.
destruct (up_spec (Z.to_nat (depth ns x)) x ltac:(lia) ltac:(lia)) as [U1 U2].
split; [exact Dx|]. apply depth_zero; [exact U1| lia].
Qed.
Lemma desc_range : forall j x, In x (desc ns j) -> 0 <= x < elen ns.
Proof. intros j x Hx. apply In_desc in Hx as [Hx _]. exact Hx. Qed.
End c0.
Definition cfail_ns (ns : list anode) (q i col1 : Z) (ok0 ok1 : bool) : list anode :=
let p := node ns q in let m := elen ns in
let c1 := m + (if ok0 then 1 else 0) in
let p' := mkN (n_lo p) (n_hi p) false (n_col p) (if ok0 then Some m else None) (if ok1 then Some c1 else None)
(n_par p) (n_depth p) (n_seg p) in
let kid0 := mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) [] in
let kid1 := mkN i (n_hi p) true col1 None None q (n_depth p + 1) [] in
zupd ns q p' ++ ((if ok0 then [kid0] else []) ++ (if ok1 then [kid1] else [])).
Theorem cfail_ok : forall cnt E0 st i col1 ok0 ok1,
cinv cnt E0 st -> c_q st < elen (c_ns st) ->
let ns' := cfail_ns (c_ns st) (c_q st) i col1 ok0 ok1 in
let L := nleaves (c_ns st) in
par_ok ns' /\ tinv (L + 1) ns' /\ n_depth (node ns' 0) = 0 /\
elen ns' = elen (c_ns st) + (if ok0 then 1 else 0) + (if ok1 then 1 else 0) /\
tree_ok ns' 0 (Z.to_nat (L + 1)).
Proof.
intros cnt E0 [E ns q] i col1 ok0 ok1 INV Hq. unfold cinv in INV. cbn [c_E c_ns c_q] in INV, Hq |- *.
unfold cfail_ns. cbv zeta.
destruct INV as ((C1a & C1b & C1c & C1d & C1e) & C2 & C3a & C3b & C4 & C5a & C5b & C6 & C7 & C8).
set (L := nleaves ns) in *. set (m := elen ns) in *. set (p := node ns q) in *.
assert (Hb0 : 0 <= (if ok0 then 1 else 0) <= 1) by (destruct ok0; lia).
assert (Hb1 : 0 <= (if ok1 then 1 else 0) <= 1) by (destruct ok1; lia).
assert (Vb0 : ok0 = true -> (if ok0 then 1 else 0) = 1) by (intros ->; reflexivity).
assert (Vb1 : ok1 = true -> (if ok1 then 1 else 0) = 1) by (intros ->; reflexivity).
assert (Wb0 : ok0 = false -> (if ok0 then 1 else 0) = 0) by (intros ->; reflexivity).
assert (Wb1 : ok1 = false -> (if ok1 then 1 else 0) = 0) by (intros ->; reflexivity).
set (b0 := if ok0 then 1 else 0) in *. set (b1 := if ok1 then 1 else 0) in *. clearbody b0 b1.
set (p' := mkN (n_lo p) (n_hi p) false (n_col p) (if ok0 then Some m else None) (if ok1 then Some (m + b0) else None)
(n_par p) (n_depth p) (n_seg p)).
set (kid0 := mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) []).
set (kid1 := mkN i (n_hi p) true col1 None None q (n_depth p + 1) []).
set (kids := (if ok0 then [kid0] else []) ++ (if ok1 then [kid1] else [])).
set (ns' := zupd ns q p' ++ kids).
pose proof (C3b q ltac:(lia)) as Hleaf. fold p in Hleaf.
pose proof (C2 q ltac:(lia)) as Cq. cbn beta in Cq. fold p in Cq. destruct Cq as (Cq1 & Cq2 & Cq3 & Cq4 & Cq5).
assert (Hkl : elen kids = b0 + b1).
{ unfold kids, elen. rewrite length_app. destruct ok0, ok1; cbn [length]; rewrite ?Vb0, ?Vb1, ?Wb0, ?Wb1 by reflexivity; reflexivity. }
assert (Hzl : elen (zupd ns q p') = m) by (unfold elen; rewrite zupd_length; reflexivity).
assert (Hlen' : elen ns' = m + b0 + b1).
{ unfold ns'. unfold elen in Hkl, Hzl |- *. rewrite length_app. lia. }
assert (NDo : forall j, 0 <= j < m -> j <> q -> node ns' j = node ns j).
{ intros j Hj Hne. unfold ns'. rewrite node_app_l by lia. rewrite node_zupd by lia. destruct (Z.eqb_spec j q); [lia| reflexivity]. }
assert (NDq : node ns' q = p').
{ unfold ns'. rewrite node_app_l by lia. rewrite node_zupd by lia. rewrite Z.eqb_refl. fold m.
destruct (Z.ltb_spec q m); [reflexivity| lia]. }
assert (NDk : forall j, m <= j < m + b0 + b1 -> node ns' j = kid0 \/ node ns' j = kid1).
{ intros j Hj. unfold ns'. rewrite node_app_r by lia. rewrite Hzl. unfold kids, node, znth.
destruct ok0, ok1; rewrite ?Vb0, ?Vb1, ?Wb0, ?Wb1 in Hj by reflexivity; cbn [app].
- destruct (Z.eq_dec j m) as [->|]; [rewrite Z.sub_diag; left; reflexivity| right].
replace (Z.to_nat (j - m)) with 1%nat by lia. reflexivity.
- left. replace (Z.to_nat (j - m)) with 0%nat by lia. reflexivity.
- right. replace (Z.to_nat (j - m)) with 0%nat by lia. reflexivity.
- lia. }
assert (NK0 : ok0 = true -> node ns' m = kid0).
{ intros E0'. unfold ns'. rewrite node_app_r by lia. rewrite Hzl, Z.sub_diag. unfold kids. rewrite E0'. reflexivity. }
assert (NK1 : ok1 = true -> node ns' (m + b0) = kid1).
{ intros E1'. unfold ns'. rewrite node_app_r by lia. rewrite Hzl. replace (m + b0 - m) with b0 by lia.
unfold kids, node, znth. rewrite E1'. destruct ok0; [rewrite (Vb0 eq_refl)| rewrite (Wb0 eq_refl)]; reflexivity. }
assert (Eo : forall j, 0 <= j < m -> n_depth (node ns' j) = n_depth (node ns j) /\ n_par (node ns' j) = n_par (node ns j)).
{ intros j Hj. destruct (Z.eq_dec j q) as [->|]; [rewrite NDq; cbn [p' n_depth n_par]; fold p; auto| rewrite NDo by lia; auto]. }
assert (NL : forall j, m <= j < m + b0 + b1 -> n_leaf (node ns' j) = true).
{ intros j Hj. destruct (NDk j Hj) as [EE|EE]; rewrite EE; reflexivity. }
assert (KIDS : forall j c, 0 <= j < m + b0 + b1 -> n_leaf (node ns' j) = false ->
(n_k0 (node ns' j) = Some c \/ n_k1 (node ns' j) = Some c) ->
j < c < m + b0 + b1 /\ n_par (node ns' c) = j /\ n_depth (node ns' c) = n_depth (node ns' j) + 1).
{ intros j c Hj Hl Hc. destruct (Z_lt_le_dec j m) as [Hjm|Hjm]; [| rewrite NL in Hl by lia; discriminate].
destruct (Z.eq_dec j q) as [->|Hne].
- rewrite NDq in Hc |- *. cbn [p' n_k0 n_k1 n_depth] in Hc |- *.
destruct Hc as [Hc|Hc].
+ destruct ok0 eqn:Eok0; [|discriminate]. injection Hc as <-. rewrite (NK0 eq_refl). cbn [kid0 n_par n_depth]. fold p.
specialize (Vb0 eq_refl). repeat split; lia.
+ destruct ok1 eqn:Eok1; [|discriminate]. injection Hc as <-. rewrite (NK1 eq_refl). cbn [kid1 n_par n_depth]. fold p.
specialize (Vb1 eq_refl). repeat split; lia.
- rewrite (NDo j) in Hl, Hc |- * by lia.
destruct (C4 j ltac:(lia) Hl) as (c' & H1 & H2 & K0 & K1 & D0 & D1 & _ & _ & _ & Q0 & Q1).
assert (Hc' : c = c' \/ c = c' + 1) by (rewrite K0, K1 in Hc; destruct Hc as [Hc|Hc]; injection Hc; lia).
assert (Hcm : 0 <= c < m) by lia.
destruct (Eo c Hcm) as [-> ->]. destruct Hc' as [-> | ->]; repeat split; try assumption; lia. }
assert (PAR : forall j, 1 <= j < m + b0 + b1 ->
0 <= n_par (node ns' j) < j /\ n_leaf (node ns' (n_par (node ns' j))) = false /\
(n_k0 (node ns' (n_par (node ns' j))) = Some j \/ n_k1 (node ns' (n_par (node ns' j))) = Some j) /\
n_depth (node ns' j) = n_depth (node ns' (n_par (node ns' j))) + 1).
{ intros j Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- destruct (Eo j ltac:(lia)) as [Ed Ep]. rewrite Ed, Ep. destruct (C8 j ltac:(lia)) as (R1 & R2 & R3 & R4).
set (pj := n_par (node ns j)) in *.
destruct (Z.eq_dec pj q) as [Epj|Hne].
+ exfalso. rewrite Epj in R2. fold p in R2. rewrite Hleaf in R2. discriminate.
+ rewrite (NDo pj) by lia. auto.
-
assert (Hkid : (ok0 = true /\ node ns' j = kid0 /\ j = m) \/ (ok1 = true /\ node ns' j = kid1 /\ j = m + b0)).
{ destruct ok0 eqn:Eok0; [specialize (Vb0 eq_refl)| specialize (Wb0 eq_refl)];
(destruct ok1 eqn:Eok1; [specialize (Vb1 eq_refl)| specialize (Wb1 eq_refl)]).
- destruct (Z.eq_dec j m) as [->|]; [left; split; [reflexivity| split; [apply NK0; reflexivity| reflexivity]]| right].
split; [reflexivity|]. split; [replace j with (m + b0) by lia; apply NK1; reflexivity| lia].
- left. split; [reflexivity|]. replace j with m by lia. split; [apply NK0; reflexivity| reflexivity].
- right. split; [reflexivity|]. replace j with (m + b0) by lia. split; [apply NK1; reflexivity| reflexivity].
- exfalso. lia. }
destruct Hkid as [(Eok0 & EE & Ej)|(Eok1 & EE & Ej)]; rewrite EE; cbn [kid0 kid1 n_par n_depth]; rewrite NDq;
cbn [p' n_leaf n_k0 n_k1 n_depth]; fold p.
+ rewrite Eok0. subst j. split; [lia|]. split; [reflexivity|]. split; [left; reflexivity| lia].
+ rewrite Eok1. subst j. split; [lia|]. split; [reflexivity|]. split; [right; reflexivity| lia]. }
assert (D0' : n_depth (node ns' 0) = 0) by (destruct (Eo 0 ltac:(lia)) as [Ed _]; rewrite Ed; exact C7).
assert (PO : par_ok ns').
{ split; [exact D0'|]. split; [rewrite Hlen'; exact PAR|]. split.
- rewrite Hlen'. intros j c Hj Hl Hc. destruct (KIDS j c Hj Hl Hc) as (X1 & X2 & X3). auto.
- rewrite Hlen'. intros j c Hj Hl. destruct (Z_lt_le_dec j m) as [Hjm|Hjm]; [| rewrite NL in Hl by lia; discriminate].
destruct (Z.eq_dec j q) as [->|Hne].
+ rewrite NDq. cbn [p' n_k0 n_k1].
destruct ok0; [specialize (Vb0 eq_refl)| specialize (Wb0 eq_refl)]; destruct ok1; try discriminate. intros EE EE'. injection EE. injection EE'. lia.
+ rewrite NDo by lia. rewrite NDo in Hl by lia. destruct (C4 j ltac:(lia) Hl) as (c' & _ & _ & K0 & K1 & _). rewrite K0, K1. intros EE EE'. injection EE. injection EE'. lia. }
assert (TI : tinv (L + 1) ns').
{ intros j Hj. rewrite Hlen' in Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- destruct (Eo j ltac:(lia)) as [Ed _]. pose proof (C2 j ltac:(lia)) as (_ & _ & D1 & D2 & _).
split; [lia|]. split; [lia|]. intros Hl.
split; intros c Hc; destruct (KIDS j c ltac:(lia) Hl ltac:(auto)) as (X1 & X2 & X3); rewrite Hlen', X3; split; lia.
- destruct (NDk j ltac:(lia)) as [EE|EE]; rewrite EE; cbn [kid0 kid1 n_depth n_leaf]; (split; [lia|]; split; [lia| intros; discriminate]). }
split; [exact PO|]. split; [exact TI|]. split; [exact D0'|]. split; [exact Hlen'|].
apply tinv_root_ok; [exact TI| lia| exact D0'].
Qed.
End z.
Definition dentry : entry := (mkcol 0 0 0, 0).
Definition ecol (E : list entry) (j : Z) : colour := fst (znth dentry E j).
Definition efreq (E : list entry) (j : Z) : Z := snd (znth dentry E j).
Definition pal_bytes (E : list entry) : list Z := flat_map (fun e => [cR (fst e); cG (fst e); cB (fst e)]) E.
Definition fr_vals (E : list entry) : list Z := map snd E.
Definition ent_ok (E : list entry) : Prop := Forall (fun e => colour_ok (fst e) /\ 1 <= snd e) E.
Definition dseg (d : Z) (E : list entry) (lo hi : Z) : list (Z * Z) :=
map (fun e => (snd e, comp d (fst e))) (zsub E lo hi).
Definition Ptest (d s m : Z) (e : entry) : bool := comp d (fst e) * s <=? m.
Lemma pal_bytes_length : forall E, length (pal_bytes E) = (3 * length E)%nat.
Proof.
induction E as [|e r IH]; cbn -[Nat.mul]; [reflexivity|].
change (flat_map _ r) with (pal_bytes r). rewrite IH. lia.
Qed.
Lemma zlen_pal_bytes : forall E, zlen (pal_bytes E) = 3 * elen E.
Proof. intros. unfold zlen, elen. rewrite pal_bytes_length. lia. Qed.
Lemma pal_bytes_nth : forall E j d, (j < length E)%nat -> (d < 3)%nat ->
nth (3 * j + d) (pal_bytes E) 0 = comp (Z.of_nat d) (fst (nth j E dentry)).
Proof.
induction E as [|e r IH]; intros j d Hj Hd; cbn [length] in Hj; [lia|].
cbn [pal_bytes flat_map]. change (flat_map _ r) with (pal_bytes r).
destruct j as [|j].
- cbn [Nat.mul Nat.add nth]. destruct d as [|[|[|d]]]; cbn; try reflexivity; lia.
- replace (3 * S j + d)%nat with (S (S (S (3 * j + d)))) by lia. cbn [nth app]. apply IH; lia.
Qed.
Lemma getz_pal_bytes : forall E j d, 0 <= j < elen E -> 0 <= d < 3 ->
getz (pal_bytes E) (3 * j + d) = comp d (ecol E j).
Proof.
intros E j d Hj Hd. unfold getz, ecol, znth, elen in *.
replace (Z.to_nat (3 * j + d)) with (3 * Z.to_nat j + Z.to_nat d)%nat by lia.
rewrite pal_bytes_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma getz_pal_bytes_at : forall E x, 0 <= x < 3 * elen E ->
getz (pal_bytes E) x = comp (x mod 3) (ecol E (x / 3)).
Proof.
intros E x Hx. pose proof (Z.div_mod x 3 ltac:(lia)). pose proof (Z.mod_pos_bound x 3 ltac:(lia)).
rewrite <- (getz_pal_bytes E (x / 3) (x mod 3)); [f_equal; lia| nia| lia].
Qed.
Lemma pal_bytes_bytes : forall E, ent_ok E -> Forall (fun v => 0 <= v < 256) (pal_bytes E).
Proof.
intros E HE. unfold pal_bytes. apply Forall_flat_map. eapply Forall_impl; [|exact HE].
intros [c f] [(Hr & Hg & Hb) _]. cbn in *. constructor; [lia|]. constructor; [lia|]. constructor; [lia| constructor].
Qed.
Lemma getz_fr_vals : forall E j, 0 <= j < elen E -> getz (fr_vals E) j = efreq E j.
Proof.
intros E j Hj. unfold getz, fr_vals, efreq, znth, elen in *.
rewrite <- (map_nth snd). apply nth_indep. rewrite length_map. lia.
Qed.
Lemma zlen_fr_vals : forall E, zlen (fr_vals E) = elen E.
Proof. intros. unfold zlen, fr_vals, elen. rewrite length_map. reflexivity. Qed.
Lemma ent_ok_at : forall E j, ent_ok E -> 0 <= j < elen E -> colour_ok (ecol E j) /\ 1 <= efreq E j.
Proof.
intros E j HE Hj. unfold ecol, efreq. apply (proj1 (Forall_forall _ _) HE). apply znth_In. exact Hj.
Qed.
Lemma comp_range : forall d c, colour_ok c -> 0 <= comp d c < 256.
Proof. intros d c (Hr & Hg & Hb). unfold comp. destruct (d =? 0); [lia|]. destruct (d =? 1); lia. Qed.
Lemma ent_ok_perm : forall E E', Permutation E E' -> ent_ok E -> ent_ok E'.
Proof. intros E E' HP HE. unfold ent_ok in *. eapply Permutation_Forall; [exact HP| exact HE]. Qed.
Lemma NoDup_fst_perm : forall (E E' : list entry), Permutation E E' -> NoDup (map fst E) -> NoDup (map fst E').
Proof. intros E E' HP Hnd. eapply Permutation_NoDup; [apply Permutation_map; exact HP| exact Hnd]. Qed.
Lemma zsum_fr_perm : forall E E', Permutation E E' -> zsum (fr_vals E') = zsum (fr_vals E).
Proof. intros E E' HP. unfold fr_vals. induction HP; cbn; lia. Qed.
Lemma ecol_eswap : forall E i k j, 0 <= i < elen E -> 0 <= k < elen E -> 0 <= j ->
ecol (eswap dentry E i k) j = if j =? k then ecol E i else if j =? i then ecol E k else ecol E j.
Proof. intros. unfold ecol. rewrite znth_eswap by assumption. destruct (j =? k), (j =? i); reflexivity. Qed.
Lemma efreq_eswap : forall E i k j, 0 <= i < elen E -> 0 <= k < elen E -> 0 <= j ->
efreq (eswap dentry E i k) j = if j =? k then efreq E i else if j =? i then efreq E k else efreq E j.
Proof. intros. unfold efreq. rewrite znth_eswap by assumption. destruct (j =? k), (j =? i); reflexivity. Qed.
Lemma elen_eswap : forall (E : list entry) i k, elen (eswap dentry E i k) = elen E.
Proof. intros. unfold elen. rewrite eswap_length. reflexivity. Qed.
Theorem pal_bytes_eswap : forall E i k x, 0 <= i < elen E -> 0 <= k < elen E -> 0 <= x < 3 * elen E ->
getz (pal_bytes (eswap dentry E i k)) x =
if (3 * k <=? x) && (x <? 3 * k + 3) then getz (pal_bytes E) (x - 3 * k + 3 * i)
else if (3 * i <=? x) && (x <? 3 * i + 3) then getz (pal_bytes E) (x - 3 * i + 3 * k)
else getz (pal_bytes E) x.
Proof.
intros E i k x Hi Hk Hx.
rewrite getz_pal_bytes_at by (rewrite elen_eswap; exact Hx).
rewrite ecol_eswap by (try assumption; apply Z.div_pos; lia).
pose proof (Z.div_mod x 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as Hm.
destruct (Z.eqb_spec (x / 3) k) as [Ek|Nk].
- replace ((3 * k <=? x) && (x <? 3 * k + 3)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace (x - 3 * k + 3 * i) with (3 * i + x mod 3) by lia. rewrite getz_pal_bytes by lia. reflexivity.
- replace ((3 * k <=? x) && (x <? 3 * k + 3)) with false.
2:{ symmetry. apply Bool.andb_false_iff. destruct (Z_lt_le_dec x (3 * k)); [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge].
assert (x / 3 <> k) by exact Nk. assert (k < x / 3 \/ x / 3 < k) as [|] by lia; [lia|].
exfalso. assert (x / 3 < k) by assumption. assert (3 * (x / 3) + 3 <= 3 * k) by lia. lia. }
destruct (Z.eqb_spec (x / 3) i) as [Ei|Ni].
+ replace ((3 * i <=? x) && (x <? 3 * i + 3)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace (x - 3 * i + 3 * k) with (3 * k + x mod 3) by lia. rewrite getz_pal_bytes by lia. reflexivity.
+ replace ((3 * i <=? x) && (x <? 3 * i + 3)) with false.
2:{ symmetry. apply Bool.andb_false_iff. destruct (Z_lt_le_dec x (3 * i)); [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge].
assert (i < x / 3 \/ x / 3 < i) as [|] by lia; [lia|]. assert (3 * (x / 3) + 3 <= 3 * i) by lia. lia. }
rewrite getz_pal_bytes_at by lia. reflexivity.
Qed.
Theorem fr_vals_eswap : forall E i k j, 0 <= i < elen E -> 0 <= k < elen E -> 0 <= j < elen E ->
getz (fr_vals (eswap dentry E i k)) j =
if j =? k then getz (fr_vals E) i else if j =? i then getz (fr_vals E) k else getz (fr_vals E) j.
Proof.
intros E i k j Hi Hk Hj. rewrite !getz_fr_vals by (rewrite ?elen_eswap; lia). apply efreq_eswap; lia.
Qed.
Lemma dseg_nil : forall d E lo, dseg d E lo (lo - 1) = [].
Proof. intros. unfold dseg, zsub. replace (lo - 1 - lo + 1) with 0 by lia. reflexivity. Qed.
Lemma firstn_S_snoc : forall {A} (l : list A) n (d : A), (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l. induction l as [|a r IH]; intros [|n] d Hn; cbn in *; try lia; [reflexivity|].
rewrite (IH n d) by lia. reflexivity.
Qed.
Lemma zsub_snoc : forall {A} (l : list A) lo hi (x : A), 0 <= lo -> lo <= hi + 1 -> hi + 1 < elen l ->
zsub l lo (hi + 1) = zsub l lo hi ++ [znth x l (hi + 1)].
Proof.
intros A l lo hi x Hlo Hle Hhi. unfold zsub, znth, elen in *.
replace (Z.to_nat (hi + 1 - lo + 1)) with (S (Z.to_nat (hi - lo + 1))) by lia.
rewrite (firstn_S_snoc _ _ x) by (rewrite length_skipn; lia).
rewrite nth_skipn. repeat f_equal. lia.
Qed.
Lemma dseg_snoc : forall d E lo hi, 0 <= lo -> lo <= hi + 1 -> hi + 1 < elen E ->
dseg d E lo (hi + 1) = dseg d E lo hi ++ [(efreq E (hi + 1), comp d (ecol E (hi + 1)))].
Proof.
intros d E lo hi Hlo Hle Hhi. unfold dseg. rewrite (zsub_snoc E lo hi dentry) by assumption.
rewrite map_app. reflexivity.
Qed.
Lemma dseg_length : forall d E lo hi, 0 <= lo -> lo <= hi + 1 -> hi < elen E ->
Z.of_nat (length (dseg d E lo hi)) = hi - lo + 1.
Proof. intros. unfold dseg. rewrite length_map, zsub_length by assumption. lia. Qed.
Lemma In_dseg : forall d E lo hi fb, 0 <= lo -> hi < elen E ->
In fb (dseg d E lo hi) <-> exists j, lo <= j <= hi /\ fb = (efreq E j, comp d (ecol E j)).
Proof.
intros d E lo hi fb Hlo Hhi. unfold dseg. rewrite in_map_iff. split.
- intros (e & <- & Hin). apply (zsub_In dentry) in Hin as (j & Hj & <-); [|assumption|assumption].
exists j. split; [exact Hj| reflexivity].
- intros (j & Hj & ->). exists (znth dentry E j). split; [reflexivity|].
apply (zsub_In dentry); [assumption| assumption|]. exists j. auto.
Qed.
Lemma dseg_node_ok : forall d E lo hi, ent_ok E -> 0 <= lo -> hi < elen E -> node_ok (dseg d E lo hi).
Proof.
intros d E lo hi HE Hlo Hhi. unfold node_ok. apply Forall_forall. intros [f b] Hin.
apply In_dseg in Hin as (j & Hj & E1); [|assumption|assumption]. injection E1 as -> ->. cbn [fst snd].
destruct (ent_ok_at E j HE ltac:(lia)) as [Hc Hf]. pose proof (comp_range d _ Hc). lia.
Qed.

Lemma wsum_dseg_split : forall d E a b c, 0 <= a -> a <= b + 1 -> b <= c -> c < elen E ->
wsum (dseg d E a c) = wsum (dseg d E a b) + wsum (dseg d E (b + 1) c).
Proof.
intros d E a b c Ha Hab. remember (Z.to_nat (c - b)) as n eqn:En. revert c En.
induction n as [|n IH]; intros c En Hbc Hc.
- replace c with b by lia. pose proof (dseg_nil d E (b + 1)) as Hn. replace (b + 1 - 1) with b in Hn by lia. rewrite Hn. cbn. lia.
- replace c with ((c - 1) + 1) by lia. rewrite !dseg_snoc by lia. rewrite !wsum_app. cbn [wsum].
rewrite (IH (c - 1)) by lia. lia.
Qed.
Lemma wsum_dseg_total : forall d E, wsum (dseg d E 0 (elen E - 1)) = zsum (fr_vals E).
Proof.
intros d E. unfold dseg, zsub, fr_vals. cbn [Z.to_nat skipn]. replace (elen E - 1 - 0 + 1) with (elen E) by lia.
unfold elen. rewrite Nat2Z.id, firstn_all. induction E as [|[c f] r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma wsum_dseg_nonneg : forall d E lo hi, ent_ok E -> 0 <= lo -> hi < elen E -> 0 <= wsum (dseg d E lo hi).
Proof.
intros d E lo hi HE Hlo Hhi. pose proof (wsum_ge_len _ (dseg_node_ok d E lo hi HE Hlo Hhi)). lia.
Qed.
Lemma wsum_dseg_le : forall d E lo hi, ent_ok E -> 0 <= lo -> lo <= hi + 1 -> hi < elen E ->
0 <= wsum (dseg d E lo hi) <= zsum (fr_vals E).
Proof.
intros d E lo hi HE Hlo Hle Hhi. split; [apply wsum_dseg_nonneg; assumption|].
rewrite <- (wsum_dseg_total d E).
destruct (Z_lt_le_dec hi lo) as [Hem|Hne].
{ replace hi with (lo - 1) by lia. rewrite dseg_nil. cbn. apply wsum_dseg_nonneg; [assumption| lia| lia]. }
rewrite (wsum_dseg_split d E 0 (lo - 1) (elen E - 1)) by lia. replace (lo - 1 + 1) with lo by lia.
rewrite (wsum_dseg_split d E lo hi (elen E - 1)) by lia.
pose proof (wsum_dseg_nonneg d E 0 (lo - 1) HE ltac:(lia) ltac:(lia)).
pose proof (wsum_dseg_nonneg d E (hi + 1) (elen E - 1) HE ltac:(lia) ltac:(lia)). lia.
Qed.
Theorem mean_witnesses : forall d E lo hi, ent_ok E -> 0 <= lo -> lo <= hi -> hi < elen E ->
let l := dseg d E lo hi in
(exists a b, In a l /\ In b l /\ snd a <> snd b) ->
(exists x, lo <= x <= hi /\ smallb dentry (Ptest d (wsum l) (wdot l)) E x = false) /\
(exists y, lo <= y <= hi /\ smallb dentry (Ptest d (wsum l) (wdot l)) E y = true).
Proof.
intros d E lo hi HE Hlo Hle Hhi l Hneq.
pose proof (dseg_node_ok d E lo hi HE Hlo Hhi) as Hok. fold l in Hok.
assert (Hne : l <> []).
{ intros El. destruct Hneq as (a & b & Ha & _). rewrite El in Ha. destruct Ha. }
assert (SM : forall j, lo <= j <= hi -> smallb dentry (Ptest d (wsum l) (wdot l)) E j = (comp d (ecol E j) * wsum l <=? wdot l)).
{ intros j Hj. reflexivity. }
split.
- destruct (exists_max_snd l Hne) as (a & Ha & Hmax).
pose proof Ha as Ha'. apply In_dseg in Ha' as (x & Hx & Ea); [|assumption|assumption].
exists x. split; [exact Hx|]. rewrite SM by exact Hx. apply Z.leb_gt.
replace (comp d (ecol E x)) with (snd a) by (rewrite Ea; reflexivity).
apply wdot_lt_max.
+ apply Forall_forall. intros fb Hfb. split.
* apply (proj1 (Forall_forall _ _) Hok). exact Hfb.
* apply (proj1 (Forall_forall _ _) Hmax). exact Hfb.
+ apply Exists_exists. destruct (not_all_equal_witness l a Hneq Ha) as (b & Hb & Hneb). exists b. split; [exact Hb|].
assert (snd b <= snd a) by (apply (proj1 (Forall_forall _ _) Hmax); exact Hb). lia.
- destruct (exists_min_snd l Hne) as (a & Ha & Hmin).
pose proof Ha as Ha'. apply In_dseg in Ha' as (y & Hy & Ea); [|assumption|assumption].
exists y. split; [exact Hy|]. rewrite SM by exact Hy. apply Z.leb_le.
replace (comp d (ecol E y)) with (snd a) by (rewrite Ea; reflexivity).
apply wdot_ge_min. apply Forall_forall. intros fb Hfb. split.
+ assert (1 <= fst fb /\ 0 <= snd fb <= 255) by (apply (proj1 (Forall_forall _ _) Hok); exact Hfb). lia.
+ apply (proj1 (Forall_forall _ _) Hmin). exact Hfb.
Qed.




Definition segd (d : Z) (seg : list entry) : list (Z * Z) := map (fun e => (snd e, comp d (fst e))) seg.
Lemma dseg_segd : forall d E lo hi, dseg d E lo hi = segd d (zsub E lo hi).
Proof. reflexivity. Qed.
Definition neqd (l : list (Z * Z)) : Prop := exists a b, In a l /\ In b l /\ snd a <> snd b.
Definition cut_ok (seg : list entry) (cut : Z) : Prop :=
0 <= cut < 3 /\ (forall d, 0 <= d < 3 -> neqd (segd d seg) -> neqd (segd cut seg)).
Section d0.
Variables (cnt : Z) (E0 : list entry) (st : cstate (A := entry)).
Hypothesis INV : cinv cnt E0 st.
Hypothesis OK0 : ent_ok E0.
Hypothesis ND0 : NoDup (map fst E0).
Let E := c_E st. Let ns := c_ns st. Let q := c_q st. Let L := nleaves ns.

Theorem crawl_continue : forall Lmax, L <= Lmax - 1 -> Lmax <= cnt ->
q < elen ns /\ 0 <= q /\ elen ns = 2 * L - 1 /\ elen ns + 1 <= 2 * Lmax - 2 /\
n_leaf (node ns q) = true /\
0 <= n_lo (node ns q) <= n_hi (node ns q) /\ n_hi (node ns q) < cnt /\
0 <= n_col (node ns q) < L /\ 1 <= L.
Proof.
intros Lmax HL Hc. pose proof (cinv_counts cnt E0 st INV) as (C1a & C1b & C1c & _).
pose proof (cinv_progress cnt E0 st INV ltac:(subst L ns; lia)) as Hq.
pose proof (cinv_node cnt E0 st INV q ltac:(subst q ns; lia)) as (N1 & N2 & _ & _ & N5).
pose proof (cinv_unprocessed_leaf cnt E0 st INV q ltac:(subst q ns; lia)) as Hl.
subst E ns q L. repeat split; try assumption; try lia.
Qed.

End d0.
Lemma kids_segments : forall (P : entry -> bool) lo hi E E' i, pdone dentry P lo hi E E' i -> 0 <= lo -> hi < elen E -> ent_ok E ->
elen E' = elen E /\ ent_ok E' /\
lo <= i - 1 /\ i - 1 < elen E' /\ i <= hi /\ hi < elen E' /\
(forall d, 1 <= wsum (dseg d E' lo (i - 1)) <= zsum (fr_vals E) /\ 1 <= wsum (dseg d E' i hi) <= zsum (fr_vals E) /\
dseg d E' lo (i - 1) <> [] /\ dseg d E' i hi <> []).
Proof.
intros P lo hi E E' i (Hi & Hlen & HP & _) Hlo Hhi HE.
assert (HE' : ent_ok E') by exact (ent_ok_perm _ _ HP HE).
assert (Hl : elen E' = elen E) by (unfold elen; rewrite Hlen; reflexivity).
split; [exact Hl|]. split; [exact HE'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros d. rewrite <- (zsum_fr_perm _ _ HP).
pose proof (wsum_dseg_le d E' lo (i - 1) HE' ltac:(lia) ltac:(lia) ltac:(lia)) as [_ B1].
pose proof (wsum_dseg_le d E' i hi HE' ltac:(lia) ltac:(lia) ltac:(lia)) as [_ B2].
pose proof (dseg_length d E' lo (i - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as L1.
pose proof (dseg_length d E' i hi ltac:(lia) ltac:(lia) ltac:(lia)) as L2.
assert (N1 : dseg d E' lo (i - 1) <> []) by (intros X; rewrite X in L1; cbn in L1; lia).
assert (N2 : dseg d E' i hi <> []) by (intros X; rewrite X in L2; cbn in L2; lia).
pose proof (wsum_pos _ (dseg_node_ok d E' lo (i - 1) HE' ltac:(lia) ltac:(lia)) N1).
pose proof (wsum_pos _ (dseg_node_ok d E' i hi HE' ltac:(lia) ltac:(lia)) N2).
repeat split; try assumption; lia.
Qed.
Lemma root_segment : forall E d, ent_ok E -> 1 <= elen E ->
dseg d E 0 (elen E - 1) <> [] /\ 1 <= wsum (dseg d E 0 (elen E - 1)) /\ wsum (dseg d E 0 (elen E - 1)) = zsum (fr_vals E) /\
node_ok (dseg d E 0 (elen E - 1)).
Proof.
intros E d HE Hlen. pose proof (dseg_length d E 0 (elen E - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as L1.
assert (N1 : dseg d E 0 (elen E - 1) <> []) by (intros X; rewrite X in L1; cbn in L1; lia).
pose proof (dseg_node_ok d E 0 (elen E - 1) HE ltac:(lia) ltac:(lia)) as Hok.
split; [exact N1|]. split; [exact (wsum_pos _ Hok N1)|]. split; [apply wsum_dseg_total| exact Hok].
Qed.
Lemma dseg_as_map : forall d E lo hi pal fr, 0 <= d < 3 -> 0 <= lo -> lo <= hi + 1 -> hi < elen E ->
(forall x, 0 <= x < 3 * elen E -> getz pal x = getz (pal_bytes E) x) ->
(forall i, 0 <= i < elen E -> getz fr i = getz (fr_vals E) i) ->
dseg d E lo hi = map (fun i => (getz fr i, getz pal (3 * i + d))) (zseq lo (hi - lo + 1)).
Proof.
intros d E lo hi pal fr Hd Hlo Hle Hhi Hpal Hfr.
remember (Z.to_nat (hi - lo + 1)) as n eqn:En. revert hi En Hle Hhi.
induction n as [|n IH]; intros hi En Hle Hhi.
- replace hi with (lo - 1) by lia. rewrite dseg_nil. unfold zseq. replace (Z.to_nat (lo - 1 - lo + 1)) with 0%nat by lia. reflexivity.
- replace hi with ((hi - 1) + 1) by lia. rewrite dseg_snoc by lia.
replace (hi - 1 + 1 - lo + 1) with ((hi - 1 - lo + 1) + 1) by lia. rewrite zseq_succ by lia. rewrite map_app.
rewrite <- (IH (hi - 1)) by lia. cbn [map]. f_equal. f_equal.
replace (lo + (hi - 1 - lo + 1)) with (hi - 1 + 1) by lia.
rewrite Hfr, Hpal by lia. rewrite getz_fr_vals, getz_pal_bytes by lia. reflexivity.
Qed.
