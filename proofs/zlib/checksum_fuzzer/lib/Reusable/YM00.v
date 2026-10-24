(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Definition rm (x : Z) (l : list Z) : list Z := List.filter (fun y => negb (y =? x)) l.
Lemma rm_cons : forall x y l,
rm x (y :: l) = if negb (y =? x) then y :: rm x l else rm x l.
Proof. reflexivity. Qed.
Lemma rm_length_le : forall l x, (length (rm x l) <= length l)%nat.
Proof.
induction l as [|y l IH]; intros x; [cbn; lia|].
rewrite rm_cons. destruct (negb (y =? x)); cbn [length]; specialize (IH x); lia.
Qed.
Lemma rm_length_lt : forall l x, In x l -> (length (rm x l) < length l)%nat.
Proof.
induction l as [|y l IH]; intros x Hin; [destruct Hin|].
rewrite rm_cons. destruct Hin as [-> | Hin].
- rewrite Z.eqb_refl. cbn [negb length]. pose proof (rm_length_le l x). lia.
- destruct (negb (y =? x)); cbn [length]; specialize (IH x Hin); lia.
Qed.
Lemma rm_in : forall l x j, In j l -> j <> x -> In j (rm x l).
Proof.
intros l x j Hin Hne. unfold rm. apply List.filter_In. split; [exact Hin|].
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hne.
Qed.
Lemma range_covered_length : forall (n : nat) (l : list Z) (lo : Z),
(forall j, lo <= j < lo + Z.of_nat n -> In j l) -> (n <= length l)%nat.
Proof.
induction n as [|n IH]; intros l lo Hcov; [lia|].
assert (Hlo : In lo l) by (apply Hcov; lia).
pose proof (rm_length_lt l lo Hlo) as Hlt.
assert (Hrest : (n <= length (rm lo l))%nat).
{ apply (IH (rm lo l) (lo + 1)). intros j Hj. apply rm_in; [apply Hcov; lia | lia]. }
lia.
Qed.
Lemma range_search : forall (n : nat) (l : list Z) (lo : Z),
(exists j, lo <= j < lo + Z.of_nat n /\ ~ In j l)
\/ (forall j, lo <= j < lo + Z.of_nat n -> In j l).
Proof.
induction n as [|n IH]; intros l lo.
- right. intros j Hj. lia.
- destruct (in_dec Z.eq_dec lo l) as [Hin | Hnin].
+ destruct (IH l (lo + 1)) as [(j & Hj & Hnj) | Hall].
* left. exists j. split; [lia | exact Hnj].
* right. intros j Hj.
destruct (Z.eq_dec j lo) as [-> | Hne]; [exact Hin | apply Hall; lia].
+ left. exists lo. split; [lia | exact Hnin].
Qed.
Lemma pigeonhole_Z : forall (l : list Z) (lo : Z) (n : nat),
(length l < n)%nat -> exists j, lo <= j < lo + Z.of_nat n /\ ~ In j l.
Proof.
intros l lo n Hlen.
destruct (range_search n l lo) as [H | Hall]; [exact H|].
pose proof (range_covered_length n l lo Hall). lia.
Qed.
End c.
Definition slot : Z := 2 ^ 40.
Definition iv_slot (p : word * word) : Z :=
(bv_unsigned (fst p) + bv_unsigned (snd p) - 1) / slot.
Lemma u64_bounds : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
intro w. pose proof (bv_unsigned_in_range 64 w) as H.
unfold bv_modulus in H. change (Z.of_N 64) with 64 in H. exact H.
Qed.
Lemma Z_to_bv64_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. apply Z_to_bv_small. unfold bv_modulus. change (Z.of_N 64) with 64. exact Hz.
Qed.
Lemma overlap_pins_slot : forall (b s : word) (j nZ : Z),
0 < nZ -> bv_unsigned s + nZ <= slot ->
0 <= j * slot < 2 ^ 64 -> nZ < 2 ^ 64 ->
iv_overlap (Z_to_bv 64 (j * slot)) (Z_to_bv 64 nZ) b s = true ->
j = iv_slot (b, s).
Proof.
intros b s j nZ HnZ Hsum Hj HnZ64 Hov.
assert (Hslotv : slot = 1099511627776) by reflexivity.
rewrite Hslotv in *.
unfold iv_overlap in Hov. apply andb_true_iff in Hov as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
rewrite (Z_to_bv64_small (j * 1099511627776)) in H1 by lia.
rewrite (Z_to_bv64_small (j * 1099511627776)) in H2 by lia.
rewrite (Z_to_bv64_small nZ) in H2 by lia.
unfold iv_slot. cbn [fst snd]. rewrite Hslotv.
pose proof (u64_bounds b). pose proof (u64_bounds s).
apply Z.le_antisymm.
- apply Z.div_le_lower_bound; lia.
- apply Z.lt_succ_r. rewrite <- Z.add_1_r.
apply Z.div_lt_upper_bound; lia.
Qed.
Theorem region_free_exists {rc : RunCeil} : forall (ivs : list (word * word)) (nZ : Z),
0 < nZ <= 2 ^ 39 ->
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 39) ivs ->
(length ivs <= 120)%nat ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs nZ HnZ Hsizes Hlen.
destruct (pigeonhole_Z (map iv_slot ivs) 1 121) as (j & Hj & Hnotin).
{ rewrite length_map. lia. }
change (Z.of_nat 121) with 121 in Hj.
assert (Hslotv : slot = 1099511627776) by reflexivity.
assert (Hjs : 0 <= j * slot < 2 ^ 64) by (rewrite Hslotv; lia).
exists (Z_to_bv 64 (j * slot)).
rewrite Z_to_bv64_small by exact Hjs.
split; [|split; [|split]].
- unfold page_size. rewrite Hslotv.
replace (j * 1099511627776) with ((j * 268435456) * 4096) by lia.
apply Z_mod_mult.
- rewrite Hslotv. lia.
- pose proof alloc_ceiling_val. rewrite Hslotv. lia.
-
induction ivs as [|[b s] ivs IH]; [reflexivity|].
cbn [region_free]. apply andb_true_iff. split.
+ apply Bool.negb_true_iff.
destruct (iv_overlap (Z_to_bv 64 (j * slot)) (Z_to_bv 64 nZ) b s) eqn:Hov; [|reflexivity].
exfalso. apply Hnotin. cbn [map]. left. symmetry.
apply (overlap_pins_slot b s j nZ); try lia.
* apply Forall_inv in Hsizes. cbn [snd] in Hsizes. rewrite Hslotv. lia.
* exact Hov.
+ apply IH.
* apply Forall_inv_tail in Hsizes. exact Hsizes.
* cbn [length] in Hlen. lia.
* intro Hin. apply Hnotin. cbn [map]. right. exact Hin.
Qed.
Lemma region_free_app : forall l1 l2 (lo n : word),
region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
induction l1 as [|[a sz] l1 IH]; intros l2 lo n; [reflexivity|].
cbn [region_free app]. rewrite IH. apply andb_assoc.
Qed.
