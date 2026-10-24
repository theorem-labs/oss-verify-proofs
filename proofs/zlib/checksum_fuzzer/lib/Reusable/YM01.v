(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05 YM00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition slot28 : Z := 2 ^ 28.
Definition JMAX : Z := 524278.
Lemma JMAX_fits : (JMAX + 1) * slot28 <= 140735332483072.
Proof. unfold JMAX, slot28. cbn. lia. Qed.
Fixpoint ivs_bytes (ivs : list (word * word)) : Z :=
match ivs with
| [] => 0
| p :: r => bv_unsigned (snd p) + ivs_bytes r
end.
Lemma ivs_bytes_nonneg : forall ivs, 0 <= ivs_bytes ivs.
Proof. induction ivs as [|p r IH]; cbn; [lia|]. pose proof (u64_bounds (snd p)). lia. Qed.
Lemma ivs_bytes_app : forall l1 l2, ivs_bytes (l1 ++ l2) = ivs_bytes l1 + ivs_bytes l2.
Proof. induction l1 as [|p r IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma ivs_bytes_live_bytes : forall ivs, ivs_bytes ivs = live_bytes ivs.
Proof. induction ivs as [|[a s] r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Fixpoint zrange (lo : Z) (n : nat) : list Z :=
match n with
| O => []
| S k => lo :: zrange (lo + 1) k
end.
Lemma zrange_in : forall n lo j, lo <= j < lo + Z.of_nat n -> In j (zrange lo n).
Proof.
induction n as [|n IH]; intros lo j Hj; cbn; [lia|].
destruct (Z.eq_dec j lo) as [-> | Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.
Lemma zrange_length : forall n lo, length (zrange lo n) = n.
Proof. induction n as [|n IH]; intros lo; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Definition blocked (nZ : Z) (p : word * word) : list Z :=
let b := bv_unsigned (fst p) in
let s := bv_unsigned (snd p) in
zrange ((b - nZ) / slot28 + 1) (Z.to_nat (s / slot28 + 2)).
Fixpoint blocked_all (nZ : Z) (ivs : list (word * word)) : list Z :=
match ivs with
| [] => []
| p :: r => blocked nZ p ++ blocked_all nZ r
end.
Lemma div_superadd : forall a b c, 0 < c -> a / c + b / c <= (a + b) / c.
Proof.
intros a b c Hc. apply Z.div_le_lower_bound; [exact Hc|].
pose proof (Z.mul_div_le a c Hc). pose proof (Z.mul_div_le b c Hc). lia.
Qed.
Lemma div_subadd : forall a b c, 0 < c -> (a + b) / c <= a / c + b / c + 1.
Proof.
intros a b c Hc.
pose proof (Z_div_mod_eq_full a c) as Ea. pose proof (Z.mod_pos_bound a c Hc) as Ma.
pose proof (Z_div_mod_eq_full b c) as Eb. pose proof (Z.mod_pos_bound b c Hc) as Mb.
apply Z.lt_succ_r. rewrite <- Z.add_1_r. apply Z.div_lt_upper_bound; [exact Hc|].
set (qa := a / c) in *. set (qb := b / c) in *. set (ma := a mod c) in *. set (mb := b mod c) in *.
clearbody qa qb ma mb. nia.
Qed.
Lemma blocked_all_length : forall nZ ivs,
Z.of_nat (length (blocked_all nZ ivs)) <= 2 * Z.of_nat (length ivs) + ivs_bytes ivs / slot28.
Proof.
intros nZ ivs. induction ivs as [|[b s] r IH].
{ cbn [blocked_all ivs_bytes length Z.of_nat]. rewrite Zdiv_0_l. lia. }
cbn [blocked_all ivs_bytes length fst snd].
rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ. unfold blocked. cbn [fst snd]. rewrite zrange_length.
pose proof (u64_bounds s) as Hs. pose proof (ivs_bytes_nonneg r) as Hr.
assert (H1 : 0 <= bv_unsigned s / slot28) by (apply Z.div_pos; unfold slot28; lia).
rewrite Z2Nat.id by lia.
pose proof (div_superadd (bv_unsigned s) (ivs_bytes r) slot28 ltac:(unfold slot28; lia)) as H2.
lia.
Qed.
Lemma overlap_in_blocked : forall (b s : word) (j nZ : Z),
0 < nZ <= slot28 ->
0 <= j * slot28 < 2 ^ 64 ->
iv_overlap (Z_to_bv 64 (j * slot28)) (Z_to_bv 64 nZ) b s = true ->
In j (blocked nZ (b, s)).
Proof.
intros b s j nZ HnZ Hj Hov.
assert (Hslotv : slot28 = 268435456) by reflexivity.
unfold iv_overlap in Hov. apply andb_true_iff in Hov as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
rewrite (Z_to_bv64_small (j * slot28)) in H1 by lia.
rewrite (Z_to_bv64_small (j * slot28)) in H2 by lia.
rewrite (Z_to_bv64_small nZ) in H2 by (rewrite Hslotv in HnZ; lia).
unfold blocked. cbn [fst snd]. apply zrange_in.
pose proof (u64_bounds b) as Hb. pose proof (u64_bounds s) as Hs.
assert (Hsl : 0 < slot28) by (rewrite Hslotv; lia).
assert (Hs0 : 0 <= bv_unsigned s / slot28) by (apply Z.div_pos; lia).
rewrite Z2Nat.id by lia.
assert (Q1 : (bv_unsigned b - nZ) / slot28 < j).
{ apply Z.div_lt_upper_bound; [exact Hsl|]. lia. }
assert (Q2 : j <= (bv_unsigned b + bv_unsigned s - 1) / slot28).
{ apply Z.div_le_lower_bound; [exact Hsl|]. lia. }
pose proof (div_subadd (bv_unsigned b - nZ) (bv_unsigned s + nZ - 1) slot28 Hsl) as D.
replace (bv_unsigned b - nZ + (bv_unsigned s + nZ - 1)) with (bv_unsigned b + bv_unsigned s - 1) in D by lia.
assert (Q3 : (bv_unsigned s + nZ - 1) / slot28 < bv_unsigned s / slot28 + 2).
{ apply Z.div_lt_upper_bound; [exact Hsl|].
pose proof (Z_div_mod_eq_full (bv_unsigned s) slot28) as E. pose proof (Z.mod_pos_bound (bv_unsigned s) slot28 Hsl) as M.
set (q := bv_unsigned s / slot28) in *. set (m := bv_unsigned s mod slot28) in *. clearbody q m. nia. }
set (qa := (bv_unsigned b - nZ) / slot28) in *.
set (qb := (bv_unsigned b + bv_unsigned s - 1) / slot28) in *.
set (qc := (bv_unsigned s + nZ - 1) / slot28) in *.
set (qd := bv_unsigned s / slot28) in *.
clearbody qa qb qc qd. lia.
Qed.
Lemma in_blocked_all : forall nZ ivs p j, In p ivs -> In j (blocked nZ p) -> In j (blocked_all nZ ivs).
Proof.
intros nZ ivs p j Hp Hj. induction ivs as [|q r IH]; [destruct Hp|].
cbn [blocked_all]. apply in_app_iff. destruct Hp as [-> | Hp]; [left; exact Hj | right; apply IH; exact Hp].
Qed.
Theorem region_free_exists28 {rc : RunCeil} : forall (ivs : list (word * word)) (nZ : Z),
0 < nZ <= slot28 ->
2 * Z.of_nat (length ivs) + ivs_bytes ivs / slot28 < JMAX ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs nZ HnZ Hcnt.
assert (Hslotv : slot28 = 268435456) by reflexivity.
pose proof (blocked_all_length nZ ivs) as HL.
destruct (pigeonhole_Z (blocked_all nZ ivs) 1 (Z.to_nat JMAX)) as (j & Hj & Hnotin).
{ unfold JMAX in *. lia. }
rewrite Z2Nat.id in Hj by (unfold JMAX; lia).
assert (Hjs : 0 <= j * slot28 < 2 ^ 64) by (unfold JMAX in Hj; rewrite Hslotv; lia).
exists (Z_to_bv 64 (j * slot28)).
rewrite Z_to_bv64_small by exact Hjs.
split; [|split; [|split]].
- unfold page_size. rewrite Hslotv.
replace (j * 268435456) with ((j * 65536) * 4096) by lia. apply Z_mod_mult.
- rewrite Hslotv. lia.
- pose proof alloc_ceiling_val. pose proof JMAX_fits. unfold JMAX in *. rewrite Hslotv in *. nia.
- induction ivs as [|[b s] ivs IH]; [reflexivity|].
cbn [region_free]. apply andb_true_iff. split.
+ apply Bool.negb_true_iff.
destruct (iv_overlap (Z_to_bv 64 (j * slot28)) (Z_to_bv 64 nZ) b s) eqn:Hov; [|reflexivity].
exfalso. apply Hnotin. cbn [blocked_all]. apply in_app_iff. left.
apply (overlap_in_blocked b s j nZ HnZ Hjs Hov).
+ apply IH.
* cbn [length ivs_bytes fst snd] in Hcnt. pose proof (u64_bounds s).
pose proof (div_superadd (bv_unsigned s) (ivs_bytes ivs) slot28 ltac:(lia)).
assert (0 <= bv_unsigned s / slot28) by (apply Z.div_pos; lia). lia.
* cbn [blocked_all length] in HL |- *. rewrite length_app, Nat2Z.inj_add in HL.
pose proof (blocked_all_length nZ ivs). exact H.
* intro Hin. apply Hnotin. cbn [blocked_all]. apply in_app_iff. right. exact Hin.
Qed.
Corollary region_free_exists28_std {rc : RunCeil} : forall (ivs : list (word * word)) (nZ : Z),
0 < nZ <= 2 ^ 28 ->
Z.of_nat (length ivs) <= 2 ^ 16 ->
ivs_bytes ivs <= 2 ^ 36 ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs nZ HnZ Hc Hb. apply region_free_exists28; [exact HnZ|].
assert (ivs_bytes ivs / slot28 <= 2 ^ 8).
{ apply Z.div_le_upper_bound; [unfold slot28; lia|]. unfold slot28. lia. }
unfold JMAX. lia.
Qed.
