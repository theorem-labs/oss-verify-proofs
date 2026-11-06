(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0a.v, with its module paths changed. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/YG0a.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Fixpoint zall (fuel : nat) (i : Z) (f : Z -> bool) : bool :=
match fuel with O => true | S n => f i && zall n (i + 1) f end.
Lemma zall_spec : forall fuel i f, zall fuel i f = true -> forall z, i <= z < i + Z.of_nat fuel -> f z = true.
Proof.
induction fuel as [|n IH]; intros i f H z Hz; cbn in H; [lia|].
apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec z i) as [->|Hne]; [exact H1|].
apply (IH (i + 1) f H2). rewrite Nat2Z.inj_succ in Hz. lia.
Qed.
Lemma zall_range : forall lo hi f, zall (Z.to_nat (hi - lo + 1)) lo f = true -> forall z, lo <= z <= hi -> f z = true.
Proof.
intros lo hi f H z Hz. apply (zall_spec _ _ _ H). rewrite Z2Nat.id; lia.
Qed.
Definition class_okb (c : Z) : bool :=
(0 <? class_size c) && (class_size c mod 32 =? 0) && (class_size c <=? kMaxSize)
&& (2 <=? max_cached c) && (max_cached c <=? 16) && (max_cached c mod 2 =? 0)
&& (max_cached c / 2 * class_size c <=? kMaxSize).
Lemma class_ok : forall c, 1 <= c <= 31 ->
0 < class_size c /\ class_size c mod 32 = 0 /\ class_size c <= kMaxSize /\
2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0 /\ max_cached c / 2 * class_size c <= kMaxSize.
Proof.
assert (H : zall (Z.to_nat (31 - 1 + 1)) 1 class_okb = true) by (vm_compute; reflexivity).
intros c Hc. pose proof (zall_range 1 31 class_okb H c Hc) as Hb. unfold class_okb in Hb.
repeat (apply andb_prop in Hb as [Hb ?X]).
repeat split; try lia; try (apply Z.eqb_eq; assumption); try (apply Z.leb_le; assumption); apply Z.ltb_lt; assumption.
Qed.
Lemma class_id_eq' : forall s, 1 <= s <= kMaxSize -> class_id s = class_id' s.
Proof.
assert (H : zall (Z.to_nat (65536 - 1 + 1)) 1 (fun s => class_id s =? class_id' s) = true) by (vm_compute; reflexivity).
intros s Hs. apply Z.eqb_eq. exact (zall_range 1 65536 _ H s Hs).
Qed.
Lemma first_class_ok : forall fuel s c,
1 <= c -> c + Z.of_nat fuel = 30 -> s <= kMaxSize ->
c <= first_class s c fuel <= 30 /\ s <= class_size (first_class s c fuel).
Proof.
induction fuel as [|n IH]; intros s c Hc Hf Hs; cbn [first_class].
- cbn in Hf. assert (c = 30) by lia. subst c. cbn. unfold kMaxSize in Hs. lia.
- destruct (s <=? class_size c) eqn:E.
+ apply Z.leb_le in E. lia.
+ rewrite Nat2Z.inj_succ in Hf. destruct (IH s (c + 1)) as [H1 H2]; try lia.
Qed.
Lemma class_id'_ok : forall s, s <= kMaxSize -> 1 <= class_id' s <= 30 /\ s <= class_size (class_id' s).
Proof.
intros s Hs. unfold class_id'. destruct (first_class_ok 29 s 1) as [H1 H2]; [lia | reflexivity | exact Hs |].
split; [lia | exact H2].
Qed.
Lemma class_id_ok : forall s, 1 <= s <= kMaxSize -> 1 <= class_id s <= 30 /\ s <= class_size (class_id s).
Proof. intros s Hs. rewrite (class_id_eq' s Hs). apply class_id'_ok. lia. Qed.
Lemma round_up_ge : forall x a, 0 < a -> x <= round_up x a < x + a /\ round_up x a mod a = 0.
Proof.
intros x a Ha. unfold round_up.
pose proof (Z.div_mod (x + a - 1) a ltac:(lia)) as H1.
pose proof (Z.mod_pos_bound (x + a - 1) a Ha) as H2.
split; [nia|]. apply Z_mod_mult.
Qed.
Lemma round_up_le : forall x a b, 0 < a -> x <= b -> b mod a = 0 -> round_up x a <= b.
Proof.
intros x a b Ha Hxb Hb. unfold round_up.
pose proof (Z.div_mod b a ltac:(lia)) as Hbm.
assert (Hq : (x + a - 1) / a < b / a + 1) by (apply Z.div_lt_upper_bound; lia).
apply Z.le_trans with (m := b / a * a); [|lia]. apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Lemma rz_size_cases : forall n, In (rz_size n) [16; 32; 64; 128; 256; 512; 1024; 2048].
Proof.
intros n. unfold rz_size, rz_log.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; tauto.
Qed.
Lemma rz_size_bounds : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
intros n. pose proof (rz_size_cases n) as H. cbn in H.
destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; lia.
Qed.
Lemma req_size_bounds : forall n, 0 <= n -> Z.max n 1 = req_size n /\ 1 <= req_size n /\ n <= req_size n <= Z.max n 8.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; lia. Qed.
Lemma rounded_size_bounds : forall n, 0 <= n -> Z.max n 8 <= rounded_size n < Z.max n 8 + 8 /\ rounded_size n mod 8 = 0.
Proof. intros n Hn. unfold rounded_size. apply round_up_ge. lia. Qed.
Lemma needed_primary_bounds : forall n, 0 <= n ->
req_size n + rz_size n <= needed_primary n /\ 24 <= needed_primary n < n + 8 + 8 + 2048 /\ needed_primary n mod 8 = 0.
Proof.
intros n Hn. unfold needed_primary.
pose proof (rounded_size_bounds n Hn) as [R1 R2]. pose proof (req_size_bounds n Hn) as (_ & Q1 & Q2).
pose proof (rz_size_bounds n) as [Z1 Z2].
split; [lia|]. split; [lia|].
rewrite Z.add_mod, R2 by lia. replace (rz_size n mod 8) with 0; [reflexivity|].
symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Z2; [|lia]. destruct Z2 as [k ->]. exists (k * 2). lia.
Qed.
Lemma primary_geometry : forall n, 0 <= n -> from_primary n = true ->
1 <= chunk_class n <= 30 /\
rz_size n + req_size n <= needed_size n <= class_size (chunk_class n) /\
class_size (chunk_class n) <= kMaxSize /\ class_size (chunk_class n) mod 32 = 0 /\ 0 < class_size (chunk_class n).
Proof.
intros n Hn Hp. unfold chunk_class, needed_size. rewrite Hp.
unfold from_primary in Hp. apply Z.leb_le in Hp.
pose proof (needed_primary_bounds n Hn) as (N1 & N2 & N3).
destruct (class_id_ok (needed_primary n)) as [C1 C2]; [lia|].
pose proof (class_ok (class_id (needed_primary n)) ltac:(lia)) as (K1 & K2 & K3 & _).
repeat split; lia.
Qed.
Lemma secondary_geometry : forall n, 0 <= n -> from_primary n = false ->
kMaxSize < needed_size n /\ needed_size n = needed_primary n + rz_size n /\
kPage + kSecRz + req_size n <= sec_map_size n /\ kPage + needed_size n <= sec_map_size n < needed_size n + 2 * kPage /\
sec_map_size n mod kPage = 0 /\ sec_map_size n <= n + 3 * kPage + 4096 + 16.
Proof.
intros n Hn Hp. unfold sec_map_size, needed_size. rewrite Hp.
unfold from_primary in Hp. apply Z.leb_gt in Hp.
pose proof (needed_primary_bounds n Hn) as (N1 & N2 & N3).
pose proof (rz_size_bounds n) as [Z1 Z2].
pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as [U1 U2].
assert (Hrz : rz_size n = 2048).
{
unfold rz_size, rz_log. unfold needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize in Hp.
repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:?E end; cbn in *;
try reflexivity; exfalso;
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end;
try lia.
all: pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)); nia. }
unfold kPage, kSecRz, kMaxSize in *. rewrite Hrz in *.
repeat split; try lia. rewrite Z.add_mod, U2 by lia. reflexivity.
Qed.
