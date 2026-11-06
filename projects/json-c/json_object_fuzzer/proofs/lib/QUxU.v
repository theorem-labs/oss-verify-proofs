(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sc_prop (s : Z) : bool :=
let c := class_id s in
(1 <=? c) && (c <=? 30) && (s <=? class_size c) && (class_size c <=? 65536)
&& (class_size c mod 32 =? 0) && (class_id (class_size c) =? c)
&& (2 <=? max_count c) && (max_count c <=? 16) && (max_count c mod 2 =? 0).

Fixpoint sc_check_up (n : nat) (s : Z) : bool :=
match n with O => true | S n' => sc_prop s && sc_check_up n' (s + 1) end.

Lemma sc_check_all : sc_check_up 65536 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sc_check_up_sound : forall n s x, sc_check_up n s = true -> s <= x < s + Z.of_nat n -> sc_prop x = true.
Proof.
induction n as [|n IH]; intros s x H Hx; [lia|].
cbn [sc_check_up] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x s) as [->|NE]; [exact H1|].
eapply IH; [exact H2|]. lia.
Qed.

Lemma sc_prop_holds : forall s, 1 <= s <= 65536 -> sc_prop s = true.
Proof.
intros s Hs. apply (sc_check_up_sound 65536%nat 1 s sc_check_all).
assert (E : Z.of_nat 65536%nat = 65536) by (vm_compute; reflexivity). rewrite E. lia.
Qed.

Lemma class_facts : forall s, 1 <= s <= 65536 ->
let c := class_id s in
1 <= c <= 30 /\ s <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ class_id (class_size c) = c
/\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
Proof.
intros s Hs. pose proof (sc_prop_holds s Hs) as H. unfold sc_prop in H. cbv zeta in H. cbv zeta.
repeat (apply andb_prop in H as [H ?X]).
repeat match goal with
| K : (_ <=? _) = true |- _ => apply Z.leb_le in K
| K : (_ =? _) = true |- _ => apply Z.eqb_eq in K
end.
repeat split; assumption.
Qed.

Lemma rz_size_cases : forall n,
rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/
rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof.
intros n. unfold rz_size.
repeat (destruct (_ <=? _); [tauto|]). tauto.
Qed.

Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; rewrite H; (split; [lia| reflexivity]). Qed.

Lemma round_up_8 : forall x, 0 <= x -> x <= round_up x 8 < x + 8 /\ round_up x 8 mod 8 = 0.
Proof. intros x Hx. unfold round_up. split; [|apply Z_mod_mult]. Z.div_mod_to_equations. lia. Qed.

Lemma round_up_ge : forall x a, 0 < a -> x <= round_up x a /\ round_up x a < x + a /\ round_up x a mod a = 0.
Proof. intros x a Ha. unfold round_up. split; [|split; [|apply Z_mod_mult]]; Z.div_mod_to_equations; nia. Qed.

Lemma needed_facts : forall n, 0 <= n ->
Z.max n 8 + rz_size n <= needed n /\ needed n < Z.max n 8 + 8 + rz_size n /\ needed n mod 8 = 0 /\ 24 <= needed n.
Proof.
intros n Hn. unfold needed. pose proof (round_up_8 (Z.max n 8) ltac:(lia)) as [A B].
pose proof (rz_size_range n) as [R1 R2].
split; [lia|]. split; [lia|]. split; [|lia].
rewrite Z.add_mod, B by lia. rewrite Z.add_0_l, Z.mod_mod by lia.
replace (rz_size n) with (16 * (rz_size n / 16)) by (Z.div_mod_to_equations; lia).
rewrite Z.mul_comm. replace 16 with (2 * 8) by reflexivity. rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

Lemma from_primary_iff : forall n, from_primary n = true <-> needed n <= kMaxSize.
Proof. intros n. unfold from_primary. rewrite Z.leb_le. tauto. Qed.

Lemma class_of_facts : forall n, 0 <= n -> from_primary n = true ->
let c := class_of n in
1 <= c <= 30 /\ needed n <= class_size c <= 65536 /\ class_size c mod 32 = 0
/\ rz_size n + Z.max n 8 <= class_size c
/\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0
/\ class_id (class_size c) = c.
Proof.
intros n Hn HP. apply from_primary_iff in HP. unfold kMaxSize in HP.
pose proof (needed_facts n Hn) as (N1 & N2 & N3 & N4).
pose proof (class_facts (needed n) ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
unfold class_of. cbv zeta. repeat split; try lia.
Qed.

