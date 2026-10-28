(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition reg_usage (st : astate) (c : Z) : Z :=
  let r := get_region st c in
  rg_mapped_user r + rg_mapped_free_array r + 40960 * (rg_mapped_user r / 262144 + rg_mapped_free_array r / 262144).
Fixpoint csum (f : Z -> Z) (c : Z) (n : nat) : Z := match n with O => 0 | S k => f c + csum f (c + 1) k end.
Definition pusage (st : astate) : Z := csum (reg_usage st) 1 31.
Definition B_PRIM : Z := 2 ^ 37.

Lemma csum_le : forall f g n c, (forall k, c <= k < c + Z.of_nat n -> f k <= g k) -> csum f c n <= csum g c n.
Proof.
  intros f g n. induction n as [|n IH]; intros c H; cbn [csum]; [lia|].
  rewrite Nat2Z.inj_succ in H. pose proof (H c ltac:(lia)). pose proof (IH (c + 1) ltac:(intros k Hk; apply H; lia)). lia.
Qed.
Lemma csum_ext : forall f g n c, (forall k, c <= k < c + Z.of_nat n -> f k = g k) -> csum f c n = csum g c n.
Proof.
  intros f g n c H. pose proof (csum_le f g n c ltac:(intros k Hk; rewrite (H k Hk); lia)).
  pose proof (csum_le g f n c ltac:(intros k Hk; rewrite (H k Hk); lia)). lia.
Qed.

Lemma csum_split : forall f n c k, c <= k < c + Z.of_nat n ->
  csum f c n = f k + csum (fun j => if j =? k then 0 else f j) c n.
Proof.
  intros f n. induction n as [|n IH]; intros c k Hk; cbn [csum]; [lia|]. rewrite Nat2Z.inj_succ in Hk.
  destruct (Z.eqb_spec c k) as [->|NE].
  - rewrite (csum_ext f (fun j => if j =? k then 0 else f j) n (k + 1)) by (intros j Hj; destruct (Z.eqb_spec j k); [lia| reflexivity]). lia.
  - rewrite (IH (c + 1) k) by lia. lia.
Qed.

Lemma pusage_ext : forall a b,
  (forall c, 1 <= c < 32 -> rg_mapped_user (get_region a c) = rg_mapped_user (get_region b c) /\ rg_mapped_free_array (get_region a c) = rg_mapped_free_array (get_region b c)) ->
  pusage a = pusage b.
Proof.
  intros a b H. unfold pusage. apply csum_ext. intros k Hk. change (1 + Z.of_nat 31) with 32 in Hk.
  unfold reg_usage. destruct (H k Hk) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Lemma pusage_grow : forall a b c,
  1 <= c < 32 ->
  (forall c', 1 <= c' < 32 -> c' <> c -> rg_mapped_user (get_region b c') = rg_mapped_user (get_region a c') /\ rg_mapped_free_array (get_region b c') = rg_mapped_free_array (get_region a c')) ->
  rg_mapped_user (get_region a c) mod 262144 = 0 -> rg_mapped_free_array (get_region a c) mod 262144 = 0 ->
  (rg_mapped_user (get_region b c) - rg_mapped_user (get_region a c)) mod 262144 = 0 ->
  (rg_mapped_free_array (get_region b c) - rg_mapped_free_array (get_region a c)) mod 262144 = 0 ->
  rg_mapped_user (get_region a c) <= rg_mapped_user (get_region b c) -> rg_mapped_free_array (get_region a c) <= rg_mapped_free_array (get_region b c) ->
  pusage b = pusage a + (rg_mapped_user (get_region b c) - rg_mapped_user (get_region a c)) + (rg_mapped_free_array (get_region b c) - rg_mapped_free_array (get_region a c))
             + 40960 * ((rg_mapped_user (get_region b c) - rg_mapped_user (get_region a c)) / 262144 + (rg_mapped_free_array (get_region b c) - rg_mapped_free_array (get_region a c)) / 262144).
Proof.
  intros a b c Hc OTH M1 M2 D1 D2 L1 L2. unfold pusage.
  rewrite (csum_split (reg_usage b) 31 1 c) by (change (1 + Z.of_nat 31) with 32; lia).
  rewrite (csum_split (reg_usage a) 31 1 c) by (change (1 + Z.of_nat 31) with 32; lia).
  rewrite (csum_ext (fun j => if j =? c then 0 else reg_usage b j) (fun j => if j =? c then 0 else reg_usage a j) 31 1).
  2:{ intros k Hk. change (1 + Z.of_nat 31) with 32 in Hk. destruct (Z.eqb_spec k c) as [->|NE]; [reflexivity|]. unfold reg_usage. destruct (OTH k Hk NE) as [E1 E2]. rewrite E1, E2. reflexivity. }
  unfold reg_usage. set (mb := rg_mapped_user (get_region b c)) in *. set (ma := rg_mapped_user (get_region a c)) in *.
  set (fb := rg_mapped_free_array (get_region b c)) in *. set (fa := rg_mapped_free_array (get_region a c)) in *.
  assert (E1 : mb / 262144 = ma / 262144 + (mb - ma) / 262144) by (Z.div_mod_to_equations; nia).
  assert (E2 : fb / 262144 = fa / 262144 + (fb - fa) / 262144) by (Z.div_mod_to_equations; nia).
  lia.
Qed.

Lemma pusage_init : forall rb sb pa env ts, pusage (init_state rb sb pa env ts) = 0.
Proof. intros. reflexivity. Qed.

Lemma pusage_regions : forall a b, as_regions a = as_regions b -> pusage a = pusage b.
Proof. intros a b E. apply pusage_ext. intros c Hc. unfold get_region. rewrite E. split; reflexivity. Qed.
