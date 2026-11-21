(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees CompressModel DeflateOverlay RefDeflSafeZ BoundDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition lit_ok (c : Z) : bool := arr_get static_ltree_dl c <=? 9.
Definition len_cost (lc : Z) : Z :=
  arr_get static_ltree_dl (arr_get length_code_a lc + LITERALS + 1) + arr_get extra_lbits_a (arr_get length_code_a lc).
Definition len_ok (lc : Z) : bool := if lc =? 0 then len_cost lc =? 7 else len_cost lc <=? 3 * lc + 4.
Definition dist_cost (d : Z) : Z := arr_get static_dtree_dl (d_code (d - 1)) + arr_get extra_dbits_a (d_code (d - 1)).
Definition dist_ok (d : Z) : bool := (dist_cost d <=? 18) && ((4096 <? d) || (dist_cost d <=? 15)).

Fixpoint allpow (k : nat) (f : Z -> bool) (lo : Z) : bool :=
  match k with
  | O => f lo
  | S k' => allpow k' f lo && allpow k' f (lo + 2 ^ Z.of_nat k')
  end.

Lemma allpow_spec : forall k f lo, allpow k f lo = true -> forall x, lo <= x < lo + 2 ^ Z.of_nat k -> f x = true.
Proof.
  induction k as [|k IH]; intros f lo H x Hx.
  - cbn in H, Hx. replace x with lo by lia. exact H.
  - cbn [allpow] in H. apply andb_prop in H as [H1 H2].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z_lt_le_dec x (lo + 2 ^ Z.of_nat k)); [apply (IH f lo H1); lia | apply (IH f _ H2); lia].
Qed.

Lemma lit_cost_ok : forall c, 0 <= c < 256 -> arr_get static_ltree_dl c <= 9.
Proof.
  intros c Hc. assert (R : allpow 8 lit_ok 0 = true) by (vm_compute; reflexivity).
  pose proof (allpow_spec 8 lit_ok 0 R c ltac:(change (2 ^ Z.of_nat 8) with 256; lia)) as H. unfold lit_ok in H. apply Z.leb_le in H. exact H.
Qed.

Lemma len_cost_ok : forall lc, 0 <= lc < 256 -> (lc = 0 -> len_cost lc = 7) /\ (lc <> 0 -> len_cost lc <= 3 * lc + 4).
Proof.
  intros lc Hc. assert (R : allpow 8 len_ok 0 = true) by (vm_compute; reflexivity).
  pose proof (allpow_spec 8 len_ok 0 R lc ltac:(change (2 ^ Z.of_nat 8) with 256; lia)) as H. unfold len_ok in H.
  destruct (Z.eqb_spec lc 0); [apply Z.eqb_eq in H | apply Z.leb_le in H]; split; intros; try lia.
Qed.

Lemma dist_cost_ok : forall d, 1 <= d <= 32768 -> dist_cost d <= 18 /\ (d <= 4096 -> dist_cost d <= 15).
Proof.
  intros d Hd. assert (R : allpow 15 dist_ok 1 = true) by (vm_compute; reflexivity).
  pose proof (allpow_spec 15 dist_ok 1 R d ltac:(change (2 ^ Z.of_nat 15) with 32768; lia)) as H. unfold dist_ok in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|]. intros Hn.
  apply orb_prop in H2 as [H2|H2]; [apply Z.ltb_lt in H2; lia | apply Z.leb_le in H2; exact H2].
Qed.

Lemma scost_sym : forall s j, sym_okb s j -> near3 s j ->
  scost s j <= 3 * symlen s j + (if sym_isdist s j then 13 else 6).
Proof.
  intros s j [Hlc Hd] HN. unfold scost, dcost, symlen, sym_xl, sym_xd, sym_lcode, sym_dcode.
  unfold near3 in HN. unfold sym_isdist in *.
  destruct (Z.eqb_spec (sym_dist s (3 * j)) 0) as [E|E]; cbn [negb].
  - pose proof (lit_cost_ok (sym_lc s (3 * j)) Hlc). lia.
  - pose proof (len_cost_ok (sym_lc s (3 * j)) Hlc) as [L0 L1]. pose proof (dist_cost_ok (sym_dist s (3 * j)) ltac:(lia)) as [D1 D2].
    unfold len_cost, dist_cost in *.
    destruct (Z.eq_dec (sym_lc s (3 * j)) 0) as [Z0|Z0].
    + specialize (L0 Z0). specialize (D2 (HN eq_refl Z0)). lia.
    + specialize (L1 Z0). lia.
Qed.

Definition nmatch (s : deflate_state) : Z := zsum (fun j => zind (sym_isdist s j)) 0 (Z.to_nat (nsym s)).

Lemma symlen_lb : forall s j, sym_okb s j -> 1 + 2 * zind (sym_isdist s j) <= symlen s j.
Proof. intros s j [Hlc _]. unfold symlen. destruct (sym_isdist s j); cbn [zind]; lia. Qed.

Lemma scost_sum_cov : forall s, 0 <= nsym s ->
  (forall j, 0 <= j < nsym s -> sym_okb s j) -> (forall j, 0 <= j < nsym s -> near3 s j) ->
  zsum (scost s) 0 (Z.to_nat (nsym s)) <= 3 * cov s + 6 * nsym s + 7 * nmatch s
  /\ nsym s + 2 * nmatch s <= cov s /\ 0 <= nmatch s <= nsym s.
Proof.
  intros s N0 OK NR. unfold cov, nmatch.
  assert (G : forall n, (n <= Z.to_nat (nsym s))%nat ->
     zsum (scost s) 0 n <= 3 * zsum (symlen s) 0 n + 6 * Z.of_nat n + 7 * zsum (fun j => zind (sym_isdist s j)) 0 n
     /\ Z.of_nat n + 2 * zsum (fun j => zind (sym_isdist s j)) 0 n <= zsum (symlen s) 0 n
     /\ 0 <= zsum (fun j => zind (sym_isdist s j)) 0 n <= Z.of_nat n).
  { induction n as [|n IH]; intros Hn; [cbn; lia|].
    rewrite !zsum_snoc, Z.add_0_l. destruct (IH ltac:(lia)) as (I1 & I2 & I3).
    pose proof (scost_sym s (Z.of_nat n) (OK (Z.of_nat n) ltac:(lia)) (NR (Z.of_nat n) ltac:(lia))) as C.
    pose proof (symlen_lb s (Z.of_nat n) (OK (Z.of_nat n) ltac:(lia))) as LB.
    destruct (sym_isdist s (Z.of_nat n)); cbn [zind] in *; lia. }
  specialize (G (Z.to_nat (nsym s)) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.
