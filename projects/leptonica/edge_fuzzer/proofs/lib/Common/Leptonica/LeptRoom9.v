(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import LeptArith LeptRoom.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RK_numa : Z := 2.
Definition RB_numa (nalloc : Z) : Z := 2 ^ 17 + (4 * nalloc + 2 ^ 22).
(* [comment removed for export] *)
Definition RB_numagrow (nalloc : Z) : Z := 8 * nalloc + 2 ^ 22.
(* [comment removed for export] *)
Definition grow_cost (k : Z) : Z := 400 * (2 ^ k - 1) + k * 2 ^ 22.
(* [comment removed for export] *)
Definition NFE_GROWS : Z := 9.
Definition RK_nfe : Z := RK_numa + NFE_GROWS.
Definition RB_nfe : Z := RB_numa 50 + grow_cost NFE_GROWS.
(* [comment removed for export] *)
Definition RK_pmes : Z := RK_numa + RK_nfe.
Definition RB_pmes (h : Z) : Z := RB_numa h + RB_nfe.
(* [comment removed for export] *)
Definition RK_edge : Z := RK_deser + RK_pmes.
Definition RB_edge (h : Z) : Z := RB_deser + RB_pmes h.

Lemma RK_edge_val : RK_edge = 18. Proof. reflexivity. Qed.
Lemma grow_cost_step : forall k, 0 <= k -> grow_cost (k + 1) = grow_cost k + RB_numagrow (50 * 2 ^ k).
Proof. intros k Hk. unfold grow_cost, RB_numagrow. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. Qed.
Lemma grow_cost_mono : forall k k', 0 <= k <= k' -> grow_cost k <= grow_cost k'.
Proof.
  intros k k' H. unfold grow_cost. assert (2 ^ k <= 2 ^ k') by (apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma RB_numa_margin : forall nalloc, 0 <= nalloc -> alloc_margin (1 * 32) + alloc_margin (nalloc * 4) <= RB_numa nalloc.
Proof.
  intros n Hn. unfold RB_numa. rewrite (alloc_margin_small (1 * 32)) by lia. pose proof (alloc_margin_le (n * 4)). lia.
Qed.
Lemma RB_numagrow_margin : forall nalloc, 0 <= nalloc -> alloc_margin (8 * nalloc) <= RB_numagrow nalloc.
Proof. intros n Hn. unfold RB_numagrow. pose proof (alloc_margin_le (8 * n)). lia. Qed.
Lemma RB_edge_le : forall h, 1 <= h <= 20000 -> 0 <= RB_edge h <= 2 ^ 29.
Proof.
  intros h Hh. unfold RB_edge, RB_pmes, RB_nfe, RB_numa, grow_cost, NFE_GROWS, RB_deser.
  change (2 ^ 9) with 512. change (2 ^ 17) with 131072. change (2 ^ 22) with 4194304. change (2 ^ 28) with 268435456. change (2 ^ 29) with 536870912. lia.
Qed.

Lemma RK_pmes_val : RK_pmes = 13. Proof. reflexivity. Qed.
Lemma RK_nfe_val : RK_nfe = 11. Proof. reflexivity. Qed.
Lemma RB_nfe_val : RB_nfe = 42278712. Proof. reflexivity. Qed.
Lemma RB_numa_nonneg : forall n, 0 <= n -> 0 <= RB_numa n.
Proof. intros n Hn. unfold RB_numa. change (2 ^ 17) with 131072. change (2 ^ 22) with 4194304. lia. Qed.
Lemma RB_pmes_split : forall h, RB_pmes h = RB_numa h + RB_nfe. Proof. reflexivity. Qed.
Lemma RB_pmes_nonneg : forall h, 0 <= h -> 0 <= RB_pmes h.
Proof. intros h Hh. rewrite RB_pmes_split, RB_nfe_val. pose proof (RB_numa_nonneg h Hh). lia. Qed.
