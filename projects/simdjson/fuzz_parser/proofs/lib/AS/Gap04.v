(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MmapComplete.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition alloc_top_min : Z := 0x7fff7f800000.
Lemma alloc_top_min_eq : alloc_top_min = sp_window_lo - stack_max_size.
Proof. reflexivity. Qed.
Lemma alloc_top_ge_min : forall h, sp_window_lo <= bv_unsigned (vm_init_sp h) -> alloc_top_min <= alloc_top h.
Proof. intros h H. unfold alloc_top, alloc_top_min, stack_max_size, sp_window_lo in *. lia. Qed.
Lemma alloc_top_lt_2_64 : forall h, alloc_top h < 2 ^ 64.
Proof. intros h. pose proof (alloc_top_lt h). unfold two_pow_64 in *. lia. Qed.

(* [comment removed for export] *)
Corollary mmap_reserve_not_refusable : forall m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a HnZ Hal Hpos Hce Hfree. unfold mmap_reserve_refusable.
  rewrite (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Hce Hfree). reflexivity.
Qed.

Corollary mmap_grant_not_refusable : forall flags m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a HnZ Hal Hpos Hce Hfree Hbud. unfold mmap_grant_refusable.
  rewrite (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Hce Hfree), Hbud. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_fresh_not_refusable : forall flags m nZ,
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_fixed_fresh_refusable flags m nZ = false.
Proof. intros flags m nZ H. unfold mmap_fixed_fresh_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_commit_not_refusable : forall flags m addr n,
  mmap_fixed_rw_budget_ok flags m addr n = true -> mmap_fixed_commit_refusable flags m addr n = false.
Proof. intros flags m addr n H. unfold mmap_fixed_commit_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mprotect_errnos_when_false : mprotect_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof. reflexivity. Qed.

Lemma errno_from_nil_in : forall e, ~ In e (mmap_errnos_when false).
Proof. intros e H. exact H. Qed.

Lemma mmap_errnos_when_incl : forall b e, In e (mmap_errnos_when b) -> In e mmap_errnos.
Proof. intros [|] e H; [exact H | destruct H]. Qed.

Lemma mprotect_errnos_when_incl : forall b e, In e (mprotect_errnos_when b) -> In e mprotect_errnos.
Proof. intros [|] e H; [exact H | destruct H]. Qed.
