(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mmap_reserve_not_refusable and mmap_grant_not_refusable take the hint and Linux's placement of the request (linux_place_is) in place of a free page-aligned range below alloc_top, proved by linux_place_is_available; imports Checks.Placement in place of ALib.MmapComplete). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import EdDefs.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition alloc_top_min : Z := 0x7fff7f800000.
Lemma alloc_top_min_eq : alloc_top_min = sp_window_lo - stack_max_size.
Proof. reflexivity. Qed.
Lemma alloc_top_ge_min : forall h, sp_window_lo <= bv_unsigned (vm_init_sp h) -> alloc_top_min <= alloc_top h.
Proof. intros h H. unfold alloc_top, alloc_top_min, stack_max_size, sp_window_lo in *. lia. Qed.
Lemma alloc_top_lt_2_64 : forall h, alloc_top h < 2 ^ 64.
Proof. intros h. pose proof (alloc_top_lt h). unfold two_pow_64 in *. lia. Qed.

(** At 08b1429 a grant exists exactly when Linux places the request
    ([EdDefs.vm_place_available]); the checker's [linux_place_is] at the
    returned address is that evidence. *)
Corollary mmap_reserve_not_refusable : forall hint m nZ (a : word),
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ a = true ->
  mmap_reserve_refusable hint m nZ = false.
Proof.
  intros hint m nZ a Hpl. unfold mmap_reserve_refusable.
  rewrite (linux_place_is_available _ _ _ _ _ Hpl). reflexivity.
Qed.

Corollary mmap_grant_not_refusable : forall flags hint m nZ (a : word),
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ a = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags hint m nZ = false.
Proof.
  intros flags hint m nZ a Hpl Hbud. unfold mmap_grant_refusable.
  rewrite (linux_place_is_available _ _ _ _ _ Hpl), Hbud. reflexivity.
Qed.

Lemma mmap_fixed_fresh_not_refusable : forall flags m nZ,
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_fixed_fresh_refusable flags m nZ = false.
Proof. intros flags m nZ H. unfold mmap_fixed_fresh_refusable. rewrite H. reflexivity. Qed.

Lemma mmap_fixed_commit_not_refusable : forall flags m addr n,
  mmap_fixed_rw_budget_ok flags m addr n = true -> mmap_fixed_commit_refusable flags m addr n = false.
Proof. intros flags m addr n H. unfold mmap_fixed_commit_refusable. rewrite H. reflexivity. Qed.

Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.

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
