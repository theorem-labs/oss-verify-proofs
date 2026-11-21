(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mmap_reserve_not_refusable over Linux placement, vm_place_available, with the hint; the first-fit gap lemmas it no longer uses removed). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require Import AllocEd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma alloc_top_lt : forall h, alloc_top h < 2 ^ 64.
Proof. intros h. pose proof (alloc_top_room h). unfold two_pow_64, stack_max_size in *. lia. Qed.

Lemma mmap_reserve_not_refusable : forall hint m nZ,
  vm_place_available (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ = true ->
  mmap_reserve_refusable hint m nZ = false.
Proof. intros hint m nZ Hg. unfold mmap_reserve_refusable. rewrite Hg. reflexivity. Qed.

Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.


(* [comment removed for export] *)
Lemma mmap_fixed_fresh_not_refusable : forall flags m nZ,
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_fixed_fresh_refusable flags m nZ = false.
Proof. intros flags m nZ H. unfold mmap_fixed_fresh_refusable. rewrite H. reflexivity. Qed.






