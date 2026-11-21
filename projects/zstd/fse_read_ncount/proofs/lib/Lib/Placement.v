(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (Linux's placement: mmap_place_found reads linux_place_b at the hint, and mmap_grant_refusable_at and mmap_reserve_refusable_at let a fresh mapping be refused only when that placement fails or, for a grant, the backing check fails; place_found_of_is, place_found_witness and two refusable_at_false_intro lemmas added; requires Checks.Placement). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
(* LPS 727298f3: Linux's placement, by qualified name only. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
Import ListNotations.
Open Scope bv_scope.

Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

Definition vm_find_base (h : VmMaps) (nZ : Z) : option word :=
  List.find (vm_base_ok h nZ) (vm_base_candidates h).

Definition vm_gap_available (h : VmMaps) (nZ : Z) : bool :=
  match vm_find_base h nZ with Some _ => true | None => false end.

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_find_base in H.
  apply List.find_some in H as [_ H]. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ H. unfold vm_gap_available in H.
  destruct (vm_find_base h nZ) as [a|]; [now exists a | discriminate].
Qed.

(* [comment removed for export] *)
Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

(* [comment removed for export] *)
Definition mmap_destructive_errnos : list Z := [].

(* [comment removed for export] *)
Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).
(* LPS 727298f3: a fresh grant takes the one address Linux places the request at
   ([Checks.Placement.linux_place_b], read at the hint), so a refusal is open exactly when that
   placement has no answer or, read-write, when the backing budget fails. *)
Definition mmap_place_found (m : Model) (addr : word) (nZ : Z) : bool :=
  match LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_b
          (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ with
  | Some _ => true
  | None => false
  end.
Definition mmap_grant_refusable_at (flags : word) (m : Model) (addr : word) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ && mmap_place_found m addr nZ).
Definition mmap_reserve_refusable_at (m : Model) (addr : word) (nZ : Z) : bool :=
  negb (mmap_place_found m addr nZ).
Lemma place_found_of_is : forall m addr nZ r,
  LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is
    (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ r = true ->
  mmap_place_found m addr nZ = true.
Proof.
  intros m addr nZ r H.
  unfold LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is in H. unfold mmap_place_found.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_b
              (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ); [reflexivity|discriminate H].
Qed.
Lemma place_found_witness : forall m addr nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  mmap_place_found m addr nZ = true ->
  exists a : word,
    LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is
      (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a = true
    /\ (bv_unsigned a mod page_size = 0)%Z.
Proof.
  intros m addr nZ Hpos Hal Hf. unfold mmap_place_found in Hf.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_b
              (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ) as [z|] eqn:Hb; [|discriminate Hf].
  pose proof (proj1 (proj1 (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_b_spec
                              (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ Hpos Hal) z) Hb) as Hpl.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_admissible
              _ _ _ _ _ Hpos Hal Hpl) as (Zal & Zpos & Ztop & _).
  pose proof (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.alloc_top_lt_two_pow_64 (m_vmmaps m)) as Hat.
  assert (Hz : bv_unsigned (Z_to_bv 64 z) = z) by (apply bv_unsigned_Z_to_bv_u64; lia).
  exists (Z_to_bv 64 z). split.
  - unfold LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is. rewrite Hb, Hz. apply Z.eqb_refl.
  - rewrite Hz. exact Zal.
Qed.
Lemma grant_refusable_at_false_intro : forall flags m addr nZ,
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_place_found m addr nZ = true ->
  mmap_grant_refusable_at flags m addr nZ = false.
Proof. intros flags m addr nZ Hb Hpf. unfold mmap_grant_refusable_at. rewrite Hb, Hpf. reflexivity. Qed.
Lemma reserve_refusable_at_false_intro : forall m addr nZ,
  mmap_place_found m addr nZ = true -> mmap_reserve_refusable_at m addr nZ = false.
Proof. intros m addr nZ Hpf. unfold mmap_reserve_refusable_at. rewrite Hpf. reflexivity. Qed.

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).
