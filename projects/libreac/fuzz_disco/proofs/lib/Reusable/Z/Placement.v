(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: libreac/fuzz_boxreg's repair of this file, with this unit's module paths. *)
(* Placement and refusal predicates for anonymous mmap and mprotect, as proof-library definitions.

   These are pure functions of the model.  [vm_find_base] searches the candidate bases (one page,
   and the page-rounded end of every reserved or mapped interval) for a free, page-aligned range
   below [alloc_top]; [Lib/MmapComplete.v] proves the search complete.  The [*_refusable] tests say
   when no grant can exist: the backing budget fails, or no free range exists.  The proofs use
   them to exhibit the grant that makes a refusal spurious under [Lib/Cfg.ACFG], and to identify
   the refusals that are forced. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
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

(* The errnos an arm admits: all of them when the refusal is forced, none otherwise. *)
Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

(* A failed MAP_FIXED that has already torn down the old mapping is never admitted. *)
Definition mmap_destructive_errnos : list Z := [].

Definition vm_place_available (h : VmMaps) (thp : bool) (hint : word) (nZ : Z) : bool :=
  match linux_place_b h thp hint nZ with Some _ => true | None => false end.

Lemma linux_place_is_available : forall h thp hint nZ a,
  linux_place_is h thp hint nZ a = true -> vm_place_available h thp hint nZ = true.
Proof.
  intros h thp hint nZ a H. unfold linux_place_is in H. unfold vm_place_available.
  destruct (linux_place_b h thp hint nZ); [reflexivity | discriminate].
Qed.
Definition vm_place_pick (h : VmMaps) (thp : bool) (hint : word) (nZ : Z) : word :=
  match linux_place_b h thp hint nZ with Some p => Z_to_bv 64 p | None => Z_to_bv 64 0 end.

Lemma vm_place_pick_ok : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_place_available h thp hint nZ = true ->
  linux_place_is h thp hint nZ (vm_place_pick h thp hint nZ) = true.
Proof.
  intros h thp hint nZ Hn Hnal H. unfold vm_place_available in H. unfold vm_place_pick.
  destruct (linux_place_b h thp hint nZ) as [p|] eqn:Hp; [|discriminate].
  pose proof (proj1 (proj1 (linux_place_b_spec h thp hint nZ Hn Hnal) p) Hp) as Hpl.
  destruct (linux_place_admissible h thp hint nZ p Hn Hnal Hpl) as (_ & Hpos & Htop & _).
  pose proof (alloc_top_room h) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  unfold linux_place_is. rewrite Hp. apply Z.eqb_eq.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.
Lemma vm_place_available_grant : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_place_available h thp hint nZ = true ->
  exists a : word, linux_place_is h thp hint nZ a = true.
Proof.
  intros h thp hint nZ Hn Hnal H. exists (vm_place_pick h thp hint nZ).
  exact (vm_place_pick_ok h thp hint nZ Hn Hnal H).
Qed.
(* A FREE RANGE IN LINUX'S BOTTOM-UP WINDOW IS ENOUGH FOR AN ADDRESS, and it is all
   a producer can offer: since 08b1429 the checker asks whether the address IS the
   one [Sys/Mm/Mmap.linux_place] gives, so a proof that merely CONSTRUCTS a free
   range no longer names a grantable address.  What the construction still buys is
   that the window is not exhausted, and [Checks.Placement.linux_place_exists]
   turns exactly that into the rule's own answer.  The address is then Linux's and
   is reached through [vm_place_pick], never through the candidate the caller
   built. *)
Lemma linux_place_is_of_fit : forall h thp hint nZ (g : Z),
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) nZ g ->
  exists a : word, linux_place_is h thp hint nZ a = true.
Proof.
  intros h thp hint nZ g Hn Hnal Hfit.
  apply (vm_place_available_grant h thp hint nZ Hn Hnal).
  unfold vm_place_available.
  destruct (linux_place_b h thp hint nZ) as [p|] eqn:Hb; [reflexivity|].
  exfalso.
  destruct (linux_place_exists h thp hint nZ Hn Hnal
              ltac:(exists g; right; exact Hfit)) as (q & Hq).
  pose proof (proj2 (proj1 (linux_place_b_spec h thp hint nZ Hn Hnal) q) Hq) as HS.
  rewrite Hb in HS. discriminate.
Qed.
(* When no grant can exist, per mmap arm. *)
Definition mmap_grant_refusable (flags hint : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_place_available (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ).

Definition mmap_reserve_refusable (hint : word) (m : Model) (nZ : Z) : bool :=
  negb (vm_place_available (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ).

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
