(** * FO.P04.Mmap — the placement decision of lps patch 04, as agent-side definitions

    The patch-04 proof trees read a handful of names that the dropped patch added to the trusted
    [Sys/Mm/Mmap.v]: a first-fit search over finitely many candidate bases ([vm_find_base]), its
    decision ([vm_gap_available]), and the conditions under which each allocation arm was forced to
    fail ([mmap_*_refusable]).  None of them is part of the specification any more; they are copied
    here verbatim (definitions and the soundness proofs, from the patch text) over the unpatched
    names they were written against, so the trees keep reading them under the qualified names
    [Mmap.vm_find_base] etc.  What they decide is unchanged: [vm_find_base_sound] says a found base
    passes the fresh-grant [choose] guard of the unpatched [mmap_spec], which is how the port shows a
    grant exists and therefore that a refusal there is avoidable. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** The errno list an arm offered under the patch: the environment failures when the model's own
    state forced a failure, nothing otherwise. *)
Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

(** The errnos of the range-destroyed resolution of a MAP_FIXED over live memory (empty under the
    patch). *)
Definition mmap_destructive_errnos : list Z := [].

(** The fresh-grant guard's own booleans (without the budget, which is not about the base). *)
Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

(** The finitely many bases worth testing: the lowest nonzero page and the page-rounded end of every
    ledger entry. *)
Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

(** First-fit over the candidates, and its decision. *)
Definition vm_find_base (h : VmMaps) (nZ : Z) : option word :=
  List.find (vm_base_ok h nZ) (vm_base_candidates h).

Definition vm_gap_available (h : VmMaps) (nZ : Z) : bool :=
  match vm_find_base h nZ with Some _ => true | None => false end.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.

(** SOUND: a found base satisfies the fresh-grant [choose] guard, conjunct for conjunct. *)
Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_find_base in H.
  apply List.find_some in H as [_ H]. exact (vm_base_ok_sound h nZ a H).
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ H. unfold vm_gap_available in H.
  destruct (vm_find_base h nZ) as [a|]; [now exists a | discriminate].
Qed.

(** When each arm was forced to fail under the patch: the negation of what that arm's success needs
    from the model's own state. *)
Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).
