(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mmap placement by the model's linux_place: the grant and reserve refusal criteria read vm_place_available at the call's hint and the kernel's THP flag instead of any free gap; the gap search floored at task_unmapped_base; vm_place_available_iff, vm_place_available_of_avail and ed_nZ_pos_aligned). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

Definition mmap_destructive_errnos : list Z := [].

Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
&& (task_unmapped_base <=? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

Definition vm_base_candidates (h : VmMaps) : list word :=
Z_to_bv 64 task_unmapped_base
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

Definition vm_find_base (h : VmMaps) (nZ : Z) : option word :=
  List.find (vm_base_ok h nZ) (vm_base_candidates h).

Definition vm_gap_available (h : VmMaps) (nZ : Z) : bool :=
  match vm_find_base h nZ with Some _ => true | None => false end.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
/\ (task_unmapped_base <= bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Halign Hpos].
apply Z.eqb_eq in Halign. apply Z.leb_le in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
/\ (task_unmapped_base <= bv_unsigned a)%Z
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

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. destruct (iv_overlap lo n b s) eqn:Ho.
  - exists b, s. split; [now left|exact Ho].
  - cbn in H. destruct (IH lo n H) as (a & sz & Hin & Hov).
    exists a, sz. split; [now right|exact Hov].
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  pose proof (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  pose proof (bv_unsigned_in_range 64 a) as [_ Ha]. unfold bv_modulus in Ha.
destruct (Z.eq_dec (bv_unsigned a) task_unmapped_base) as [Heq|Hne].
  { left. left. rewrite <- Heq. apply Z_to_bv_bv_unsigned. }
assert (Hge : (task_unmapped_base + page_size <= bv_unsigned a)%Z).
{ unfold page_size, task_unmapped_base in *.
    pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { subst a'. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus, page_size, task_unmapped_base in *. lia. }
  destruct (vm_base_ok h nZ a') eqn:Hok'.
  { right. exists a'. split; [exact Ua'|exact Hok']. }
  left. unfold vm_base_ok in Hok'. rewrite Ua' in Hok'.
  assert (H1 : ((bv_unsigned a - page_size) mod page_size =? 0)%Z = true)
    by (apply Z.eqb_eq; rewrite Zminus_mod, Hal, Z_mod_same_full; reflexivity).
assert (H2 : (task_unmapped_base <=? bv_unsigned a - page_size)%Z = true)
by (apply Z.leb_le; unfold page_size in *; lia).
  assert (H3 : (bv_unsigned a - page_size + nZ <=? alloc_top h)%Z = true)
    by (apply Z.leb_le; unfold page_size in *; lia).
  rewrite H1, H2, H3 in Hok'. cbn [andb] in Hok'.
  destruct (region_free_false_In _ _ _ Hok') as (lo & sz & Hin & Hov).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hnov.
  unfold iv_overlap in Hov, Hnov. rewrite Ua' in Hov.
  apply andb_true_iff in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  apply andb_false_iff in Hnov as [N|N]; apply Z.ltb_ge in N;
    [|unfold page_size in *; lia].
  right. apply in_map_iff. exists (lo, sz). split; [|exact Hin].
  cbn [fst snd].
  replace (page_round_up_Z (bv_unsigned lo + bv_unsigned sz))
    with (bv_unsigned a); [apply Z_to_bv_bv_unsigned|].
  unfold page_round_up_Z, page_size in *.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hq.
  rewrite Hal, Z.add_0_r in Hq.
  rewrite <- (Z.div_unique_pos (bv_unsigned lo + bv_unsigned sz + 4096 - 1)
                4096 (bv_unsigned a / 4096)
                (bv_unsigned lo + bv_unsigned sz + 4096 - 1
                 - 4096 * (bv_unsigned a / 4096))); lia.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros h nZ k. induction k as [|k IH]; intros a Hk Hok.
- pose proof (vm_base_ok_sound h nZ a Hok) as (_ & Hpos & _). cbn in Hk.
unfold task_unmapped_base in Hpos. lia.
  - destruct (vm_base_ok_step h nZ a Hok) as [Hin | (a' & Ua' & Hok')].
    + exists a. split; assumption.
    + apply (IH a'); [|exact Hok'].
      rewrite Ua'. rewrite Nat2Z.inj_succ in Hk. unfold page_size in *. lia.
Qed.

Lemma vm_find_base_complete : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  pose proof (bv_unsigned_in_range 64 a) as [Ha _].
  destruct (vm_find_base_complete_aux h nZ (Z.to_nat (bv_unsigned a)) a)
    as (c & Hin & Hc); [unfold page_size; lia|exact Hok|].
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) eqn:Hf;
    [reflexivity|exfalso].
  pose proof (List.find_none _ _ Hf c Hin) as Hn. cbn beta in Hn.
  rewrite Hc in Hn. discriminate Hn.
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
/\ (task_unmapped_base <= bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - intros H. apply vm_gap_available_find in H as [a Ha].
    exists a. exact (vm_find_base_sound h nZ a Ha).
  - intros (a & Hal & Hpos & Htop & Hfree).
    apply (vm_find_base_complete h nZ a). unfold vm_base_ok.
rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.leb_le _ _) Hpos),
      (proj2 (Z.leb_le _ _) Htop), Hfree. reflexivity.
Qed.

(* LPS 08b1429: [mmap_spec]'s grant arms pick Linux's one address
   ([Mmap.linux_place]); a grant outcome exists exactly when the placement
   rule has an answer, so the refusal criteria read the placement, not any
   free gap. *)
Definition vm_place_available (h : VmMaps) (thp : bool) (hint : word) (nZ : Z) : bool :=
  match linux_place_b h thp hint nZ with Some _ => true | None => false end.

Lemma vm_place_available_iff : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_place_available h thp hint nZ = true <->
  exists a : word, linux_place h thp hint nZ (bv_unsigned a).
Proof.
  intros h thp hint nZ Hn Hal.
  destruct (linux_place_b_spec h thp hint nZ Hn Hal) as [Hs Hnone].
  unfold vm_place_available. destruct (linux_place_b h thp hint nZ) as [z|] eqn:Hb.
  - split; [intros _|reflexivity].
    pose proof (proj1 (Hs z) eq_refl) as Hz.
    destruct (linux_place_admissible h thp hint nZ z Hn Hal Hz) as (_ & Hpos & Htop & _).
    pose proof (alloc_top_lt_two_pow_64 h) as Hat.
    exists (Z_to_bv 64 z). rewrite bv_unsigned_Z_to_bv_u64; [exact Hz|].
    unfold page_size in *. lia.
  - split; [discriminate|]. intros (a & Ha). exfalso. exact (proj1 Hnone eq_refl _ Ha).
Qed.

Lemma vm_place_available_of_gap : forall h thp hint nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) nZ g ->
  vm_place_available h thp hint nZ = true.
Proof.
  intros h thp hint nZ g Hn Hnal Hg.
  destruct (linux_place_exists h thp hint nZ Hn Hnal (ex_intro _ g (or_intror Hg))) as [a Ha].
  destruct (linux_place_b_spec h thp hint nZ Hn Hnal) as [_ Hnone].
  unfold vm_place_available. destruct (linux_place_b h thp hint nZ) eqn:E; [reflexivity|].
  exfalso. exact (proj1 Hnone eq_refl a Ha).
Qed.

(* LPS 727298f3: a gap [vm_gap_available] finds sits in the bottom-up window
   [task_unmapped_base, alloc_top) (the floor of [vm_base_ok], as in
   projects/bzip2/bzip2_compress_target/proofs/lib/Common/AllocRefusal.v), so Linux's
   search has an answer there ([Placement.linux_place_exists]). *)
Lemma vm_place_available_of_avail : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_gap_available h nZ = true -> vm_place_available h thp hint nZ = true.
Proof.
  intros h thp hint nZ Hn Hnal H.
  apply vm_gap_available_iff in H as (a & Hal & Hlo & Htop & Hfree).
  apply (vm_place_available_of_gap h thp hint nZ (bv_unsigned a) Hn Hnal).
  unfold gap_fits. rewrite Z_to_bv_bv_unsigned. repeat split; assumption.
Qed.

Lemma ed_nZ_pos_aligned : forall len : word, w_is0 len = false ->
  (0 < page_round_up_Z (bv_unsigned len))%Z /\ (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z.
Proof.
  (* [bv_eqb_neq] is not a name this file can see: the model declares it in
     Common/PropExec.v and in the other direction.  [Sys/Syscall.w_is0_false_pos]
     is the model's own lemma for exactly this step, and [Specs] exports it. *)
  intros len H. pose proof (w_is0_false_pos len H) as Hu.
  pose proof (bv_unsigned_in_range 64 len) as [H0 _].
  unfold page_round_up_Z, page_size. split.
  - apply Z.mul_pos_pos; [|lia]. apply Z.div_str_pos. lia.
  - apply Z_mod_mult.
Qed.

Definition mmap_grant_refusable (hint flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_place_available (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ).

Definition mmap_reserve_refusable (hint : word) (m : Model) (nZ : Z) : bool :=
  negb (vm_place_available (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z)
    : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).

Definition w_nilb {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Lemma w_nilb_true {A} (l : list A) : w_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.
