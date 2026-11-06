(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Placement and budget tests for anonymous mmap / mprotect, and the filtered step relation of the
   alloc_forced_only reading ([Run.alloc_only_cfg false]), stated over the release model.

   The tree's proofs speak of "the request is refusable" ([mmap_grant_refusable] and its siblings): the
   model's budget or free address range cannot satisfy it.  On the release model a refusal (ENOMEM) is an
   outcome of every such request, and the reading's filter [Run.spurious_refusal_cfg] removes it exactly
   when a non-refusal outcome exists at the same input and model.  The lemmas at the end connect the two:
   an ENOMEM outcome that survives the filter has no grant beside it. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Import ListNotations.
Open Scope bv_scope.

(* ---------------------------------------------------------------------------------------------------
   Placement search: is there a page-aligned, nonzero base below [alloc_top] whose range of [nZ] bytes
   meets no reservation and no mapping?  [vm_gap_available_iff] states it without the search.
   --------------------------------------------------------------------------------------------------- *)

Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

(* The page above 0 and the first page above each reservation or mapping: the lowest acceptable base,
   if any, is one of these. *)
Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
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

(* An acceptable base is a candidate, or the page below it is acceptable too. *)
Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  pose proof (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  pose proof (bv_unsigned_in_range 64 a) as [_ Ha]. unfold bv_modulus in Ha.
  destruct (Z.eq_dec (bv_unsigned a) page_size) as [Heq|Hne].
  { left. left. rewrite <- Heq. apply Z_to_bv_bv_unsigned. }
  assert (Hge : (2 * page_size <= bv_unsigned a)%Z).
  { unfold page_size in *.
    pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { subst a'. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus, page_size in *. lia. }
  destruct (vm_base_ok h nZ a') eqn:Hok'.
  { right. exists a'. split; [exact Ua'|exact Hok']. }
  left. unfold vm_base_ok in Hok'. rewrite Ua' in Hok'.
  assert (H1 : ((bv_unsigned a - page_size) mod page_size =? 0)%Z = true)
    by (apply Z.eqb_eq; rewrite Zminus_mod, Hal, Z_mod_same_full; reflexivity).
  assert (H2 : (0 <? bv_unsigned a - page_size)%Z = true)
    by (apply Z.ltb_lt; unfold page_size in *; lia).
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
  - pose proof (vm_base_ok_sound h nZ a Hok) as (_ & Hpos & _). cbn in Hk. lia.
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
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - intros H. apply vm_gap_available_find in H as [a Ha].
    exists a. exact (vm_find_base_sound h nZ a Ha).
  - intros (a & Hal & Hpos & Htop & Hfree).
    apply (vm_find_base_complete h nZ a). unfold vm_base_ok.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
      (proj2 (Z.leb_le _ _) Htop), Hfree. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------
   Refusable requests, one test per mmap arm the tree uses, and mprotect's.
   --------------------------------------------------------------------------------------------------- *)

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

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).

(* The errno lists the release specs and checkers answer from, under the names the tree's statements
   use: every arm answers from [mmap_errnos] / [mprotect_errnos], refusable or not. *)
Definition mmap_errnos_when (forced : bool) : list Z := mmap_errnos.
Definition mprotect_errnos_when (forced : bool) : list Z := mprotect_errnos.
Definition mmap_destructive_errnos : list Z := mmap_errnos.

Definition w_nilb {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Lemma w_nilb_true {A} (l : list A) : w_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.

(* ---------------------------------------------------------------------------------------------------
   The filtered step relation of the reading, with the tree's arities.
   --------------------------------------------------------------------------------------------------- *)

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

Definition sstep_a (segs : list Segment) : config -> list event -> step_to -> Prop :=
  sstep_cfg segs ACFG.
Definition star_a (segs : list Segment) : config -> list event -> config -> Prop :=
  star_cfg segs ACFG.
Definition obs_trace_a (segs : list Segment) : config -> list event -> Prop :=
  obs_trace_cfg segs ACFG.
Definition reaches_error_a (segs : list Segment) : config -> Prop :=
  reaches_error_cfg segs ACFG.
Definition reaches_unmodeled_a (segs : list Segment) : config -> Prop :=
  reaches_unmodeled_cfg segs ACFG.

(* A syscall outcome the filtered relation can consume.  The filter's premise is required only of outcomes
   that leave the halting state as it was: a step that halts the process ([sstep_cfg_exit],
   [sstep_cfg_killed]) consumes its outcome without it. *)
Definition syscall_spec_ns (i : SyscallInput) (m : Model) (R : outcome SyscallEffect) : Prop :=
  syscall_spec i m R
  /\ forall eff m' evs, R = Ok eff m' evs -> m_halted m' = m_halted m ->
       ~ spurious_refusal_cfg ACFG i m eff.

Lemma syscall_spec_ns_spec : forall i m R, syscall_spec_ns i m R -> syscall_spec i m R.
Proof. intros i m R [H _]. exact H. Qed.

(* ---------------------------------------------------------------------------------------------------
   When the filter removes an outcome.
   --------------------------------------------------------------------------------------------------- *)

Lemma ns_family_on : forall i m eff,
  injected_family_off ACFG i = false -> ~ spurious_refusal_cfg ACFG i m eff.
Proof. intros. apply spurious_refusal_family_on. assumption. Qed.

(* Only the allocation family is off in this reading, so a syscall outside [alloc_mark_sysnos] never
   loses an outcome. *)
Lemma ns_not_alloc : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hout. apply ns_family_on.
  unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:Ha; [|reflexivity].
  destruct (ia_family a) eqn:Hf; try reflexivity.
  exfalso. apply Hout. exact (alloc_family_dispatched _ a Ha Hf).
Qed.

Lemma ns_not_refusal : forall i m eff,
  refusal_b i m (eff_ret eff) = false -> ~ spurious_refusal_cfg ACFG i m eff.
Proof. intros. apply spurious_refusal_not_refusal. assumption. Qed.

Lemma not_alloc_sysno : forall i n,
  bv_unsigned (in_sysno i) = n -> existsb (Z.eqb n) alloc_mark_sysnos = false ->
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i n Hn Hb Hin. rewrite Hn in Hin.
  assert (E : existsb (Z.eqb n) alloc_mark_sysnos = true)
    by (apply existsb_exists; exists n; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

(* "Not a spurious refusal" for a syscall outside the allocation family, from the hypothesis that pins
   its number (or a disjunction of such hypotheses). *)
Ltac ns_sysno :=
  first
  [ match goal with H : bv_unsigned (in_sysno ?i) = ?n |- ~ In (bv_unsigned (in_sysno ?i)) _ =>
      exact (not_alloc_sysno i n H eq_refl) end
  | match goal with H : bv_unsigned (in_sysno _) = _ \/ _ |- _ =>
      destruct H as [H|H]; ns_sysno end
  | cbn [in_sysno sys_input];
    match goal with H : bv_unsigned ?x = ?n |- ~ In (bv_unsigned ?x) _ =>
      rewrite H; cbn; intuition discriminate end ].

Ltac ns_auto := apply ns_not_alloc; ns_sysno.

Lemma ns_all_same_ret : forall i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> eff_ret eff' = eff_ret eff) ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hall (_ & Hb & (eff' & m' & evs' & Hs & Hnr)).
  rewrite (Hall _ _ _ Hs) in Hnr. congruence.
Qed.

Lemma ns_brk : forall i m eff, bv_unsigned (in_sysno i) = 214%Z ->
  brk_refusal_b m (in_arg i 0) (eff_ret eff) = false -> ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno H. apply ns_not_refusal. unfold refusal_b. cbv zeta. rewrite Hno.
  cbn [Z.eqb Pos.eqb]. exact H.
Qed.

Lemma ns_brk_query : forall i m eff, bv_unsigned (in_sysno i) = 214%Z -> in_arg i 0 = Z_to_bv 64 0 ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof. intros i m eff Hno H0. apply ns_brk; [exact Hno|]. unfold brk_refusal_b. rewrite H0. reflexivity. Qed.

Lemma ns_brk_moved : forall i m eff, bv_unsigned (in_sysno i) = 214%Z ->
  eff_ret eff <> vm_brk (m_vmmaps m) -> ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno Hne. apply ns_brk; [exact Hno|]. unfold brk_refusal_b. cbv zeta.
  destruct (bv_eqb (eff_ret eff) (vm_brk (m_vmmaps m))) eqn:E;
    [apply bv_eqb_eq in E; contradiction | rewrite !andb_false_r; reflexivity].
Qed.

Coercion syscall_spec_ns_spec : syscall_spec_ns >-> syscall_spec.

Lemma grant_not_refusable_of : forall flags m nZ a,
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a Hal Hpos Htop Hfree Hb.
  unfold mmap_grant_refusable. rewrite Hb. cbn [negb orb].
  apply negb_false_iff. apply vm_gap_available_iff. exists a. repeat split; assumption.
Qed.

Lemma reserve_not_refusable_of : forall m nZ a,
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a Hal Hpos Htop Hfree.
  unfold mmap_reserve_refusable. apply negb_false_iff. apply vm_gap_available_iff. exists a.
  repeat split; assumption.
Qed.

Lemma ret_zero_not_enomem : Z_to_bv 64 0 <> errno_ret ENOMEM.
Proof. intro E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. Qed.

Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r Hno. unfold refusal_b. rewrite Hno. cbn [Z.eqb Pos.eqb].
  change (injected_arm 222) with (Some (mkInjectedArm 222 FamAlloc mmap_errnos)).
  cbn [ia_errnos ret_in_errnos mmap_errnos existsb]. rewrite orb_false_r. reflexivity.
Qed.

Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r Hno. unfold refusal_b. rewrite Hno. cbn [Z.eqb Pos.eqb].
  change (injected_arm 226) with (Some (mkInjectedArm 226 FamAlloc mprotect_errnos)).
  cbn [ia_errnos ret_in_errnos mprotect_errnos existsb]. rewrite orb_false_r. reflexivity.
Qed.

Lemma family_off_mmap : forall i,
  bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off. rewrite Hno. reflexivity. Qed.

Lemma family_off_mprotect : forall i,
  bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off. rewrite Hno. reflexivity. Qed.

(* An ENOMEM answer to mmap that survives the filter has no non-ENOMEM answer beside it. *)
Lemma ns_enomem_mmap : forall i m eff eff' m' evs',
  ~ spurious_refusal_cfg ACFG i m eff ->
  bv_unsigned (in_sysno i) = 222%Z ->
  eff_ret eff = errno_ret ENOMEM ->
  syscall_spec i m (Ok eff' m' evs') ->
  eff_ret eff' = errno_ret ENOMEM.
Proof.
  intros i m eff eff' m' evs' Hns Hno Hr Hs.
  destruct (bv_eqb (eff_ret eff') (errno_ret ENOMEM)) eqn:E.
  - apply bv_eqb_eq in E. exact E.
  - exfalso. apply Hns. split; [exact (family_off_mmap i Hno)|]. split.
    + rewrite refusal_b_mmap by exact Hno. rewrite Hr. apply bv_eqb_eq; reflexivity.
    + exists eff', m', evs'. split; [exact Hs|]. rewrite refusal_b_mmap by exact Hno. exact E.
Qed.

Lemma ns_enomem_mprotect : forall i m eff eff' m' evs',
  ~ spurious_refusal_cfg ACFG i m eff ->
  bv_unsigned (in_sysno i) = 226%Z ->
  eff_ret eff = errno_ret ENOMEM ->
  syscall_spec i m (Ok eff' m' evs') ->
  eff_ret eff' = errno_ret ENOMEM.
Proof.
  intros i m eff eff' m' evs' Hns Hno Hr Hs.
  destruct (bv_eqb (eff_ret eff') (errno_ret ENOMEM)) eqn:E.
  - apply bv_eqb_eq in E. exact E.
  - exfalso. apply Hns. split; [exact (family_off_mprotect i Hno)|]. split.
    + rewrite refusal_b_mprotect by exact Hno. rewrite Hr. apply bv_eqb_eq; reflexivity.
    + exists eff', m', evs'. split; [exact Hs|]. rewrite refusal_b_mprotect by exact Hno. exact E.
Qed.

(* Conversely an mmap / mprotect answer is never filtered when every answer at that input is ENOMEM
   (a forced refusal), nor when it is not ENOMEM. *)
Lemma ns_forced_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> eff_ret eff' = errno_ret ENOMEM) ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno Hall (_ & _ & (eff' & m' & evs' & Hs & Hnr)).
  rewrite refusal_b_mmap in Hnr by exact Hno. rewrite (Hall _ _ _ Hs) in Hnr.
  rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in Hnr. discriminate.
Qed.

Lemma ns_forced_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> eff_ret eff' = errno_ret ENOMEM) ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno Hall (_ & _ & (eff' & m' & evs' & Hs & Hnr)).
  rewrite refusal_b_mprotect in Hnr by exact Hno. rewrite (Hall _ _ _ Hs) in Hnr.
  rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in Hnr. discriminate.
Qed.

Lemma ns_nonenomem_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z -> eff_ret eff <> errno_ret ENOMEM ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno Hne. apply ns_not_refusal. rewrite refusal_b_mmap by exact Hno.
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.

Lemma ns_nonenomem_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z -> eff_ret eff <> errno_ret ENOMEM ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hno Hne. apply ns_not_refusal. rewrite refusal_b_mprotect by exact Hno.
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.

(* Close a hypothesis [check ... = c] whose left side is a chain of [if]/[match] that ends in results
   other than [c]. *)
Ltac check_shape_discriminate H :=
  cbv beta iota zeta in H;
  first
  [ discriminate H
  | lazymatch type of H with
    | (if ?c then _ else _) = _ => destruct c; check_shape_discriminate H
    | (match ?x with _ => _ end) = _ => destruct x; check_shape_discriminate H
    end ].
