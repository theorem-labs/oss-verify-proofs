(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

(* [comment removed for export] *)
Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z)
    : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

(* [comment removed for export] *)
Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma not_errno_below_top : forall es (a : word) nZ h,
  errnos_ok es = true -> 0 <= nZ -> bv_unsigned a + nZ <= alloc_top h -> errno_ret_in es a = false.
Proof.
  intros es a nZ h Hes HnZ Htop. destruct (errno_ret_in es a) eqn:E; [|reflexivity]. exfalso.
  apply errno_ret_in_true in E as (e & Hin & ->).
  destruct (errnos_ok_range es e Hes Hin) as [He1 He2].
  pose proof (alloc_top_room h) as Hroom. unfold stack_max_size in Hroom.
  rewrite errno_ret_unsigned in Htop by lia. lia.
Qed.

(* [comment removed for export] *)

Lemma nstep_mmap_noerr_of_chk : forall addr len prot flags mo eff mo' evs eff' m' evs',
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk m' evs' ->
  errno_ret_in mmap_errnos (eff_ret eff') = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs eff' m' evs' Hchk Hnr H.
  apply (nstep_mm_nonrefusal_of_witness (NMmap addr len prot flags) (mmap_in addr len prot flags)
           mo eff mo' evs eff' m' evs' eq_refl (mmap_family_off _ _ _ _)); [|exact Hnr|exact H].
  apply check_syscall_ok_iff. unfold mmap_in. dispatch_pure check_syscall_mmap. exact Hchk.
Qed.

Lemma nstep_mprotect_noerr_of_chk : forall addr len prot mo eff mo' evs eff' m' evs',
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff' mo = CheckOk m' evs' ->
  errno_ret_in mprotect_errnos (eff_ret eff') = false ->
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  errno_ret_in mprotect_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot mo eff mo' evs eff' m' evs' Hchk Hnr H.
  apply (nstep_mm_nonrefusal_of_witness (NMprotect addr len prot) (mprotect_in addr len prot)
           mo eff mo' evs eff' m' evs' eq_refl (mprotect_family_off _ _ _)); [|exact Hnr|exact H].
  apply check_syscall_ok_iff. unfold mprotect_in. dispatch_pure check_syscall_mprotect. exact Hchk.
Qed.

(* [comment removed for export] *)
Lemma nstep_brk_norefusal_of_chk : forall req mo eff mo' evs eff' m' evs',
  check_brk (Z_to_bv 64 req) eff' mo = CheckOk m' evs' ->
  brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff') = false ->
  nstep (NBrk req) mo eff mo' evs ->
  brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff) = false.
Proof.
  intros req mo eff mo' evs eff' m' evs' Hchk Hnr H.
  apply (nstep_mm_nonrefusal_of_witness (NBrk req) (brk_in req)
           mo eff mo' evs eff' m' evs' eq_refl (brk_family_off _)); [|exact Hnr|exact H].
  apply check_syscall_ok_iff. unfold brk_in. dispatch_pure check_syscall_brk. exact Hchk.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_grant_witness : forall addr len prot flags mo,
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = false ->
  exists eff' m', check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk m' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff') = false.
Proof.
  intros addr len prot flags mo nZ Hanon Hlen Hmod Hnr.
  unfold mmap_grant_refusable in Hnr. apply orb_false_elim in Hnr as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  apply vm_gap_available_iff in Hg as (a & Hal & Hpos & Htop & Hfree).
  assert (HnZ : 0 <= nZ) by (apply page_round_up_Z_nonneg; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 len)); lia).
  assert (Hne : errno_ret_in mmap_errnos a = false) by (apply (not_errno_below_top _ a nZ (m_vmmaps mo)); [reflexivity|exact HnZ|exact Htop]).
  eexists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), _. split; [|exact Hne].
  unfold check_mmap. change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. rewrite Hanon, Hlen, Hmod. cbn [negb].
  rewrite Hne. cbv zeta. fold nZ.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htop), Hfree, Hb, listNN_eqb_refl.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_reserve_witness : forall addr len prot flags mo,
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable mo nZ = false ->
  exists eff' m', check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk m' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff') = false.
Proof.
  intros addr len prot flags mo nZ Hanon Hlen Hmod Hna Hnr.
  unfold mmap_reserve_refusable in Hnr. apply negb_false_iff in Hnr.
  apply vm_gap_available_iff in Hnr as (a & Hal & Hpos & Htop & Hfree).
  assert (HnZ : 0 <= nZ) by (apply page_round_up_Z_nonneg; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 len)); lia).
  assert (Hne : errno_ret_in mmap_errnos a = false) by (apply (not_errno_below_top _ a nZ (m_vmmaps mo)); [reflexivity|exact HnZ|exact Htop]).
  eexists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), _. split; [|exact Hne].
  unfold check_mmap. change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. rewrite Hanon, Hlen, Hmod, Hna. cbn [negb].
  rewrite Hne. cbv zeta. fold nZ.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htop), Hfree, listNN_eqb_refl.
  reflexivity.
Qed.

Lemma nstep_mmap_grant_noerr : forall addr len prot flags mo eff mo' evs,
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_grant_refusable (Z_to_bv 64 flags) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs Hanon Hlen Hmod Hnr H.
  destruct (mmap_grant_witness addr len prot flags mo Hanon Hlen Hmod Hnr) as (eff' & m' & Hchk & Hne).
  exact (nstep_mmap_noerr_of_chk _ _ _ _ _ _ _ _ _ _ _ Hchk Hne H).
Qed.

Lemma nstep_mmap_reserve_noerr : forall addr len prot flags mo eff mo' evs,
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs Hanon Hlen Hmod Hna Hnr H.
  destruct (mmap_reserve_witness addr len prot flags mo Hanon Hlen Hmod Hna Hnr) as (eff' & m' & Hchk & Hne).
  exact (nstep_mmap_noerr_of_chk _ _ _ _ _ _ _ _ _ _ _ Hchk Hne H).
Qed.
