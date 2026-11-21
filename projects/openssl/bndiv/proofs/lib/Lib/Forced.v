(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (Linux's placement linux_place_b replaces the free-range search, so the mmap refusability tests take the hint, after libreac/fuzz_ctrl's placement file; the mmap grant and reserve witnesses take the place_declined_b premise). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Mmap.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* 08b1429: [mmap_spec]'s anonymous grant arms choose exactly Linux's address ([Mmap.linux_place],
   decided by [Checks.Placement.linux_place_b]), not any free range below [alloc_top].  So a grant
   exists iff Linux places the request (and, for a backed mapping, the budget admits it): a free
   range the two search windows miss is no grant.  The refusability tests below therefore take
   the mmap hint and ask [linux_place_b], not whether some free range exists.  (Ported from
   libreac/fuzz_ctrl Reusable/Z/Placement.v.) *)
Definition vm_place_available (h : VmMaps) (thp : bool) (hint : word) (nZ : Z) : bool :=
  match Placement.linux_place_b h thp hint nZ with Some _ => true | None => false end.

Lemma linux_place_is_available : forall h thp hint nZ a,
  Placement.linux_place_is h thp hint nZ a = true -> vm_place_available h thp hint nZ = true.
Proof.
  intros h thp hint nZ a H. unfold Placement.linux_place_is in H. unfold vm_place_available.
  destruct (Placement.linux_place_b h thp hint nZ); [reflexivity | discriminate].
Qed.

(* Linux's address as a word, computed. *)
Definition vm_place_pick (h : VmMaps) (thp : bool) (hint : word) (nZ : Z) : word :=
  match Placement.linux_place_b h thp hint nZ with Some p => Z_to_bv 64 p | None => Z_to_bv 64 0 end.

Lemma vm_place_pick_ok : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_place_available h thp hint nZ = true ->
  Placement.linux_place_is h thp hint nZ (vm_place_pick h thp hint nZ) = true.
Proof.
  intros h thp hint nZ Hn Hnal H. unfold vm_place_available in H. unfold vm_place_pick.
  destruct (Placement.linux_place_b h thp hint nZ) as [p|] eqn:Hp; [|discriminate].
  pose proof (proj1 (proj1 (Placement.linux_place_b_spec h thp hint nZ Hn Hnal) p) Hp) as Hpl.
  destruct (Placement.linux_place_admissible h thp hint nZ p Hn Hnal Hpl) as (_ & Hpos & Htop & _).
  pose proof (alloc_top_room h) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  unfold Placement.linux_place_is. rewrite Hp. apply Z.eqb_eq.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  unfold bv_modulus. clear Hnal. lia.
Qed.

Lemma vm_place_available_grant : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  vm_place_available h thp hint nZ = true ->
  exists a : word, Placement.linux_place_is h thp hint nZ a = true.
Proof.
  intros h thp hint nZ Hn Hnal H. exists (vm_place_pick h thp hint nZ).
  exact (vm_place_pick_ok h thp hint nZ Hn Hnal H).
Qed.

(* A free page-aligned range in Linux's upper window [task_unmapped_base, alloc_top]
   (task_unmapped_base = 0x2aaaaab000 = 183251939328) makes Linux place the request, whatever
   the hint: [Placement.linux_place_exists] with its second disjunct, as
   VCommon/Ax/AxModelRel.MR_place_exists does. *)
Lemma vm_place_available_of_gap : forall h thp hint nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (g mod page_size = 0)%Z -> (183251939328 <= g)%Z -> (g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  vm_place_available h thp hint nZ = true.
Proof.
  intros h thp hint nZ g Hn Hnal Hg Hlo Hhi Hfree.
  destruct (Placement.linux_place_exists h thp hint nZ Hn Hnal) as [a Ha].
  { exists g. right. exact (conj Hg (conj Hlo (conj Hhi Hfree))). }
  destruct (Placement.linux_place_admissible h thp hint nZ a Hn Hnal Ha) as (_ & Hpos & Htop & _).
  pose proof (alloc_top_room h) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. clear Hnal Hg. lia. }
  apply (linux_place_is_available h thp hint nZ (Z_to_bv 64 a)).
  apply (proj2 (Placement.linux_place_is_iff h thp hint nZ (Z_to_bv 64 a) Hn Hnal)).
  rewrite Ua. exact Ha.
Qed.

(* [comment removed for export] *)
Definition mmap_grant_refusable (flags hint : word) (m : Model) (nZ : Z) : bool :=
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
  mmap_grant_refusable (Z_to_bv 64 flags) (Z_to_bv 64 addr) mo nZ = false ->
  (* LPS 727298f3: a PRODUCER of a [CheckOk], so the premise is needed -- the model
     answers [CheckUnmodeled] for a declined hint whatever the effect is.  The hint here is
     [Z_to_bv 64 addr] and nothing above constrains it, so the premise is carried to the
     caller; a NULL-hint caller closes it with [place_declined_b_null]. *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ = false ->
  exists eff' m', check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk m' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff') = false.
Proof.
  intros addr len prot flags mo nZ Hanon Hlen Hmod Hnr Hdecl.
  destruct (Checks.Sys.Mm.Mmap.mmap_grant_len_ok _ Hlen) as [Hn0 Hnal]. fold nZ in Hn0, Hnal.
  unfold mmap_grant_refusable in Hnr. apply orb_false_elim in Hnr as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  destruct (vm_place_available_grant _ _ _ _ Hn0 Hnal Hg) as (a & Hpl). fold nZ in Hpl.
  destruct (Placement.linux_place_is_admissible _ _ _ _ _ Hn0 Hnal Hpl) as (_ & _ & Htop & _).
  assert (HnZ : 0 <= nZ) by (apply Z.lt_le_incl; exact Hn0).
  assert (Hne : errno_ret_in mmap_errnos a = false) by (apply (not_errno_below_top _ a nZ (m_vmmaps mo)); [reflexivity|exact HnZ|exact Htop]).
  eexists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), _. split; [|exact Hne].
  unfold check_mmap, check_mmap_fixed_overflow. change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. rewrite Hanon, Hlen, Hmod. cbn [negb].
  rewrite Hne. cbv zeta. fold nZ.
  (* after the [fold]: [Hdecl] is stated over the folded [nZ] *)
  rewrite Hdecl.
  rewrite Hpl, Hb, listNN_eqb_refl.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_reserve_witness : forall addr len prot flags mo,
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable (Z_to_bv 64 addr) mo nZ = false ->
  (* LPS 727298f3: the noaccess arm carries the same decline; a producer, so the same premise. *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr) nZ = false ->
  exists eff' m', check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk m' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff') = false.
Proof.
  intros addr len prot flags mo nZ Hanon Hlen Hmod Hna Hnr Hdecl.
  destruct (Checks.Sys.Mm.Mmap.mmap_grant_len_ok _ Hlen) as [Hn0 Hnal]. fold nZ in Hn0, Hnal.
  unfold mmap_reserve_refusable in Hnr. apply negb_false_iff in Hnr.
  destruct (vm_place_available_grant _ _ _ _ Hn0 Hnal Hnr) as (a & Hpl). fold nZ in Hpl.
  destruct (Placement.linux_place_is_admissible _ _ _ _ _ Hn0 Hnal Hpl) as (_ & _ & Htop & _).
  assert (HnZ : 0 <= nZ) by (apply Z.lt_le_incl; exact Hn0).
  assert (Hne : errno_ret_in mmap_errnos a = false) by (apply (not_errno_below_top _ a nZ (m_vmmaps mo)); [reflexivity|exact HnZ|exact Htop]).
  eexists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), _. split; [|exact Hne].
  unfold check_mmap, check_mmap_fixed_overflow. change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. rewrite Hanon, Hlen, Hmod, Hna. cbn [negb].
  rewrite Hne. cbv zeta. fold nZ.
  rewrite Hdecl.
  rewrite Hpl, listNN_eqb_refl.
  reflexivity.
Qed.

Lemma nstep_mmap_grant_noerr : forall addr len prot flags mo eff mo' evs,
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_grant_refusable (Z_to_bv 64 flags) (Z_to_bv 64 addr) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
    (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs Hanon Hlen Hmod Hnr Hdecl H.
  destruct (mmap_grant_witness addr len prot flags mo Hanon Hlen Hmod Hnr Hdecl) as (eff' & m' & Hchk & Hne).
  exact (nstep_mmap_noerr_of_chk _ _ _ _ _ _ _ _ _ _ _ Hchk Hne H).
Qed.

Lemma nstep_mmap_reserve_noerr : forall addr len prot flags mo eff mo' evs,
  mmap_anon_b (Z_to_bv 64 flags) = true -> w_is0 (Z_to_bv 64 len) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable (Z_to_bv 64 addr) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
    (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs Hanon Hlen Hmod Hna Hnr Hdecl H.
  destruct (mmap_reserve_witness addr len prot flags mo Hanon Hlen Hmod Hna Hnr Hdecl) as (eff' & m' & Hchk & Hne).
  exact (nstep_mmap_noerr_of_chk _ _ _ _ _ _ _ _ _ _ _ Hchk Hne H).
Qed.
