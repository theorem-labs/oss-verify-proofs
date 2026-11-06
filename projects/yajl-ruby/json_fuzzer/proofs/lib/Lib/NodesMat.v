(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mat_shape (m m' : Model) : Prop := m_vm_materialized m = [] -> m_vm_materialized m' = [].

Lemma mat_shape_refl : forall m, mat_shape m m. Proof. intros m H; exact H. Qed.
Lemma mat_shape_trans : forall m1 m2 m3, mat_shape m1 m2 -> mat_shape m2 m3 -> mat_shape m1 m3.
Proof. intros m1 m2 m3 A B H. exact (B (A H)). Qed.

Lemma m_vm_materialized_with_fds : forall v m, m_vm_materialized (with_fds v m) = m_vm_materialized m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_tid : forall v m, m_vm_materialized (with_tid v m) = m_vm_materialized m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_halted : forall v m, m_vm_materialized (with_halted v m) = m_vm_materialized m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall v m, m_vm_materialized (with_vmmaps v m) = m_vm_materialized m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_materialized_with_vm_backing : forall l p m, m_vm_materialized (with_vm_backing l p m) = p.
Proof. intros l p m; destruct m; reflexivity. Qed.
Lemma m_vm_materialized_init : forall reserved brk mbase sp lim inp, m_vm_materialized (init_model reserved brk mbase sp lim inp) = [].  (* [comment removed for export] *)
Proof. intros. reflexivity. Qed.

Lemma mat_shape_with_vmmaps : forall h m, mat_shape m (with_vmmaps h m).
Proof. intros h m H. rewrite m_vm_materialized_with_vmmaps. exact H. Qed.

Lemma mat_shape_vm_forget_range : forall lo hi m, mat_shape m (vm_forget_range lo hi m).
Proof. intros lo hi m H. unfold vm_forget_range. rewrite m_vm_materialized_with_vm_backing, H. reflexivity. Qed.

Lemma mat_shape_forget_vm_ranges : forall ranges m, mat_shape m (forget_vm_ranges ranges m).
Proof.
  induction ranges as [|[a n] ranges IH]; intros m; cbn [forget_vm_ranges]; [apply mat_shape_refl|].
  eapply mat_shape_trans; [apply mat_shape_vm_forget_range| apply IH].
Qed.

Lemma mat_shape_with_brk_next : forall m req r, mat_shape m (with_brk_next m req r).
Proof.
  intros. unfold with_brk_next. cbv zeta. eapply mat_shape_trans; [apply mat_shape_with_vmmaps| apply mat_shape_forget_vm_ranges].
Qed.

Lemma mat_shape_vm_add_lazy : forall a n m, mat_shape m (vm_add_lazy a n m).
Proof. intros a n m H. unfold vm_add_lazy. rewrite m_vm_materialized_with_vm_backing. exact H. Qed.

Lemma mat_shape_with_mmap_backing : forall flags a n m m0,
  mat_shape m0 m -> mat_shape m0 (with_mmap_backing flags a n m).
Proof.
  intros flags a n m m0 Hs. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|exact Hs].
  eapply mat_shape_trans; [exact Hs | apply mat_shape_vm_add_lazy].
Qed.

Lemma mat_shape_with_mmap_destroyed : forall a n h m, mat_shape m (with_mmap_destroyed a n h m).
Proof.
  intros. unfold with_mmap_destroyed. eapply mat_shape_trans; [apply mat_shape_with_vmmaps| apply mat_shape_vm_forget_range].
Qed.

Lemma mat_shape_with_mmap_replacement : forall flags a n h m,
  mat_shape m (with_mmap_replacement flags a n (with_vmmaps h m)).
Proof.
  intros flags a n h m. unfold with_mmap_replacement. apply mat_shape_with_mmap_backing.
  eapply mat_shape_trans; [apply mat_shape_with_vmmaps| apply mat_shape_vm_forget_range].
Qed.

Lemma mat_shape_mprotect_model_next : forall m a n, mat_shape m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply mat_shape_with_vmmaps. Qed.

Lemma mat_shape_vm_resize_backing : forall sl old old_n dst new_n m, mat_shape m (vm_resize_backing sl old old_n dst new_n m).
Proof.
  intros sl old old_n dst new_n m H. unfold vm_resize_backing. cbv zeta.
  rewrite m_vm_materialized_with_vm_backing, H. destruct sl; reflexivity.
Qed.

Lemma mat_shape_mremap_model_next : forall m old old_n dst new_n,
  mat_shape m (mremap_model_next m old old_n dst new_n).
Proof.
  intros. unfold mremap_model_next.
  eapply mat_shape_trans; [apply (mat_shape_with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n))|].
  apply mat_shape_vm_resize_backing.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ =>
              let E := fresh "E" in
              apply check_ret_only_ok_iff in H as (E & ? & ?); first [subst | inversion E; subst; clear E]
          | (match ?x with _ => _ end) = _ => destruct x
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

Ltac mat_done :=
  first [ apply mat_shape_refl | apply mat_shape_with_brk_next
        | apply mat_shape_with_mmap_backing; apply mat_shape_with_vmmaps
        | apply mat_shape_with_mmap_destroyed
        | apply mat_shape_with_mmap_replacement
        | apply mat_shape_mprotect_model_next | apply mat_shape_mremap_model_next ].

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma check_brk_mat : forall req eff m m' evs, check_brk req eff m = CheckOk m' evs -> mat_shape m m'.
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; mat_done. Qed.

Lemma check_mmap_mat : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> mat_shape m m'.
Proof. intros until evs; intros H. unfold check_mmap in H. crush_check H; mat_done. Qed.

Lemma check_munmap_mat : forall addr len eff m m' evs, check_munmap addr len eff m = CheckOk m' evs -> mat_shape m m'.
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; mat_done. Qed.

Lemma check_mprotect_mat : forall addr len prot eff m m' evs, check_mprotect addr len prot eff m = CheckOk m' evs -> mat_shape m m'.
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; mat_done. Qed.

Lemma check_mremap_mat : forall old osz nsz flags eff m m' evs, check_mremap old osz nsz flags eff m = CheckOk m' evs -> mat_shape m m'.
Proof. intros until evs; intros H. unfold check_mremap in H. crush_check H; mat_done. Qed.

(* [comment removed for export] *)
Theorem nstep_mat_shape : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> mat_shape mo mo'.
Proof.
  intros n mo rsp mo' evs H. destruct n.
  - (* [comment removed for export] *) destruct H as [-> _]. apply mat_shape_refl.
  - (* [comment removed for export] *) destruct H as [-> _]. apply mat_shape_refl.
  - (* [comment removed for export] *) cbn [nstep] in H. destruct H as [_ H].
    assert (OR : forall ent, open_result mo ent rsp mo' -> mat_shape mo mo').
    { intros ent [(e & _ & _ & ->) | (_ & _ & ->)]; [apply mat_shape_refl | intros M; rewrite m_vm_materialized_with_fds; exact M]. }
    destruct (path_max <=? length path)%nat; [destruct H as [_ ->]; apply mat_shape_refl|].
    destruct path; [destruct H as [_ ->]; apply mat_shape_refl|].
    destruct (path_is_dirref _); [exact (OR _ H)|].
    destruct (fs_lookup _ _); [exact (OR _ H)| destruct H as [_ ->]; apply mat_shape_refl].
  - (* [comment removed for export] *) cbn [nstep] in H. destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[| p off | p off | p off | p off | | | | |]|]; try contradiction;
      try (destruct H as [_ ->]; apply mat_shape_refl).
    destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->]. intros M; rewrite m_vm_materialized_with_fds; exact M.
  - (* [comment removed for export] *) cbn [nstep] in H. destruct H as (_ & _ & H).
    destruct (fd_lookup _ _); destruct H as [_ ->]; [intros M; rewrite m_vm_materialized_with_fds; exact M | apply mat_shape_refl].
  - (* [comment removed for export] *) destruct H as (_ & _ & ->). apply mat_shape_refl.
  - (* [comment removed for export] *) cbn [nstep] in H. destruct H as (_ & t & _ & H).
    destruct (m_tid mo); destruct H as [_ ->]; [apply mat_shape_refl | intros M; rewrite m_vm_materialized_with_tid; exact M].
  - (* [comment removed for export] *) exfalso. exact H.
  - apply nstep_brk_iff in H. eapply check_brk_mat; exact H.
  - apply nstep_mmap_iff in H. eapply check_mmap_mat; exact H.
  - apply nstep_munmap_iff in H. eapply check_munmap_mat; exact H.
  - apply nstep_mprotect_iff in H. eapply check_mprotect_mat; exact H.
  - apply nstep_mremap_iff in H. eapply check_mremap_mat; exact H.
Qed.

Corollary nstep_mat_nil : forall n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> m_vm_materialized mo = [] -> m_vm_materialized mo' = [].
Proof. intros n mo rsp mo' evs H. exact (nstep_mat_shape _ _ _ _ _ H). Qed.

Lemma nexit_mat_nil : forall n mo code mo',
  nexit n mo code mo' -> m_vm_materialized mo = [] -> m_vm_materialized mo' = [].
Proof.
  intros n mo code mo' H M. destruct n; try (exfalso; exact H).
  destruct H as [_ ->]. rewrite m_vm_materialized_with_halted. exact M.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End RC__2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition vmc_shape (m m' : Model) : Prop :=
  vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m)
  /\ vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m)
  /\ vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m).

Lemma vmc_refl : forall m, vmc_shape m m. Proof. intros m; repeat split; reflexivity. Qed.
Lemma vmc_of_vmmaps : forall m m', m_vmmaps m' = m_vmmaps m -> vmc_shape m m'.
Proof. intros m m' E. unfold vmc_shape. rewrite E. repeat split; reflexivity. Qed.
Lemma vmc_trans : forall m1 m2 m3, vmc_shape m1 m2 -> vmc_shape m2 m3 -> vmc_shape m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold vmc_shape. rewrite B1, B2, B3, B4. auto. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros. unfold vm_forget_range. apply m_vmmaps_with_vm_backing. Qed.
Lemma m_vmmaps_vm_add_lazy : forall a n m, m_vmmaps (vm_add_lazy a n m) = m_vmmaps m.
Proof. intros. unfold vm_add_lazy. apply m_vmmaps_with_vm_backing. Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n m, m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [apply m_vmmaps_vm_add_lazy | reflexivity]. Qed.
Lemma m_vmmaps_with_mmap_replacement : forall flags a n m, m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. apply m_vmmaps_vm_forget_range. Qed.
Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.
Lemma m_vmmaps_mprotect_model_next : forall m a n,
  m_vmmaps (mprotect_model_next m a n) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
    (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. intros. unfold mprotect_model_next. apply m_vmmaps_with_vmmaps. Qed.

End RC__3.
Ltac vmc_done :=
  unfold vmc_shape;
  rewrite ?m_vmmaps_with_brk_next, ?m_vmmaps_with_mmap_destroyed, ?m_vmmaps_with_mmap_replacement,
          ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_vmmaps, ?m_vmmaps_mprotect_model_next,
          ?m_vmmaps_mremap_model_next, ?m_vmmaps_with_fds, ?m_vmmaps_with_tid;
  cbn [vm_reserved vm_limit vm_start_brk vm_mmap_base brk_model_next mremap_maps_next];
  repeat split; reflexivity.

Section RC__4.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma check_brk_vmc : forall req eff m m' evs, check_brk req eff m = CheckOk m' evs -> vmc_shape m m'.
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; vmc_done. Qed.

Lemma check_mmap_vmc : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vmc_shape m m'.
Proof. intros until evs; intros H. unfold check_mmap in H. crush_check H; vmc_done. Qed.

Lemma check_munmap_vmc : forall addr len eff m m' evs, check_munmap addr len eff m = CheckOk m' evs -> vmc_shape m m'.
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; vmc_done. Qed.

Lemma check_mprotect_vmc : forall addr len prot eff m m' evs, check_mprotect addr len prot eff m = CheckOk m' evs -> vmc_shape m m'.
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; vmc_done. Qed.

Lemma check_mremap_vmc : forall old osz nsz flags eff m m' evs, check_mremap old osz nsz flags eff m = CheckOk m' evs -> vmc_shape m m'.
Proof. intros until evs; intros H. unfold check_mremap in H. crush_check H; vmc_done. Qed.

Theorem nstep_vmc_shape : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> vmc_shape mo mo'.
Proof.
  intros n mo rsp mo' evs H. destruct n.
  - destruct H as [-> _]. apply vmc_refl.
  - destruct H as [-> _]. apply vmc_refl.
  - cbn [nstep] in H. destruct H as [_ H].
    assert (OR : forall ent, open_result mo ent rsp mo' -> vmc_shape mo mo').
    { intros ent [(e & _ & _ & ->) | (_ & _ & ->)]; [apply vmc_refl | apply vmc_of_vmmaps; apply m_vmmaps_with_fds]. }
    destruct (path_max <=? length path)%nat; [destruct H as [_ ->]; apply vmc_refl|].
    destruct path; [destruct H as [_ ->]; apply vmc_refl|].
    destruct (path_is_dirref _); [exact (OR _ H)|].
    destruct (fs_lookup _ _); [exact (OR _ H)| destruct H as [_ ->]; apply vmc_refl].
  - cbn [nstep] in H. destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[| p off | p off | p off | p off | | | | |]|]; try contradiction;
      try (destruct H as [_ ->]; apply vmc_refl).
    destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->]. apply vmc_of_vmmaps; apply m_vmmaps_with_fds.
  - cbn [nstep] in H. destruct H as (_ & _ & H).
    destruct (fd_lookup _ _); destruct H as [_ ->]; [apply vmc_of_vmmaps; apply m_vmmaps_with_fds | apply vmc_refl].
  - destruct H as (_ & _ & ->). apply vmc_refl.
  - cbn [nstep] in H. destruct H as (_ & t & _ & H).
    destruct (m_tid mo); destruct H as [_ ->]; [apply vmc_refl | apply vmc_of_vmmaps; apply m_vmmaps_with_tid].
  - exfalso. exact H.
  - apply nstep_brk_iff in H. eapply check_brk_vmc; exact H.
  - apply nstep_mmap_iff in H. eapply check_mmap_vmc; exact H.
  - apply nstep_munmap_iff in H. eapply check_munmap_vmc; exact H.
  - apply nstep_mprotect_iff in H. eapply check_mprotect_vmc; exact H.
  - apply nstep_mremap_iff in H. eapply check_mremap_vmc; exact H.
Qed.

Corollary nstep_vm_consts : forall n mo rsp mo' evs, nstep n mo rsp mo' evs ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) /\ vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)
  /\ vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) /\ vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo).
Proof. intros n mo rsp mo' evs H. exact (nstep_vmc_shape _ _ _ _ _ H). Qed.

Lemma nexit_vm_consts : forall n mo code mo', nexit n mo code mo' -> m_vmmaps mo' = m_vmmaps mo.
Proof.
  intros n mo code mo' H. destruct n; try (exfalso; exact H).
  destruct H as [_ ->]. apply m_vmmaps_with_halted.
Qed.
End RC__4.
