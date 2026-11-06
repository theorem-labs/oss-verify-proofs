(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv LimMremap.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma leb_mono : forall x L L', (L <= L')%Z -> negb (x <=? L)%Z = false -> negb (x <=? L')%Z = false.
Proof. intros x L L' Hle H. apply negb_false_iff in H. apply Z.leb_le in H. apply negb_false_iff. apply Z.leb_le. lia. Qed.

Lemma brk_gate_mono : forall L L' m req, (L <= L')%Z ->
  brk_budget_refused_b (m_relim L m) req = false -> brk_budget_refused_b (m_relim L' m) req = false.
Proof.
  intros L L' m req Hle H. unfold brk_budget_refused_b, brk_budget_ok in *. cbv zeta in *. autorewrite with relim in *.
  apply andb_false_iff in H. apply andb_false_iff. destruct H as [H | H]; [left; exact H | right; exact (leb_mono _ L L' Hle H)].
Qed.

Lemma mremap_gate_mono : forall L L' m old old_size new_size flags, (L <= L')%Z ->
  mremap_budget_refused_b old old_size new_size flags (m_relim L m) = false ->
  mremap_budget_refused_b old old_size new_size flags (m_relim L' m) = false.
Proof.
  intros L L' m old old_size new_size flags Hle H. unfold mremap_budget_refused_b in *. cbv zeta in *.
  rewrite source_b_relim, uniform_relim, final_budget_relim, move_budget_relim in *.
  repeat match goal with |- (if ?c then _ else _) = false => destruct c; [first [reflexivity | exact H] |] end.
  apply negb_false_iff in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2.
  apply negb_false_iff. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma noreserve_backed_mono : forall L L' flags m nZ, (L <= L')%Z ->
  negb (mmap_noreserve_backed_ok flags (m_relim L m) nZ) = false -> negb (mmap_noreserve_backed_ok flags (m_relim L' m) nZ) = false.
Proof.
  intros L L' flags m nZ Hle H. unfold mmap_noreserve_backed_ok in *. destruct (mmap_noreserve_b flags); [reflexivity |].
  autorewrite with relim in *. exact (leb_mono _ L L' Hle H).
Qed.
Lemma within_limit_relim : forall L (F : Model -> Model) m,
  (forall K, m_vmmaps (F (m_relim K m)) = vm_relim K (m_vmmaps (F m))) ->
  (forall K, m_vm_lazy (F (m_relim K m)) = m_vm_lazy (F m)) ->
  (forall K, m_vm_materialized (F (m_relim K m)) = m_vm_materialized (F m)) ->
  vm_backing_within_limit (F (m_relim L m)) = (vm_backing_used (F m) <=? L)%Z.
Proof.
  intros L F m H1 H2 H3. unfold vm_backing_within_limit, vm_backing_used, vm_backed_maps. rewrite H1, H2, H3. reflexivity.
Qed.
Lemma fixed_rw_mono : forall L L' flags m addr n, (L <= L')%Z ->
  negb (mmap_fixed_rw_budget_ok flags (m_relim L m) addr n) = false -> negb (mmap_fixed_rw_budget_ok flags (m_relim L' m) addr n) = false.
Proof.
  intros L L' flags m addr n Hle H. unfold mmap_fixed_rw_budget_ok in *.
  rewrite (within_limit_relim L (fun x => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps x) addr n) x)) m) in H;
    [| intros K; unfold with_mmap_replacement, with_mmap_backing; destruct (mmap_noreserve_b flags); reflexivity ..].
  rewrite (within_limit_relim L' (fun x => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps x) addr n) x)) m);
    [| intros K; unfold with_mmap_replacement, with_mmap_backing; destruct (mmap_noreserve_b flags); reflexivity ..].
  exact (leb_mono _ L L' Hle H).
Qed.
Lemma fixed_rw_span_mono : forall L L' flags m addr n, (L <= L')%Z ->
  negb (mmap_fixed_rw_span_budget_ok flags (m_relim L m) addr n) = false -> negb (mmap_fixed_rw_span_budget_ok flags (m_relim L' m) addr n) = false.
Proof.
  intros L L' flags m addr n Hle H. unfold mmap_fixed_rw_span_budget_ok in *.
  rewrite (within_limit_relim L (fun x => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps x) addr n) x)) m) in H;
    [| intros K; unfold with_mmap_replacement, with_mmap_backing; destruct (mmap_noreserve_b flags); reflexivity ..].
  rewrite (within_limit_relim L' (fun x => with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps x) addr n) x)) m);
    [| intros K; unfold with_mmap_replacement, with_mmap_backing; destruct (mmap_noreserve_b flags); reflexivity ..].
  exact (leb_mono _ L L' Hle H).
Qed.

Lemma mmap_gate_mono : forall L L' m addr len prot flags fd off, (L <= L')%Z ->
  mmap_budget_refused_b addr len prot flags fd off (m_relim L m) = false ->
  mmap_budget_refused_b addr len prot flags fd off (m_relim L' m) = false.
Proof.
  intros L L' m addr len prot flags fd off Hle H. unfold mmap_budget_refused_b in *. cbv zeta in *.
  change (m_vmmaps (m_relim L m)) with (vm_relim L (m_vmmaps m)) in H. change (m_vmmaps (m_relim L' m)) with (vm_relim L' (m_vmmaps m)).
  change (alloc_top (vm_relim L (m_vmmaps m))) with (alloc_top (m_vmmaps m)) in H. change (alloc_top (vm_relim L' (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  autorewrite with relim in *.
  repeat match goal with |- (if ?c then _ else _) = false => destruct c; try reflexivity end.
  all: cbv iota in H.
  all: lazymatch goal with
       | |- negb (mmap_noreserve_backed_ok _ _ _) = false => exact (noreserve_backed_mono L L' _ _ _ Hle H)
       | |- negb (mmap_fixed_rw_budget_ok _ _ _ _) = false => exact (fixed_rw_mono L L' _ _ _ _ Hle H)
       | |- negb (mmap_fixed_rw_span_budget_ok _ _ _ _) = false => exact (fixed_rw_span_mono L L' _ _ _ _ Hle H)
       end.
Qed.

Lemma mprotect_gate_mono : forall L L' m addr len prot, (L <= L')%Z ->
  mprotect_budget_refused_b addr len prot (m_relim L m) = false ->
  mprotect_budget_refused_b addr len prot (m_relim L' m) = false.
Proof.
  intros L L' m addr len prot Hle H. unfold mprotect_budget_refused_b in *. cbv zeta in *.
  autorewrite with relim in *.
  repeat match goal with |- (if ?c then _ else _) = false => destruct c; try reflexivity end.
  unfold mprotect_budget_ok in *.
  rewrite (within_limit_relim L (fun x => mprotect_model_next x addr _) m) in H by (intros K; reflexivity).
  rewrite (within_limit_relim L' (fun x => mprotect_model_next x addr _) m) by (intros K; reflexivity).
  exact (leb_mono _ L L' Hle H).
Qed.

Theorem gate_mono : forall L L' i m, (L <= L')%Z ->
  alloc_budget_refused_b i (m_relim L m) = false -> alloc_budget_refused_b i (m_relim L' m) = false.
Proof.
  intros L L' i m Hle H. unfold alloc_budget_refused_b in *. cbv zeta in *.
  destruct (bv_unsigned (in_sysno i) =? 214)%Z; [exact (brk_gate_mono L L' m _ Hle H) |].
  destruct (bv_unsigned (in_sysno i) =? 216)%Z; [exact (mremap_gate_mono L L' m _ _ _ _ Hle H) |].
  destruct (bv_unsigned (in_sysno i) =? 222)%Z; [exact (mmap_gate_mono L L' m _ _ _ _ _ _ Hle H) |].
  destruct (bv_unsigned (in_sysno i) =? 226)%Z; [exact (mprotect_gate_mono L L' m _ _ _ Hle H) |].
  reflexivity.
Qed.
