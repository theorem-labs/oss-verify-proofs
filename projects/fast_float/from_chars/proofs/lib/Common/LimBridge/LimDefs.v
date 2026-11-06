(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition vm_relim (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h)
               (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition m_relim (L : Z) (m : Model) : Model := with_vmmaps (vm_relim L (m_vmmaps m)) m.
Definition o_relim {A} (L : Z) (o : outcome A) : outcome A :=
  match o with Ok x m evs => Ok x (m_relim L m) evs | Unmodeled => Unmodeled end.
Definition c_relim (L : Z) (c : config) : config := mkCfg (cfg_ms c) (m_relim L (cfg_model c)).

Definition m_limit (m : Model) : Z := vm_limit (m_vmmaps m).

Lemma m_relim_idem : forall L L' m, m_relim L (m_relim L' m) = m_relim L m.
Proof. reflexivity. Qed.
Lemma m_relim_eta : forall m, m_relim (m_limit m) m = m.
Proof. intros [fd [[r mp na sb b l mb sp] lz mt] io fs pr lm tm]. reflexivity. Qed.
Lemma m_relim_same : forall L m, m_limit m = L -> m_relim L m = m.
Proof. intros L m <-. apply m_relim_eta. Qed.
Lemma m_limit_relim : forall L m, m_limit (m_relim L m) = L.
Proof. reflexivity. Qed.
Lemma c_relim_idem : forall L L' c, c_relim L (c_relim L' c) = c_relim L c.
Proof. reflexivity. Qed.
Lemma c_relim_same : forall L c, m_limit (cfg_model c) = L -> c_relim L c = c.
Proof. intros L [ms m] H. unfold c_relim. cbn [cfg_ms cfg_model] in *. rewrite (m_relim_same L m H). reflexivity. Qed.

(* [comment removed for export] *)
Section Acc.
Variable L : Z. Variable m : Model.
Let R := m_relim L m.
Lemma relim_m_fd : m_fd R = m_fd m. Proof. reflexivity. Qed.
Lemma relim_m_io : m_io R = m_io m. Proof. reflexivity. Qed.
Lemma relim_m_fsys : m_fsys R = m_fsys m. Proof. reflexivity. Qed.
Lemma relim_m_proc : m_proc R = m_proc m. Proof. reflexivity. Qed.
Lemma relim_m_lim : m_lim R = m_lim m. Proof. reflexivity. Qed.
Lemma relim_m_time : m_time R = m_time m. Proof. reflexivity. Qed.
Lemma relim_m_fds : m_fds R = m_fds m. Proof. reflexivity. Qed.
Lemma relim_m_pipes : m_pipes R = m_pipes m. Proof. reflexivity. Qed.
Lemma relim_m_vm_lazy : m_vm_lazy R = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma relim_m_vm_materialized : m_vm_materialized R = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma relim_m_stdin : m_stdin R = m_stdin m. Proof. reflexivity. Qed.
Lemma relim_m_urandom : m_urandom R = m_urandom m. Proof. reflexivity. Qed.
Lemma relim_m_net : m_net R = m_net m. Proof. reflexivity. Qed.
Lemma relim_m_conn_ix : m_conn_ix R = m_conn_ix m. Proof. reflexivity. Qed.
Lemma relim_m_fs : m_fs R = m_fs m. Proof. reflexivity. Qed.
Lemma relim_m_halted : m_halted R = m_halted m. Proof. reflexivity. Qed.
Lemma relim_m_tid : m_tid R = m_tid m. Proof. reflexivity. Qed.
Lemma relim_m_setsid_succeeded : m_setsid_succeeded R = m_setsid_succeeded m. Proof. reflexivity. Qed.
Lemma relim_m_has_children : m_has_children R = m_has_children m. Proof. reflexivity. Qed.
Lemma relim_m_sigaltstack_installed : m_sigaltstack_installed R = m_sigaltstack_installed m. Proof. reflexivity. Qed.
Lemma relim_m_sigmask : m_sigmask R = m_sigmask m. Proof. reflexivity. Qed.
Lemma relim_m_killed : m_killed R = m_killed m. Proof. reflexivity. Qed.
Lemma relim_m_sigabrt_pending : m_sigabrt_pending R = m_sigabrt_pending m. Proof. reflexivity. Qed.
Lemma relim_m_abort_terminal : m_abort_terminal R = m_abort_terminal m. Proof. reflexivity. Qed.
Lemma relim_m_utsname : m_utsname R = m_utsname m. Proof. reflexivity. Qed.
Lemma relim_m_statpins : m_statpins R = m_statpins m. Proof. reflexivity. Qed.
Lemma relim_m_rlimit_core : m_rlimit_core R = m_rlimit_core m. Proof. reflexivity. Qed.
Lemma relim_m_nofile : m_nofile R = m_nofile m. Proof. reflexivity. Qed.
Lemma relim_m_clock : m_clock R = m_clock m. Proof. reflexivity. Qed.
Lemma relim_m_creds : m_creds R = m_creds m. Proof. reflexivity. Qed.
Lemma relim_m_vmmaps : m_vmmaps R = vm_relim L (m_vmmaps m). Proof. reflexivity. Qed.
Lemma relim_vm_backing_used : vm_backing_used R = vm_backing_used m. Proof. reflexivity. Qed.
End Acc.
Section AccVm.
Variable L : Z. Variable h : VmMaps.
Lemma relim_vm_reserved : vm_reserved (vm_relim L h) = vm_reserved h. Proof. reflexivity. Qed.
Lemma relim_vm_maps : vm_maps (vm_relim L h) = vm_maps h. Proof. reflexivity. Qed.
Lemma relim_vm_noaccess : vm_noaccess (vm_relim L h) = vm_noaccess h. Proof. reflexivity. Qed.
Lemma relim_vm_start_brk : vm_start_brk (vm_relim L h) = vm_start_brk h. Proof. reflexivity. Qed.
Lemma relim_vm_brk : vm_brk (vm_relim L h) = vm_brk h. Proof. reflexivity. Qed.
Lemma relim_vm_mmap_base : vm_mmap_base (vm_relim L h) = vm_mmap_base h. Proof. reflexivity. Qed.
Lemma relim_vm_init_sp : vm_init_sp (vm_relim L h) = vm_init_sp h. Proof. reflexivity. Qed.
Lemma relim_vm_limit : vm_limit (vm_relim L h) = L. Proof. reflexivity. Qed.
End AccVm.
Create Rewrite HintDb relim.
#[export] Hint Rewrite relim_m_fd relim_m_io relim_m_fsys relim_m_proc relim_m_lim relim_m_time relim_m_fds relim_m_pipes
  relim_m_vm_lazy relim_m_vm_materialized relim_m_stdin relim_m_urandom relim_m_net relim_m_conn_ix relim_m_fs relim_m_halted
  relim_m_tid relim_m_setsid_succeeded relim_m_has_children relim_m_sigaltstack_installed relim_m_sigmask relim_m_killed
  relim_m_sigabrt_pending relim_m_abort_terminal relim_m_utsname relim_m_statpins relim_m_rlimit_core relim_m_nofile
  relim_m_clock relim_m_creds relim_m_vmmaps relim_vm_backing_used
  relim_vm_reserved relim_vm_maps relim_vm_noaccess relim_vm_start_brk relim_vm_brk relim_vm_mmap_base relim_vm_init_sp
  relim_vm_limit : relim.

(* [comment removed for export] *)
Lemma materialize_relim_up : forall L L' m acc m1,
  materialize_model_accesses (m_relim L m) acc = Some m1 -> (L <= L')%Z ->
  materialize_model_accesses (m_relim L' m) acc = Some (m_relim L' m1).
Proof.
  intros L L' m acc m1 H Hle. unfold materialize_model_accesses in *.
  autorewrite with relim in *. unfold materialize_accesses in *.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc) as [| p ps] eqn:E.
  - injection H as <-. reflexivity.
  - destruct (Z.leb_spec (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size) L) as [Hl | Hl]; [| discriminate H].
    injection H as <-.
    destruct (Z.leb_spec (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size) L') as [Hl' | Hl']; [reflexivity | lia].
Qed.

Lemma materialize_relim_down : forall L m acc m',
  materialize_model_accesses m acc = Some m' ->
  materialize_model_accesses (m_relim L m) acc = None
  \/ materialize_model_accesses (m_relim L m) acc = Some (m_relim L m').
Proof.
  intros L m acc m' H. unfold materialize_model_accesses in *.
  autorewrite with relim in *. unfold materialize_accesses in *.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc) as [| p ps] eqn:E.
  - injection H as <-. right. reflexivity.
  - destruct (Z.leb (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size) (vm_limit (m_vmmaps m))); [| discriminate H].
    injection H as <-.
    destruct (Z.leb (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size) L); [right; reflexivity | left; reflexivity].
Qed.

Lemma materialize_limit : forall m acc m',
  materialize_model_accesses m acc = Some m' -> m_limit m' = m_limit m.
Proof.
  intros m acc m' H. destruct (materialize_model_accesses_frame m acc m' H) as (_ & Hv & _).
  unfold m_limit. rewrite Hv. reflexivity.
Qed.
