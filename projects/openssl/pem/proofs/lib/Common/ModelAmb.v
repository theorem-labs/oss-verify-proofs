(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Common Require Export SpecConsts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Record AmbIn := mkAmbIn {
  ia_stdin  : InputStream;   (* [comment removed for export] *)
  ia_uid    : word;          (* [comment removed for export] *)
  ia_gid    : word;          (* [comment removed for export] *)
  ia_groups : list word;     (* [comment removed for export] *)
  ia_net    : NetQueue;      (* [comment removed for export] *)
  ia_nofile : word;          (* [comment removed for export] *)
  ia_sigmask : word;         (* [comment removed for export] *)
  ia_hwcap  : word;          (* [comment removed for export] *)
  ia_abort_terminal : bool;  (* [comment removed for export] *)
  ia_va : VaSize;            (* [comment removed for export] *)
  ia_urandom : InputStream   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition amb_creds (a : AmbIn) : Creds :=
  mkCreds (ia_uid a) (ia_uid a) (ia_uid a) (ia_gid a) (ia_gid a) (ia_gid a) (ia_groups a).

(* [comment removed for export] *)
Definition mkModelA (fds : list (word * FdEntry)) (vm : VmMaps) (a : AmbIn)
    (fs : Fs.Fs) (halted : option word) (tid : option word)
    (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [])
            (mkIoState (ia_stdin a) (ia_urandom a) (ia_net a) (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid (amb_creds a)
               false (ia_sigmask a) false None false false false (ia_abort_terminal a) [])
            (mkLimState rlim (ia_nofile a))
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputA (argv envp : list (list byte)) (fs : Fs.Fs) (a : AmbIn) : ProcInput :=
  mkProcInput_full argv envp fs (ia_stdin a) (ia_uid a) (ia_gid a) (ia_groups a) (ia_net a)
              (ia_nofile a) (ia_sigmask a) (ia_hwcap a) (ia_abort_terminal a) (ia_va a)
              (ia_urandom a) [].

Definition amb_of (inp : ProcInput) : AmbIn :=
  mkAmbIn (in_stdin inp) (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
          (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
          (in_urandom inp).

(* [comment removed for export] *)
Lemma mkProcInputA_of_fs : forall inp : ProcInput,
  in_fs (mkProcInputA (in_argv inp) (in_envp inp) (in_fs inp) (amb_of inp)) = in_fs inp.
Proof. reflexivity. Qed.

Lemma mkProcInputA_of_init_model : forall reserved (brk0 mbase sp : word) lim (inp : ProcInput),
  init_model reserved brk0 mbase sp lim (mkProcInputA (in_argv inp) (in_envp inp) (in_fs inp) (amb_of inp))
  = init_model reserved brk0 mbase sp lim inp.
Proof. reflexivity. Qed.

Lemma amb_of_mkProcInputA : forall argv envp fs a,
  amb_of (mkProcInputA argv envp fs a) = a.
Proof. intros argv envp fs a. destruct a. reflexivity. Qed.

Lemma in_argv_A : forall argv envp fs a, in_argv (mkProcInputA argv envp fs a) = argv.
Proof. reflexivity. Qed.
Lemma in_envp_A : forall argv envp fs a, in_envp (mkProcInputA argv envp fs a) = envp.
Proof. reflexivity. Qed.
Lemma in_fs_A : forall argv envp fs a, in_fs (mkProcInputA argv envp fs a) = fs.
Proof. reflexivity. Qed.
Lemma in_uid_A : forall argv envp fs a, in_uid (mkProcInputA argv envp fs a) = ia_uid a.
Proof. reflexivity. Qed.
Lemma in_gid_A : forall argv envp fs a, in_gid (mkProcInputA argv envp fs a) = ia_gid a.
Proof. reflexivity. Qed.
Lemma in_groups_A : forall argv envp fs a, in_groups (mkProcInputA argv envp fs a) = ia_groups a.
Proof. reflexivity. Qed.
Lemma in_net_A : forall argv envp fs a, in_net (mkProcInputA argv envp fs a) = ia_net a.
Proof. reflexivity. Qed.
Lemma in_stdin_A : forall argv envp fs a, in_stdin (mkProcInputA argv envp fs a) = ia_stdin a.
Proof. reflexivity. Qed.
Lemma in_nofile_A : forall argv envp fs a, in_nofile (mkProcInputA argv envp fs a) = ia_nofile a.
Proof. reflexivity. Qed.
Lemma in_sigmask_A : forall argv envp fs a, in_sigmask (mkProcInputA argv envp fs a) = ia_sigmask a.
Proof. reflexivity. Qed.
Lemma in_hwcap_A : forall argv envp fs a, in_hwcap (mkProcInputA argv envp fs a) = ia_hwcap a.
Proof. reflexivity. Qed.
Lemma in_abort_terminal_A : forall argv envp fs a,
  in_abort_terminal (mkProcInputA argv envp fs a) = ia_abort_terminal a.
Proof. reflexivity. Qed.
Lemma in_va_size_A : forall argv envp fs a,
  in_va_size (mkProcInputA argv envp fs a) = ia_va a.
Proof. reflexivity. Qed.
Lemma in_urandom_A : forall argv envp fs a,
  in_urandom (mkProcInputA argv envp fs a) = ia_urandom a.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma init_model_A : forall reserved (brk0 mbase sp : word) lim argv envp fs a,
  init_model reserved brk0 mbase sp lim (mkProcInputA argv envp fs a)
  = mkModelA [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) a fs None None None.
Proof. reflexivity. Qed.

Lemma with_tid_init_model_A : forall reserved (brk0 mbase sp : word) lim argv envp fs a tid,
  with_tid tid (init_model reserved brk0 mbase sp lim (mkProcInputA argv envp fs a))
  = mkModelA [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) a fs None (Some tid) None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma init_model_amb_of : forall reserved (brk0 mbase sp : word) lim inp,
  init_model reserved brk0 mbase sp lim inp
  = mkModelA [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) (amb_of inp) (in_fs inp)
             None None None.
Proof. intros. destruct inp. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_fds_mkModelA : forall fds vm a fs halted tid rlim,
  m_fds (mkModelA fds vm a fs halted tid rlim) = fds.
Proof. reflexivity. Qed.
Lemma m_pipes_mkModelA : forall fds vm a fs halted tid rlim,
  m_pipes (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_vmmaps_mkModelA : forall fds vm a fs halted tid rlim,
  m_vmmaps (mkModelA fds vm a fs halted tid rlim) = vm.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_mkModelA : forall fds vm a fs halted tid rlim,
  m_vm_lazy (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_vm_materialized_mkModelA : forall fds vm a fs halted tid rlim,
  m_vm_materialized (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_stdin_mkModelA : forall fds vm a fs halted tid rlim,
  m_stdin (mkModelA fds vm a fs halted tid rlim) = ia_stdin a.
Proof. reflexivity. Qed.
Lemma m_urandom_mkModelA : forall fds vm a fs halted tid rlim,
  m_urandom (mkModelA fds vm a fs halted tid rlim) = ia_urandom a.
Proof. reflexivity. Qed.
Lemma m_net_mkModelA : forall fds vm a fs halted tid rlim,
  m_net (mkModelA fds vm a fs halted tid rlim) = ia_net a.
Proof. reflexivity. Qed.
Lemma m_conn_ix_mkModelA : forall fds vm a fs halted tid rlim,
  m_conn_ix (mkModelA fds vm a fs halted tid rlim) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
Lemma m_fs_mkModelA : forall fds vm a fs halted tid rlim,
  m_fs (mkModelA fds vm a fs halted tid rlim) = fs.
Proof. reflexivity. Qed.
Lemma m_halted_mkModelA : forall fds vm a fs halted tid rlim,
  m_halted (mkModelA fds vm a fs halted tid rlim) = halted.
Proof. reflexivity. Qed.
Lemma m_tid_mkModelA : forall fds vm a fs halted tid rlim,
  m_tid (mkModelA fds vm a fs halted tid rlim) = tid.
Proof. reflexivity. Qed.
Lemma m_rlimit_core_mkModelA : forall fds vm a fs halted tid rlim,
  m_rlimit_core (mkModelA fds vm a fs halted tid rlim) = rlim.
Proof. reflexivity. Qed.
Lemma m_nofile_mkModelA : forall fds vm a fs halted tid rlim,
  m_nofile (mkModelA fds vm a fs halted tid rlim) = ia_nofile a.
Proof. reflexivity. Qed.
Lemma m_creds_mkModelA : forall fds vm a fs halted tid rlim,
  m_creds (mkModelA fds vm a fs halted tid rlim) = amb_creds a.
Proof. reflexivity. Qed.
Lemma m_setsid_succeeded_mkModelA : forall fds vm a fs halted tid rlim,
  m_setsid_succeeded (mkModelA fds vm a fs halted tid rlim) = false.
Proof. reflexivity. Qed.
Lemma m_has_children_mkModelA : forall fds vm a fs halted tid rlim,
  m_has_children (mkModelA fds vm a fs halted tid rlim) = false.
Proof. reflexivity. Qed.
Lemma m_sigaltstack_installed_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigaltstack_installed (mkModelA fds vm a fs halted tid rlim) = false.
Proof. reflexivity. Qed.
Lemma m_sigmask_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigmask (mkModelA fds vm a fs halted tid rlim) = ia_sigmask a.
Proof. reflexivity. Qed.
Lemma m_killed_mkModelA : forall fds vm a fs halted tid rlim,
  m_killed (mkModelA fds vm a fs halted tid rlim) = None.
Proof. reflexivity. Qed.
Lemma m_sigabrt_pending_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigabrt_pending (mkModelA fds vm a fs halted tid rlim) = false.
Proof. reflexivity. Qed.
Lemma m_abort_terminal_mkModelA : forall fds vm a fs halted tid rlim,
  m_abort_terminal (mkModelA fds vm a fs halted tid rlim) = ia_abort_terminal a.
Proof. reflexivity. Qed.
Lemma m_utsname_mkModelA : forall fds vm a fs halted tid rlim,
  m_utsname (mkModelA fds vm a fs halted tid rlim) = None.
Proof. reflexivity. Qed.
Lemma m_statpins_mkModelA : forall fds vm a fs halted tid rlim,
  m_statpins (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_clock_mkModelA : forall fds vm a fs halted tid rlim,
  m_clock (mkModelA fds vm a fs halted tid rlim) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

#[export] Hint Rewrite m_fds_mkModelA m_pipes_mkModelA m_vmmaps_mkModelA
  m_vm_lazy_mkModelA m_vm_materialized_mkModelA m_stdin_mkModelA m_urandom_mkModelA m_net_mkModelA
  m_conn_ix_mkModelA m_fs_mkModelA m_halted_mkModelA m_tid_mkModelA m_rlimit_core_mkModelA
  m_nofile_mkModelA m_creds_mkModelA m_setsid_succeeded_mkModelA m_has_children_mkModelA
  m_sigaltstack_installed_mkModelA m_sigmask_mkModelA m_killed_mkModelA
  m_sigabrt_pending_mkModelA m_abort_terminal_mkModelA m_utsname_mkModelA
  m_statpins_mkModelA m_clock_mkModelA : model.

(* [comment removed for export] *)
Lemma with_fds_mkModelA : forall v fds vm a fs halted tid rlim,
  with_fds v (mkModelA fds vm a fs halted tid rlim) = mkModelA v vm a fs halted tid rlim.
Proof. reflexivity. Qed.
Lemma with_vmmaps_mkModelA : forall v fds vm a fs halted tid rlim,
  with_vmmaps v (mkModelA fds vm a fs halted tid rlim) = mkModelA fds v a fs halted tid rlim.
Proof. reflexivity. Qed.
Lemma with_halted_mkModelA : forall v fds vm a fs halted tid rlim,
  with_halted v (mkModelA fds vm a fs halted tid rlim) = mkModelA fds vm a fs (Some v) tid rlim.
Proof. reflexivity. Qed.
Lemma with_tid_mkModelA : forall v fds vm a fs halted tid rlim,
  with_tid v (mkModelA fds vm a fs halted tid rlim) = mkModelA fds vm a fs halted (Some v) rlim.
Proof. reflexivity. Qed.
Lemma with_fs_mkModelA : forall v fds vm a fs halted tid rlim,
  with_fs v (mkModelA fds vm a fs halted tid rlim) = mkModelA fds vm a v halted tid rlim.
Proof. reflexivity. Qed.
Lemma with_rlimit_core_mkModelA : forall v fds vm a fs halted tid rlim,
  with_rlimit_core v (mkModelA fds vm a fs halted tid rlim) = mkModelA fds vm a fs halted tid (Some v).
Proof. reflexivity. Qed.

#[export] Hint Rewrite with_fds_mkModelA with_vmmaps_mkModelA with_halted_mkModelA
  with_tid_mkModelA with_fs_mkModelA with_rlimit_core_mkModelA : model.
