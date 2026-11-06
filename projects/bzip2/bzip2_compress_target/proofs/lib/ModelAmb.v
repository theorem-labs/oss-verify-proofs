(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Module SpecConsts.
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MAX_RW_COUNT_ge31 : (2147479552 <= MAX_RW_COUNT)%Z.
Proof. unfold MAX_RW_COUNT. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma TASK_SIZE_val : TASK_SIZE = 140737488355328%Z.
Proof. reflexivity. Qed.

Lemma access_okb_intro_num : forall buf cnt : word,
  (bv_unsigned buf + bv_unsigned cnt <= 140737488355328)%Z ->
  access_okb buf (bv_unsigned cnt) = true.
Proof. intros buf cnt H. apply access_okb_intro. rewrite TASK_SIZE_val. exact H. Qed.

(* [comment removed for export] *)
End SpecConsts.

Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts.
Import ListNotations.
Open Scope bv_scope.

Record AmbIn := mkAmbIn {
  ia_stdin  : InputStream;   (* [comment removed for export] *)
  ia_uid    : word;          (* [comment removed for export] *)
  ia_gid    : word;          (* [comment removed for export] *)
  ia_groups : list word;     (* [comment removed for export] *)
  ia_net    : NetQueue;      (* [comment removed for export] *)
  (* [comment removed for export] *)
  ia_nofile : word;          (* [comment removed for export] *)
  ia_sigmask : word;         (* [comment removed for export] *)
  ia_hwcap  : word;          (* [comment removed for export] *)
  ia_abort_terminal : bool;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ia_va_size : VaSize;
  (* [comment removed for export] *)
  ia_urandom : InputStream
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
            (mkProcState halted tid (amb_creds a) false (ia_sigmask a) false None false
                         false false (ia_abort_terminal a) [])
            (mkLimState rlim (ia_nofile a))
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkProcInputA (argv envp : list (list byte)) (fs : Fs.Fs) (a : AmbIn) : ProcInput :=
  mkProcInput_full argv envp fs (ia_stdin a) (ia_uid a) (ia_gid a) (ia_groups a) (ia_net a)
              (ia_nofile a) (ia_sigmask a) (ia_hwcap a) (ia_abort_terminal a) (ia_va_size a)
              (ia_urandom a) [].

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_argv_A : forall argv envp fs a, in_argv (mkProcInputA argv envp fs a) = argv.
Proof. reflexivity. Qed.
Lemma in_envp_A : forall argv envp fs a, in_envp (mkProcInputA argv envp fs a) = envp.
Proof. reflexivity. Qed.
Lemma in_fs_A : forall argv envp fs a, in_fs (mkProcInputA argv envp fs a) = fs.
Proof. reflexivity. Qed.
Lemma in_uid_A : forall argv envp fs a, in_uid (mkProcInputA argv envp fs a) = ia_uid a.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma in_hwcap_A : forall argv envp fs a, in_hwcap (mkProcInputA argv envp fs a) = ia_hwcap a.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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
(* [comment removed for export] *)
Lemma m_net_mkModelA : forall fds vm a fs halted tid rlim,
  m_net (mkModelA fds vm a fs halted tid rlim) = ia_net a.
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
Lemma m_creds_mkModelA : forall fds vm a fs halted tid rlim,
  m_creds (mkModelA fds vm a fs halted tid rlim) = amb_creds a.
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
Lemma m_nofile_mkModelA : forall fds vm a fs halted tid rlim,
  m_nofile (mkModelA fds vm a fs halted tid rlim) = ia_nofile a.
Proof. reflexivity. Qed.
Lemma m_sigmask_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigmask (mkModelA fds vm a fs halted tid rlim) = ia_sigmask a.
Proof. reflexivity. Qed.
Lemma m_statpins_mkModelA : forall fds vm a fs halted tid rlim,
  m_statpins (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.

#[export] Hint Rewrite m_fds_mkModelA m_pipes_mkModelA m_vmmaps_mkModelA
  m_vm_lazy_mkModelA m_vm_materialized_mkModelA m_stdin_mkModelA m_net_mkModelA
  m_fs_mkModelA m_halted_mkModelA m_tid_mkModelA m_rlimit_core_mkModelA
  m_creds_mkModelA m_killed_mkModelA m_sigabrt_pending_mkModelA m_abort_terminal_mkModelA
  m_nofile_mkModelA m_sigmask_mkModelA m_statpins_mkModelA : model.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
