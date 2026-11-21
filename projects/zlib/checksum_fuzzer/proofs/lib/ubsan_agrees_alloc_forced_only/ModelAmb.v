(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Export SpecConsts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Record AmbIn := mkAmbIn {
  ia_stdin  : InputStream;
  ia_uid    : word;
  ia_gid    : word;
  ia_groups : list word;
  ia_net    : NetQueue;
  ia_nofile : word;
  ia_sigmask : word;
  ia_hwcap  : word;
  ia_abort_terminal : bool;
  ia_va_size : VaSize;
  ia_urandom : InputStream;
  (* port727 (root family, ): the five launch facts ProcInput gained at , in its order
     (in_kernel, in_execfn, in_channel_reader, in_sigpipe_default, in_sigpipe_terminal). *)
  ia_kernel : KernelBuild;
  ia_execfn : list byte;
  ia_channel_reader : bool;
  ia_sigpipe_default : bool;
  ia_sigpipe_terminal : bool;
  (* port727 (): the vDSO run of the model (Run.init_config applies with_vdso over init_model), so
     that mkModelA over [amb_of inp v] IS the run's model (init_model_amb below). *)
  ia_vdso : VdsoRun
}.

Definition amb_creds (a : AmbIn) : Creds :=
  mkCreds (ia_uid a) (ia_uid a) (ia_uid a) (ia_gid a) (ia_gid a) (ia_gid a) (ia_groups a).

Definition mkModelA (fds : list (word * FdEntry)) (vm : VmMaps) (a : AmbIn)
    (fs : Fs.Fs) (halted : option word) (tid : option word)
    (rlim : option (list byte)) : Model :=
  (* port727: VmState gains the kernel build and the vDSO run, ProcState four fields, both in
     State.init_model's form; the vDSO run is the AmbIn's own (ia_vdso), so Run.init_config's [with_vdso] over
     init_model is again an mkModelA (init_model_amb). *)
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] (ia_kernel a) (ia_vdso a))
            (mkIoState (ia_stdin a) (ia_urandom a) (ia_net a) (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid (amb_creds a)
                         false (ia_sigmask a) false None false false false
                         (ia_abort_terminal a) [] false (ia_channel_reader a)
                         (sigpipe_action_at_exec (ia_sigpipe_default a)) (ia_sigpipe_terminal a))
            (mkLimState rlim (ia_nofile a))
            (mkTimeState (Z_to_bv 64 0)).

Definition mkProcInputA (argv envp : list (list byte)) (fs : Fs.Fs) (a : AmbIn) : ProcInput :=
  mkProcInput_full argv envp fs (ia_stdin a) (ia_uid a) (ia_gid a) (ia_groups a) (ia_net a)
              (ia_nofile a) (ia_sigmask a) (ia_hwcap a) (ia_abort_terminal a) (ia_va_size a)
              (ia_urandom a) [] (ia_kernel a) (ia_execfn a) (ia_channel_reader a) (ia_sigpipe_default a)
              (ia_sigpipe_terminal a).

(* port727: the new launch facts, read back. *)
Lemma in_gid_A : forall argv envp fs a, in_gid (mkProcInputA argv envp fs a) = ia_gid a.
Proof. reflexivity. Qed.
Lemma in_kernel_A : forall argv envp fs a, in_kernel (mkProcInputA argv envp fs a) = ia_kernel a.
Proof. reflexivity. Qed.
Lemma in_execfn_A : forall argv envp fs a, in_execfn (mkProcInputA argv envp fs a) = ia_execfn a.
Proof. reflexivity. Qed.



Lemma in_argv_A : forall argv envp fs a, in_argv (mkProcInputA argv envp fs a) = argv.
Proof. reflexivity. Qed.
Lemma in_envp_A : forall argv envp fs a, in_envp (mkProcInputA argv envp fs a) = envp.
Proof. reflexivity. Qed.
Lemma in_uid_A : forall argv envp fs a, in_uid (mkProcInputA argv envp fs a) = ia_uid a.
Proof. reflexivity. Qed.
Lemma in_hwcap_A : forall argv envp fs a, in_hwcap (mkProcInputA argv envp fs a) = ia_hwcap a.
Proof. reflexivity. Qed.



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
Lemma m_nofile_mkModelA : forall fds vm a fs halted tid rlim,
  m_nofile (mkModelA fds vm a fs halted tid rlim) = ia_nofile a.
Proof. reflexivity. Qed.
Lemma m_sigmask_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigmask (mkModelA fds vm a fs halted tid rlim) = ia_sigmask a.
Proof. reflexivity. Qed.
Lemma m_abort_terminal_mkModelA : forall fds vm a fs halted tid rlim,
  m_abort_terminal (mkModelA fds vm a fs halted tid rlim) = ia_abort_terminal a.
Proof. reflexivity. Qed.
Lemma m_statpins_mkModelA : forall fds vm a fs halted tid rlim,
  m_statpins (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.

#[export] Hint Rewrite m_fds_mkModelA m_pipes_mkModelA m_vmmaps_mkModelA
  m_vm_lazy_mkModelA m_vm_materialized_mkModelA m_stdin_mkModelA m_net_mkModelA
  m_fs_mkModelA m_halted_mkModelA m_tid_mkModelA m_rlimit_core_mkModelA
  m_creds_mkModelA m_killed_mkModelA m_nofile_mkModelA m_sigmask_mkModelA
  m_abort_terminal_mkModelA m_statpins_mkModelA : model.


(* port727: the two VmState fields added, read back. *)
Lemma m_kernel_mkModelA : forall fds vm a fs halted tid rlim,
  m_kernel (mkModelA fds vm a fs halted tid rlim) = ia_kernel a.
Proof. reflexivity. Qed.
Lemma m_vdso_mkModelA : forall fds vm a fs halted tid rlim,
  m_vdso (mkModelA fds vm a fs halted tid rlim) = ia_vdso a.
Proof. reflexivity. Qed.
Lemma m_channel_reader_mkModelA : forall fds vm a fs halted tid rlim,
  m_channel_reader (mkModelA fds vm a fs halted tid rlim) = ia_channel_reader a.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_kernel_mkModelA m_vdso_mkModelA m_channel_reader_mkModelA : model.

(* port727 (): the AmbIn of a launch input and a vDSO run, and THE BRIDGE: the run's start model
   (with_vdso over State.init_model, then the thread id) is an mkModelA, field for field. So texts over
   [stdin0 : AmbIn] / [fs0 : Fs] keep their mkModelA forms; the top instantiates stdin0 := amb_of inp v and
   fs0 := in_fs inp. *)
Definition amb_of (inp : ProcInput) (v : VdsoRun) : AmbIn :=
  mkAmbIn (in_stdin inp) (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp)
          (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
          (in_kernel inp) (in_execfn inp) (in_channel_reader inp) (in_sigpipe_default inp) (in_sigpipe_terminal inp) v.

Definition amb_fds0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Lemma init_model_amb : forall reserved brk0 mbase sp lim inp tid v,
  with_tid tid (with_vdso v (init_model reserved brk0 mbase sp lim inp)) =
  mkModelA amb_fds0 (mkVmMapsFull (init_reserved reserved mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
           (amb_of inp v) (in_fs inp) None (Some tid) None.
Proof. reflexivity. Qed.

Lemma ia_channel_reader_amb_of : forall inp v, ia_channel_reader (amb_of inp v) = in_channel_reader inp.
Proof. reflexivity. Qed.
Lemma ia_kernel_amb_of : forall inp v, ia_kernel (amb_of inp v) = in_kernel inp.
Proof. reflexivity. Qed.
Lemma ia_vdso_amb_of : forall inp v, ia_vdso (amb_of inp v) = v.
Proof. reflexivity. Qed.
