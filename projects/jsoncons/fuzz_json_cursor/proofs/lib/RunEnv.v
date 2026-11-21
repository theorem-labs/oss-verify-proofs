(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, walks lifted to the run's segments, the vDSO, the launch input's kernel build): changed RunEnv, init_model_E, mkModelE and 3 more; added ReaderOn, mkModelE_reader, rdr and 2 more. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Vdso Run.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.

Class RunEnv := mkRunEnv {
  re_creds   : Creds;
  re_urandom : InputStream;
  re_net     : NetQueue;
  re_nofile  : word;
  re_sigmask : word;
  re_abort   : bool;
  re_kernel  : KernelBuild;
  re_reader  : bool;
  re_sigdfl  : bool;
  re_sigterm : bool;
  (* the run's vDSO state: [Run.init_config] wraps [init_model] in
     [with_vdso (vdso_run_init (ed_vdso draw))] *)
  re_vdso    : VdsoRun
}.

Definition run_env_of (inp : ProcInput) : RunEnv :=
  {| re_creds := mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
                         (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp);
     re_urandom := in_urandom inp;
     re_net := in_net inp;
     re_nofile := in_nofile inp;
     re_sigmask := in_sigmask inp;
     re_abort := in_abort_terminal inp;
     re_kernel := in_kernel inp;
     re_reader := in_channel_reader inp;
     re_sigdfl := in_sigpipe_default inp;
     re_sigterm := in_sigpipe_terminal inp;
     re_vdso := vdso_run_init vdso_draw_keep |}.

(** The environment of the configured run: [run_env_of] with the launch's
    vDSO state. *)
Definition run_env_at (inp : ProcInput) (v : VdsoRun) : RunEnv :=
  {| re_creds := mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
                         (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp);
     re_urandom := in_urandom inp;
     re_net := in_net inp;
     re_nofile := in_nofile inp;
     re_sigmask := in_sigmask inp;
     re_abort := in_abort_terminal inp;
     re_kernel := in_kernel inp;
     re_reader := in_channel_reader inp;
     re_sigdfl := in_sigpipe_default inp;
     re_sigterm := in_sigpipe_terminal inp;
     re_vdso := v |}.

(* 08b1429: write/writev read [m_channel_reader] (recipes/channel-reader-premise.md).  The run's reader
   is [re_reader]; a section that writes takes [ReaderOn] as a class, so its callers need not pass it,
   and the root discharges it from [Run.valid_input_channel_reader]. *)
Class ReaderOn {RE : RunEnv} : Prop := reader_on : re_reader = true.

Section WithEnv.
  Context {RE : RunEnv}.

  Definition mkModelE (fds : list (word * FdEntry)) (vm : VmMaps)
      (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
      (tid : option word) (rlim : option (list byte)) : Model :=
    mkModelOf (mkFdState fds [])
      (mkVmState vm [] [] re_kernel re_vdso)
      (mkIoState stdin re_urandom re_net (Z_to_bv 64 0))
      (mkFsState fs)
      (mkProcState halted tid re_creds false re_sigmask false None false false false
         re_abort [] false re_reader (sigpipe_action_at_exec re_sigdfl) re_sigterm)
      (mkLimState rlim re_nofile)
      (mkTimeState (Z_to_bv 64 0)).

  Lemma m_fds_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_fds (mkModelE fds vm stdin fs halted tid rlim) = fds.
  Proof. reflexivity. Qed.
  Lemma m_vmmaps_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vmmaps (mkModelE fds vm stdin fs halted tid rlim) = vm.
  Proof. reflexivity. Qed.
  Lemma m_stdin_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_stdin (mkModelE fds vm stdin fs halted tid rlim) = stdin.
  Proof. reflexivity. Qed.
  Lemma m_fs_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_fs (mkModelE fds vm stdin fs halted tid rlim) = fs.
  Proof. reflexivity. Qed.
  Lemma m_halted_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_halted (mkModelE fds vm stdin fs halted tid rlim) = halted.
  Proof. reflexivity. Qed.
  Lemma m_tid_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_tid (mkModelE fds vm stdin fs halted tid rlim) = tid.
  Proof. reflexivity. Qed.
  Lemma m_rlimit_core_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_rlimit_core (mkModelE fds vm stdin fs halted tid rlim) = rlim.
  Proof. reflexivity. Qed.
  Lemma m_vm_lazy_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vm_lazy (mkModelE fds vm stdin fs halted tid rlim) = [].
  Proof. reflexivity. Qed.
  Lemma m_vm_materialized_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_vm_materialized (mkModelE fds vm stdin fs halted tid rlim) = [].
  Proof. reflexivity. Qed.
  Lemma m_pipes_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_pipes (mkModelE fds vm stdin fs halted tid rlim) = [].
  Proof. reflexivity. Qed.
  Lemma m_creds_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_creds (mkModelE fds vm stdin fs halted tid rlim) = re_creds.
  Proof. reflexivity. Qed.
  Lemma m_urandom_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_urandom (mkModelE fds vm stdin fs halted tid rlim) = re_urandom.
  Proof. reflexivity. Qed.
  Lemma m_net_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_net (mkModelE fds vm stdin fs halted tid rlim) = re_net.
  Proof. reflexivity. Qed.
  Lemma m_nofile_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_nofile (mkModelE fds vm stdin fs halted tid rlim) = re_nofile.
  Proof. reflexivity. Qed.
  Lemma m_sigmask_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_sigmask (mkModelE fds vm stdin fs halted tid rlim) = re_sigmask.
  Proof. reflexivity. Qed.
  Lemma m_abort_terminal_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_abort_terminal (mkModelE fds vm stdin fs halted tid rlim) = re_abort.
  Proof. reflexivity. Qed.
  Lemma m_killed_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_killed (mkModelE fds vm stdin fs halted tid rlim) = None.
  Proof. reflexivity. Qed.
  Lemma m_sigabrt_pending_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_sigabrt_pending (mkModelE fds vm stdin fs halted tid rlim) = false.
  Proof. reflexivity. Qed.
  Lemma m_conn_ix_mkModelE : forall fds vm stdin fs halted tid rlim,
    m_conn_ix (mkModelE fds vm stdin fs halted tid rlim) = Z_to_bv 64 0.
  Proof. reflexivity. Qed.

  Lemma with_fds_mkModelE : forall fds' fds vm stdin fs halted tid rlim,
    with_fds fds' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds' vm stdin fs halted tid rlim.
  Proof. reflexivity. Qed.
  Lemma with_vmmaps_mkModelE : forall vm' fds vm stdin fs halted tid rlim,
    with_vmmaps vm' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm' stdin fs halted tid rlim.
  Proof. reflexivity. Qed.
  Lemma with_tid_mkModelE : forall t fds vm stdin fs halted tid rlim,
    with_tid t (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs halted (Some t) rlim.
  Proof. reflexivity. Qed.
  Lemma with_halted_mkModelE : forall c fds vm stdin fs halted tid rlim,
    with_halted c (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs (Some c) tid rlim.
  Proof. reflexivity. Qed.
  Lemma with_fs_mkModelE : forall fs' fds vm stdin fs halted tid rlim,
    with_fs fs' (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm stdin fs' halted tid rlim.
  Proof. reflexivity. Qed.
  Lemma with_stdin_mkModelE : forall s fds vm stdin fs halted tid rlim,
    with_stdin s (mkModelE fds vm stdin fs halted tid rlim) = mkModelE fds vm s fs halted tid rlim.
  Proof. reflexivity. Qed.
  Lemma mkModelE_reader {RO : ReaderOn} : forall fds vm stdin fs halted tid rlim,
    m_channel_reader (mkModelE fds vm stdin fs halted tid rlim) = true.
  Proof. intros. exact reader_on. Qed.
End WithEnv.
End FPX_1.

#[export] Hint Rewrite @m_fds_mkModelE @m_vmmaps_mkModelE @m_stdin_mkModelE @m_fs_mkModelE
  @m_halted_mkModelE @m_tid_mkModelE @m_rlimit_core_mkModelE @m_vm_lazy_mkModelE
  @m_vm_materialized_mkModelE @m_pipes_mkModelE @m_creds_mkModelE @m_net_mkModelE
  @m_nofile_mkModelE @m_sigmask_mkModelE @m_abort_terminal_mkModelE @m_killed_mkModelE
  @m_sigabrt_pending_mkModelE @m_conn_ix_mkModelE @m_urandom_mkModelE
  @with_fds_mkModelE @with_vmmaps_mkModelE @with_tid_mkModelE @with_halted_mkModelE
  @with_fs_mkModelE @with_stdin_mkModelE : model.
Section FPX_2. Context {fx : PropExec.FPState}.

Definition fds_init : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma init_model_E : forall reserved brk0 mbase sp lim inp,
  init_model reserved brk0 mbase sp lim inp
  = @mkModelE (run_env_of inp) fds_init
      (mkVmMapsFull (init_reserved reserved mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
      (in_stdin inp) (in_fs inp) None None None.
Proof. reflexivity. Qed.

Lemma with_tid_init_model_E : forall tid reserved brk0 mbase sp lim inp,
  with_tid tid (init_model reserved brk0 mbase sp lim inp)
  = @mkModelE (run_env_of inp) fds_init
      (mkVmMapsFull (init_reserved reserved mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
      (in_stdin inp) (in_fs inp) None (Some tid) None.
Proof. reflexivity. Qed.

Lemma with_tid_with_vdso_init_model_E : forall tid v reserved brk0 mbase sp lim inp,
  with_tid tid (with_vdso v (init_model reserved brk0 mbase sp lim inp))
  = @mkModelE (run_env_at inp v) fds_init
      (mkVmMapsFull (init_reserved reserved mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
      (in_stdin inp) (in_fs inp) None (Some tid) None.
Proof. reflexivity. Qed.

End FPX_2.

Ltac rdr := first [ assumption | exact reader_on | apply mkModelE_reader | (cbn; exact reader_on) ].
