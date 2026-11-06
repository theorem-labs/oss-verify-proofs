(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.


Class RunEnv := mkRunEnv {
  re_creds   : Creds;
  re_urandom : InputStream;
  re_net     : NetQueue;
  re_nofile  : word;
  re_sigmask : word;
  re_abort   : bool
}.

(* [comment removed for export] *)
Definition run_env_of (inp : ProcInput) : RunEnv :=
  {| re_creds := mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
                         (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp);
     re_urandom := in_urandom inp;
     re_net := in_net inp;
     re_nofile := in_nofile inp;
     re_sigmask := in_sigmask inp;
     re_abort := in_abort_terminal inp |}.

Section WithEnv.
  Context {RE : RunEnv}.

  Definition mkModelE (fds : list (word * FdEntry)) (vm : VmMaps)
      (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
      (tid : option word) (rlim : option (list byte)) : Model :=
    with_abort_terminal re_abort
     (with_sigmask re_sigmask
     (with_nofile re_nofile
      (with_net re_net (with_urandom re_urandom (with_creds re_creds (mkModel fds vm stdin fs halted tid rlim)))))).

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

  (* [comment removed for export] *)
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


(* [comment removed for export] *)
Definition fds_init : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

(* [comment removed for export] *)
Lemma init_model_E : forall reserved brk0 mbase sp lim inp,
  init_model reserved brk0 mbase sp lim inp
  = @mkModelE (run_env_of inp) fds_init (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
              (in_stdin inp) (in_fs inp) None None None.
Proof. reflexivity. Qed.

Lemma with_tid_init_model_E : forall tid reserved brk0 mbase sp lim inp,
  with_tid tid (init_model reserved brk0 mbase sp lim inp)
  = @mkModelE (run_env_of inp) fds_init (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
              (in_stdin inp) (in_fs inp) None (Some tid) None.
Proof. reflexivity. Qed.

End FPX_2.
