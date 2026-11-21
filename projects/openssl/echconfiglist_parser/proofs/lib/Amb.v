(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the ambient record gains the kernel build, execfn, channel-reader and SIGPIPE fields of the input; the initial maps hold init_reserved; new lemmas valid_launch_canon and entry_launch_canon). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State Run.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;
  a_abort_terminal : bool;
  a_va_size : VaSize;   (* [comment removed for export] *)
  a_urandom : InputStream   (* [comment removed for export] *);
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool
}.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] a_kernel (vdso_run_init vdso_draw_keep))
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask false None
                         false false false a_abort_terminal [] false a_channel_reader (sigpipe_action_at_exec a_sigpipe_default) a_sigpipe_terminal)
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net
              a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size a_urandom []
              a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
        (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
        (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp).

(* [comment removed for export] *)
Definition inpC (inp : ProcInput) : ProcInput :=
  @mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp).

Lemma in_fs_C : forall {AMB : Amb} av ev fs stdin, in_fs (mkProcInputC av ev fs stdin) = fs.
Proof. reflexivity. Qed.

Lemma init_model_canon : forall reserved brk0 mbase sp lim inp,
  init_model reserved brk0 mbase sp lim inp
  = init_model reserved brk0 mbase sp lim (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof. intros reserved brk0 mbase sp lim [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st]. reflexivity. Qed.

Lemma init_config_canon : forall segs pc ph sp brk0 mbase rnd lim inp,
  init_config segs pc ph sp brk0 mbase rnd lim inp
  = init_config segs pc ph sp brk0 mbase rnd lim (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof. intros segs pc ph sp brk0 mbase rnd lim [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st]. reflexivity. Qed.

(* [Run.valid_launch] and [Run.entry_launch_ok_va] read neither the image nor /tmp, so the launch
   facts of an input hold of the canonical input [init_model_canon] runs over, by conversion. *)
Lemma valid_launch_canon : forall inp, valid_launch inp ->
  valid_launch (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof. intros [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st] H. exact H. Qed.

Lemma entry_launch_canon : forall v sp brk mbase draw inp,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  entry_launch_ok_va v (mkEntry sp brk mbase draw)
    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof. intros v sp brk mbase draw [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st] H. exact H. Qed.

(* [comment removed for export] *)
Lemma in_hwcap_C : forall {AMB : Amb} av ev fs stdin,
  in_hwcap (mkProcInputC av ev fs stdin) = a_hwcap.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
  Lemma m_fds_C : forall fds vm si fs h t r, m_fds (mkModelC fds vm si fs h t r) = fds. Proof. reflexivity. Qed.
  Lemma m_vmmaps_C : forall fds vm si fs h t r, m_vmmaps (mkModelC fds vm si fs h t r) = vm. Proof. reflexivity. Qed.
  Lemma m_stdin_C : forall fds vm si fs h t r, m_stdin (mkModelC fds vm si fs h t r) = si. Proof. reflexivity. Qed.
  Lemma m_fs_C : forall fds vm si fs h t r, m_fs (mkModelC fds vm si fs h t r) = fs. Proof. reflexivity. Qed.
  Lemma m_halted_C : forall fds vm si fs h t r, m_halted (mkModelC fds vm si fs h t r) = h. Proof. reflexivity. Qed.
  Lemma m_tid_C : forall fds vm si fs h t r, m_tid (mkModelC fds vm si fs h t r) = t. Proof. reflexivity. Qed.
  Lemma m_vm_lazy_C : forall fds vm si fs h t r, m_vm_lazy (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
  Lemma m_vm_materialized_C : forall fds vm si fs h t r, m_vm_materialized (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
  Lemma m_killed_C : forall fds vm si fs h t r, m_killed (mkModelC fds vm si fs h t r) = None. Proof. reflexivity. Qed.
  Lemma m_abort_terminal_C : forall fds vm si fs h t r, m_abort_terminal (mkModelC fds vm si fs h t r) = a_abort_terminal. Proof. reflexivity. Qed.
  Lemma m_nofile_C : forall fds vm si fs h t r, m_nofile (mkModelC fds vm si fs h t r) = a_nofile. Proof. reflexivity. Qed.
  Lemma with_fds_C : forall fds' fds vm si fs h t r,
    with_fds fds' (mkModelC fds vm si fs h t r) = mkModelC fds' vm si fs h t r. Proof. reflexivity. Qed.
  Lemma with_vmmaps_C : forall vm' fds vm si fs h t r,
    with_vmmaps vm' (mkModelC fds vm si fs h t r) = mkModelC fds vm' si fs h t r. Proof. reflexivity. Qed.
  Lemma with_stdin_C : forall si' fds vm si fs h t r,
    with_stdin si' (mkModelC fds vm si fs h t r) = mkModelC fds vm si' fs h t r. Proof. reflexivity. Qed.
  Lemma with_halted_C : forall c fds vm si fs h t r,
    with_halted c (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs (Some c) t r. Proof. reflexivity. Qed.
  Lemma with_tid_C : forall t' fds vm si fs h t r,
    with_tid t' (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs h (Some t') r. Proof. reflexivity. Qed.
End Proj.
