(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the Amb carries the launch's kernel build, execfn, channel reader, SIGPIPE settings and vDSO run (a_vdso, amb_set_vdso), and the models and inputs it builds use them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State Run.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;      (* [comment removed for export] *)
  a_abort : bool;      (* [comment removed for export] *)
  a_va : VaSize;       (* [comment removed for export] *)
  a_urandom : InputStream;
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool;
  (* the vDSO run the launch draws (EntryDraw.ed_vdso); not part of the published input: mkProcInputC
     ignores it, mkModelC carries it so the walks' models after start-up keep the mkModelC shape *)
  a_vdso : VdsoRun
}.

(* replace the vDSO run of an ambient *)
Definition amb_set_vdso (a : Amb) (v : VdsoRun) : Amb :=
  @mkAmb (@a_uid a) (@a_gid a) (@a_groups a) (@a_net a) (@a_nofile a) (@a_sigmask a) (@a_hwcap a)
         (@a_abort a) (@a_va a) (@a_urandom a) (@a_kernel a) (@a_execfn a) (@a_channel_reader a)
         (@a_sigpipe_default a) (@a_sigpipe_terminal a) v.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] a_kernel a_vdso)
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask false None false false false a_abort [] false a_channel_reader (sigpipe_action_at_exec a_sigpipe_default) a_sigpipe_terminal)
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort a_va
                   a_urandom []
                   a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

Lemma in_fs_mkProcInputC : forall {AMB : Amb} av ev fs si, in_fs (mkProcInputC av ev fs si) = fs.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp)
    (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp) (vdso_run_init vdso_draw_keep).

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (with_vdso a_vdso (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  a_vdso = vdso_run_init vdso_draw_keep ->
  init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof. intros AMB reserved brk0 mbase sp lim av ev fs stdin Hv. unfold mkModelC. rewrite Hv. reflexivity. Qed.

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
