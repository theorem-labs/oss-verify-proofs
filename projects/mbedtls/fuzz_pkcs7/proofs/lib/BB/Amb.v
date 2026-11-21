(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the ambient record gains the kernel build, exec file name, channel reader with its fact a_reader, SIGPIPE settings and vDSO run; mkModelC, mkProcInputC and amb_of fill the new model and input fields, and init_model_C, with_tid_init_model_C and init_model_C_of are restated with the launch's vDSO run and reserved ledger; Vdso import added). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State Run.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;          (* [comment removed for export] *)
  a_sigmask : word;         (* [comment removed for export] *)
  a_hwcap : word;           (* [comment removed for export] *)
  a_abort : bool;           (* [comment removed for export] *)
  a_va : VaSize;            (* [comment removed for export] *)
  a_urandom : InputStream   (* [comment removed for export] *);
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool;
  (* 08b1429: [Run.init_config] starts the model with the launch's vDSO run
     ([with_vdso (vdso_run_init (ed_vdso draw))]); the ambient record carries it so the
     model the start-up hands over is [mkModelC] *)
  a_vdso : VdsoRun;
  (* 08b1429: writev reads the channel reader; every published input predicate pins it
     (Run.valid_input_channel_reader), so the ambient record carries the fact
     (recipes/channel-reader-premise.md, fourth shape) *)
  a_reader : a_channel_reader = true
}.

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
(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort a_va a_urandom []
              a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) (Hrd : in_channel_reader inp = true) (vr : VdsoRun) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
        (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp) vr Hrd.

(* [comment removed for export] *)
Lemma init_model_C_of : forall reserved brk0 mbase sp lim inp Hrd vr,
  init_model reserved brk0 mbase sp lim (@mkProcInputC (amb_of inp Hrd vr) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
  = init_model reserved brk0 mbase sp lim inp.
Proof. intros reserved brk0 mbase sp lim [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st] Hrd vr. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_hwcap_C : forall {AMB : Amb} av ev fs si, in_hwcap (mkProcInputC av ev fs si) = a_hwcap.
Proof. intros. reflexivity. Qed.
Lemma in_uid_C : forall {AMB : Amb} av ev fs si, in_uid (mkProcInputC av ev fs si) = a_uid.
Proof. intros. reflexivity. Qed.
Lemma in_argv_C : forall {AMB : Amb} av ev fs si, in_argv (mkProcInputC av ev fs si) = av.
Proof. intros. reflexivity. Qed.
Lemma in_envp_C : forall {AMB : Amb} av ev fs si, in_envp (mkProcInputC av ev fs si) = ev.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (with_vdso a_vdso (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  with_vdso a_vdso (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
  #[using="Type"] Lemma m_fds_C : forall fds vm si fs h t r, m_fds (mkModelC fds vm si fs h t r) = fds. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_vmmaps_C : forall fds vm si fs h t r, m_vmmaps (mkModelC fds vm si fs h t r) = vm. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_stdin_C : forall fds vm si fs h t r, m_stdin (mkModelC fds vm si fs h t r) = si. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_fs_C : forall fds vm si fs h t r, m_fs (mkModelC fds vm si fs h t r) = fs. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_halted_C : forall fds vm si fs h t r, m_halted (mkModelC fds vm si fs h t r) = h. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_tid_C : forall fds vm si fs h t r, m_tid (mkModelC fds vm si fs h t r) = t. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_vm_lazy_C : forall fds vm si fs h t r, m_vm_lazy (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
  #[using="Type"] Lemma m_vm_materialized_C : forall fds vm si fs h t r, m_vm_materialized (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
  #[using="Type"] Lemma with_fds_C : forall fds' fds vm si fs h t r,
    with_fds fds' (mkModelC fds vm si fs h t r) = mkModelC fds' vm si fs h t r. Proof. reflexivity. Qed.
  #[using="Type"] Lemma with_vmmaps_C : forall vm' fds vm si fs h t r,
    with_vmmaps vm' (mkModelC fds vm si fs h t r) = mkModelC fds vm' si fs h t r. Proof. reflexivity. Qed.
  #[using="Type"] Lemma with_stdin_C : forall si' fds vm si fs h t r,
    with_stdin si' (mkModelC fds vm si fs h t r) = mkModelC fds vm si' fs h t r. Proof. reflexivity. Qed.
  #[using="Type"] Lemma with_halted_C : forall c fds vm si fs h t r,
    with_halted c (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs (Some c) t r. Proof. reflexivity. Qed.
  #[using="Type"] Lemma with_tid_C : forall t' fds vm si fs h t r,
    with_tid t' (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs h (Some t') r. Proof. reflexivity. Qed.
End Proj.
