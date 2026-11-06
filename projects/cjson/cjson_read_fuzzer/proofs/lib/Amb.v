(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;     (* [comment removed for export] *)
  a_sigmask : word;    (* [comment removed for export] *)
  a_hwcap : word;      (* [comment removed for export] *)
  a_abort : bool;      (* [comment removed for export] *)
  a_va_size : VaSize;  (* [comment removed for export] *)
  a_urandom : InputStream;  (* [comment removed for export] *)
  a_tmp : Fs.Fs        (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [])
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask false None false false false a_abort [])
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort a_va_size a_urandom a_tmp.

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp)
        (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) (in_urandom inp) (in_tmp inp).

Lemma mkProcInputC_of : forall inp,
  @mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) = inp.
Proof. intros [av ev fs si u g gs n nf sm hw ab va ur tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin (fs_seed_tmp fs a_tmp) None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin (fs_seed_tmp fs a_tmp) None None None.
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
