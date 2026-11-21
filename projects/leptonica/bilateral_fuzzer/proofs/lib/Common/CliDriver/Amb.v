(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO and vvar pages; writev's channel-reader flag; recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State StackLayout Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Amb () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01i69OSSVerify5KrLib6Common9CliDriver3Amb3Amb00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib6Common9CliDriver3Amb6amb_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc69OSSVerify5KrLib6Common9CliDriver3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes6option00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00".
Import ListNotations.

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;
  a_abort_terminal : bool;
  a_va_size : VaSize;
  a_draw : EntryDraw;
  a_mbase : word;               (* the launch's mmap base: the stack image's vDSO auxv entry reads it *)
  a_urandom : InputStream;
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool;
  (* fd 1/2 have a reader: [Run.valid_input_channel_reader] pins [in_channel_reader] to true *)
  a_reader : a_channel_reader = true
}.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] a_kernel (vdso_run_init (ed_vdso a_draw)))
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask false None
                         false false false a_abort_terminal [] false a_channel_reader
                         (sigpipe_action_at_exec a_sigpipe_default) a_sigpipe_terminal)
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size
                   a_urandom []
                   a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

(* [comment removed for export] *)
(* The vDSO pair [State.init_reserved] appends: at most two entries and at most 20 pages
   ([State.vdso_len_bounds], every kernel). *)
Lemma vdso_reserved_ledger : forall kb top,
  (length (vdso_reserved kb top) <= 2)%nat /\ (live_bytes (vdso_reserved kb top) <= 0x14000)%Z.
Proof.
  intros kb top. unfold vdso_reserved. cbv zeta.
  destruct (top - vdso_len kb <? page_size)%Z; [cbn [length live_bytes]; split; lia|].
  pose proof (vdso_len_bounds kb) as Hb. pose proof (vdso_text_pages_pos kb) as Hp.
  unfold vdso_len in Hb. unfold page_size, vdso_vvar_pages in *.
  assert (U : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
  split; [cbn [length]; lia|].
  cbn [live_bytes]. rewrite !U by lia. lia.
Qed.

(* LPS 08b1429: a driver's vm ledger holds the image's reservations and the vDSO pair
   [State.init_reserved] appends, placed by the ledger's own mmap base and the entry sp. *)
Definition vm_resv {AMB : Amb} (rsv : list (word * word)) (sp0 : word) (vm : VmMaps) : Prop :=
  vm_reserved vm = init_reserved rsv (vm_mmap_base vm) sp0 a_kernel.

Lemma vm_resv_step : forall {AMB : Amb} rsv sp0 vm vm',
  vm_resv rsv sp0 vm -> vm_reserved vm' = vm_reserved vm -> vm_mmap_base vm' = vm_mmap_base vm ->
  vm_resv rsv sp0 vm'.
Proof. intros AMB rsv sp0 vm vm' H E1 E2. unfold vm_resv in *. rewrite E1, E2. exact H. Qed.

(* the allocator interface's premise ([AllocBase.ai_malloc] and siblings) *)
Lemma vm_resv_incl : forall {AMB : Amb} rsv sp0 vm,
  vm_resv rsv sp0 vm -> vm_init_sp vm = sp0 ->
  incl (vdso_reserved a_kernel (vdso_top vm)) (vm_reserved vm).
Proof.
  intros AMB rsv sp0 vm Hr Hs. unfold vm_resv in Hr.
  assert (Et : vdso_top vm = page_round_down_Z (Z.min (bv_unsigned (vm_mmap_base vm)) (bv_unsigned sp0 - stack_max_size))).
  { unfold vdso_top, mmap_top, alloc_top. rewrite Hs. apply page_round_down_Z_min_r. }
  rewrite Et, Hr. unfold init_reserved. apply incl_appr. apply incl_refl.
Qed.

Definition amb_of (inp : ProcInput) (draw : EntryDraw) (mbase : word) (Hrd : in_channel_reader inp = true) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_hwcap inp)
        (in_abort_terminal inp) (in_va_size inp) draw mbase (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp) Hrd.

Lemma in_fs_C : forall {AMB : Amb} av ev fs si, in_fs (mkProcInputC av ev fs si) = fs.
Proof.
intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma init_model_C_of : forall inp draw mb Hrd reserved brk0 mbase sp lim,
  init_model reserved brk0 mbase sp lim inp
  = init_model reserved brk0 mbase sp lim
      (@mkProcInputC (amb_of inp draw mb Hrd) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
intros [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st] draw mb Hrd reserved brk0 mbase sp lim. reflexivity. Qed.

(* [comment removed for export] *)
Lemma init_config_C_of : forall segs pc ph sp brk mbase draw lim inp mb Hrd,
  init_config segs pc ph sp brk mbase draw lim inp
  = init_config segs pc ph sp brk mbase draw lim
      (@mkProcInputC (amb_of inp draw mb Hrd) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
intros segs pc ph sp brk mbase draw lim [av ev fs si u g gs n nf sm hw ab va ur tm kb ef cr sd st] mb Hrd. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
  with_vdso (vdso_run_init (ed_vdso a_draw)) (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof.
intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
  with_tid tid (with_vdso (vdso_run_init (ed_vdso a_draw)) (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)))
  = mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
               (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
               (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
             (mkVmMapsFull (init_reserved reserved mbase sp a_kernel) [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof.
intros. reflexivity. Qed.

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
  Lemma m_fds_C : forall fds vm si fs h t r, m_fds (mkModelC fds vm si fs h t r) = fds.
Proof.
reflexivity. Qed.
  Lemma m_vmmaps_C : forall fds vm si fs h t r, m_vmmaps (mkModelC fds vm si fs h t r) = vm.
Proof.
reflexivity. Qed.
  Lemma m_stdin_C : forall fds vm si fs h t r, m_stdin (mkModelC fds vm si fs h t r) = si.
Proof.
reflexivity. Qed.
  Lemma m_fs_C : forall fds vm si fs h t r, m_fs (mkModelC fds vm si fs h t r) = fs.
Proof.
reflexivity. Qed.
  Lemma m_halted_C : forall fds vm si fs h t r, m_halted (mkModelC fds vm si fs h t r) = h.
Proof.
reflexivity. Qed.
  Lemma m_tid_C : forall fds vm si fs h t r, m_tid (mkModelC fds vm si fs h t r) = t.
Proof.
reflexivity. Qed.
  Lemma m_vm_lazy_C : forall fds vm si fs h t r, m_vm_lazy (mkModelC fds vm si fs h t r) = [].
Proof.
reflexivity. Qed.
  Lemma m_vm_materialized_C : forall fds vm si fs h t r, m_vm_materialized (mkModelC fds vm si fs h t r) = [].
Proof.
reflexivity. Qed.
  Lemma with_fds_C : forall fds' fds vm si fs h t r,
    with_fds fds' (mkModelC fds vm si fs h t r) = mkModelC fds' vm si fs h t r.
Proof.
reflexivity. Qed.
  Lemma with_vmmaps_C : forall vm' fds vm si fs h t r,
    with_vmmaps vm' (mkModelC fds vm si fs h t r) = mkModelC fds vm' si fs h t r.
Proof.
reflexivity. Qed.
  Lemma with_stdin_C : forall si' fds vm si fs h t r,
    with_stdin si' (mkModelC fds vm si fs h t r) = mkModelC fds vm si' fs h t r.
Proof.
reflexivity. Qed.
  Lemma with_halted_C : forall c fds vm si fs h t r,
    with_halted c (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs (Some c) t r.
Proof.
reflexivity. Qed.
  Lemma with_tid_C : forall t' fds vm si fs h t r,
    with_tid t' (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs h (Some t') r.
Proof.
reflexivity. Qed.
End Proj.
