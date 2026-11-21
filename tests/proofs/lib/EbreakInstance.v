(** What the instance controls of the ebreak toy share (tests/instances/,
    tests/README.md): the inputs an instance of a pair statement of
    [toy/ebreak] names, and the premises of each agreement, bound and
    decidability shape on them.

    Each input is [oft check]'s rendering of an instance
    ([tools/oft/shapes.py], [instance_input]) for the argv0 "ebreak" and
    the input file "input.bin" that the controls' instance.yaml files give:
    argv ["ebreak"; "input.bin"] (path reaches-harness) or ["ebreak"] (path
    refused-by-driver).  The process input of an agreement statement has no
    environment, one file "input.bin" with [data], end of input, the other
    fields of [OSSVerify.Core.Premises.witness_input], and the abort
    declaration its shape reads ([abort]).  The finite input of a bound or
    decidability statement is MeasureLib's [core_input] of the [file_core] a
    harness's Distribution.v builds its entries with, over the file system
    [("input.bin", [])].  No validity predicate says anything about a file's
    contents, so each input is valid for every [data].  Each does bound the
    launch, as [Exit0Instance] says: [Run.valid_launch] asks that argv, the
    environment and the exec name fit under the E2BIG limit together, which
    [valid_argv] alone does not give, so the lemmas below take
    [launch_argv argv], [valid_argv argv] and that bound.  The bound is the
    same for every input here with argument vector [argv].

    [Images.plain] is lps's ebreak image: its first instruction faults, at
    every entry and on every input, before any system call, so its run is
    never refused memory, at any budget, unconfigured ([run]) and under every
    configuration ([run_scfg]).  [Images.asan] is lps's exit0 image.  Both
    have a valid entry on every valid input, under either abort declaration:
    lps's [demo_entry_of inp], which places the stack by the input. *)
From Stdlib Require Import ZArith List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType StackLayout State Run RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput MeasureLib.
(* Exit0Instance loads the exit0 toy's Images; the ebreak toy's is required
   after it, so that the short name [Images] below is the ebreak toy's. *)
From OSSVerify.Tests.proofs.lib Require Exit0Instance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

(** The 7 bytes of the reaches-harness controls' file, input.bin: those of
    the exit0 toy's controls. *)
Abbreviation seven := Exit0Instance.seven.

(** The bytes of "ebreak"; those of "input.bin" are [Exit0Instance.path]. *)
Definition prog : list byte :=
  [Z_to_bv 8 101; Z_to_bv 8 98; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 97; Z_to_bv 8 107].

(** The process input with abort declaration [abort] and argument vector
    [argv] whose file holds [data]. *)
Definition input (abort : bool) (argv : list (list byte)) (data : list byte) : ProcInput :=
  mkProcInput argv [] [(Exit0Instance.path, data)] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc abort Sv48.

(** The finite input with argument vector [argv] whose file holds [data]. *)
Definition fin_input (argv : list (list byte)) (data : list byte) : FinProcInput :=
  core_input (file_core argv [] [(Exit0Instance.path, [])] Exit0Instance.path [] data).

(** The argument vectors of the two paths. *)
Definition reaches_harness : list (list byte) := [prog; Exit0Instance.path].
Definition refused_by_driver : list (list byte) := [prog].

(** The validity of the argument vectors, as [Exit0Instance] proves those
    of the exit0 toy's. *)
Lemma prog_no_nul : ~ In (Z_to_bv 8 0) prog.
Proof.
  unfold prog. intros H.
  repeat (destruct H as [H | H];
          [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H |]).
  destruct H.
Qed.

Lemma valid_argv_reaches_harness : valid_argv reaches_harness.
Proof.
  unfold valid_argv, reaches_harness.
  split; [split; apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split.
  { apply Forall_cons; [apply Z.leb_le; vm_compute; reflexivity |].
    apply Forall_cons; [apply Z.leb_le; vm_compute; reflexivity | apply Forall_nil]. }
  split.
  { apply Forall_cons; [exact prog_no_nul |].
    apply Forall_cons; [exact Exit0Instance.path_no_nul | apply Forall_nil]. }
  cbn [tl]. apply Forall_cons; [split; vm_compute; reflexivity | apply Forall_nil].
Qed.

Lemma valid_argv_refused_by_driver : valid_argv refused_by_driver.
Proof.
  unfold valid_argv, refused_by_driver.
  split; [split; apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split.
  { apply Forall_cons; [apply Z.leb_le; vm_compute; reflexivity | apply Forall_nil]. }
  split.
  { apply Forall_cons; [exact prog_no_nul | apply Forall_nil]. }
  cbn [tl]. apply Forall_nil.
Qed.

(** The launch bound, as [Exit0Instance.launch_argv] states it for the
    exit0 toy's inputs.  [Run.launch_bytes] reads the argv, the environment
    and the exec name of an input, never its file system or its abort
    declaration, so it is the same for every input here with argument
    vector [argv] ([launch_bytes_input], [launch_bytes_fin_input]). *)
Definition launch_argv (argv : list (list byte)) : Prop :=
  valid_argv argv /\ (launch_bytes (input false argv []) <= e2big_limit)%Z.

Lemma launch_bytes_input : forall abort argv data,
  launch_bytes (input abort argv data) = launch_bytes (input false argv []).
Proof. reflexivity. Qed.

Lemma launch_bytes_fin_input : forall argv data,
  launch_bytes (to_proc_input (fin_input argv data)) = launch_bytes (input false argv []).
Proof. reflexivity. Qed.

Lemma launch_argv_reaches_harness : launch_argv reaches_harness.
Proof.
  split; [exact valid_argv_reaches_harness |].
  apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma launch_argv_refused_by_driver : launch_argv refused_by_driver.
Proof.
  split; [exact valid_argv_refused_by_driver |].
  apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma input_launch : forall abort argv data, launch_argv argv -> valid_launch (input abort argv data).
Proof.
  intros abort argv data [_ Hl]. split; [exact Exit0Instance.default_execfn_valid |].
  rewrite launch_bytes_input. exact Hl.
Qed.

Lemma fin_input_launch : forall argv data, launch_argv argv ->
  valid_launch (to_proc_input (fin_input argv data)).
Proof.
  intros argv data [_ Hl]. split; [exact Exit0Instance.default_execfn_valid |].
  rewrite launch_bytes_fin_input. exact Hl.
Qed.

(** The validity of the inputs: the process input under each abort
    declaration, with its RV64GC word, and the finite input.  Each conjunct
    of the predicate, in [Run.valid_input]'s order, holds as
    [Exit0Instance.input_valid] proves it: argv and the launch from
    [launch_argv], the file system by [Exit0Instance]'s lemmas, and the
    fixed fields by computation.  The AT_HWCAP conjunct is the RV64GC
    equation or [valid_hwcap], and the abort declaration is the input's. *)
Local Ltac input_conjuncts argv data Hargv HL :=
  repeat match goal with |- _ /\ _ => split end;
  [ exact Hargv
  | exact Exit0Instance.valid_envp_nil
  | exact (Exit0Instance.valid_fs_file data)
  | exact (Exit0Instance.fs_keys_relative_file argv data)
  | exact (Exit0Instance.fs_image_real_file data)
  | unfold valid_creds, valid_id; split; apply Z.ltb_lt; vm_compute; reflexivity
  | unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity
  | unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity
  | first [reflexivity | unfold valid_hwcap; left; reflexivity]
  | reflexivity
  | reflexivity
  | unfold valid_urandom; exact State.default_urandom_infinite
  | exact HL
  | reflexivity
  | reflexivity
  | reflexivity ].

Lemma input_valid_rv64gc : forall argv data, launch_argv argv ->
  valid_input_hwcap_rv64gc (input false argv data).
Proof.
  intros argv data Hl. pose proof (input_launch false argv data Hl) as HL. destruct Hl as [Hargv _].
  unfold valid_input_hwcap_rv64gc. input_conjuncts argv data Hargv HL.
Qed.

Lemma input_valid_abort_rv64gc : forall argv data, launch_argv argv ->
  valid_input_abort_hwcap_rv64gc (input true argv data).
Proof.
  intros argv data Hl. pose proof (input_launch true argv data Hl) as HL. destruct Hl as [Hargv _].
  unfold valid_input_abort_hwcap_rv64gc. input_conjuncts argv data Hargv HL.
Qed.

Lemma input_valid : forall argv data, launch_argv argv -> valid_input (input false argv data).
Proof.
  intros argv data Hl.
  exact (valid_input_of_valid_input_hwcap_rv64gc _ (input_valid_rv64gc argv data Hl)).
Qed.

Lemma input_valid_abort : forall argv data, launch_argv argv -> valid_input_abort (input true argv data).
Proof.
  intros argv data Hl.
  exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _
           (input_valid_abort_rv64gc argv data Hl)).
Qed.

Lemma fin_input_valid : forall argv data, launch_argv argv -> valid_fin_input (fin_input argv data).
Proof.
  intros argv data Hl. pose proof (fin_input_launch argv data Hl) as HL. destruct Hl as [Hargv _].
  unfold valid_fin_input, valid_input. input_conjuncts argv data Hargv HL.
Qed.

Lemma fin_input_rv64gc : forall argv data,
  in_hwcap (to_proc_input (fin_input argv data)) = hwcap_rv64gc.
Proof. reflexivity. Qed.

(** Both builds have the valid entry [demo_entry_of inp] on every valid
    input [inp], under either abort declaration. *)
Lemma entries : forall inp, valid_input inp ->
  valid_entry Images.plain (demo_entry_of inp) inp /\ valid_entry Images.asan (demo_entry_of inp) inp.
Proof. intros inp Hv. exact (conj (demo_entry_valid_ebreak inp Hv) (demo_entry_valid_exit0 inp Hv)). Qed.

Lemma entries_abort : forall inp, valid_input_abort inp ->
  valid_entry Images.plain (demo_entry_of inp) inp /\ valid_entry Images.asan (demo_entry_of inp) inp.
Proof.
  intros inp Hv. exact (conj (demo_entry_valid_ebreak_abort inp Hv) (demo_entry_valid_exit0_abort inp Hv)).
Qed.

(** The plain build is never refused memory: its first instruction, an
    ebreak, faults from every initial machine state, whatever the stack
    pointer, the mmap base, the entry draw and the input, so the run ends
    at once, at no budget-refused configuration.  The run reads the image's
    segment, then the vDSO pair ([Run.run_segments]); the fetch is answered
    by the image's segment, so the pair is never computed, and the stack's
    contents are abstracted before computing, as in [Exit0Run].  At every
    budget, entry and input, unconfigured ([run]) and under every
    configuration ([run_scfg]). *)
Lemma plain_faults : forall sp mbase draw inp,
  RiscvSemantics.step (run_segments ebreak_segments inp sp mbase)
    (init_machine_state (run_segments ebreak_segments inp sp mbase) 0x100%N demo_phdrs
       sp mbase draw inp)
  = MachineFault.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state (run_segments ebreak_segments inp sp mbase) 0x100%N
                        demo_phdrs sp mbase draw inp)).
  intros mem. unfold run_segments. vm_compute. reflexivity.
Qed.

Lemma plain_not_budget_refused_at : forall sp mbase draw inp model,
  ~ budget_refused_at (run_segments ebreak_segments inp sp mbase)
      (mkCfg (init_machine_state (run_segments ebreak_segments inp sp mbase) 0x100%N demo_phdrs
                sp mbase draw inp) model).
Proof.
  intros sp mbase draw inp model
    (_ & [(_ & [(r & E & _) | (HU & _)]) | (x8 & Hx8 & _)]); cbn [cfg_ms cfg_model] in *.
  - match type of E with RiscvSemantics.step_accesses ?segs ?ms = _ =>
      pose proof (drop_step_accesses segs ms) as Hd end.
    rewrite E, plain_faults in Hd. discriminate Hd.
  - apply mi_account_step_unmodeled_inv in HU.
    match type of HU with RiscvSemantics.step_accesses ?segs ?ms = _ =>
      pose proof (drop_step_accesses segs ms) as Hd end.
    rewrite HU, plain_faults in Hd. discriminate Hd.
  - discriminate Hx8.
Qed.

Lemma plain_never_budget_refused : forall lim en inp, ~ run_budget_refused Images.plain lim en inp.
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  unfold run_budget_refused, Images.plain, ebreak_image, init_config. cbv zeta.
  intros (tr & c & Hstar & Hb).
  inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
  - exact (plain_not_budget_refused_at _ _ _ _ _ Hb).
  - apply sstep_fault_only in Hss;
      [| first [reflexivity | vm_compute; reflexivity]
       | first [reflexivity | vm_compute; reflexivity]
       | apply plain_faults].
    destruct Hss as (_ & Habs). discriminate Habs.
Qed.

Lemma plain_never_refused_cfg : forall cfg lim en inp,
  ~ run_scfg_budget_refused cfg Images.plain lim en inp.
Proof.
  intros cfg lim en inp H.
  exact (plain_never_budget_refused lim en inp (run_scfg_budget_refused_sub _ _ _ _ _ H)).
Qed.

(** ** The premises of each shape on these inputs

    For each agreement shape, at every budget and environment: valid
    entries of both builds, the input valid for the shape's predicate, and
    the plain build's run never refused memory.  For the bound and
    decidability shapes: the finite input valid, with the RV64GC word for
    the [_rv64gc] ones, and valid entries of both builds on it. *)
Lemma agrees_premises : forall lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input false argv data)
    /\ valid_entry Images.asan es (input false argv data)
    /\ valid_input (input false argv data)
    /\ ~ run_budget_refused Images.plain lim ep (input false argv data).
Proof.
  intros lim argv data Hl. pose proof (input_valid argv data Hl) as Hv.
  destruct (entries _ Hv) as [Hp Hs]. do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_budget_refused _ _ _)))).
Qed.

Lemma agrees_abort_modelled_premises : forall lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input true argv data)
    /\ valid_entry Images.asan es (input true argv data)
    /\ valid_input_abort (input true argv data)
    /\ ~ run_budget_refused Images.plain lim ep (input true argv data).
Proof.
  intros lim argv data Hl. pose proof (input_valid_abort argv data Hl) as Hv.
  destruct (entries_abort _ Hv) as [Hp Hs]. do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_budget_refused _ _ _)))).
Qed.

Lemma agrees_in_premises : forall env lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input false argv data)
    /\ valid_entry Images.asan es (input false argv data)
    /\ valid_input (input false argv data)
    /\ ~ run_scfg_budget_refused env Images.plain lim ep (input false argv data).
Proof.
  intros env lim argv data Hl. pose proof (input_valid argv data Hl) as Hv.
  destruct (entries _ Hv) as [Hp Hs]. do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_refused_cfg _ _ _ _)))).
Qed.

Lemma agrees_in_abort_modelled_premises : forall env lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input true argv data)
    /\ valid_entry Images.asan es (input true argv data)
    /\ valid_input_abort (input true argv data)
    /\ ~ run_scfg_budget_refused env Images.plain lim ep (input true argv data).
Proof.
  intros env lim argv data Hl. pose proof (input_valid_abort argv data Hl) as Hv.
  destruct (entries_abort _ Hv) as [Hp Hs]. do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_refused_cfg _ _ _ _)))).
Qed.

Lemma agrees_rv64gc_premises : forall lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input false argv data)
    /\ valid_entry Images.asan es (input false argv data)
    /\ valid_input_hwcap_rv64gc (input false argv data)
    /\ ~ run_budget_refused Images.plain lim ep (input false argv data).
Proof.
  intros lim argv data Hl. pose proof (input_valid_rv64gc argv data Hl) as Hv.
  destruct (entries _ (valid_input_of_valid_input_hwcap_rv64gc _ Hv)) as [Hp Hs].
  do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_budget_refused _ _ _)))).
Qed.

Lemma agrees_abort_modelled_rv64gc_premises : forall lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input true argv data)
    /\ valid_entry Images.asan es (input true argv data)
    /\ valid_input_abort_hwcap_rv64gc (input true argv data)
    /\ ~ run_budget_refused Images.plain lim ep (input true argv data).
Proof.
  intros lim argv data Hl. pose proof (input_valid_abort_rv64gc argv data Hl) as Hv.
  destruct (entries_abort _ (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv)) as [Hp Hs].
  do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_budget_refused _ _ _)))).
Qed.

Lemma agrees_in_rv64gc_premises : forall env lim argv data, launch_argv argv ->
  exists ep es, valid_entry Images.plain ep (input false argv data)
    /\ valid_entry Images.asan es (input false argv data)
    /\ valid_input_hwcap_rv64gc (input false argv data)
    /\ ~ run_scfg_budget_refused env Images.plain lim ep (input false argv data).
Proof.
  intros env lim argv data Hl. pose proof (input_valid_rv64gc argv data Hl) as Hv.
  destruct (entries _ (valid_input_of_valid_input_hwcap_rv64gc _ Hv)) as [Hp Hs].
  do 2 eexists.
  exact (conj Hp (conj Hs (conj Hv (plain_never_refused_cfg _ _ _ _)))).
Qed.

Lemma fin_premises : forall argv data, launch_argv argv ->
  valid_fin_input (fin_input argv data)
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input argv data))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input argv data))).
Proof.
  intros argv data Hl. pose proof (fin_input_valid argv data Hl) as Hv.
  destruct (entries _ Hv) as [Hp Hs].
  exact (conj Hv (ex_intro _ _ (ex_intro _ _ (conj Hp Hs)))).
Qed.

Lemma fin_premises_rv64gc : forall argv data, launch_argv argv ->
  valid_fin_input (fin_input argv data)
  /\ in_hwcap (to_proc_input (fin_input argv data)) = hwcap_rv64gc
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input argv data))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input argv data))).
Proof.
  intros argv data Hl. destruct (fin_premises argv data Hl) as [Hv He].
  exact (conj Hv (conj (fin_input_rv64gc argv data) He)).
Qed.
