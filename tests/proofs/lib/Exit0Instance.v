(** What the instance controls of the exit0 toy share (tests/instances/,
    tests/README.md): the process inputs an instance of a halts statement of
    [toy/exit0] names, and the premises of the two halts shapes on them.

    Each input is [oft check]'s rendering of an instance
    ([tools/oft/shapes.py], [instance_input]) for the argv0 "exit0" and the
    input file "input.bin" that the controls' instance.yaml files give: argv
    ["exit0"; "input.bin"] (path reaches-harness) or ["exit0"] (path
    refused-by-driver), no environment, one file "input.bin" with [data], end
    of input, and the other fields of [OSSVerify.Core.Premises.witness_input].
    [Run.valid_input] says nothing about a file's contents, so each input is
    valid for every [data].  It does bound the launch: [Run.valid_launch]
    asks that the argv strings, the environment strings and the exec name,
    with 8 bytes for each argv and envp pointer, fit under the E2BIG limit
    together, which [valid_argv] alone does not give.  So the lemmas below
    take [launch_argv argv]: [valid_argv argv] and that bound, which reads
    no file contents either.  The plain toy calls exit_group(0) at its third
    instruction and never asks for memory, so its run is never refused memory,
    at any budget, entry and input ([BudgetPremise.exits_c_no_budget_refused],
    as lps proves it of its own exit0 image). *)
From Stdlib Require Import ZArith List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From OSSVerify.Core Require Import Shapes Premises.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Exit0Run.
Import ListNotations.

(** The bytes of "exit0" and of "input.bin". *)
Definition prog : list byte :=
  [Z_to_bv 8 101; Z_to_bv 8 120; Z_to_bv 8 105; Z_to_bv 8 116; Z_to_bv 8 48].
Definition path : list byte :=
  [Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 112; Z_to_bv 8 117; Z_to_bv 8 116; Z_to_bv 8 46;
   Z_to_bv 8 98; Z_to_bv 8 105; Z_to_bv 8 110].

(** The input with argument vector [argv] whose file holds [data]. *)
Definition input (argv : list (list byte)) (data : list byte) : ProcInput :=
  mkProcInput argv [] [(path, data)] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48.

(** The argument vectors of the two paths. *)
Definition reaches_harness : list (list byte) := [prog; path].
Definition refused_by_driver : list (list byte) := [prog].

(** The file of the reaches-harness controls, 7 bytes and no NUL byte: the
    config word 01 80 (config length 1, and bit 15, counting mode), one config
    byte and the four bytes of the allocation mask, "AAAAA". *)
Definition seven : list byte :=
  [Z_to_bv 8 1; Z_to_bv 8 128; Z_to_bv 8 65; Z_to_bv 8 65; Z_to_bv 8 65; Z_to_bv 8 65; Z_to_bv 8 65].

(** The validity of the inputs, by the proof of curl fuzz_fnmatch's budget
    witness input ([projects/curl/fuzz_fnmatch/proofs/lib/BudgetWit/WitInput.v],
    [wit_valid_input]), for these argument vectors and any file contents. *)
Lemma prog_no_nul : ~ In (Z_to_bv 8 0) prog.
Proof.
  unfold prog. intros H.
  repeat (destruct H as [H | H];
          [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H |]).
  destruct H.
Qed.

Lemma path_no_nul : ~ In (Z_to_bv 8 0) path.
Proof.
  unfold path. intros H.
  repeat (destruct H as [H | H];
          [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H |]).
  destruct H.
Qed.

Lemma path_relative : key_is_relative path.
Proof.
  change (Z_to_bv 8 105 <> path_slash_byte). unfold path_slash_byte.
  intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
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
    apply Forall_cons; [exact path_no_nul | apply Forall_nil]. }
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

(** The launch bound.  [Run.launch_bytes] reads the argv, the environment
    and the exec name of an input, never its file system, so it is the same
    for every [data] ([launch_bytes_input]); [launch_argv] states it at the
    empty file. *)
Definition launch_argv (argv : list (list byte)) : Prop :=
  valid_argv argv /\ (launch_bytes (input argv []) <= e2big_limit)%Z.

Lemma launch_bytes_input : forall argv data,
  launch_bytes (input argv data) = launch_bytes (input argv []).
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

(** The exec name of every input, lps's [default_execfn] "a": one byte,
    not NUL, so a name [getname_flags] can return. *)
Lemma default_execfn_valid : valid_execfn default_execfn.
Proof.
  unfold valid_execfn, valid_path_name, default_execfn. left.
  split; [split; apply Z.leb_le; vm_compute; reflexivity |].
  intros H. destruct H as [H | []].
  apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
Qed.

Lemma input_launch : forall argv data, launch_argv argv -> valid_launch (input argv data).
Proof.
  intros argv data [_ Hl]. split; [exact default_execfn_valid |].
  rewrite launch_bytes_input. exact Hl.
Qed.

Lemma valid_envp_nil : valid_envp [].
Proof.
  unfold valid_envp.
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split; apply Forall_nil.
Qed.

Lemma valid_fs_file : forall data, valid_fs [(path, data)].
Proof.
  intros data. unfold valid_fs. split; [vm_compute; reflexivity |].
  apply Forall_cons; [exact path_no_nul | apply Forall_nil].
Qed.

Lemma fs_keys_relative_file : forall argv data, fs_keys_relative (in_image_fs (input argv data)).
Proof.
  intros argv data. unfold fs_keys_relative. apply Forall_cons; [exact path_relative | apply Forall_nil].
Qed.

(** The image is a real file system whatever the file holds: [fs_image_real]
    reads the keys only. *)
Lemma fs_image_real_file : forall data, fs_image_real [(path, data)] = true.
Proof. intros data. vm_compute. reflexivity. Qed.

(** Each conjunct of [Run.valid_input], in its order. *)
Lemma input_valid : forall argv data, launch_argv argv -> valid_input (input argv data).
Proof.
  intros argv data Hl. pose proof (input_launch argv data Hl) as HL. destruct Hl as [Hargv _].
  unfold valid_input. repeat match goal with |- _ /\ _ => split end.
  - exact Hargv.
  - exact valid_envp_nil.
  - exact (valid_fs_file data).
  - exact (fs_keys_relative_file argv data).
  - exact (fs_image_real_file data).
  - unfold valid_creds, valid_id. split; apply Z.ltb_lt; vm_compute; reflexivity.
  - unfold valid_nofile. apply Z.leb_le. vm_compute. reflexivity.
  - unfold valid_sigmask. apply bv_eq. vm_compute. reflexivity.
  - unfold valid_hwcap. left. reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold valid_urandom. exact State.default_urandom_infinite.
  - exact HL.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The plain toy is never refused memory: at every budget, entry and input,
    unconfigured ([run]) and under every configuration ([run_scfg]). *)
Lemma plain_never_budget_refused : forall lim en inp, ~ run_budget_refused Images.plain lim en inp.
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  unfold run_budget_refused, Images.plain, init_config.
  apply exits_c_no_budget_refused with (code := verdict_accept) (fuel := 8%nat);
    [reflexivity | reflexivity | apply Exit0Run.exit0_exits_c].
Qed.

Lemma plain_never_refused_cfg : forall cfg lim en inp,
  ~ run_scfg_budget_refused cfg Images.plain lim en inp.
Proof.
  intros cfg lim en inp.
  change (source_within_budget_scfg cfg lim Images.plain en inp).
  apply source_within_budget_scfg_of_source_within_budget.
  exact (plain_never_budget_refused lim en inp).
Qed.

(** The premises of [halts_within_budget] at the standard budget, and of
    [halts_may_fail], on [input argv data]: a valid entry, the input valid,
    and (for the first) the run never refused memory. *)
Lemma halts_within_budget_premises : forall argv data, launch_argv argv ->
  exists en, valid_entry Images.plain en (input argv data) /\ valid_input (input argv data)
    /\ ~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en
           (input argv data).
Proof.
  intros argv data Hl. pose proof (input_valid argv data Hl) as Hv.
  destruct (valid_input_entry Images.plain _ Images.plain_wf Hv) as [en Hen].
  exists en. exact (conj Hen (conj Hv (plain_never_refused_cfg _ _ en _))).
Qed.

Lemma halts_may_fail_premises : forall argv data, launch_argv argv ->
  exists en, valid_entry Images.plain en (input argv data) /\ valid_input (input argv data).
Proof.
  intros argv data Hl. pose proof (input_valid argv data Hl) as Hv.
  destruct (valid_input_entry Images.plain _ Images.plain_wf Hv) as [en Hen].
  exists en. exact (conj Hen Hv).
Qed.
