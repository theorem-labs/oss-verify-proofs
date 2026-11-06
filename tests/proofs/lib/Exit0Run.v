(** What the exit0 and exit1 proofs share: each toy program, from its entry
    point, runs its few instructions and reaches exit_group with a fixed
    status, whatever the kernel chose at execve and whatever the input is.

    lps's executable checker [Checks.Examples.exits_c] runs the machine until
    a system call is pending and checks that it is exit or exit_group with the
    given status.  The programs never read memory other than their own
    instructions, so the stack's contents are abstracted before computing, and
    [vm_compute] never builds them.  The rest turns that one computation into
    the facts the statements need, through lps's lemmas: every execution exits
    ([exits_c_must_exit_at_cfg]), none errs ([exits_c_exec]), the traces are
    exactly the prefixes of the exit event ([exec_obs_iff]), and no execution
    is refused memory for its budget ([exits_c_no_budget_refused]). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Classifier.
From OSSVerify.Tests.toy.exit0.images Require Plain Padded.
From OSSVerify.Tests.toy.exit1.images Require Plain.
Import ListNotations.

Module E0 := OSSVerify.Tests.toy.exit0.images.Plain.M.
Module E0P := OSSVerify.Tests.toy.exit0.images.Padded.M.
Module E1 := OSSVerify.Tests.toy.exit1.images.Plain.M.

Lemma exit0_exits_c : forall sp rnd argv envp uid hw,
  exits_c E0.loaded_segments verdict_accept 8
    (init_machine_state E0.loaded_segments E0.init_pc E0.phdrs sp rnd argv envp uid hw)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state E0.loaded_segments E0.init_pc E0.phdrs
                        sp rnd argv envp uid hw)).
  intros mem. vm_compute. reflexivity.
Qed.

Lemma padded_exits_c : forall sp rnd argv envp uid hw,
  exits_c E0P.loaded_segments verdict_accept 8
    (init_machine_state E0P.loaded_segments E0P.init_pc E0P.phdrs sp rnd argv envp uid hw)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state E0P.loaded_segments E0P.init_pc E0P.phdrs
                        sp rnd argv envp uid hw)).
  intros mem. vm_compute. reflexivity.
Qed.

Lemma exit1_exits_c : forall sp rnd argv envp uid hw,
  exits_c E1.loaded_segments verdict_reject 8
    (init_machine_state E1.loaded_segments E1.init_pc E1.phdrs sp rnd argv envp uid hw)
  = true.
Proof.
  intros. rewrite (with_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state E1.loaded_segments E1.init_pc E1.phdrs
                        sp rnd argv envp uid hw)).
  intros mem. vm_compute. reflexivity.
Qed.

(** The trace sets of the two exit0 programs: the prefixes of exit_group(0). *)
Lemma exit0_obs : forall sp brk0 mbase rnd lim inp tr,
  obs_trace E0.loaded_segments
    (init_config E0.loaded_segments E0.init_pc E0.phdrs sp brk0 mbase rnd lim inp) tr
  <-> is_prefix tr [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros. apply exec_obs_iff. eapply exec_conseq.
  - unfold init_config. apply (exits_c_exec _ verdict_accept 8); [reflexivity | reflexivity | apply exit0_exits_c].
  - intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma padded_obs : forall sp brk0 mbase rnd lim inp tr,
  obs_trace E0P.loaded_segments
    (init_config E0P.loaded_segments E0P.init_pc E0P.phdrs sp brk0 mbase rnd lim inp) tr
  <-> is_prefix tr [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros. apply exec_obs_iff. eapply exec_conseq.
  - unfold init_config. apply (exits_c_exec _ verdict_accept 8); [reflexivity | reflexivity | apply padded_exits_c].
  - intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit0_never_errors : forall sp brk0 mbase rnd lim inp,
  coexec E0.loaded_segments
    (init_config E0.loaded_segments E0.init_pc E0.phdrs sp brk0 mbase rnd lim inp) never_errors.
Proof.
  intros. apply exec_coexec. eapply exec_conseq.
  - unfold init_config. apply (exits_c_exec _ verdict_accept 8); [reflexivity | reflexivity | apply exit0_exits_c].
  - intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

Lemma padded_never_errors : forall sp brk0 mbase rnd lim inp,
  coexec E0P.loaded_segments
    (init_config E0P.loaded_segments E0P.init_pc E0P.phdrs sp brk0 mbase rnd lim inp) never_errors.
Proof.
  intros. apply exec_coexec. eapply exec_conseq.
  - unfold init_config. apply (exits_c_exec _ verdict_accept 8); [reflexivity | reflexivity | apply padded_exits_c].
  - intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
