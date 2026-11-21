(** Refutation of OSSVerify.Tests.toy.exit1.Statements.plain_halts.

    Outline.  Take one valid input (one empty argument, nothing else) and one
    valid entry (the stack where lps's launch puts it for that input, the
    break just above the program).  The program is never refused memory
    ([Checks.BudgetPremise.exits_c_no_budget_refused]), so the statement
    applies, and says every execution exits with 0 or 2.  But the program's
    one execution exits with 1 ([Exit0Run.exit1_exits_c]), and a statement
    that holds of a configuration holds of every configuration it reaches,
    including the halted one, where the status must be allowed. *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples SpuriousCfg BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit HaltsAllowed Classifier.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit1 Require Statements Images.
From OSSVerify.Tests.proofs.lib Require Exit0Run.
Import ListNotations.

Definition input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** The entry lps's launch computes for [input] ([Run.launch_entry_va]), as
    [Checks.Examples.demo_entry_of] does, with the break one page above the
    program's reservation rather than at 0x1000. *)
Definition entry : ExecEntry :=
  launch_entry_va (in_va_size input) input (Z_to_bv 64 0x11000) demo_random vdso_keeps_all.

Lemma entry_valid : valid_entry Images.plain entry input.
Proof.
  pose proof demo_input_valid as Hvalid.
  red in Hvalid.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold valid_entry, entry, Images.plain.
  apply launch_entry_va_valid; try assumption.
  unfold valid_brk.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Theorem plain_halts_refuted : ~ Statements.plain_halts.
Proof.
  unfold Statements.plain_halts. intros H.
  assert (Hb : ~ run_scfg_budget_refused forced_only_cfg Images.plain
                 Budgets.Standard.lim_source entry input).
  { intros Hr. apply run_scfg_budget_refused_sub in Hr. revert Hr.
    unfold run_budget_refused, Images.plain. rewrite (entry_eta entry).
    cbn beta iota zeta. unfold init_config.
    apply exits_c_no_budget_refused with (code := verdict_reject) (fuel := 8%nat);
      [reflexivity | reflexivity | apply Exit0Run.exit1_exits_c]. }
  specialize (H entry input entry_valid demo_input_valid Hb).
  unfold Images.plain in H. rewrite (entry_eta entry) in H.
  cbn beta iota zeta delta [must_exit_in_scfg] in H.
  assert (Hme : must_exit_at_cfg forced_only_cfg
                  (run_segments Exit0Run.E1.loaded_segments input (en_sp entry) (en_mmap_base entry))
                  verdict_reject
                  (init_config
                     (run_segments Exit0Run.E1.loaded_segments input (en_sp entry) (en_mmap_base entry))
                     Exit0Run.E1.init_pc Exit0Run.E1.phdrs
                     (en_sp entry) (en_brk entry) (en_mmap_base entry) (en_draw entry)
                     Budgets.Standard.lim_source input)).
  { unfold init_config. apply (exits_c_must_exit_at_cfg _ _ _ 8);
      [reflexivity | reflexivity | apply Exit0Run.exit1_exits_c]. }
  destruct (must_exit_at_cfg_realizes _ _ _ _ Hme eq_refl) as (tr & fs & c' & Hstar & Hh).
  pose proof (must_exit_in_at_cfg_star _ _ _ _ _ _ H Hstar) as Hc'.
  destruct (must_exit_in_at_cfg_halted_inv _ _ _ _ _ Hc' Hh) as (Hin & _).
  apply In_status_allowed in Hin. vm_compute in Hin. discriminate.
Qed.
