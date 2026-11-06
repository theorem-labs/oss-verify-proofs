(** Refutation of OSSVerify.Tests.toy.exit1.Statements.plain_halts.

    Outline.  Take one valid input (one empty argument, nothing else) and one
    valid entry (the stack at the bottom of its window, the break just above
    the program).  The program is never refused memory
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

Definition entry : ExecEntry :=
  mkEntry (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x11000) (Z_to_bv 64 mmap_base_max) demo_draw.

Lemma entry_valid : valid_entry Images.plain entry input.
Proof.
  pose proof demo_input_valid as Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [Images.plain entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Theorem plain_halts_refuted : ~ Statements.plain_halts.
Proof.
  unfold Statements.plain_halts. intros H.
  assert (Hb : ~ run_scfg_budget_refused forced_only_cfg Images.plain
                 Budgets.Standard.lim_source entry input).
  { intros Hr. apply run_scfg_budget_refused_sub in Hr. revert Hr.
    unfold run_budget_refused, Images.plain, entry, init_config.
    apply exits_c_no_budget_refused with (code := verdict_reject) (fuel := 8%nat);
      [reflexivity | reflexivity | apply Exit0Run.exit1_exits_c]. }
  specialize (H entry input entry_valid demo_input_valid Hb).
  unfold Images.plain, entry in H. cbn [must_exit_in_scfg] in H.
  assert (Hme : must_exit_at_cfg forced_only_cfg Exit0Run.E1.loaded_segments verdict_reject
                  (init_config Exit0Run.E1.loaded_segments Exit0Run.E1.init_pc Exit0Run.E1.phdrs
                     (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x11000) (Z_to_bv 64 mmap_base_max)
                     demo_draw Budgets.Standard.lim_source input)).
  { unfold init_config. apply (exits_c_must_exit_at_cfg _ _ _ 8);
      [reflexivity | reflexivity | apply Exit0Run.exit1_exits_c]. }
  destruct (must_exit_at_cfg_realizes _ _ _ _ Hme eq_refl) as (tr & fs & c' & Hstar & Hh).
  pose proof (must_exit_in_at_cfg_star _ _ _ _ _ _ H Hstar) as Hc'.
  destruct (must_exit_in_at_cfg_halted_inv _ _ _ _ _ Hc' Hh) as (Hin & _).
  apply In_status_allowed in Hin. vm_compute in Hin. discriminate.
Qed.
