From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.libdiginet.fuzz_codec Require Images Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Theorems.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD2o.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YD2o.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit Require BudgetWitness.

(** * libdiginet / fuzz_codec: the three agreement statements are not vacuous

    [Statements.ubsan_agrees], [asan_agrees] and [asan_ubsan_agrees] are
    [agrees_in Env.alloc_forced_only lim_plain lim_san Images.plain san]: for every
    entry of each build and every input, with four premises, [valid_entry
    Images.plain en_plain inp], [valid_entry san en_san inp], [valid_input inp] and
    the budget premise [~ run_scfg_budget_refused Env.alloc_forced_only
    Images.plain lim_plain en_plain inp], which is on the plain build only.

    [BudgetWit.BudgetWitness.usage_never_refused] gives the budget premise of the
    plain build for every spurious-failure configuration and every limit, at every
    valid entry and every valid input whose argv has not two entries;
    [Premises.valid_input_entry] gives a valid entry of each build at
    [Premises.witness_input false] (argc = 1).  So each lemma below takes those, and
    applies the released proof of the statement (the term its [Proof.v] gives:
    [Theorems.libdiginet_fuzz_codec_ubsan_agrees], [A.AD2o.codec_asan_agrees_closed],
    [AU.YD2o.codec_asan_ubsan_agrees_closed]) there: the statement's conclusion
    holds at a pair of entries and an input that meet all four of its premises,
    with no hypothesis left. *)

(** The plain build's half: one entry of the plain build at
    [Premises.witness_input false], at which no limit and no spurious-failure
    configuration makes the run refused by the budget. *)
Lemma plain_entry_never_refused :
exists en, valid_entry OSSVerify.libdiginet.fuzz_codec.Images.plain en (Premises.witness_input false) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.libdiginet.fuzz_codec.Images.plain lim en (Premises.witness_input false).
Proof.
destruct (Premises.valid_input_entry OSSVerify.libdiginet.fuzz_codec.Images.plain (Premises.witness_input false)
  OSSVerify.libdiginet.fuzz_codec.Images.plain_wf Premises.witness_valid_input) as [en Hen].
exists en. split; [exact Hen |].
intros cfg lim.
apply (BudgetWitness.usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.

(** [Statements.ubsan_agrees] at a pair of entries and an input that meet all four
    of its premises. *)
Theorem ubsan_agrees_not_vacuous :
exists (en_plain en_san : ExecEntry) (inp : ProcInput),
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.plain en_plain inp /\
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.ubsan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Standard.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Standard.lim_source en_plain inp) /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.ubsan
    Budgets.Standard.lim_target en_san inp) /\
trace_equiv
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Standard.lim_source en_plain inp))
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.ubsan
    Budgets.Standard.lim_target en_san inp)).
Proof.
destruct (Premises.valid_input_entry OSSVerify.libdiginet.fuzz_codec.Images.ubsan (Premises.witness_input false)
  OSSVerify.libdiginet.fuzz_codec.Images.ubsan_wf Premises.witness_valid_input) as [ens Hs].
destruct plain_entry_never_refused as (enp & Hp & Hnr).
exists enp, ens, (Premises.witness_input false).
split; [exact Hp |].
split; [exact Hs |].
split; [exact Premises.witness_valid_input |].
split; [exact (Hnr _ _) |].
exact (OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Theorems.libdiginet_fuzz_codec_ubsan_agrees
  enp ens (Premises.witness_input false) Hp Hs Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees] at a pair of entries and an input that meet all four
    of its premises. *)
Theorem asan_agrees_not_vacuous :
exists (en_plain en_san : ExecEntry) (inp : ProcInput),
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.plain en_plain inp /\
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.asan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp) /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.asan
    Budgets.Asan.lim_target en_san inp) /\
trace_equiv
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp))
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.asan
    Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (Premises.valid_input_entry OSSVerify.libdiginet.fuzz_codec.Images.asan (Premises.witness_input false)
  OSSVerify.libdiginet.fuzz_codec.Images.asan_wf Premises.witness_valid_input) as [ens Hs].
destruct plain_entry_never_refused as (enp & Hp & Hnr).
exists enp, ens, (Premises.witness_input false).
split; [exact Hp |].
split; [exact Hs |].
split; [exact Premises.witness_valid_input |].
split; [exact (Hnr _ _) |].
exact (OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.AD2o.codec_asan_agrees_closed
  enp ens (Premises.witness_input false) Hp Hs Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees] at a pair of entries and an input that meet all
    four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
exists (en_plain en_san : ExecEntry) (inp : ProcInput),
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.plain en_plain inp /\
valid_entry OSSVerify.libdiginet.fuzz_codec.Images.asan_ubsan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp) /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.asan_ubsan
    Budgets.Asan.lim_target en_san inp) /\
trace_equiv
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.plain
    Budgets.Asan.lim_source en_plain inp))
  (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libdiginet.fuzz_codec.Images.asan_ubsan
    Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (Premises.valid_input_entry OSSVerify.libdiginet.fuzz_codec.Images.asan_ubsan (Premises.witness_input false)
  OSSVerify.libdiginet.fuzz_codec.Images.asan_ubsan_wf Premises.witness_valid_input) as [ens Hs].
destruct plain_entry_never_refused as (enp & Hp & Hnr).
exists enp, ens, (Premises.witness_input false).
split; [exact Hp |].
split; [exact Hs |].
split; [exact Premises.witness_valid_input |].
split; [exact (Hnr _ _) |].
exact (OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.YD2o.codec_asan_ubsan_agrees_closed
  enp ens (Premises.witness_input false) Hp Hs Premises.witness_valid_input (Hnr _ _)).
Qed.
