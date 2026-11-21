(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/U1UsageTop.v's u1_usage_top, over BudgetWit.SRealizes.srealizes; adds the budget-premise witness for the UBSan build and the lemma that applies the released proof of ubsan_halts there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; the usage walk lifted to the run's segments, run_segments, from the run's own start). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer Require Images Statements.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ShapeAlg ArgvEnv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit Require Import SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import U1UsageTop.
Import ListNotations.
Open Scope Z_scope.

(** * spirv-tools / spvtools_binary_parser_fuzzer: the budget premise on the UBSan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget]), at [forced_only_cfg] and
    [Budgets.Standard.lim_source].  (The agreement statements carry theirs on the
    plain build; [BudgetWit.BudgetWitness] ties those off.)  This file gives that
    premise for this build, for every configuration and every limit, and applies the
    released proof of [ubsan_halts] at a point that meets all its premises.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  The UBSan build's start-up and
    usage path are the plain build's at other addresses: the released tree proves
    them in [Drv/U1*.v], the files [Drv/S1*.v] are for the plain build, and the
    image-independent modules are shared.  On that path the program makes
    set_tid_address (96), writev (66), exit or exit_group (93, 94), no allocation
    call and no lazy mapping, so no configuration the run reaches is refused by the
    budget.  This shows the budget premise satisfiable on the usage path, not yet on
    an input that reaches [LLVMFuzzerTestOneInput].

    The proof is [BudgetWit.BudgetWitness]'s at the UBSan build's walk:
    [BudgetWit.Drv.U1UsageTop.u1_usage_top] and the [BudgetWit.Drv.U1*] files it
    imports are the released [Drv/U1*] files over [BudgetWit.SRealizes.srealizes];
    [BudgetWit.SRealizes] and the other image-independent twins are shared with the
    plain build, since [srealizes] and its soundness are stated for every segment
    list. *)

(** On every valid entry of the UBSan build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & _ & _ & Hfits & Hlau).
  pose proof (valid_input_channel_reader _ Hinp) as Hrd.
  assert (Hvl : valid_launch inp) by (clear - Hinp; unfold valid_input in Hinp; tauto).
  destruct Hinp as (Hva & Hve & _).
  (* LPS 08b1429: the walk lifted to the run's segments, as in [BudgetWit.BudgetWitness]. *)
  exact (srz_never_refused_cfg _ cfg _ _
           (SRealizes.srun_init M.loaded_segments inp sp mbase M.init_pc M.phdrs brk rnd lim _ eq_refl
              (u1_usage_top sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hrd Hlen))).
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan en inp /\ valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
        Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
              (Premises.witness_input false) OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan_wf
              Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_ubsan]
    proves, at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp,
    valid_entry OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan en inp /\ valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
        Budgets.Standard.lim_source en inp /\
    must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.Images.ubsan
        Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Theorems.halts_allowed_spirv_tools_spvtools_binary_parser_fuzzer_halts_ubsan
           en inp Hen Hinp Hnr).
Qed.
