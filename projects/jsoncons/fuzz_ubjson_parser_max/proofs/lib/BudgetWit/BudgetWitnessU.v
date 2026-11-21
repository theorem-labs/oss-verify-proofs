(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of Ju0DrvMain.v's ub0_realizes_spec, over BudgetWit.SpinAlgB.rzb; adds the budget-premise witness for the UBSan build and the lemma that applies the released proof of the statement whose budget premise is on the UBSan build. *)
(* Modified by Theorem Labs, 2026-11: usage_rzb_u and usage_never_refused_u take the launch facts valid_launch, entry_launch_ok_va and in_channel_reader, run over the vDSO-initialised model and lift the walk to the run's segments with rzb_run_init, as BudgetWitness.v does for the plain build. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Images Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv PropExec ShapeAlg SpinAlg Spec
  Ju0Startup Ju0MainEntry Ju0Usage.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Theorems.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import SpinAlgB Ju0StartupB Ju0UsageB.
Import ListNotations.

(** * jsoncons / fuzz_ubjson_parser_max: the budget premise on the UBSan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget], [forced_only_cfg],
    [Budgets.Standard.lim_source], [Images.ubsan]).  This file gives that
    premise for this build at [Premises.witness_input false], for every
    configuration and every limit, and applies the released proof of
    [ubsan_halts] there.

    The argument is [BudgetWitness.v]'s for the plain build, on the UBSan
    build's own released walk: [Ju0Startup.ref_startup], the argc <> 2 arms of
    [Ju0DrvMain.ub0_realizes_spec] and [Ju0Usage.ref_usage_w], restated over
    [BudgetWit.SpinAlgB.rzb] at [may_fail_cfg] ([Ju0StartupB], [Ju0UsageB] and
    the files they import, generated from the released [Ju0*] files themselves,
    so every address in them is the UBSan build's own).  On the usage path the
    program makes only set_tid_address (96), writev (66) and exit/exit_group
    (93, 94), none an allocation call, and no mapping is lazy.  This shows the
    budget premise satisfiable on the usage path, not yet on an input that
    reaches [LLVMFuzzerTestOneInput]. *)

#[local] Existing Instance PropExec.fx0.

Lemma usage_rzb_u : forall sp brk mbase (rdraw : EntryDraw) (lim : Z) (inp : ProcInput),
  valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  in_channel_reader inp = true ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb Ubsan.M.loaded_segments may_fail_cfg
    (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rdraw lim inp)
    (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw lim inp Hsp Hbrk Hvl Hlau Hrd Hva Hve Hargc.
  apply ref_startup_b; try assumption.
  intros tid regs mem Htid ME.
  rewrite with_tid_with_vdso_init_model_E.
  set (RE := run_env_at inp (Vdso.vdso_run_init (ed_vdso rdraw))).
  assert (RO : @ReaderOn RE) by exact Hrd.
  clearbody RE.
  exact (ref_usage_w_b may_fail_cfg sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem
           brk mbase (in_fs inp) (in_stdin inp) lim Hva Hve Hsp Htid inp _ ME Hargc).
Qed.

(** On every valid entry of the UBSan build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused_u : forall en inp,
  valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  pose proof (valid_input_launch _ Hinp) as Hvl.
  pose proof (valid_input_channel_reader _ Hinp) as Hrd.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & _ & Hlau).
  destruct Hinp as (Hva & Hve & _).
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init may_fail_cfg Ubsan.M.loaded_segments inp sp mbase
              Ubsan.M.init_pc Ubsan.M.phdrs brk rnd lim _ eq_refl
              (usage_rzb_u sp brk mbase rnd lim inp Hsp Hbrk Hvl Hlau Hrd Hva Hve Hlen))).
Qed.

Lemma ubsan_witness_entry : exists en,
  valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan lim en
      (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
              (Premises.witness_input false)
              OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused_u en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The budget premise of the UBSan group at one entry and one input. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_jsoncons_fuzz_ubjson_parser_max_halts_ubsan] proves,
    at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp,
  valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan en inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]].
  exact ((OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_parser_max_halts_ubsan
            : OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_halts)
           en (Premises.witness_input false) Hen Premises.witness_valid_input (Hnr _ _)).
Qed.
