(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branches of RefMain.v's ref_realizes_spec_lim, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the witness reads the launch conjunct and the channel reader from its premises, applies the vDSO bridge (Rzb.rzb_with_vdso_no_text) and lifts the walk to the run's segments (rzb_run_init). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.coturn.FuzzStunClient Require Images Statements.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Theorems.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Halts.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import Rzb RefStartupB RefUsageB.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg Require RomStable.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommute VdsoCommuteSys.
Import ListNotations.
Open Scope Z_scope.

(** * coturn / FuzzStunClient: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build:
    - [plain_halts] ([halts_within_budget]):
      [~ run_scfg_budget_refused forced_only_cfg Images.plain lim en inp] at
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees]): [~ run_budget_refused Images.plain lim en inp]
      at [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees]): the same at
      [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc =
    1), no environment, an empty file system.  With argc <> 2 the driver's
    [main] writes its usage line to fd 2 and exits with status 2.  On that path
    the program makes three kinds of system call: set_tid_address (96) in musl's
    start-up, writev (66) for the line, exit or exit_group (93, 94).  None is an
    allocation call (brk 214, mremap 216, mmap 222, mprotect 226), so no
    configuration the run reaches is refused by the budget.  This shows the
    budget premise satisfiable on the usage path, not yet on an input that
    reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([RefStartup.ref_startup], the
    argc <> 2 branches of [RefMain.ref_realizes_spec_lim],
    [RefUsage.ref_usage_w]) restated over [BudgetWit.Rzb.rzb], the released
    [Common.ShapeAlg.realizes] with a no-allocation-call check at each node
    ([BudgetWit.Rzb] says why [realizes] itself cannot carry the fact).
    [usage_rzb] is that walk; [Rzb.rzb_never_refused] and
    [Rzb.rzb_never_refused_cfg] turn it into the budget premise, for the
    unconfigured run and for every spurious-failure configuration, at every
    limit ([usage_never_refused_run], [usage_never_refused]).  Each
    [<statement>_not_vacuous] gives the premises of one of the four statements
    at one input to the released proof of that statement (the term its
    [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at a
    point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 branches of [RefMain.ref_realizes_spec_lim], over [rzb]:
    start-up ([RefStartupB.ref_startup_b]), bridge (A) for the launch's vDSO draw
    ([Rzb.rzb_with_vdso_no_text], as [RefMain] applies [VdsoBridge.realizes_with_vdso_no_text]),
    then [main]'s usage path ([RefUsageB.ref_usage_w_b]).  The walk is over the binary's own
    segments; [usage_never_refused] lifts it to the run's. *)
Lemma usage_rzb : forall sp brk mbase rdraw lim inp,
  valid_entry (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkEntry sp brk mbase rdraw) inp ->
  valid_input inp -> (length (in_argv inp) <> 2)%nat ->
  rzb Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rdraw lim inp)
    (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw lim inp VE VI Hlen.
  pose proof (valid_input_va_size _ VI) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE.
  (* LPS 727298f3: [valid_entry]'s Sv48 form ends with the launch conjunct, and the start-up
     walk reads it and [Run.valid_input]'s [valid_launch]; the usage walk's stderr write reads
     the channel reader [Run.valid_input] pins.  All three come from the premises here. *)
  destruct VE as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  pose proof (valid_input_launch _ VI) as Hvl.
  pose proof (valid_input_channel_reader _ VI) as Hcr.
  destruct VI as (Hva & Hve & Hfs & _).
  apply (ref_startup_b sp brk mbase rdraw lim inp _ Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  (* Bridge (A), as [RefMain.ref_realizes_spec_lim]: the hand-off model carries the launch's
     vDSO draw and the usage walk is stated without it; over the image's own segments there is
     no vDSO text. *)
  rewrite VdsoCommute.with_tid_with_vdso.
  lazymatch goal with |- rzb ?s (mkCfg ?ms (with_vdso ?v ?m)) ?T =>
    change (rzb s (VdsoCommuteSys.cfg_with_vdso v (mkCfg ms m)) T) end.
  apply (rzb_with_vdso_no_text Plain.M.loaded_segments ltac:(reflexivity)).
  rewrite (init_model_of _ _ _ _ _ inp).
  (* the launch's channel reader, as the Amb the usage walk reads it from (Amb.v:59) *)
  assert (Hrdr0 : @a_channel_reader (amb_of inp) = true) by exact Hcr.
  (* the section's variables by position, its hypotheses by [eassumption] (see RefLeafDir) *)
  eapply (@ref_usage_w_b (amb_of inp) sp (in_argv inp) (in_envp inp) rdraw tid regs mem brk mbase
            (in_fs inp) (in_stdin inp) lim); eassumption.
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and whatever the limit.
    LPS 08b1429: [Run.run_scfg_budget_refused] reads the run over
    [run_segments Plain.M.loaded_segments inp sp mbase] and from the start configuration over
    that list, so [Rzb.rzb_run_init] lifts [usage_rzb], as [RefMain.ref_realizes_spec] lifts
    the [realizes] walk; [vdso_image Plain.M.loaded_segments = None] by computation. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.coturn.FuzzStunClient.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rdraw] inp Hen Hinp Hlen cfg lim.
  assert (Hnone : vdso_image Plain.M.loaded_segments = None)
    by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
  exact (rzb_never_refused_cfg _ cfg _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase Plain.M.init_pc Plain.M.phdrs brk rdraw lim _
              Hnone (usage_rzb sp brk mbase rdraw lim inp Hen Hinp Hlen))).
Qed.

(** The same for the unconfigured run ([Run.run_budget_refused]), the form
    the agreement statements use. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (lim : Z),
  ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rdraw] inp Hen Hinp Hlen lim.
  assert (Hnone : vdso_image Plain.M.loaded_segments = None)
    by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
  exact (rzb_never_refused _ _ _
           (rzb_run_init Plain.M.loaded_segments inp sp mbase Plain.M.init_pc Plain.M.phdrs brk rdraw lim _
              Hnone (usage_rzb sp brk mbase rdraw lim inp Hen Hinp Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en (Premises.witness_input false) /\
  (forall (cfg : SpuriousCfg) (lim : Z),
     ~ run_scfg_budget_refused cfg OSSVerify.coturn.FuzzStunClient.Images.plain lim en
         (Premises.witness_input false)) /\
  (forall (lim : Z),
     ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain lim en
         (Premises.witness_input false)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.coturn.FuzzStunClient.Images.plain
              (Premises.witness_input false) OSSVerify.coturn.FuzzStunClient.Images.plain_wf
              Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen | split].
  - apply (usage_never_refused en _ Hen Premises.witness_valid_input). cbn. discriminate.
  - apply (usage_never_refused_run en _ Hen Premises.witness_valid_input). cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at
    [Premises.witness_input false] and the entry [Premises.valid_input_entry]
    gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.coturn.FuzzStunClient.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr & _).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.plain_halts], which the released
    [Corpus.Halts.coturn_fuzzstunclient_plain_halts] proves, at an entry and an
    input that meet all three of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem plain_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.coturn.FuzzStunClient.Images.plain
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.coturn.FuzzStunClient.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact ((OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus.Halts.coturn_fuzzstunclient_plain_halts
          : OSSVerify.coturn.FuzzStunClient.Statements.plain_halts) en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false],
    constructed here so that the input stays the witness input, with the budget
    premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (lim : Z),
  ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain lim en_plain
      (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & _ & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzstunclient_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en_plain inp /\
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp /\
  (error_free (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp)
   /\ error_free (run OSSVerify.coturn.FuzzStunClient.Images.asan Budgets.Asan.lim_target en_san inp)
   /\ trace_equiv (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp))
                  (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.asan Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct (agree_witness OSSVerify.coturn.FuzzStunClient.Images.asan
              OSSVerify.coturn.FuzzStunClient.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.strong_universal_error_free_fuzzstunclient_asan
          : OSSVerify.coturn.FuzzStunClient.Statements.asan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzstunclient_ubsan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en_plain inp /\
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Standard.lim_source en_plain inp /\
  (error_free (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Standard.lim_source en_plain inp)
   /\ error_free (run OSSVerify.coturn.FuzzStunClient.Images.ubsan Budgets.Standard.lim_target en_san inp)
   /\ trace_equiv (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Standard.lim_source en_plain inp))
                  (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.ubsan Budgets.Standard.lim_target en_san inp))).
Proof.
  destruct (agree_witness OSSVerify.coturn.FuzzStunClient.Images.ubsan
              OSSVerify.coturn.FuzzStunClient.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.strong_universal_error_free_fuzzstunclient_ubsan
          : OSSVerify.coturn.FuzzStunClient.Statements.ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzzstunclient_both] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.plain en_plain inp /\
  valid_entry OSSVerify.coturn.FuzzStunClient.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp /\
  (error_free (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp)
   /\ error_free (run OSSVerify.coturn.FuzzStunClient.Images.asan_ubsan Budgets.Asan.lim_target en_san inp)
   /\ trace_equiv (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.plain Budgets.Asan.lim_source en_plain inp))
                  (bh_traces (run OSSVerify.coturn.FuzzStunClient.Images.asan_ubsan Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct (agree_witness OSSVerify.coturn.FuzzStunClient.Images.asan_ubsan
              OSSVerify.coturn.FuzzStunClient.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.coturn.FuzzStunClient.lib.Theorems.strong_universal_error_free_fuzzstunclient_both
          : OSSVerify.coturn.FuzzStunClient.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.
