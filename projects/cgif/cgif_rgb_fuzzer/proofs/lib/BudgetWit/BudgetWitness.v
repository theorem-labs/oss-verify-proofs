(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of YL0f.v's src2_realizes_spec, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the usage witness takes the launch premises valid_launch and entry_launch_ok_va and the run's channel-reader fact in place of entry_stack_fits, over the initial model carrying the entry's vDSO draw and the CONFIG_RSEQ-indexed main state; the budget walk is lifted by Rzb.rzb_run_init to the run's segment list with the vDSO appended; Vdso imported). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.cgif.cgif_rgb_fuzzer Require Images Statements.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YH04 YH05 YH07 YO3p YL0t.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.BudgetWit Require Import Rzb StartB UsageB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

(** * cgif / cgif_rgb_fuzzer: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build:
    - [plain_halts] ([halts_within_budget]):
      [~ run_scfg_budget_refused forced_only_cfg Images.plain
      Budgets.Standard.lim_source en inp];
    - [ubsan_agrees] ([agrees]):
      [~ run_budget_refused Images.plain Budgets.Standard.lim_source en inp];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees]):
      [~ run_budget_refused Images.plain Budgets.Asan.lim_source en inp].
    The three agreement statements are stated over the unfiltered run
    ([Run.run], [Run.run_budget_refused]), not under a spurious-failure
    configuration.  A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, unfiltered and under every configuration, for
    every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  On that path the program makes
    three kinds of system call: set_tid_address (96) in musl's start-up, writev (66)
    for the line, exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy ([m_vm_lazy = []]
    throughout), so no configuration the run reaches is refused by the budget.
    So the budget premise is non-vacuous; shown on the usage path, not yet on a
    fuzz input: this input never reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([YO3p.src2_start], the argc <> 2
    branch of [YL0f.src2_realizes_spec], [YL0t.src2_usage]) restated over
    [BudgetWit.Rzb.rzb], the released [YK15.realizes] with a budget check at each
    node ([BudgetWit.Rzb] says why [realizes] itself does not carry the fact).
    [usage_rzb] is that walk; [Rzb.rzb_never_refused] turns it into the unfiltered
    budget premise for every limit ([usage_never_refused_run]), and
    [Run.run_scfg_budget_refused_sub] into the configured one for every
    spurious-failure configuration ([usage_never_refused]).
    [plain_budget_witness] is [plain_halts]'s three premises at one entry and one
    input.  Each [<statement>_not_vacuous] gives the premises of one of the four
    statements at one input to the released proof of that statement (the term its
    [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at a
    point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 branch of [YL0f.src2_realizes_spec], over [rzb]: start-up
    ([StartB.src2_start_b]), then [main]'s usage path ([UsageB.src2_usage_b]). *)
Lemma usage_rzb : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
in_channel_reader inp = true ->
(length (in_argv inp) <> 2)%nat ->
rzb src2segs (init_config src2segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hcr Hlen.
apply (src2_start_b false sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau I).
intros ms tid Htid HS HR.
set (md := with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd))
(init_model (segments_reserved src2segs) brk mbase sp lim inp))).
assert (Hh : m_halted md = None) by reflexivity.
assert (Hlz : m_vm_lazy md = []) by reflexivity.
assert (Hfd2 : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md)
by (split; [reflexivity | split; [reflexivity | exact Hcr]]).
assert (HS' : st_ok src2segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd)
(add_cond (ss_main false (kb_rseq (in_kernel inp))) usage_cond) ms).
{ apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) 3)
= Z.of_nat (length (in_argv inp))) by (unfold E_main; eapply ew3; eassumption).
unfold branch_taken, usage_cond. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia. }
change (in_fs inp) with (m_fs md).
eapply (@src2_usage_b YK11.fx0); eassumption.
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration the unfiltered run reaches is refused by the
    budget, whatever the limit. *)
Theorem usage_never_refused_run : forall en inp,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (lim : Z),
~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen lim.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & _ & _ & _ & Hlau).
pose proof (valid_input_launch inp Hinp) as Hvl.
pose proof (valid_input_channel_reader inp Hinp) as Hcr.
destruct Hinp as (Hva & Hve & _).
(* LPS 727298f3: [Run.run_budget_refused] reads the run against [run_segments src2segs inp sp
   mbase] -- the binary's segments with the run's vDSO appended -- and from the start
   configuration over that list, while [usage_rzb] is a walk over the binary's own segments.
   [Rzb.rzb_run_init] lifts it, exactly as [RomStable.run_init] lifts the [realizes] walk;
   [vdso_image src2segs = None] by computation. *)
exact (rzb_never_refused _ _ _
(rzb_run_init src2segs inp sp mbase Plain_init_pc Plain_phdrs brk rnd lim _
ltac:(first [reflexivity | unfold vdso_image, vdso_text_seg; vm_compute; reflexivity])
(usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hcr Hlen))).
Qed.

(** ...and so under every spurious-failure configuration. *)
Theorem usage_never_refused : forall en inp,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en inp.
Proof.
intros en inp Hen Hinp Hlen cfg lim Hr.
exact (usage_never_refused_run en inp Hen Hinp Hlen lim
  (run_scfg_budget_refused_sub cfg OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en inp Hr)).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, unfiltered or under any configuration, whatever the limit. *)
Lemma plain_witness_entry : exists en,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en (Premises.witness_input false) /\
(forall (lim : Z),
 ~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en (Premises.witness_input false)) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en (Premises.witness_input false).
Proof.
destruct (Premises.valid_input_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain (Premises.witness_input false)
  OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain_wf Premises.witness_valid_input) as [en Hen].
exists en. split; [exact Hen | split].
- apply (usage_never_refused_run en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
- apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
exists en inp, valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
    Budgets.Standard.lim_source en inp.
Proof.
destruct plain_witness_entry as (en & Hen & _ & Hnr).
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.plain_halts], which the released
    [Theorems.halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain_forced_only] proves, at
    an entry and an input that meet all three of its premises: its conclusion holds
    there with no hypothesis left. *)
Theorem plain_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain
    Budgets.Standard.lim_source en inp.
Proof.
destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
assert (Hst : Statements.plain_halts)
  by exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.halts_allowed_cgif_cgif_rgb_fuzzer_halts_plain_forced_only.
exact (Hst en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false] (the pair
    [Premises.agrees_premises] builds, constructed here so that the input stays the
    witness input), with the unfiltered budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
exists en_plain en_san,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en_plain (Premises.witness_input false) /\
valid_entry san en_san (Premises.witness_input false) /\
forall (lim : Z),
~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain lim en_plain (Premises.witness_input false).
Proof.
intros san Hwf.
destruct plain_witness_entry as (en_plain & Hep & Hnr & _).
destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
  as [en_san Hes].
exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_cgif_rgb_fuzzer_ubsan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en_plain inp /\
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan en_san inp /\
valid_input inp /\
~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Standard.lim_source en_plain inp /\
error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Standard.lim_source en_plain inp)
/\ error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan Budgets.Standard.lim_target en_san inp)
/\ trace_equiv (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Standard.lim_source en_plain inp))
               (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan Budgets.Standard.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan_wf)
  as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
assert (Hst : Statements.ubsan_agrees)
  by exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.strong_universal_error_free_cgif_rgb_fuzzer_ubsan.
exact (Hst ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_cgif_rgb_fuzzer_asan] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en_plain inp /\
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan en_san inp /\
valid_input inp /\
~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp /\
error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp)
/\ error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp))
               (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_wf)
  as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
assert (Hst : Statements.asan_agrees)
  by exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.strong_universal_error_free_cgif_rgb_fuzzer_asan.
exact (Hst ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_cgif_rgb_fuzzer_both] proves, at entries
    and an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain en_plain inp /\
valid_entry OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_ubsan en_san inp /\
valid_input inp /\
~ run_budget_refused OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp /\
error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp)
/\ error_free (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_ubsan Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain Budgets.Asan.lim_source en_plain inp))
               (bh_traces (run OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_ubsan Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_ubsan
  OSSVerify.cgif.cgif_rgb_fuzzer.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
assert (Hst : Statements.asan_ubsan_agrees)
  by exact OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.Theorems.strong_universal_error_free_cgif_rgb_fuzzer_both.
exact (Hst ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.
