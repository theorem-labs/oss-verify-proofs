(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of Js0DrvMain.v's src0_realizes_spec, over BudgetWit.SpinAlgB.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build. *)
(* Modified by Theorem Labs, 2026-11: usage_rzb and the usage_never_refused theorems now take valid_launch, entry_launch_ok_va and channel-reader premises and use the vDSO init model and rzb_run_init, as in fuzz_bigint's copy; explanatory comments and indentation removed; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/BudgetWitness.v, 21 lines within its lines 73-146. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max Require Images Statements.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv PropExec ShapeAlg SpinAlg Spec
Js0Startup Js0MainEntry Js0Usage.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Theorems.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import SpinAlgB Js0StartupB Js0UsageB.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Lemma usage_rzb : forall sp brk mbase (rdraw : EntryDraw) (lim : Z) (inp : ProcInput),
valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
in_channel_reader inp = true ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
(length (in_argv inp) <> 2)%nat ->
rzb Plain.M.loaded_segments may_fail_cfg
(init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rdraw lim inp)
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
Theorem usage_never_refused_sv48 : forall en inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp ->
in_va_size inp = Sv48 -> valid_launch inp -> in_channel_reader inp = true ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hv Hvl Hrd Hva Hve Hlen cfg lim.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & Hbrk & _ & _ & Hlau).
exact (rzb_never_refused_cfg _ cfg _ _
(rzb_run_init may_fail_cfg Plain.M.loaded_segments inp sp mbase
Plain.M.init_pc Plain.M.phdrs brk rnd lim _ eq_refl
(usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hvl Hlau Hrd Hva Hve Hlen))).
Qed.
Theorem usage_never_refused : forall en inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en inp.
Proof.
intros en inp Hen Hinp Hlen.
pose proof (valid_input_va_size _ Hinp) as Hv.
pose proof (valid_input_launch _ Hinp) as Hvl.
pose proof (valid_input_channel_reader _ Hinp) as Hrd.
destruct Hinp as (Hva & Hve & _).
exact (usage_never_refused_sv48 en inp Hen Hv Hvl Hrd Hva Hve Hlen).
Qed.
Theorem usage_never_refused_abort : forall en inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp -> valid_input_abort inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en inp.
Proof.
intros en inp Hen Hinp Hlen.
pose proof (valid_input_abort_va_size _ Hinp) as Hv.
assert (Hvl : valid_launch inp) by (red in Hinp; tauto).
assert (Hrd : in_channel_reader inp = true) by (red in Hinp; tauto).
destruct Hinp as (Hva & Hve & _).
exact (usage_never_refused_sv48 en inp Hen Hv Hvl Hrd Hva Hve Hlen).
Qed.
Lemma plain_witness_entry : exists en,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en (Premises.witness_input false) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en
(Premises.witness_input false).
Proof.
destruct (Premises.valid_input_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
(Premises.witness_input false)
OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain_wf Premises.witness_valid_input) as [en Hen].
exists en. split; [exact Hen |].
apply (usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.
Lemma plain_witness_entry_abort : exists en,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en (Premises.witness_input true) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en
(Premises.witness_input true).
Proof.
destruct (Premises.valid_input_abort_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
(Premises.witness_input true)
OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain_wf Premises.witness_valid_input_abort) as [en Hen].
exists en. split; [exact Hen |].
apply (usage_never_refused_abort en _ Hen Premises.witness_valid_input_abort).
cbn. discriminate.
Qed.
Theorem plain_budget_witness :
exists en inp, valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en inp.
Proof.
destruct plain_witness_entry as (en & Hen & Hnr).
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.
Theorem plain_budget_witness_abort :
exists en inp, valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp /\ valid_input_abort inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en inp.
Proof.
destruct plain_witness_entry_abort as (en & Hen & Hnr).
exists en, (Premises.witness_input true).
split; [exact Hen | split; [exact Premises.witness_valid_input_abort | split; apply Hnr]].
Qed.
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
exists en_plain en_san,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en_plain (Premises.witness_input true) /\
valid_entry san en_san (Premises.witness_input true) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain lim en_plain
(Premises.witness_input true).
Proof.
intros san Hwf.
destruct plain_witness_entry_abort as (en_plain & Hep & Hnr).
destruct (Premises.valid_input_abort_entry san (Premises.witness_input true) Hwf
Premises.witness_valid_input_abort) as [en_san Hes].
exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.
Theorem plain_halts_not_vacuous :
exists en inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en inp /\
valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en inp.
Proof.
destruct plain_witness_entry as (en & Hen & Hnr).
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]].
exact ((OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.halts_allowed_jsoncons_fuzz_ubjson_parser_max_halts_plain
: OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.plain_halts)
en (Premises.witness_input false) Hen Premises.witness_valid_input (Hnr _ _)).
Qed.
Theorem ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en_plain inp /\
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan en_san inp /\
valid_input_abort inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en_plain inp /\
error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en_plain inp)
/\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
Budgets.Standard.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Standard.lim_source en_plain inp))
(bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
Budgets.Standard.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan
OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.ubsan_wf) as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input true).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
exact ((OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_ubjson_parser_max_ubsan
: OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.ubsan_agrees)
ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
Theorem asan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en_plain inp /\
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan en_san inp /\
valid_input_abort inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp /\
error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp)
/\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan
Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp))
(bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan
Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan
OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_wf) as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input true).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
exact ((OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_ubjson_parser_max_asan
: OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.asan_agrees)
ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
Theorem asan_ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain en_plain inp /\
valid_entry OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_ubsan en_san inp /\
valid_input_abort inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp /\
error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp)
/\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_ubsan
Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.plain
Budgets.Asan.lim_source en_plain inp))
(bh_traces (run_scfg Env.alloc_forced_only OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_ubsan
Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_ubsan
OSSVerify.jsoncons.fuzz_ubjson_parser_max.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input true).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input_abort | split; [apply Hnr |]]]].
exact ((OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Theorems.strong_universal_error_free_fuzz_ubjson_parser_max_both
: OSSVerify.jsoncons.fuzz_ubjson_parser_max.Statements.asan_ubsan_agrees)
ep es (Premises.witness_input true) Hep Hes Premises.witness_valid_input_abort (Hnr _ _)).
Qed.
