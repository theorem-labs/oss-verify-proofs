(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of Reusable/YL0j.v's src0_realizes_specX, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the four statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed usage_rzb, usage_never_refused (the launch premises and the channel-reader fact given to the start-up and usage walks; the walk lifted to the run over run_segments); its imports changed. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.libreac.fuzz_boxreg Require Images Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO05 YH00 YH01 YH03 YN3e YL0y.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Plain.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Theorems.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit Require Import Rzb StartB UsageB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require RomStableK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

(** * libreac / fuzz_boxreg: the budget premise on the plain build holds together with the other premises

    Four statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp]:
    - [plain_halts] ([halts_within_budget]), at [forced_only_cfg] and
      [Budgets.Standard.lim_source];
    - [ubsan_agrees] ([agrees_in]), at [Env.alloc_forced_only] and
      [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees] ([agrees_in]), at
      [Env.alloc_forced_only] and [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  On that path the program makes
    three kinds of system call: set_tid_address (96) in musl's start-up, writev (66)
    for the line, exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy ([m_vm_lazy = []]
    throughout), so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an
    input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([YN3e.src0_start], the argc <> 2
    branch of [YL0j.src0_realizes_specX], [YL0y.src0_usage]) restated over
    [BudgetWit.Rzb.rzb], the released [YK15.realizes] with no cut and a
    no-allocation-call check at each node ([BudgetWit.Rzb] says why [realizes]
    itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.rzb_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    [plain_budget_witness] is [plain_halts]'s three premises at one entry and one
    input.  Each [<statement>_not_vacuous] gives the premises of one of the four
    statements at one input to the released proof of that statement (the term its
    [proofs/<statement>/Proof.v] is), so the statement's conclusion holds at a
    point that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 branch of [YL0j.src0_realizes_specX], over [rzb]: start-up
    ([StartB.src0_start_b]), then [main]'s usage path ([UsageB.src0_usage_b]). *)
Lemma usage_rzb : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
in_channel_reader inp = true ->
(length (in_argv inp) <> 2)%nat ->
rzb src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen.
apply (src0_start_b false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits Hvl Hlau I).
intros ms tid Htid HS HR.
lazymatch goal with |- rzb _ (mkCfg _ ?m) _ => set (md0 := m) end.
assert (Hh : m_halted md0 = None) by reflexivity.
assert (Hlz : m_vm_lazy md0 = []) by reflexivity.
change (in_fs inp) with (m_fs md0).
(* LPS 727298f3: [src0_usage_b] is stated over the launch's ProcInput and holds at every run
   ceiling; take the run's own. *)
apply (src0_usage_b (fx:=YK11.fx0)
  (rc:=YM05.RunCeilOf (bv_unsigned sp) ltac:(destruct Hsp as [Hlo [Hhi _]]; split; assumption))
  sp inp mbase brk tid rnd Hsp Hva Hve Hvl Hlau Hfits Hlen ms _).
- apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp tid rnd) 3) = Z.of_nat (length (in_argv inp)))
by (unfold E_main; exact (YP08.ew3 src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd))).
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
- exact HR.
- exact Hh.
- exact Hlz.
- (* LPS 727298f3: [fdchan]'s third conjunct is the launch's channel-reader fact. *)
  split; [reflexivity | split; [reflexivity |]].
  first [ (unfold md0; cbn; exact Hcr) | (unfold md0, init_model; autorewrite with model; exact Hcr) ].
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.libreac.fuzz_boxreg.Images.plain lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & _ & _ & Hfits & Hlau).
pose proof (valid_input_argv inp Hinp) as Hva. pose proof (valid_input_envp inp Hinp) as Hve.
pose proof (valid_input_launch inp Hinp) as Hvl. pose proof (valid_input_channel_reader inp Hinp) as Hcr.
(* LPS 727298f3: [Run.run_scfg_budget_refused] reads the run against [run_segments] (the binary's
   segments with the run's vDSO appended); [Rzb.rzb_run_init] lifts the walk over the binary's own
   segments, which carry no vDSO text. *)
exact (rzb_never_refused_cfg _ cfg _ _
  (rzb_run_init src0segs inp sp mbase Plain_init_pc Plain_phdrs brk rnd lim _ ltac:(RomStableK.vdso_none)
     (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en (Premises.witness_input false) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.libreac.fuzz_boxreg.Images.plain lim en (Premises.witness_input false).
Proof.
destruct (Premises.valid_input_entry OSSVerify.libreac.fuzz_boxreg.Images.plain (Premises.witness_input false)
  OSSVerify.libreac.fuzz_boxreg.Images.plain_wf Premises.witness_valid_input) as [en Hen].
exists en. split; [exact Hen |].
apply (usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
exists en inp, valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Standard.lim_source en inp.
Proof.
destruct plain_witness_entry as (en & Hen & Hnr).
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.plain_halts], which the released [Theorems.libreac_fuzz_boxreg_plain_halts]
    proves, at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem plain_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Standard.lim_source en inp.
Proof.
destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_plain_halts en inp Hen Hinp Hnr).
Qed.

(** The three agreement statements: an entry of the plain build and one of the
    sanitizer build on the same input [Premises.witness_input false] (the pair
    [Premises.agrees_in_premises] builds, constructed here so that the input stays
    the witness input), with the budget premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
exists en_plain en_san,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en_plain (Premises.witness_input false) /\
valid_entry san en_san (Premises.witness_input false) /\
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.libreac.fuzz_boxreg.Images.plain lim en_plain (Premises.witness_input false).
Proof.
intros san Hwf.
destruct plain_witness_entry as (en_plain & Hep & Hnr).
destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
  as [en_san Hes].
exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.libreac_fuzz_boxreg_ubsan_agrees] proves, at entries and an input
    that meet all four of its premises: its conclusion holds there with no
    hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en_plain inp /\
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.ubsan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Standard.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Standard.lim_source en_plain inp)
/\ error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.ubsan
    Budgets.Standard.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
                   Budgets.Standard.lim_source en_plain inp))
               (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.ubsan
                   Budgets.Standard.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.libreac.fuzz_boxreg.Images.ubsan OSSVerify.libreac.fuzz_boxreg.Images.ubsan_wf)
  as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
exact (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_ubsan_agrees
  ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.libreac_fuzz_boxreg_asan_agrees] proves, at entries and an input that
    meet all four of its premises: its conclusion holds there with no hypothesis
    left. *)
Theorem asan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en_plain inp /\
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.asan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Asan.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Asan.lim_source en_plain inp)
/\ error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.asan
    Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
                   Budgets.Asan.lim_source en_plain inp))
               (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.asan
                   Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.libreac.fuzz_boxreg.Images.asan OSSVerify.libreac.fuzz_boxreg.Images.asan_wf)
  as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
exact (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_asan_agrees
  ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.libreac_fuzz_boxreg_asan_ubsan_agrees] proves, at entries and an
    input that meet all four of its premises: its conclusion holds there with no
    hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
exists en_plain en_san inp,
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.plain en_plain inp /\
valid_entry OSSVerify.libreac.fuzz_boxreg.Images.asan_ubsan en_san inp /\
valid_input inp /\
~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Asan.lim_source en_plain inp /\
error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
    Budgets.Asan.lim_source en_plain inp)
/\ error_free (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.asan_ubsan
    Budgets.Asan.lim_target en_san inp)
/\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.plain
                   Budgets.Asan.lim_source en_plain inp))
               (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.libreac.fuzz_boxreg.Images.asan_ubsan
                   Budgets.Asan.lim_target en_san inp)).
Proof.
destruct (agree_witness OSSVerify.libreac.fuzz_boxreg.Images.asan_ubsan
  OSSVerify.libreac.fuzz_boxreg.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
exists ep, es, (Premises.witness_input false).
split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
exact (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Theorems.libreac_fuzz_boxreg_asan_ubsan_agrees
  ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
