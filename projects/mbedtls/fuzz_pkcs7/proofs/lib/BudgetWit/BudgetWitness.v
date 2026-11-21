(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of P/P_main_skel.v's P_realizes_spec, over BudgetWit.Rzb.realizes; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_rzb restated as P/P_main_skel.v's P_realizes_spec argc <> 2 branch was: the channel-reader, valid_launch and entry_launch_ok_va premises, the five new ProcInput fields and amb_of with the reader fact and the launch's vDSO run; new lemmas that lift a BudgetWit.Rzb.realizes walk over the binary's segments to the run's segment list, run_segments, as Lib/RomStable.v does for Shape.realizes, and vdso_none_plain; usage_never_refused proves the three launch facts from its valid_entry and valid_input premises and lifts the walk; RomBase, RomStep and Lib.RomStable required). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.mbedtls.fuzz_pkcs7 Require Images Statements.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require Theorems.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require P_startupB P_mainleaf_usageB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require RomBase RomStep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require RomStable.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(** * mbedtls / fuzz_pkcs7: the budget premise on the plain build holds together with the other premises

    Three statements of [Statements] carry a budget premise on the plain build,
    [~ run_budget_refused Images.plain lim en inp] ([agrees]):
    - [ubsan_agrees], at [Budgets.Standard.lim_source];
    - [asan_agrees] and [asan_ubsan_agrees], at [Budgets.Asan.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every limit (and, as a corollary, for
    every spurious-failure configuration).

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  On that path the program makes
    three kinds of system call: set_tid_address (96) in musl's start-up, writev (66)
    for the line, exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy ([m_vm_lazy = []]
    throughout), so no configuration the run reaches is refused by the budget.
    This shows the budget premise satisfiable on the usage path, not yet on an
    input that reaches [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path ([P_startup.ref_startup], the
    argc <> 2 branch of [P_main_skel.P_realizes_spec], [P_mainleaf_usage.ref_usage_w])
    restated over [BudgetWit.Rzb.realizes], the released [Shape.realizes] with a
    no-allocation-call check at each node ([BudgetWit.Rzb] says why
    [Shape.realizes] itself cannot carry the fact).  [usage_rzb] is that walk;
    [Rzb.realizes_not_refused] turns it into the budget premise
    ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the premises of
    one of the three statements at one input to the released proof of that
    statement (the term its [proofs/<statement>/Proof.v] is), so the statement's
    conclusion holds at a point that meets all its premises, with no hypothesis
    left. *)

(** ** The walk over the binary's own segments, lifted to the run

    At the revision [Run.run_budget_refused] reads the run against
    [run_segments Plain.M.loaded_segments inp sp mbase] -- the binary's segments with the
    run's vDSO pair appended -- and from the start configuration over that list, while
    [usage_rzb] below is a walk over the binary's own segments.  These are
    [Lib.RomStable]'s [realizes_wrom], [realizes_app_tail], [realizes_run_segments] and
    [run_init] over [Rzb.realizes]; every node-level step is [Lib.RomStable]'s own.  The one
    new part is [Rzb.grant_free], which reads only the system-call number and the argument
    registers ([Run.alloc_budget_refused_b]), so neither a larger read-only backing nor a
    longer segment list changes it. *)

Lemma budget_refused_b_regs : forall segs1 segs2 ms1 ms2 x8 m,
  syscall_args ms1 = syscall_args ms2 ->
  alloc_budget_refused_b (sys_input segs1 ms1 x8) m = alloc_budget_refused_b (sys_input segs2 ms2 x8) m.
Proof.
  intros segs1 segs2 ms1 ms2 x8 m E. unfold alloc_budget_refused_b, sys_input. rewrite E.
  cbn [in_sysno in_args in_arg]. reflexivity.
Qed.

Lemma grant_free_cwrom : forall segs c r,
  grant_free segs c -> grant_free segs (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.cwrom c r).
Proof.
  intros segs [ms model] r Hg x8 Hx8.
  change (ms_svc_pending ms = Some x8) in Hx8.
  change (alloc_budget_refused_b
            (sys_input segs (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.wrom ms r) x8) model = false).
  rewrite (budget_refused_b_regs segs segs
             (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.wrom ms r) ms x8 model eq_refl).
  exact (Hg x8 Hx8).
Qed.

Lemma grant_free_segs : forall segs segs' c, grant_free segs c -> grant_free segs' c.
Proof.
  intros segs segs' [ms model] Hg x8 Hx8.
  change (alloc_budget_refused_b (sys_input segs' ms x8) model = false).
  rewrite (budget_refused_b_regs segs' segs ms ms x8 model eq_refl).
  exact (Hg x8 Hx8).
Qed.

Theorem realizes_wrom_b : forall segs, vdso_image segs = None ->
  forall c T, realizes segs c T ->
  forall r, OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.rom_ext (ms_rom (cfg_ms c)) r ->
  realizes segs (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.cwrom c r) T.
Proof.
  intros segs Hvi c T H;
    induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (Rzb.rz_node segs (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.cwrom c r) I evs
             (fun i => OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.cwrom (nx i) r) T i0).
    + eapply OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.RomStable.node_wrom; eassumption.
    + exact (grant_free_cwrom segs c r Hg).
    + intros i. apply IH.
      match goal with |- OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomBase.rom_ext ?x _ =>
        replace x with (ms_rom (cfg_ms c)) end; [exact Hr|].
      symmetry. eapply OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.RomStable.node_rom; eassumption.
  - apply Rzb.rz_halt. exact Hh.
  - eapply Rzb.rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.

Theorem realizes_app_tail_b : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, realizes segs c T -> realizes (segs ++ tail) c T.
Proof.
  intros segs tail Hnx Hnw Hvi c T H;
    induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq].
  - apply (Rzb.rz_node (segs ++ tail) c I evs nx T i0).
    + eapply OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.RomStable.node_ok_app_tail; eassumption.
    + exact (grant_free_segs segs (segs ++ tail) c Hg).
    + exact IH.
  - apply Rzb.rz_halt. exact Hh.
  - eapply Rzb.rz_conseq; [exact IH | exact Heq].
Qed.

Theorem realizes_run_segments_b : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  realizes segs c T -> realizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (realizes_app_tail_b segs _
           (fun s Hs => OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomStep.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomStep.vdso_segments_nw _ _ _ s Hs)
           Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is a walk of the
    run's start over the run's segment list ([Lib.RomStable.run_init] over [Rzb.realizes]). *)
Theorem run_init_b : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomStep.init_config_run_segments.
  apply realizes_run_segments_b; [exact Hvi|].
  apply (realizes_wrom_b segs Hvi); [exact H|].
  rewrite OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomStep.init_config_rom.
  apply OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg.RomStep.rom_ext_run_segments.
Qed.

(** The plain build carries no vDSO text mapping of its own ([run_init_b]'s side condition). *)
Lemma vdso_none_plain : RiscvSemantics.vdso_image Plain.M.loaded_segments = None.
Proof. reflexivity. Qed.

(** The argc <> 2 branch of [P_main_skel.P_realizes_spec], over [Rzb.realizes]:
    start-up ([P_startupB.ref_startup]), then [main]'s usage path
    ([P_mainleaf_usageB.ref_usage_w]). *)
Lemma usage_rzb : forall sp brk mbase rd lim inp,
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (* LPS 727298f3: the start-up walk reads the launch and the usage line's writev the channel
     reader, as in P_main_skel.P_realizes_spec; [usage_never_refused] proves the three from its
     [valid_entry] and [valid_input] premises *)
  in_channel_reader inp = true -> valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rd) inp ->
  (length (in_argv inp) <> 2)%nat ->
  exists T, realizes Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rd lim inp) T.
Proof.
  intros sp brk mbase rd lim [argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st]
    Hsp Hbrk Hva Hve Hfit Hrd Hvl Hlau Hlen.
  cbn [in_argv in_envp] in *.
  set (fs0 := fs_seed_tmp ifs tm).
  pose (AMB := amb_of (mkProcInput_full argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st)
                 Hrd (Vdso.vdso_run_init (ed_vdso rd))).
  eexists.
  apply (P_startupB.ref_startup sp brk mbase rd lim _ _ Hrd Hsp Hbrk Hva Hve Hfit Hvl Hlau).
  change (amb_of _ _ _) with AMB.
  match goal with |- context [init_model ?r ?b ?m ?s ?l (mkProcInput_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)] =>
    change (init_model r b m s l (mkProcInput_full argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st))
      with (init_model r b m s l (@mkProcInputC AMB argv envp fs0 stdin0)) end.
  change (Vdso.vdso_run_init (ed_vdso rd)) with (@a_vdso AMB).
  intros tid regs mem Htid ME.
  apply (P_mainleaf_usageB.ref_usage_w sp argv envp tid rd regs mem brk mbase fs0 stdin0 lim
           Hva Hve Hsp Htid ME).
  exact Hlen.
Qed.

(** On every valid entry of the plain build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget,
    whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfits & Hlau).
  (* the launch clause and the channel reader of [valid_input]
     ([Run.valid_input_launch], [Run.valid_input_channel_reader]) *)
  pose proof (valid_input_launch _ Hinp) as Hvl.
  pose proof (valid_input_channel_reader _ Hinp) as Hrdr.
  destruct Hinp as (Hva & Hve & _).
  destruct (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hfits Hrdr Hvl Hlau Hlen) as [T HT].
  exact (realizes_not_refused _ _ _
           (run_init_b Plain.M.loaded_segments inp sp mbase Plain.M.init_pc Plain.M.phdrs brk rnd lim T
              vdso_none_plain HT)).
Qed.

(** The same, for every spurious-failure configuration: a configured run reaches
    fewer configurations, never more ([Run.run_scfg_budget_refused_sub]). *)
Corollary usage_never_refused_cfg : forall en inp,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.mbedtls.fuzz_pkcs7.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim H.
  exact (usage_never_refused en inp Hen Hinp Hlen lim (run_scfg_budget_refused_sub _ _ _ _ _ H)).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en (Premises.witness_input false) /\
  forall lim : Z,
  ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain lim en (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain (Premises.witness_input false)
    OSSVerify.mbedtls.fuzz_pkcs7.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The plain build's three [agrees] premises that read only the plain build
    hold together: at [Premises.witness_input false] and the entry
    [Premises.valid_input_entry] gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en inp /\ valid_input inp /\
  forall lim : Z, ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain lim en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | exact Hnr]].
Qed.

(** An entry of the plain build and one of the sanitizer build on the same input
    [Premises.witness_input false] (the pair [Premises.agrees_premises] builds,
    constructed here so that the input stays the witness input), with the budget
    premise from [plain_witness_entry]. *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall lim : Z,
  ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain lim en_plain (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_pkcs7_asan] proves, at entries and
    an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en_plain inp /\
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp /\
  error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp)
  /\ error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.asan Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.asan Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.mbedtls.fuzz_pkcs7.Images.asan OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Theorems.strong_universal_error_free_fuzz_pkcs7_asan
            : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_pkcs7_ubsan] proves, at entries and
    an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en_plain inp /\
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Standard.lim_source en_plain inp /\
  error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Standard.lim_source en_plain inp)
  /\ error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Theorems.strong_universal_error_free_fuzz_pkcs7_ubsan
            : OSSVerify.mbedtls.fuzz_pkcs7.Statements.ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_pkcs7_both] proves, at entries and
    an input that meet all four of its premises: its conclusion holds there with
    no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.plain en_plain inp /\
  valid_entry OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_budget_refused OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp /\
  error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp)
  /\ error_free (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.plain Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (Run.run OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan
    OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact ((OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Theorems.strong_universal_error_free_fuzz_pkcs7_both
            : OSSVerify.mbedtls.fuzz_pkcs7.Statements.asan_ubsan_agrees)
           ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _)).
Qed.
