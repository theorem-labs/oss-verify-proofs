(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/ModelOK.v, PlainTree.v and Theorems.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the four statements whose budget premise names the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_unfiltered restated for the revision's model; usage_never_refused_run re-proved; imports; prog_model_ok_tnf re-proved with GI_init's new premises: the input's channel reader (valid_input_either_reader), the valid mmap base and the reserved-size bounds (resv_plain); GI_init's state is moved to the run's initial model (init_model with the vDSO draw installed) by GI_with_vdso). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Image InitMem RegsEquiv RunSegs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Prog KInv KLink KEv StepB Gap ModelInv ImgFacts.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Require OSSVerify.Proofs.zstd.huf_decompress.lib.Plain.PlainClosed.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Theorems.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BudgetWit Require Import NoAlloc UsageNA.
From OSSVerify.zstd.huf_decompress Require Images.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Import Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * zstd / huf_decompress: the plain build's budget premise holds on the usage path

    Four statements of this harness carry the budget premise
    [~ run_scfg_budget_refused env Images.plain lim en inp] on the plain
    build: [plain_halts] and [ubsan_agrees] at [Budgets.Standard.lim_source],
    [asan_agrees] and [asan_ubsan_agrees] at [Budgets.Asan.lim_source].  A
    statement whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image; the budget premise reads the run, and this file gives
    it for the plain build.

    The input is [Premises.witness_input false]: one empty argument (argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver writes
    its usage line to fd 2 and exits with status 2.  On that path the program
    makes set_tid_address (96), writev (66), possibly ioctl (29) and writev
    on fd 1 when stdout is flushed, and exit_group (94).  None is an
    allocation call (brk 214, mremap 216, mmap 222, mprotect 226), and no
    mapping is lazy.

    The proof uses the released tree of the plain build ([Prog.prog] at
    [PREAD_STAGE], with [Plain.PlainClosed.plain_impl_closed]) unchanged:
    [UsageNA.usage_tree_na] shows that, when argc <> 2, every node of that
    tree is one of the four non-allocating nodes, and
    [NoAlloc.tree_never_refused] turns that into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    The released [ModelOK.prog_model_ok] gives the tree's leaves and safety
    from the never-forced premise [StepB.tnf], which the released
    [LB_Main.never_forced] proves at limits of 2^31 or more;
    [prog_model_ok_tnf] is that proof with [tnf] as a hypothesis, which
    [NoAlloc.tnf_tna] discharges on the usage path at every limit.
    [plain_budget_witness] is the three premises of [plain_halts] at one
    entry and one input; each [<statement>_not_vacuous] gives the premises of
    that statement together to its released proof, so its conclusion holds
    at an entry and an input that meet all of them, with no hypothesis left. *)

(** [ModelOK.prog_model_ok] for the plain build, with the never-forced
    premise as a hypothesis in place of [LB_Main.never_forced]; the limit is
    free. *)
Lemma prog_model_ok_tnf : forall rs lim en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tnf (Prog.prog psegs rs inp en) (mo0 psegs lim en inp) ->
  leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs lim en inp).
Proof.
  intros rs lim en inp Hen Hinp HNF.
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  pose proof (valid_input_either_reader _ Hinp) as Hrdr.
  destruct Hen as ((HspL & HspH & _) & Hbrk & Hmb & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold Prog.prog, Prog.prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GI []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - apply GI_with_vdso. eapply GI_init; [exact Hbrk| exact top_pos_plain| split; [exact HspL| exact HspH]| reflexivity| exact ceil_plain| exact Hrdr| exact Hmb| exact resv_plain].
  - exact HNF.
Qed.

(** The run of the plain build reaches no budget-refused configuration under
    the unfiltered step, when argv has not two entries.  LPS 727298f3 runs the
    binary over [run_segments] (its segments and the vDSO pair, [vsegs]) from
    the vDSO initial state; the tree walk is lifted to that list by
    [RunSegs.impl_lift], as [TopLevel.run_of_tree] does. *)
Lemma usage_unfiltered : forall en inp lim,
  valid_entry OSSVerify.zstd.huf_decompress.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  ~ reaches_budget_refused (vsegs psegs en inp)
      (mkCfg (init_machine_state (vsegs psegs en inp) p_init_pc p_phdrs (en_sp en) (en_mmap_base en)
                (en_draw en) inp)
             (mo0 psegs lim en inp)).
Proof.
  intros en inp lim Hen Hinp Hlen.
  pose proof (valid_input_either_of_valid_input inp Hinp) as Hvi.
  pose proof (usage_tree_na psegs PREAD_STAGE inp en Hlen) as Hna.
  destruct (prog_model_ok_tnf PREAD_STAGE lim en inp Hen Hvi (tnf_tna _ _ _ Hna)) as [Hl Hs].
  pose proof (Plain.PlainClosed.plain_impl_closed en inp Hen Hvi) as Himpl0.
  pose proof (impl_lift psegs (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
                (vsegs_tail_high psegs p_init_pc p_phdrs en inp Hen (valid_input_either_va_size inp Hvi)
                   ltac:(change (segs_top psegs) with 0x59000%Z; lia))
                _ _ _ Himpl0) as Himpl.
  change (psegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) with (vsegs psegs en inp) in Himpl.
  rewrite <- init_ms_vsegs in Himpl.
  eapply (tree_never_refused (vsegs psegs en inp) _ (Prog.prog psegs PREAD_STAGE inp en) _
            (init_ms (vsegs psegs en inp) p_init_pc p_phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp)).
  - exact (init_machine_state_eqv (vsegs psegs en inp) p_init_pc p_phdrs (en_sp en) (en_mmap_base en)
             (en_draw en) inp).
  - split; [exact Himpl|].
    split; [exact Hl|]. split; [apply mo0_not_halted|].
    split; [exact (mo0_minv psegs p_init_pc p_phdrs lim en inp Hen (valid_input_either_va_size inp Hvi)
                     (valid_input_either_reader inp Hvi))|].
    exact Hs.
  - exact Hna.
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the limit: the run-level form. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.zstd.huf_decompress.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.zstd.huf_decompress.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen lim.
  pose proof (usage_unfiltered en inp lim Hen Hinp Hlen) as H.
  rewrite <- mo0_vsegs in H.
  destruct en as [sp brk mbase rnd]. exact H.
Qed.

(** ...and so whatever the spurious-failure configuration
    ([Run.run_scfg_budget_refused_sub]). *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.zstd.huf_decompress.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.zstd.huf_decompress.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim
           (run_scfg_budget_refused_sub cfg OSSVerify.zstd.huf_decompress.Images.plain lim en inp Hr)).
Qed.

(** At [Premises.witness_input false], argc = 1. *)
Lemma witness_never_refused : forall en (cfg : SpuriousCfg) (lim : Z),
  valid_entry OSSVerify.zstd.huf_decompress.Images.plain en (Premises.witness_input false) ->
  ~ run_scfg_budget_refused cfg OSSVerify.zstd.huf_decompress.Images.plain lim en (Premises.witness_input false).
Proof.
  intros en cfg lim Hen.
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at
    [Premises.witness_input false] and the entry [Premises.valid_input_entry]
    gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.zstd.huf_decompress.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.zstd.huf_decompress.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.plain (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  exact (witness_never_refused en forced_only_cfg Budgets.Standard.lim_source Hen).
Qed.

(** [Statements.plain_halts] ([halts_within_budget Budgets.Standard.lim_source
    Exits.ok_or_refused Images.plain]), which the released
    [Theorems.halts_allowed_zstd_huf_decompress_halts_plain] proves, at an
    entry and an input that meet all three of its premises. *)
Theorem plain_halts_not_vacuous :
  exists en inp,
    valid_entry OSSVerify.zstd.huf_decompress.Images.plain en inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.zstd.huf_decompress.Images.plain
        Budgets.Standard.lim_source en inp /\
    must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.zstd.huf_decompress.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.halts_allowed_zstd_huf_decompress_halts_plain
           en inp Hen Hinp Hnr).
Qed.

(** [Statements.ubsan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain
    Images.ubsan]), which the released
    [Theorems.strong_universal_error_free_huf_decompress_ubsan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.zstd.huf_decompress.Images.plain en_plain inp /\
    valid_entry OSSVerify.zstd.huf_decompress.Images.ubsan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                  Budgets.Standard.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                                 Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.ubsan
                                 Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.plain (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.ubsan (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.ubsan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Standard.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_ubsan
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.

(** [Statements.asan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain
    Images.asan]), which the released
    [Theorems.strong_universal_error_free_huf_decompress_asan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.zstd.huf_decompress.Images.plain en_plain inp /\
    valid_entry OSSVerify.zstd.huf_decompress.Images.asan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                  Budgets.Asan.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.asan
                     Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.asan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.plain (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.asan (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.asan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_asan
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.

(** [Statements.asan_ubsan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain
    Images.asan_ubsan]), which the released
    [Theorems.strong_universal_error_free_huf_decompress_both] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.zstd.huf_decompress.Images.plain en_plain inp /\
    valid_entry OSSVerify.zstd.huf_decompress.Images.asan_ubsan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                  Budgets.Asan.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.zstd.huf_decompress.Images.asan_ubsan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.plain (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.zstd.huf_decompress.Images.asan_ubsan (Premises.witness_input false)
    OSSVerify.zstd.huf_decompress.Images.asan_ubsan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.zstd.huf_decompress.lib.Theorems.strong_universal_error_free_huf_decompress_both
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.
