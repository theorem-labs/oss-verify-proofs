(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/ModelOK.v, Plain/PlainClosed.v and Theorems.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the three statements whose budget premise names the plain build there. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/BudgetWit/BudgetWitness.v: module paths and target names for simdjson/fuzz_utf8's plain binary; as in that file, made from Spec/ModelOK.v, Plain/PlainClosed.v and Theorems.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the three statements whose budget premise names the plain build there; as in that file, ported to LPS 727298f3: prog_model_ok_tnf's initial invariant is GI_init's, with the input's channel-reader fact, carried onto the initial model holding the entry's vDSO draw (GI_fds, minv_with_vdso); mo0_minv is passed the channel-reader fact; and usage_unfiltered is stated over the run's segments (run_segments) and init_config, the tree lifted onto them as TopLevel.run_of_tree does; taken from projects/simdjson/fuzz_minifyimpl/proofs/lib/BudgetWit/BudgetWitness.v, lines 6-253, as in the LPS 727298f3 update. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.simdjson.fuzz_utf8 Require Images Statements.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode Image InitMem RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState ProgP KInv KLink KEv StepB Gap ModelInv ImgFacts.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
Require OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain.PlainClosed.
Require OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain.PM_client.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Theorems.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BudgetWit Require Import NoAlloc UsageNA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * simdjson / fuzz_utf8: the plain build's budget premise holds on the usage path

    The three agreement statements [Statements.asan_agrees], [ubsan_agrees] and
    [asan_ubsan_agrees] are [agrees_in_abort_modelled] statements.  Each
    quantifies over the entries of the plain and the sanitizer build and over
    every input, and has four premises: two [valid_entry], [valid_input_abort],
    and the budget premise [~ run_scfg_budget_refused Env.alloc_forced_only
    Images.plain lim en inp] at 2 GiB (asan, asan_ubsan) or 16 GiB (ubsan).  A
    theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the first three for well-formed images and
    leaves the budget premise, which reads the run; this file gives it for the
    plain build.

    The input is [Premises.witness_input true]: one empty argument (argc = 1),
    no environment, an empty file system, and abort() read as death by
    SIGABRT.  With argc <> 2 the driver writes its usage line to fd 2 and exits
    with status 2.  On that path the program makes set_tid_address (96),
    writev (66), possibly ioctl (29) and writev on fd 1 when stdout is flushed,
    and exit or exit_group (93, 94).  None is an allocation call (brk 214,
    mremap 216, mmap 222, mprotect 226), and no mapping is lazy.

    The proof uses the released tree of the plain build ([ProgP.prog] at
    [PREAD_STAGE]) and its released machine-code refinement
    ([Plain.PlainClosed.plain_impl_closed_modulo_client] on the released client
    proof [Plain.PM_client.plain_client_proof], the term [Theorems] uses)
    unchanged: [UsageNA.usage_tree_na] shows that, when argc <> 2, every node
    of that tree is one of the four non-allocating nodes, and
    [NoAlloc.tree_never_refused] turns that into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    The released [ModelOK.prog_model_ok] gives the tree's leaves and safety
    from the never-forced premise [StepB.tnf], which the released
    [LB_Main.never_forced] proves at limits of 2^31 or more;
    [prog_model_ok_tnf] is that proof with [tnf] as a hypothesis, which
    [NoAlloc.tnf_tna] discharges on the usage path at every limit.
    [plain_budget_witness] is the premises at one entry and one input; each
    [<statement>_not_vacuous] gives them to the released proof
    [Theorems.strong_universal_error_free_fuzz_utf8_<build>] (the term
    that [proofs/<statement>/Proof.v] closes its statement with), so the
    statement's conclusion holds at a pair that meets all its premises, with
    no hypothesis left. *)

(** [ModelOK.prog_model_ok] for the plain build, with the never-forced
    premise as a hypothesis in place of [LB_Main.never_forced]; the limit is
    free. *)
Lemma prog_model_ok_tnf : forall rs lim en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tnf (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp) ->
  leaves_unreachable_m nstep (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafe (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp).
Proof.
  intros rs lim en inp Hen Hinp HNF.
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  pose proof (valid_input_either_reader _ Hinp) as Hrdr.
  destruct Hen as ((HspL & HspH & _) & Hbrk & _ & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold ProgP.prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GIo []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - (* LPS 727298f3: [mo0] carries the entry's vDSO draw ([with_vdso]); the VM ledger, the kernel
       state and the halt flag are [init_model]'s (as Spec/ModelOK.prog_model_ok) *)
    exists None. cbn [TargetSafe.clb app].
    eapply GI_fds;
      [ apply (GI_init psegs brk0 mbase sp lim inp _ Hbrk top_pos_plain ltac:(split; [exact HspL| exact HspH]) eq_refl ceil_plain Hrdr)
      | reflexivity | reflexivity | apply minv_with_vdso, minv_init; [split; [exact HspL| exact HspH] | exact Hrdr] | reflexivity ].
  - exact HNF.
Qed.

(** The released machine-code refinement of the plain build, closed by the
    released client proof. *)
Lemma plain_impl : forall en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  impl psegs (at_node psegs) (ProgP.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
       (ms0 psegs p_init_pc p_phdrs en inp).
Proof.
  exact (OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain.PlainClosed.plain_impl_closed_modulo_client
           OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain.PM_client.plain_client_proof).
Qed.

(** The run of the plain build reaches no budget-refused configuration under
    the unfiltered step, when argv has not two entries.  LPS 727298f3: the run
    steps over [run_segments] (the loaded segments and the vDSO pair), and its
    model is [TopLevel.mo0] ([init_config]'s, with the vDSO draw); the tree is
    lifted onto those segments as [TopLevel.run_of_tree] does. *)
Lemma usage_unfiltered : forall en inp lim,
  valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en inp -> valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  let vsegs := run_segments psegs inp (en_sp en) (en_mmap_base en) in
  ~ reaches_budget_refused vsegs
      (init_config vsegs p_init_pc p_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp).
Proof.
  intros en inp lim Hen Hvi Hlen vsegs.
  pose proof (usage_tree_na psegs PREAD_STAGE inp en Hlen) as Hna.
  destruct (prog_model_ok_tnf PREAD_STAGE lim en inp Hen Hvi (tnf_tna _ _ _ Hna)) as [Hl Hs].
  set (V := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  assert (Hcfg : init_config vsegs p_init_pc p_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
                 = mkCfg (init_machine_state (psegs ++ V) p_init_pc p_phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp)
                         (mo0 psegs lim en inp)).
  { unfold vsegs, V, mo0. rewrite <- (run_segments_reserved psegs inp (en_sp en) (en_mmap_base en)). reflexivity. }
  rewrite Hcfg.
  eapply (tree_never_refused (psegs ++ V) _ (ProgP.prog psegs PREAD_STAGE inp en) _
            (init_ms (psegs ++ V) p_init_pc p_phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp)).
  - exact (init_machine_state_eqv (psegs ++ V) p_init_pc p_phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp).
  - split.
    { pose proof (impl_lift psegs V (ProgP.prog psegs PREAD_STAGE inp en) _ (ms0 psegs p_init_pc p_phdrs en inp)
                    (vdso_nonexec _ _ _) (plain_impl en inp Hen Hvi)) as Himpl'.
      rewrite set_rom_ms0 in Himpl'. exact Himpl'. }
    split; [exact Hl|]. split; [apply mo0_not_halted|].
    split; [split; [exact (mo0_minv psegs p_init_pc p_phdrs lim en inp Hen (valid_input_either_va_size inp Hvi)
                             (valid_input_either_reader _ Hvi))
                   | exact (valid_input_either_reader _ Hvi)]|].
    exact Hs.
  - exact Hna.
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the spurious-failure configuration and the limit
    ([Run.run_scfg_budget_refused_sub]). *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en inp -> valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.simdjson.fuzz_utf8.Images.plain lim en inp.
Proof.
  intros en inp Hen Hvi Hlen cfg lim Hr.
  apply run_scfg_budget_refused_sub in Hr.
  destruct en as [sp brk mbase rnd].
  exact (usage_unfiltered (mkEntry sp brk mbase rnd) inp lim Hen Hvi Hlen Hr).
Qed.

(** The plain build's premises hold together at [Premises.witness_input true]
    and the entry [Premises.valid_input_abort_entry] gives for it, the budget
    premise under every configuration and at every limit. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en inp /\ valid_input_abort inp /\
  forall (cfg : SpuriousCfg) (lim : Z),
    ~ run_scfg_budget_refused cfg OSSVerify.simdjson.fuzz_utf8.Images.plain lim en inp.
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_utf8.Images.plain (Premises.witness_input true)
    OSSVerify.simdjson.fuzz_utf8.Images.plain_wf Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  intros cfg lim.
  assert (Hlen : (length (in_argv (Premises.witness_input true)) <> 2)%nat) by (cbn; discriminate).
  exact (usage_never_refused en _ Hen (valid_input_either_of_valid_input_abort _ Premises.witness_valid_input_abort)
           Hlen cfg lim).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_fuzz_utf8_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.asan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_utf8.Images.asan inp
    OSSVerify.simdjson.fuzz_utf8.Images.asan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Asan.lim_source) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Theorems.strong_universal_error_free_fuzz_utf8_asan en_plain en_san inp Hp Hs Hinp Hb).
Qed.

(** [Statements.ubsan_agrees] and the released
    [Theorems.strong_universal_error_free_fuzz_utf8_ubsan], likewise. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Standard.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.ubsan
        Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_utf8.Images.ubsan inp
    OSSVerify.simdjson.fuzz_utf8.Images.ubsan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Standard.lim_source) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Theorems.strong_universal_error_free_fuzz_utf8_ubsan en_plain en_san inp Hp Hs Hinp Hb).
Qed.

(** [Statements.asan_ubsan_agrees] and the released
    [Theorems.strong_universal_error_free_fuzz_utf8_both], likewise. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_utf8.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.asan_ubsan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_utf8.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_utf8.Images.asan_ubsan inp
    OSSVerify.simdjson.fuzz_utf8.Images.asan_ubsan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Asan.lim_source) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Theorems.strong_universal_error_free_fuzz_utf8_both en_plain en_san inp Hp Hs Hinp Hb).
Qed.
