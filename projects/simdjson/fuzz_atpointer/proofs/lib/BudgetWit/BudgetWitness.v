(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from TopPlain.v's P_canon_lim and TopFinal_plain.v; adds the budget-premise witness for the plain build and the lemmas that apply the three released agreement proofs there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch stated over the run's whole input). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.simdjson.fuzz_atpointer Require Images Statements.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import ITree Nodes Image Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel Obligations ProofBase TopPlain.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prog Zfb Zfc Zf3 Z11h Zfv Zg1.
Require OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.TopFinal_plain.
Require OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Theorems.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.BudgetWit Require Import Quiet Tree Usage.
Import ListNotations.
Open Scope Z_scope.

(** * simdjson / fuzz_atpointer: the plain build's budget premise holds, on the usage path

    The three agreement statements [Statements.asan_agrees], [ubsan_agrees] and
    [asan_ubsan_agrees] are [agrees_in_abort_modelled] statements.  Each quantifies
    over the entries of the plain and the sanitizer build and over every input,
    and has four premises: two [valid_entry], [valid_input_abort], and the budget
    premise [~ run_scfg_budget_refused Env.alloc_forced_only Images.plain lim en
    inp] at 2 GiB (asan, asan_ubsan) or 16 GiB (ubsan).  A theorem whose premises
    never hold together proves nothing.  [OSSVerify.Core.Premises] gives the first
    three for well-formed images and leaves the budget premise, which reads the
    run; this file gives it for the plain build.

    The input is [Premises.witness_input true]: one empty argument (so argc = 1),
    no environment, an empty file system, and abort() read as death by SIGABRT.
    With argc <> 2 the driver's [main] writes its usage line to fd 2 and exits
    with status 2.  On that path the program makes set_tid_address (96), writev
    (66), and exit or exit_group (93, 94), and may make ioctl (29) when it
    flushes stdout; none is an allocation call (brk 214, mremap 216, mmap 222,
    mprotect 226).

    The proof reuses the released program tree: [impl_P] is the released
    [impl_P_stmt] (the machine code refines [Obligations.the_prog]), and
    [plain_tree] is [TopPlain.P_canon_lim]'s model facts at any limit of at least
    [KLIM + SMALLREQ] (about 1.36 GiB).  [Usage.usage_tall] checks that on the
    usage path the tree has no allocation node, and [Tree.run_never_budget_refused]
    turns the three into the budget premise, for every spurious-failure
    configuration ([usage_never_refused]).  [plain_budget_witness] is the
    premises at one entry and one input; each [<statement>_not_vacuous] gives
    them to the released proof [Theorems.strong_universal_error_free_fuzz_atpointer_<build>] (the term that
    [proofs/<statement>/Proof.v] closes its statement with), so the statement's
    conclusion holds at a pair that meets all its premises, with no hypothesis
    left.

    The limit bound is the one condition the witness carries beyond
    libreac/fuzz_knock's BudgetWit: [prog_no_enomem_any], which [plain_tree] reads, is proved for
    limits of at least [KLIM + SMALLREQ]; both plain-build limits the statements name (2 GiB and
    16 GiB) are above it ([klim_le_asan], [klim_le_standard]). *)

(** The released machine-code refinement of the plain build. *)
Lemma impl_P : impl_P_stmt.
Proof.
  apply OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.TopFinal_plain.HP. intros CE RN.
  exact (@OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41.rfuzz_one_closed CE RN).
Qed.

(** [TopPlain.P_canon_lim]'s tree facts, at any limit the allocator invariant
    covers. *)
Lemma plain_tree : forall lim en inp,
  KLIM + SMALLREQ <= lim ->
  valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_either inp ->
  impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
       (ms0 psegs Plain.M.init_pc Plain.M.phdrs en inp)
  /\ leaves_unreachable_m nstep (the_prog psegs pstage inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafeU (the_prog psegs pstage inp en) (mo0 psegs lim en inp).
Proof.
  intros lim en inp Hlim He Hi.
  pose proof (prog_no_enomem_any psegs pstage Plain.M.init_pc Plain.M.phdrs lim segs_pu_P Hlim) as Hne.
  destruct (prog_model_ok (CE__:=run_ceiling en) (raw_malloc_some (CE__:=run_ceiling en)) psegs pstage _ _ lim en inp segs_pu_P He Hi
              (run_ceiling_eqA _ _ _ _ _ (vie_va_size _ Hi) He) (Hne en inp He Hi)) as [Hl Hs].
  split; [exact (impl_P en inp He Hi)|]. split; [exact Hl|].
  exact (tsafe_conj nstep nsafe unforced _ _ Hs (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced (Hne en inp He Hi))).
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration, at every limit of at least
    [KLIM + SMALLREQ]. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain en inp -> valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z), KLIM + SMALLREQ <= lim ->
  ~ run_scfg_budget_refused cfg OSSVerify.simdjson.fuzz_atpointer.Images.plain lim en inp.
Proof.
  intros en inp He Hi Hlen cfg lim Hlim.
  destruct (plain_tree lim en inp Hlim He Hi) as (Ht & Hl & Hs).
  assert (Hq : tsafe nstep nsafeQ (the_prog psegs pstage inp en) (mo0 psegs lim en inp)).
  { apply (tsafe_mono nstep (fun n mo => nsafeU n mo /\ (fun n (_ : Model) => nalloc n) n mo) nsafeQ).
    - intros n mo H. exact H.
    - apply (tsafe_conj nstep nsafeU (fun n (_ : Model) => nalloc n)); [exact Hs|].
      apply tall_tsafe. exact (usage_tall (run_ceiling en) psegs pstage (in_argv inp) Hlen). }
  exact (run_never_budget_refused psegs Plain.M.init_pc Plain.M.phdrs lim en inp cfg _ _ Ht Hl Hq (vie_reader inp Hi)).
Qed.

Lemma klim_le_asan : KLIM + SMALLREQ <= Budgets.Asan.lim_source.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma klim_le_standard : KLIM + SMALLREQ <= Budgets.Standard.lim_source.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(** The plain build's premises hold together at [Premises.witness_input true]
    and the entry [Premises.valid_input_abort_entry] gives for it, the budget
    premise under every configuration and at every limit of at least
    [KLIM + SMALLREQ]. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain en inp /\ valid_input_abort inp /\
  forall (cfg : SpuriousCfg) (lim : Z), KLIM + SMALLREQ <= lim ->
    ~ run_scfg_budget_refused cfg OSSVerify.simdjson.fuzz_atpointer.Images.plain lim en inp.
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain (Premises.witness_input true)
    OSSVerify.simdjson.fuzz_atpointer.Images.plain_wf Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  intros cfg lim Hlim.
  assert (Hlen : (length (in_argv (Premises.witness_input true)) <> 2)%nat) by (cbn; discriminate).
  exact (usage_never_refused en _ Hen (valid_input_either_of_valid_input_abort _ Premises.witness_valid_input_abort)
           Hlen cfg lim Hlim).
Qed.

(** [Statements.asan_agrees], which the released [Theorems.strong_universal_error_free_fuzz_atpointer_asan]
    proves, at entries and an input that meet all four of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.asan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_atpointer.Images.asan inp
    OSSVerify.simdjson.fuzz_atpointer.Images.asan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Asan.lim_source klim_le_asan) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Theorems.strong_universal_error_free_fuzz_atpointer_asan en_plain en_san inp Hp Hs Hinp Hb).
Qed.

(** [Statements.ubsan_agrees] and the released [Theorems.strong_universal_error_free_fuzz_atpointer_ubsan],
    likewise. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Standard.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.ubsan
        Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_atpointer.Images.ubsan inp
    OSSVerify.simdjson.fuzz_atpointer.Images.ubsan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Standard.lim_source klim_le_standard) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Theorems.strong_universal_error_free_fuzz_atpointer_ubsan en_plain en_san inp Hp Hs Hinp Hb).
Qed.

(** [Statements.asan_ubsan_agrees] and the released
    [Theorems.strong_universal_error_free_fuzz_atpointer_both], likewise. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.plain en_plain inp /\
    valid_entry OSSVerify.simdjson.fuzz_atpointer.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
        Budgets.Asan.lim_source en_plain inp)
    /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.asan_ubsan
        Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.simdjson.fuzz_atpointer.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct plain_budget_witness as (en_plain & inp & Hp & Hinp & Hnr).
  destruct (Premises.valid_input_abort_entry OSSVerify.simdjson.fuzz_atpointer.Images.asan_ubsan inp
    OSSVerify.simdjson.fuzz_atpointer.Images.asan_ubsan_wf Hinp) as [en_san Hs].
  pose proof (Hnr Env.alloc_forced_only Budgets.Asan.lim_source klim_le_asan) as Hb.
  exists en_plain, en_san, inp.
  split; [exact Hp|]. split; [exact Hs|]. split; [exact Hinp|]. split; [exact Hb|].
  exact (OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Theorems.strong_universal_error_free_fuzz_atpointer_both en_plain en_san inp Hp Hs Hinp Hb).
Qed.
