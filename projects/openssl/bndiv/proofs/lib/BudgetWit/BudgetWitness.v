(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from TopBndivHaltsP.v and TopBndivPlain.v: the budget-premise witness for the plain build on the usage path, and the lemmas that apply the released proofs of the four statements whose budget premise names the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_unfiltered is stated over the run's segment list run_segments and its initial configuration init_config, rewritten with init_config_run; the walk is carried to that list with RsLift.impl_rs_nodes; mo0_minv takes the channel-reader conjunct). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage ITree Nodes RegsEquiv.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import RsLift.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopHalts TopBndivPlain.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
Require OSSVerify.openssl.bndiv.images.Plain.
From OSSVerify.Proofs.openssl.bndiv.lib Require Theorems.
From OSSVerify.Proofs.openssl.bndiv.lib.BudgetWit Require Import NoAlloc UsageNA.
From OSSVerify.openssl.bndiv Require Images Statements.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Import Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * openssl / bndiv: the plain build's budget premise holds on the usage path

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

    The proof uses the released tree of the plain build
    ([ProgGDet.the_progG], with [TopBndivPlain.implG_plain] and
    [ProgGDet.progG_model_ok_run]) unchanged: [UsageNA.usage_tree_na] shows
    that, when argc <> 2, every node of that tree is one of the four
    non-allocating nodes, and [NoAlloc.tree_never_refused] turns that into the
    budget premise, for every spurious-failure configuration and every
    limit ([usage_never_refused]).  [plain_budget_witness] is the three
    premises of [plain_halts] at one entry and one input; each
    [<statement>_not_vacuous] gives the premises of that statement together
    to its released proof, so its conclusion holds at an entry and an input
    that meet all of them, with no hypothesis left. *)

(** The run of the plain build reaches no budget-refused configuration under
    the unfiltered step, when argv has not two entries. *)
Lemma usage_unfiltered : forall en inp lim,
  valid_entry OSSVerify.openssl.bndiv.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  ~ reaches_budget_refused (run_segments psegs inp (en_sp en) (en_mmap_base en))
      (init_config (run_segments psegs inp (en_sp en) (en_mmap_base en)) Plain.M.init_pc Plain.M.phdrs
         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp).
Proof.
  intros en inp lim Hen Hinp Hlen.
  (* LPS 727298f3: the run reads [run_segments psegs inp sp mbase] = psegs ++ tail, and
     its initial model is [mo0] ([TopLevel.init_config_run]). *)
  rewrite (init_config_run psegs Plain.M.init_pc Plain.M.phdrs lim en inp).
  pose proof (valid_input_either_of_valid_input inp Hinp) as Hvi.
  pose proof (usage_tree_na LM_bndiv psegs pstage inp en Hlen) as Hna.
  destruct (progG_model_ok_run (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv
              Pcap_nonneg caps H_init H_one bn_H_rc
              psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit image_low_psegs lim_source_ok
              en inp Hen Hvi) as [Hl _].
  set (tail := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  pose proof (vdso_segments_inert (in_kernel inp) (en_sp en) (en_mmap_base en)) as Hin. fold tail in Hin.
  change (run_segments psegs inp (en_sp en) (en_mmap_base en)) with (psegs ++ tail).
  pose proof (impl_rs_nodes psegs tail Hin _ (the_progG (LM := LM_bndiv) psegs pstage inp en) _
                (ms0 psegs Plain.M.init_pc Plain.M.phdrs en inp) (implG_plain en inp Hen Hvi)) as HI'.
  change (rs_ms psegs tail (ms0 psegs Plain.M.init_pc Plain.M.phdrs en inp))
    with (ms0 (psegs ++ tail) Plain.M.init_pc Plain.M.phdrs en inp) in HI'.
  eapply (tree_never_refused (psegs ++ tail) _ (the_progG (LM := LM_bndiv) psegs pstage inp en) _
            (ms0 (psegs ++ tail) Plain.M.init_pc Plain.M.phdrs en inp)).
  - exact (init_machine_state_eqv (psegs ++ tail) Plain.M.init_pc Plain.M.phdrs (en_sp en) (en_mmap_base en)
             (en_draw en) inp).
  - split; [exact HI'|].
    split; [exact (leaves_setL _ _ (mo0 psegs lim en inp) source_alloc_limit Hna Hl)|].
    split; [apply mo0_not_halted|]. split; [apply mo0_minv; exact (vie_reader _ Hvi)|].
    exact (tsafe_na _ _ _ Hna).
  - exact Hna.
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the limit: the run-level form ([agrees] premises). *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.openssl.bndiv.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.openssl.bndiv.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen lim.
  pose proof (usage_unfiltered en inp lim Hen Hinp Hlen) as H.
  destruct en as [sp brk mbase rnd]. exact H.
Qed.

(** ...and so whatever the spurious-failure configuration
    ([Run.run_scfg_budget_refused_sub]). *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.openssl.bndiv.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.openssl.bndiv.Images.plain lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim
           (run_scfg_budget_refused_sub cfg OSSVerify.openssl.bndiv.Images.plain lim en inp Hr)).
Qed.

(** At [Premises.witness_input false], argc = 1. *)
Lemma witness_never_refused : forall en (cfg : SpuriousCfg) (lim : Z),
  valid_entry OSSVerify.openssl.bndiv.Images.plain en (Premises.witness_input false) ->
  ~ run_scfg_budget_refused cfg OSSVerify.openssl.bndiv.Images.plain lim en (Premises.witness_input false).
Proof.
  intros en cfg lim Hen.
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [plain_halts]'s three premises hold together: at
    [Premises.witness_input false] and the entry [Premises.valid_input_entry]
    gives for it. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.openssl.bndiv.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.openssl.bndiv.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.plain (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  exact (witness_never_refused en forced_only_cfg Budgets.Standard.lim_source Hen).
Qed.

(** [Statements.plain_halts] ([halts_within_budget Budgets.Standard.lim_source
    Exits.ok_or_refused Images.plain]), which the released
    [Theorems.halts_allowed_openssl_bndiv_halts_plain] proves, at an entry
    and an input that meet all three of its premises. *)
Theorem plain_halts_not_vacuous :
  exists en inp,
    valid_entry OSSVerify.openssl.bndiv.Images.plain en inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.openssl.bndiv.Images.plain
        Budgets.Standard.lim_source en inp /\
    must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.openssl.bndiv.Images.plain
      Budgets.Standard.lim_source en inp.
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.openssl.bndiv.lib.Theorems.halts_allowed_openssl_bndiv_halts_plain en inp Hen Hinp Hnr).
Qed.

(** [Statements.ubsan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain
    Images.ubsan]), which the released
    [Theorems.strong_universal_error_free_bndiv_ubsan] proves, at entries and
    an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.openssl.bndiv.Images.plain en_plain inp /\
    valid_entry OSSVerify.openssl.bndiv.Images.ubsan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                  Budgets.Standard.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                                 Budgets.Standard.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.ubsan
                                 Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.plain (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.ubsan (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.ubsan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Standard.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_ubsan
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.

(** [Statements.asan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain
    Images.asan]), which the released
    [Theorems.strong_universal_error_free_bndiv_asan] proves, at entries and
    an input that meet all four of its premises. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.openssl.bndiv.Images.plain en_plain inp /\
    valid_entry OSSVerify.openssl.bndiv.Images.asan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                  Budgets.Asan.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.asan
                     Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.asan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.plain (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.asan (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.asan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_asan
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.

(** [Statements.asan_ubsan_agrees] ([agrees_in Env.alloc_forced_only
    Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain
    Images.asan_ubsan]), which the released
    [Theorems.strong_universal_error_free_bndiv_both] proves, at entries and
    an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
    valid_entry OSSVerify.openssl.bndiv.Images.plain en_plain inp /\
    valid_entry OSSVerify.openssl.bndiv.Images.asan_ubsan en_san inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                  Budgets.Asan.lim_source en_plain inp)
    /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.plain
                                 Budgets.Asan.lim_source en_plain inp))
                   (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.openssl.bndiv.Images.asan_ubsan
                                 Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.plain (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.plain_wf Premises.witness_valid_input) as [ep Hep].
  destruct (Premises.valid_input_entry OSSVerify.openssl.bndiv.Images.asan_ubsan (Premises.witness_input false)
    OSSVerify.openssl.bndiv.Images.asan_ubsan_wf Premises.witness_valid_input) as [es Hes].
  pose proof (witness_never_refused ep Env.alloc_forced_only Budgets.Asan.lim_source Hep) as Hnr.
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [exact Hnr |]]]].
  exact (OSSVerify.Proofs.openssl.bndiv.lib.Theorems.strong_universal_error_free_bndiv_both
           ep es _ Hep Hes Premises.witness_valid_input Hnr).
Qed.
