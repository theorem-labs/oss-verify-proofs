(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from E2/Top/Final_ubsan.v, E2/Top/Halts_ubsan.v and E2/Equiv/HaltsFinal.v: the budget-premise witness for the UBSan build on the usage path, and the lemma that applies the released proof of the statement whose budget premise names the UBSan build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: usage_unfiltered runs over the run's segments (the binary's with the vDSO pair appended) from the new init_machine_state, the released tree lifted onto them by RsLift.impl_rs_nodes as TopLevel.run_of_tree lifts it, with NoAlloc.tree_never_refused at the walk's own peek function (RsLift.nodes_sound_rs), and usage_never_refused_run reads the run's start through TopLevel.init_config_run. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes RegsEquiv ImgTgtUbsan RsLift.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Theorems.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.BudgetWit Require Import NoAlloc UsageNA.
From OSSVerify.libpcap.fuzz_pcap Require Images.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Import Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * libpcap / fuzz_pcap: the UBSan build's budget premise holds on the usage path

    One statement of this harness carries the budget premise on the UBSan
    build: [ubsan_halts], [~ run_scfg_budget_refused forced_only_cfg
    Images.ubsan Budgets.Standard.lim_source en inp].  This file gives that
    premise as [../BudgetWitness.v] gives the plain build's: the released
    tree of the UBSan build is the same [EquivPlan.ptree] over [usegs]
    ([EquivPlan.treeS] at [usegs], [Final_ubsan.tbT] and [Final_ubsan.stkT],
    with [Final_ubsan.IMPL_T_final], as [Halts_ubsan.fuzz_pcap_halts_ubsan]
    gives them to [HaltsFinal.halts_final]), so [UsageNA.ptree_na] and
    [NoAlloc.tree_never_refused] apply to it unchanged; only the image, the
    segments and the start-up facts differ.

    The input is [Premises.witness_input false]: one empty argument
    (argc = 1).  With argc <> 2 the driver writes its usage line to fd 2 and
    exits with status 2, making only set_tid_address (96), writev (66), ioctl
    (29), lseek (62) and exit or exit_group (93, 94): no allocation call, and
    no lazy mapping. *)

(** The released tree of the UBSan build is a tree of the run at
    [target_alloc_limit] ([Final_ubsan.image_ok_ubsan]). *)
Lemma tree_ok_ubsan :
  exists Q, tree_ok usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit (treeS usegs tbT stkT sec) Q.
Proof.
  apply (tree_ok_S_final usegs Ubsan.M.init_pc Ubsan.M.phdrs tbT stkT sec sec_range target_alloc_limit image_ok_ubsan).
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.TwB.tls_in_image_usegs.
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_T _ A B).
  - exact IMPL_T_final.
Qed.

(** The run of the UBSan build reaches no budget-refused configuration under
    the unfiltered step, when argv has not two entries. *)
Lemma usage_unfiltered : forall en inp lim,
  valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  ~ reaches_budget_refused (run_segments usegs inp (en_sp en) (en_mmap_base en))
      (mkCfg (init_machine_state (run_segments usegs inp (en_sp en) (en_mmap_base en)) Ubsan.M.init_pc Ubsan.M.phdrs
                (en_sp en) (en_mmap_base en) (en_draw en) inp)
             (mo0 usegs lim en inp)).
Proof.
  intros en inp lim Hen Hinp Hlen.
  destruct tree_ok_ubsan as [Q HTS].
  destruct (HTS en inp Hen Hinp) as (Himpl & Hl & Hs).
  pose proof (ptree_na usegs tbT stkT sec inp en Hlen) as Hna.
  (* the run walks the binary's segments with the vDSO pair appended; the tree is lifted
     onto them by [RsLift.impl_rs_nodes], as [TopLevel.run_of_tree] lifts it *)
  set (tail := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  pose proof (vdso_segments_inert (in_kernel inp) (en_sp en) (en_mmap_base en)) as Hin. fold tail in Hin.
  change (run_segments usegs inp (en_sp en) (en_mmap_base en)) with (usegs ++ tail).
  pose proof (impl_rs_nodes usegs tail Hin _ (treeS usegs tbT stkT sec inp en) Q
                (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp) Himpl) as Himpl'.
  change (rs_ms usegs tail (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp))
    with (ms0 (usegs ++ tail) Ubsan.M.init_pc Ubsan.M.phdrs en inp) in Himpl'.
  eapply (tree_never_refused (usegs ++ tail) (npeek usegs) (nodes_sound_rs usegs tail) _ (treeS usegs tbT stkT sec inp en) _
            (ms0 (usegs ++ tail) Ubsan.M.init_pc Ubsan.M.phdrs en inp)).
  - exact (init_machine_state_eqv (usegs ++ tail) Ubsan.M.init_pc Ubsan.M.phdrs (en_sp en) (en_mmap_base en) (en_draw en) inp).
  - split; [exact Himpl'|]. split.
    { apply (leaves_setL _ (treeS usegs tbT stkT sec inp en) (mo0 usegs lim en inp) target_alloc_limit Hna).
      rewrite mo0_setL. exact Hl. }
    split; [apply mo0_not_halted|]. split; [exact (mo0_minv usegs lim en inp Hinp)|].
    apply (tsafe_setL _ (treeS usegs tbT stkT sec inp en) (mo0 usegs lim en inp) target_alloc_limit Hna).
    rewrite mo0_setL. exact Hs.
  - exact Hna.
Qed.

(** On every valid entry of the UBSan build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the limit: the run-level form. *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall lim : Z, ~ run_budget_refused OSSVerify.libpcap.fuzz_pcap.Images.ubsan lim en inp.
Proof.
  intros en inp Hen Hinp Hlen lim.
  pose proof (usage_unfiltered en inp lim Hen Hinp Hlen) as H.
  rewrite <- init_config_run in H.
  destruct en as [sp brk mbase rnd]. exact H.
Qed.

(** ...and so whatever the spurious-failure configuration
    ([Run.run_scfg_budget_refused_sub]). *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.libpcap.fuzz_pcap.Images.ubsan lim en inp.
Proof.
  intros en inp Hen Hinp Hlen cfg lim Hr.
  exact (usage_never_refused_run en inp Hen Hinp Hlen lim
           (run_scfg_budget_refused_sub cfg OSSVerify.libpcap.fuzz_pcap.Images.ubsan lim en inp Hr)).
Qed.

(** At [Premises.witness_input false], argc = 1. *)
Lemma witness_never_refused : forall en (cfg : SpuriousCfg) (lim : Z),
  valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en (Premises.witness_input false) ->
  ~ run_scfg_budget_refused cfg OSSVerify.libpcap.fuzz_pcap.Images.ubsan lim en (Premises.witness_input false).
Proof.
  intros en cfg lim Hen.
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** [ubsan_halts]'s three premises hold together: at
    [Premises.witness_input false] and the entry [Premises.valid_input_entry]
    gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.libpcap.fuzz_pcap.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan (Premises.witness_input false)
    OSSVerify.libpcap.fuzz_pcap.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  exact (witness_never_refused en forced_only_cfg Budgets.Standard.lim_source Hen).
Qed.

(** [Statements.ubsan_halts] ([halts_within_budget Budgets.Standard.lim_source
    Exits.ok_or_refused Images.ubsan]), which the released
    [Theorems.halts_allowed_libpcap_fuzz_pcap_halts_ubsan] proves, at an entry
    and an input that meet all three of its premises. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp,
    valid_entry OSSVerify.libpcap.fuzz_pcap.Images.ubsan en inp /\
    valid_input inp /\
    ~ run_scfg_budget_refused forced_only_cfg OSSVerify.libpcap.fuzz_pcap.Images.ubsan
        Budgets.Standard.lim_source en inp /\
    must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libpcap.fuzz_pcap.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Theorems.halts_allowed_libpcap_fuzz_pcap_halts_ubsan en inp Hen Hinp Hnr).
Qed.
