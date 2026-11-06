(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Frame Exec ITree Nodes Zp3 Image Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel Obligations ProofBase TopPlain.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prog Zfb Canon Zfv Zft.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Zfc Zf3.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z10a.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section TargetSide.
Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).

Definition S3s_stmt : Prop :=
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input inp ->
    srealizes tsegs (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (canonT (argv_Z (in_argv inp)) (in_fs inp)).

Theorem T_canon : S3s_stmt ->
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage tsegs tpc tph) target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (run_scfg ACFG (mkImage tsegs tpc tph) target_alloc_limit en inp).
Proof.
  intros HS en inp He Hi. pose proof (HS en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  split.
  - intros tr. exact (srealizes_obs_iff tsegs _ _ Hr tr).
  - exact (srealizes_no_error tsegs _ _ Hr).
Qed.

Definition S3s_stmt_e : Prop :=
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input_either inp ->
    srealizes tsegs (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (canonT (argv_Z (in_argv inp)) (in_fs inp)).

Theorem T_canon_e : S3s_stmt_e ->
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage tsegs tpc tph) target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (run_scfg ACFG (mkImage tsegs tpc tph) target_alloc_limit en inp).
Proof.
  intros HS en inp He Hi. pose proof (HS en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  split.
  - intros tr. exact (srealizes_obs_iff tsegs _ _ Hr tr).
  - exact (srealizes_no_error tsegs _ _ Hr).
Qed.

Lemma S3s_of_e : S3s_stmt_e -> S3s_stmt.
Proof. intros H en inp He Hi. exact (H en inp He (valid_input_either_of_valid_input _ Hi)). Qed.

Theorem error_free_of_S3s :
  impl_P_stmt ->
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
  S3s_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage tsegs tpc tph).
Proof.
  intros HP Hne HS enS enT inp HeS HeT Hi.
  destruct (P_canon HP Hne enS inp HeS (valid_input_either_of_valid_input _ Hi)) as [HtrP HerrP].
  destruct (T_canon HS enT inp HeT Hi) as [HtrT HerrT].
  split; [exact HerrP|]. split; [exact HerrT|].
  intros tr. rewrite (HtrP tr). symmetry. exact (HtrT tr).
Qed.

End TargetSide.
