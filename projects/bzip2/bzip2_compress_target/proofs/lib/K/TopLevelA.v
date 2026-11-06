(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require Import CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Section TargetSide.
Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).

(* [comment removed for export] *)
Definition S3s_stmt : Prop :=
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input_either inp ->
    srealizes tsegs (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (canonT (argv_Z (in_argv inp)) (in_fs inp)).

Theorem T_canon : S3s_stmt ->
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage tsegs tpc tph) target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage tsegs tpc tph) target_alloc_limit en inp).
Proof.
  intros HS en inp He Hi. pose proof (HS en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [Run.run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  change (Run.alloc_only_cfg false) with kit_cfg.
  split.
  - intros tr. exact (srealizes_obs_iff tsegs _ _ Hr tr).
  - exact (srealizes_no_error tsegs _ _ Hr).
Qed.

(* [comment removed for export] *)

End TargetSide.

(* [comment removed for export] *)
