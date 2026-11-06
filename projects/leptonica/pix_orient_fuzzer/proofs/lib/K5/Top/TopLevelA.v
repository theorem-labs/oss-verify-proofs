(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prog Canon.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section TargetSide.
Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).

(* [comment removed for export] *)
Definition S3s_stmt : Prop :=
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input inp ->
    srealizes tsegs (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (canonT (argv_Z (in_argv inp)) (in_fs inp)).

Theorem T_canon : S3s_stmt ->
  forall en inp,
    valid_entry (mkImage tsegs tpc tph) en inp -> valid_input inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage tsegs tpc tph) target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage tsegs tpc tph) target_alloc_limit en inp).
Proof.
  intros HS en inp He Hi. pose proof (HS en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [Run.run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  split.
  - intros tr. exact (srealizes_obs_iff tsegs _ _ Hr tr).
  - exact (srealizes_no_error tsegs _ _ Hr).
Qed.

End TargetSide.
