(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.openssl.ct.lib Require Import TopLevel Obligations ProofBase.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prog ModelInv Canon ProgDetIface ProgDet.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import ShapeAlg SpinAlg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma run_ceiling_eqA : forall segs pc ph en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  bv_unsigned (en_sp en) - stack_max_size = @alloc_ceiling (run_ceiling en).
Proof.
  intros segs pc ph en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  cbn [en_sp]. unfold run_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. cbn [en_sp].
  rewrite ceiling_of_sp_eq; [reflexivity| lia| exact H3].
Qed.
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
    trace_equiv (bh_traces (Run.run_scfg ncfg (mkImage tsegs tpc tph) target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg ncfg (mkImage tsegs tpc tph) target_alloc_limit en inp).
Proof.
  intros HS en inp He Hi. pose proof (HS en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [Run.run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  split.
  - intros tr. exact (srealizes_obs_iff tsegs _ _ Hr tr).
  - exact (srealizes_no_error tsegs _ _ Hr).
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)


End TargetSide.

(* [comment removed for export] *)
