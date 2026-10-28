(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_adrain F_afreeC_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.

(* [comment removed for export] *)
Local Ltac drain_tail MX FR ST sp :=
  step; step; zstep; step; step;             (* [comment removed for export] *)
  step;                                      (* [comment removed for export] *)
  apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX;
  step;                                      (* [comment removed for export] *)
  let K3 := fresh "K3" in
  step; step; step; if_cases K3; zify_cond K3; [exfalso; unfold Q_MAX in *; lia|];   (* [comment removed for export] *)
  zstep; step; step; zstep; zstep; zstep; zstep; zstep;   (* [comment removed for export] *)
  apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX; change (0 + 256 * 0) with 0 in MX;
  amo_step; lits;                            (* [comment removed for export] *)
  do 4 zstep;                                (* [comment removed for export] *)
  amo_step;                                  (* [comment removed for export] *)
  step; if_lit;                              (* [comment removed for export] *)
  zstep; zstep; step; if_lit;                (* [comment removed for export] *)
  apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX;
  step;                                      (* [comment removed for export] *)
  do 6 step;                                 (* [comment removed for export] *)
  step;                                      (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp);
  unfold drain_torec_post; finish.

Section CANSEC1. Context {rc : runConstT}.
Theorem drain_torec : drain_torec_stmt.
Proof.
  unfold drain_torec_stmt.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GQ63 GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, Q_MIN, Q_CACHE, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xcca08, 0xcca08 + 4);
                          (0xcca10, 0xcca10 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - destruct GFULL as (GNB1 & GLB & GL0 & GL1 & DTG).
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. step. zstep.                   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    drain_tail MX FR ST sp.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].    (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    drain_tail MX FR ST sp.
    subst gnb. exact GC.
Qed.
End CANSEC1.
