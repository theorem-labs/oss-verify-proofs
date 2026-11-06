(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpCarve CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_cmp_smV A0_b2c_hcV A0_b2c_wrV AsanKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueCarve.
Local Open Scope Z_scope.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition STRMD (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 w56 w64 w72 : word) : list cell :=
  [C8 w0; C4 w8; C4 w12; C4 w16; CB 4 q1; C8 w24; C4 w32; C4 w36; C4 w40; CB 4 q2; C8 w48; C8 w56; C8 w64; C8 w72].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DISAVED (v0 s3 s2 s1 s0 ra : word) : list cell := [C8 v0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition DHEAD2 (strm small : Z) (p20 p4 p3 pv p12 : list byte) : list cell :=
  [C8 (Z_to_bv 64 strm); C4 (Z_to_bv 64 10); CB 20 p20; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   CB 4 p4; C1 (Z_to_bv 8 small); CB 3 p3; C4 (Z_to_bv 64 0); CB 4 pv; CB 12 p12].
Definition DHEAD3 (strm small verb : Z) (p20 p4 p3 p12 : list byte) : list cell :=
  [C8 (Z_to_bv 64 strm); C4 (Z_to_bv 64 10); CB 20 p20; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   CB 4 p4; C1 (Z_to_bv 8 small); CB 3 p3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 verb); CB 12 p12].
(* [comment removed for export] *)
Definition DMID2 (q24 q12 q4 : list byte) : list cell := [CB 24 q24; CB 12 q12; C4 (Z_to_bv 64 0); CB 4 q4].

Section WithSegs.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Lemma rw_cells_recell : forall m A cs cs', rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
    rw_cells segs m A cs'.
  Proof. intros m A cs cs' [[Hwf Hb] Hw] W' B' S'. split; [split; [exact W'| rewrite B'; exact Hb]| rewrite S'; exact Hw]. Qed.

  (* [comment removed for export] *)
  Lemma DHEAD3_init : forall m S strm small p20 p4 p3 p12,
    rw_cells segs m S (DHEAD3 strm small 0 p20 p4 p3 p12) -> rw_cells segs m S (GlueCarve.dhead_init strm small p20 p4 p3 p12).
  Proof.
    intros m S strm small p20 p4 p3 p12 H. eapply rw_cells_recell; [exact H| | reflexivity| reflexivity].
    destruct H as [[W _] _]. unfold DHEAD3, GlueCarve.dhead_init in *. cbn [cells_wf cell_wf] in *. tauto.
  Qed.
  (* [comment removed for export] *)
  Lemma DMID3_init : forall m A q12 q4,
    rw_cells segs m A [CB 24 (repeat (Z_to_bv 8 0) 24); CB 12 q12; C4 (Z_to_bv 64 0); CB 4 q4] -> rw_cells segs m A (GlueCarve.dmid_init q12 q4).
  Proof.
    intros m A q12 q4 H. eapply rw_cells_recell; [exact H| | reflexivity| reflexivity].
    destruct H as [[W _] _]. unfold GlueCarve.dmid_init. cbn [cells_wf cell_wf] in *. tauto.
  Qed.
End WithSegs.

End ACeilS1.
