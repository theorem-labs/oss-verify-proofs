(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Notation S0FR A mm j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb :=
  (rw_cells s0segs mm (bv_unsigned (a_sp A) + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 f88; C8 f96;
      C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192; C8 f200;
      C8 f208; C8 f216;
      CB 8 pb; C8 (a_s11 A); C8 (a_s10 A); C8 (a_s9 A); C8 (a_s8 A); C8 (a_s7 A); C8 (a_s6 A); C8 (a_s5 A);
      C8 (a_s4 A); C8 (a_s3 A); C8 (a_s2 A); C8 (a_s1 A); C8 (a_s0 A); C8 (a_ra A)]) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma rw_cells_merge_firstn : forall segs m A cs (k : nat),
  rw_cells segs m A cs -> rw_cells segs m A (CB (cells_size (firstn k cs)) (cells_bytes (firstn k cs)) :: skipn k cs).
Proof.
  intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H.
  pose proof (rw_cells_merge segs m A [] (firstn k cs) (skipn k cs)) as M. cbn [app] in M. apply M. exact H.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_merge_mid : forall segs m A cs (p k : nat),
  rw_cells segs m A cs ->
  rw_cells segs m A (firstn p cs ++ CB (cells_size (firstn k (skipn p cs))) (cells_bytes (firstn k (skipn p cs))) :: skipn k (skipn p cs)).
Proof.
  intros segs m A cs p k H. rewrite <- (firstn_skipn p cs) in H. rewrite <- (firstn_skipn k (skipn p cs)) in H.
  apply (rw_cells_merge segs m A (firstn p cs) (firstn k (skipn p cs)) (skipn k (skipn p cs))). exact H.
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac s2img := cbn [di_segs di_got di_stderrp di_crc di_rnums di_dec DI_S0] in *.
Section ACeilS2. Context {ACEIL__ : ACeil}.


Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation POST := (POST14 DI_S0 A).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End R.

End ACeilS2.
