(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacFR2 S0F_decRet S0F_decCutsM S0F_decCuts8.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_dec8A U0_dec8B U0_dec8C U0_dec8S.
Module S0F_dec_U8A := OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_dec8A.S0F_dec_U8A.
Module S0F_dec_U8B := OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_dec8B.S0F_dec_U8B.
Module S0F_dec_U8C := OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_dec8C.S0F_dec_U8C.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts8 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U8S.S0F_dec_U8A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U8S.S0F_dec_U8B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U8S.S0F_dec_U8C.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Lemma S0F_dec_U8S : forall A, act_ok 320 A -> forall F,
  S0F_cut_HEOB A F -> S0F_cut_HLIT A F -> S0F_cut_HRUN A F -> S0F_cut_SYM A F.
Proof. intros A AOK F HE HL HR. exact (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_dec8S.S0F_dec_U8S A AOK F HE HL HR). Qed.

(* [comment removed for export] *)
Lemma S0F_dec_U8 : forall A, act_ok 320 A -> forall F,
  (forall F', (F' < F)%nat -> S0F_cut_SYM A F') ->
  (forall F', (F' < F)%nat -> S0F_cut_HRUN A F') ->
  (forall F', (F' < F)%nat -> S0F_cut_HRUNEND A F') ->
  S0F_cut_HEOB A F ->
  (S0F_cut_HMTFC A F -> S0F_cut_HLIT A F) ->
  (S0F_cut_HMTFB A F -> S0F_cut_HRUN A F) ->
  (S0F_cut_SYM A F -> S0F_cut_HRUNEND A F) ->
  S0F_cut_HMTFC A F /\ S0F_cut_HLIT A F /\ S0F_cut_HMTFB A F /\ S0F_cut_HRUN A F /\
  S0F_cut_SYM A F /\ S0F_cut_HRUNEND A F /\ S0F_cut_HMTF1 A F.
Proof.
  intros A AOK F HS HR HN HE U10 U9a U9b.
  pose proof (S0F_dec_U8C A AOK F HS) as C. pose proof (U10 C) as L.
  pose proof (S0F_dec_U8B A AOK F HR HN) as B. pose proof (U9a B) as R.
  pose proof (S0F_dec_U8S A AOK F HE L R) as Y. pose proof (U9b Y) as N.
  pose proof (S0F_dec_U8A A AOK F HS) as M1.
  repeat split; assumption.
Qed.

End ACeilS1.
