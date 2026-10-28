(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition di_in_img (I : dimg) : Prop :=
  (65536 <= di_got I /\ di_got I + 40 <= 212992 /\ 65536 <= di_stderrp I /\ di_stderrp I + 8 <= 212992 /\
   65536 <= di_rnums I /\ di_rnums I + 2048 <= 212992)%Z.
(* [comment removed for export] *)
Definition di_in_img_b (I : dimg) : bool :=
  ((65536 <=? di_got I) && (di_got I + 40 <=? 212992) && (65536 <=? di_stderrp I) && (di_stderrp I + 8 <=? 212992) &&
   (65536 <=? di_rnums I) && (di_rnums I + 2048 <=? 212992))%bool%Z.
Lemma di_in_img_ok : forall I, di_in_img_b I = true -> di_in_img I.
Proof.
  intros I H. unfold di_in_img_b in H. rewrite !Bool.andb_true_iff in H. rewrite !Z.leb_le in H. unfold di_in_img. tauto.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACeilS1. Context {ACEIL__ : ACeil}.

Section GbKit.
  Variables (fr : Z) (A : act14).
  Hypothesis AOK : act_ok fr A.
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation usp := (bv_unsigned (a_sp A)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Section Close.
    Variable I : dimg.
    Hypothesis IOK : di_in_img I.
    Let segs := di_segs I.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    (* [comment removed for export] *)
  End Close.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End GbKit.
End ACeilS1.
