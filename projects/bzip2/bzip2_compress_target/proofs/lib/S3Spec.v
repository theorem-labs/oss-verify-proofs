(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.  (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export Spec.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition NAME : list byte := s2b "generate_temporary_file.aef000".

Inductive fd_outcome : Type := FO_keep | FO_empty | FO_full | FO_gone.

(* [comment removed for export] *)
Definition fs_apply (o : fd_outcome) (cp : list byte) (fs : Fs.Fs) : Fs.Fs :=
  match o with
  | FO_keep  => fs
  | FO_empty => fs_set fs NAME []
  | FO_full  => fs_set fs NAME cp
  | FO_gone  => fs_remove (fs_set fs NAME []) NAME   (* [comment removed for export] *)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fd_reachable (fs : Fs.Fs) (o : fd_outcome) : Prop :=
  fs_under fs NAME = false \/ o = FO_keep.

(* [comment removed for export] *)
Definition t_fd_union (fs : Fs.Fs) (K : fd_outcome -> TSet) : TSet :=
  fun tr => exists o, fd_reachable fs o /\ K o tr.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCompressor.
  (* [comment removed for export] *)
  Variable C : list byte -> list byte.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WithCompressor.
