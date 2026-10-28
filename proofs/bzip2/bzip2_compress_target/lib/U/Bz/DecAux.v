(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzInv BzContracts DecCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
From Stdlib Require Import List. Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
Section ACeilS2. Context {ACEIL__ : ACeil}.


Definition selm_ok (l : list byte) (n ng : Z) : Prop :=
  forall k, (0 <= k < n)%Z -> exists b, nth_error l (Z.to_nat k) = Some b /\ (bv_unsigned b < ng)%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS2.
