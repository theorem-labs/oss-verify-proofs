(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


Definition sd_facts (e : est) (nG nSel : Z) : Prop :=
  let A := e_nInUse e + 2 in let NM := e_nMTF e in
  (3 <= A <= 258) /\ (2 <= nG <= 6) /\ (1 <= nSel <= 18002) /\ (1 <= NM) /\ (2 * (NM + 50) <= ARR1_SIZE) /\
  zbok (e_arr1 e) /\
  (forall i, 0 <= i < NM -> 0 <= mtfv_at (e_arr1 e) i < A) /\
  (forall k, 0 <= k < 256 -> zdef (e_inUse e) k = true /\ 0 <= zget (e_inUse e) k < 256) /\
  (forall i, 0 <= i < nSel -> zdef (e_selectorMtf e) i = true /\ 0 <= zget (e_selectorMtf e) i < nG) /\
  (forall i, 0 <= i < nSel -> zdef (e_selector e) i = true /\ 0 <= zget (e_selector e) i < nG) /\
  (forall t v, 0 <= t < nG -> 0 <= v < A -> zdef (e_len e) (258 * t + v) = true /\ 1 <= zget (e_len e) (258 * t + v) <= 17) /\
  (forall t v, 0 <= t < nG -> 0 <= v < A -> zdef (e_code e) (258 * t + v) = true /\ 0 <= zget (e_code e) (258 * t + v) < 4294967296) /\
  (forall b, snd (sm_put_data (Z.to_nat (NM + 1)) b (e_len e) (e_code e) (e_arr1 e) (e_selector e) NM 0 0) = nSel).

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
