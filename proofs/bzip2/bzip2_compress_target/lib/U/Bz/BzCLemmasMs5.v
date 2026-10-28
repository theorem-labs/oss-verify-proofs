(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition step1N (qoff nb ss j : Z) (s : mss) : Prop := 0 <= s_nqs s /\ s_nqs s + nb <= 2147483647.

(* [comment removed for export] *)
Definition bigN (qoff nb : Z) (ro : zarr) (i : Z) (s : mss) : Prop :=
  forall k, (k < 256)%nat -> let s' := ms_step1 k qoff nb (zget ro i) 0 s in s_exit s' = false -> step1N qoff nb (zget ro i) (Z.of_nat k) s'.
