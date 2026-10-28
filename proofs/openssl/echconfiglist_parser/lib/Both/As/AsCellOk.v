(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition cell_ok (mem : word -> option byte) (c : Z * nat * Z) : Prop :=
  match c with (a, w, v) =>
    rdn RSEGS mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end.
Definition cells_ok (mem : word -> option byte) (cs : list (Z * nat * Z)) : Prop :=
  Forall (cell_ok mem) cs.
