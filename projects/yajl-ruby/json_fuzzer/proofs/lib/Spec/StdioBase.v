(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record stdout_st := mkStdout {
  so_active : bool;      (* [comment removed for export] *)
  so_buf : list Z;        (* [comment removed for export] *)
  so_lbf_nl : bool;      (* [comment removed for export] *)
  so_first : bool         (* [comment removed for export] *)
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.
