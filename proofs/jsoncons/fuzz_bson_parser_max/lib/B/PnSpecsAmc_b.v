(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.

Module PMAMC.
Definition mcmp_cells (C : asan_statics_cells) : Prop :=
  In (0x140918, 1, 1) (asc_cells C) /\ In (0x1392f8, 8, 0x1298d0) (asc_cells C) /\ In (0x1d1866, 1, 1) (asc_cells C) /\ In (0x1d1867, 1, 1) (asc_cells C).
Definition mcmp_cells_b (C : asan_statics_cells) : Prop :=
  In (0x1408d8, 1, 1) (asc_cells C) /\ In (0x1392b8, 8, 0x129894) (asc_cells C) /\ In (0x1d1826, 1, 1) (asc_cells C) /\ In (0x1d1827, 1, 1) (asc_cells C).   (* [comment removed for export] *)
End PMAMC.
