(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.

Module PMAMC.
Definition mcmp_cells (C : asan_statics_cells) : Prop :=
  In (0x13e498, 1, 1) (asc_cells C) /\ In (0x136e10, 8, 0x127324) (asc_cells C) /\ In (0x1cf3e6, 1, 1) (asc_cells C) /\ In (0x1cf3e7, 1, 1) (asc_cells C).
Definition mcmp_cells_b (C : asan_statics_cells) : Prop :=
  In (0x1408d8, 1, 1) (asc_cells C) /\ In (0x1392b8, 8, 0x129894) (asc_cells C) /\ In (0x1d1826, 1, 1) (asc_cells C) /\ In (0x1d1827, 1, 1) (asc_cells C).   (* [comment removed for export] *)
End PMAMC.
