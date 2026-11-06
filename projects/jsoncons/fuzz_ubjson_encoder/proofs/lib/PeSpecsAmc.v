(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.

Module PMAMC.
Definition mcmp_cells (C : asan_statics_cells) : Prop :=
  In (0x1426d8, 1, 1) (asc_cells C) /\ In (0x13aff0, 8, 0x12b458) (asc_cells C) /\ In (0x1d3626, 1, 1) (asc_cells C) /\ In (0x1d3627, 1, 1) (asc_cells C).
Definition mcmp_cells_b (C : asan_statics_cells) : Prop :=
  In (0x146dd8, 1, 1) (asc_cells C) /\ In (0x13f700, 8, 0x12fc00) (asc_cells C) /\ In (0x1d7d26, 1, 1) (asc_cells C) /\ In (0x1d7d27, 1, 1) (asc_cells C).   (* [comment removed for export] *)
End PMAMC.
