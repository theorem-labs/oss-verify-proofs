(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.
Module PMAMC.
Definition mcmp_cells (C : asan_statics_cells) : Prop :=
In (0x13b9d8, 1, 1) (asc_cells C) /\ In (0x134470, 8, 0x12497c) (asc_cells C) /\ In (0x1cc926, 1, 1) (asc_cells C) /\ In (0x1cc927, 1, 1) (asc_cells C).
Definition mcmp_cells_b (C : asan_statics_cells) : Prop :=
In (0x13d718, 1, 1) (asc_cells C) /\ In (0x1361d8, 8, 0x1267b4) (asc_cells C) /\ In (0x1ce666, 1, 1) (asc_cells C) /\ In (0x1ce667, 1, 1) (asc_cells C).
End PMAMC.
