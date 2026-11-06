(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition rsmr_statics (m : mem) (cnr : word) : Prop :=
  rw_cells bsegs m 0xa6228 [C8 (Z_to_bv 64 0x601590)] /\ rw_cells bsegs m 0x601590 [C8 cnr] /\ rw_cells bsegs m 0x601810 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x1401dc [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0x1401c3 [C1 (Z_to_bv 8 1)].
