(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
#[global] Instance ubs0_sink_head : sink_head := {| sk_ofl_head := ubs0_D_ofl_head |}.
Definition CBL_STK_U : Z := 80.
