(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AZ03 AD2p.
Definition strong_universal_error_free_cgif_file_fuzzer_asan_closed :=
strong_universal_error_free_cgif_file_fuzzer_asan_of_tfib TFIB_T_closed.
