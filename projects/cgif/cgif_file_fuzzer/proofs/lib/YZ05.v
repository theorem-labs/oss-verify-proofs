(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YZ03 YD2p.
Definition strong_universal_error_free_cgif_file_fuzzer_both_closed :=
strong_universal_error_free_cgif_file_fuzzer_both_of_tfib TFIB_T_closed.
