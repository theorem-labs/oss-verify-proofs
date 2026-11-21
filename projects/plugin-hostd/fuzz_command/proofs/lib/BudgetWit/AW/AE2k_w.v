(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build; the fopen/fclose wrapper, REAL and GOT definitions and their two tfib_icells cells are dropped (fuzz_command's image has neither function); A_RWA, A_WB, A_TRAILER and A_PATH, cgif's sink-file strings, are 0, since fuzz_command's image holds none of them and nothing fuzz_command reaches reads them. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x604c90.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
