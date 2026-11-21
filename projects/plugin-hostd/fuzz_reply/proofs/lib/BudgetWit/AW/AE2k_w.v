(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (24 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: the fopen/fclose trampolines, musl fopen/fclose and their interception GOT cells (FF_*_fopen, FF_*_fclose) and cgif's sink strings (A_RWA, A_WB, A_TRAILER, A_PATH) have no twin in fuzz_reply.asan: cut from the definitions, from tfib_icells and from tfib_K (see Reusable/YE00.v). *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5f9b68.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
