(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 24 address literal(s) rewritten, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: cgif's output-file strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen/fclose wrapper, real-function and GOT names dropped (fuzz_manifest.asan has none of them); tfib_K and tfib_icells without them; FF_mask moved to fuzz_manifest.asan's copy of the constant at 0x10398. *)
(* Modified by Theorem Labs, 2026-10: the sink kit is a Theorem Labs lane's shared parameter form (a working branch) instantiated for fuzz_manifest: tfib_owned is the sink's own static cells (ak_owned) and tfib_K's four string fields are 0 (fuzz_manifest writes no file). *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5f5468.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
