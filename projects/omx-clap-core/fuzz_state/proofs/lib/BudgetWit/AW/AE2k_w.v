(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: cgif's output-file strings (A_PATH, A_WB, A_RWA, A_TRAILER) dropped (fuzz_state.asan has none of them and links no fopen or fclose), so tfib_K's four string fields are 0 and asink_strs is never stated for it. FF_mask stays 0x103c0: that is where fuzz_state.asan stores its copy of the 0xafffff00000fffff constant (file offset 0x3c0, the only copy in the image). tfib_owned is the sink's own static cells (ak_owned), the cells fuzz_state's aenv_addr named before the sink kit took the shared parameter form. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5fb628.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
