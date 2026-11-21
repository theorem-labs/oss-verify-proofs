(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_scene.asan holds none of them (it links no fopen or fclose and writes no file), so tfib_K's four string fields are 0; FF_got_fflush is real_fflush's cell in that build (__interception::real_fflush + 0); FF_got_canary and FF_got_shadow are that build's .got cells of __stack_chk_guard and __asan_shadow_memory_dynamic_address; and tfib_owned is the sink's own static cells (ak_owned). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE2k.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5f0f08.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
