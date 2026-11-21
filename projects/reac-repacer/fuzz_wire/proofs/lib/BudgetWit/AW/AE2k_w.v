(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v at theorem-labs/oss-verify-proofs@6b32741d849a, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_grant.asan holds none of them, so tfib_K's four string fields are 0; FF_got_fflush is real_fflush's cell in that build; and tfib_owned is the sink's own static cells (ak_owned). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AE2k.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5f3e08.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
(* fuzz_wire writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
