(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan, index/binaries.tsv: eacfa205...); the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_boxreg.asan holds none of them (no fopen or fclose function or interceptor; the driver writes no file, see A/AD2k.v), so tfib_K's four string fields are 0; and tfib_owned is the sink's own static cells (ak_owned), as in libreac/fuzz_grant's copy (a working branch). *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: two internal commit ids removed from a line above. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Sources: fuzz_boxreg.nm.txt for the addresses. A_ofl_head = ofl_head. (A/AE2k.v's note on the other
   cells and addresses describes declarations this twin does not keep.) *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
Import ListNotations.
Open Scope Z_scope.
Definition A_ofl_head : Z := 0x5f4608.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
