(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_grant.asan holds none of them, so tfib_K's four string fields are 0; FF_got_fflush is real_fflush's cell in that build; and tfib_owned is the sink's own static cells (ak_owned). *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YE2k.v (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x41074.
Definition FF_pc_wrap_fwrite : Z := 0x41088.
Definition FF_pc_wrap_fflush : Z := 0x410c4.
Definition FF_real_strchr : Z := 0x90954.
Definition FF_real_fwrite : Z := 0x8ca10.
Definition FF_real_fflush : Z := 0x8c4a4.
Definition FF_got_strchr : Z := 0x98e38.
Definition FF_got_fwrite : Z := 0x98e60.
Definition FF_got_fflush : Z := 0x98ec8.
Definition FF_meta_ptr : Z := 0x9e940.
Definition FF_meta_mem : Z := 0x9e948.
Definition FF_got_cflags : Z := 0x97118.
Definition FF_cflags : Z := 0x130c28.
Definition FF_got_shadow : Z := 0x97128.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f2780.
Definition A_ofl_head : Z := 0x5f2788.
Definition A_threaded : Z := 0x5f2321.
Definition A_need_locks : Z := 0x5f2323.
Definition A_stdio_read : Z := 0x8c034.
Definition A_stdio_write : Z := 0x8c154.
Definition A_stdio_seek : Z := 0x8c14c.
Definition A_stdio_close : Z := 0x8c008.
Definition FF_got_canary : Z := 0x97db0.
Definition FF_canary : Z := 0x5f20d0.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_grant writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
