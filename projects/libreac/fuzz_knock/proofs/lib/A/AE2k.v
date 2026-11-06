(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; tfib_K follows a Theorem Labs lane's shared sink form: the four string fields are 0 (fuzz_knock writes no file) and tfib_owned is the sink's own static cells (ak_owned). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x40eb8.
Definition FF_pc_wrap_fwrite : Z := 0x40ecc.
Definition FF_pc_wrap_fflush : Z := 0x40f08.
Definition FF_real_strchr : Z := 0x8fe04.
Definition FF_real_fwrite : Z := 0x8bec0.
Definition FF_real_fflush : Z := 0x8b954.
Definition FF_got_strchr : Z := 0x982e0.
Definition FF_got_fwrite : Z := 0x98308.
Definition FF_got_fflush : Z := 0x98370.
Definition FF_meta_ptr : Z := 0x9dd80.
Definition FF_meta_mem : Z := 0x9dd88.
Definition FF_got_cflags : Z := 0x965c0.
Definition FF_cflags : Z := 0x130068.
Definition FF_got_shadow : Z := 0x965d0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f1bc0.
Definition A_ofl_head : Z := 0x5f1bc8.
Definition A_threaded : Z := 0x5f1761.
Definition A_need_locks : Z := 0x5f1763.
Definition A_stdio_read : Z := 0x8b4e4.
Definition A_stdio_write : Z := 0x8b604.
Definition A_stdio_seek : Z := 0x8b5fc.
Definition A_stdio_close : Z := 0x8b4b8.
Definition FF_got_canary : Z := 0x97258.
Definition FF_canary : Z := 0x5f1510.
Definition tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.   (* knock asan ofl_head 0x5f1bc8; not an instance: every SK use names it (@ ... tfib_sink_head), so no inferred sink_head can reach the core *)
Definition FF_mask : Z := 0x10390.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_knock writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
