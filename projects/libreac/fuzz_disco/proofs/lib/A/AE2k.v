(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build; the wrapper table keeps the wrappers fuzz_disco links (strchr, fwrite, fflush), each with its REAL() cell and target, and the canary is fuzz_disco's GOT slot of __stack_chk_guard; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) are removed, as fuzz_disco.asan holds none of them, so tfib_K's four string fields are 0; and tfib_owned is the sink's own static cells (ak_owned). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x429d0.
Definition FF_pc_wrap_fwrite : Z := 0x429e8.
Definition FF_pc_wrap_fflush : Z := 0x42a24.
Definition FF_real_strchr : Z := 0x99c6c.
Definition FF_real_fwrite : Z := 0x95d24.
Definition FF_real_fflush : Z := 0x957b8.
Definition FF_got_strchr : Z := 0xa2220.
Definition FF_got_fwrite : Z := 0xa2250.
Definition FF_got_fflush : Z := 0xa22b8.
Definition FF_meta_ptr : Z := 0xa8900.
Definition FF_meta_mem : Z := 0xa8908.
Definition FF_got_cflags : Z := 0xa0500.
Definition FF_cflags : Z := 0x13abe8.
Definition FF_got_shadow : Z := 0xa0510.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fc740.
Definition A_ofl_head : Z := 0x5fc748.
Definition A_threaded : Z := 0x5fc2e1.
Definition A_need_locks : Z := 0x5fc2e3.
Definition A_stdio_read : Z := 0x95348.
Definition A_stdio_write : Z := 0x95468.
Definition A_stdio_seek : Z := 0x95460.
Definition A_stdio_close : Z := 0x9531c.
Definition FF_got_canary : Z := 0xa1198.
Definition FF_canary : Z := 0x5fc090.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103b8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_disco writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
