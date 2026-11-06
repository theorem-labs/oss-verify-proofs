(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *) (* Modified by Theorem Labs, 2026-10: the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) are removed, as fuzz_decode.asan-ubsan holds none of them (the donor's 0x20dc0 output-path string, 0x20e20 "wb", 0x200e6 "rwa" and 0x20e60 ";" have no counterpart in this image), so tfib_K's four string fields are 0 and asink_strs is never stated; the fopen and fclose cells are already deleted by the release's delete-with-uses; tfib_owned is the sink's own static cells *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x4159c.
Definition FF_pc_wrap_fwrite : Z := 0x415b4.

Definition FF_pc_wrap_fflush : Z := 0x415f0.

Definition FF_real_strchr : Z := 0x92b14.
Definition FF_real_fwrite : Z := 0x8ebcc.

Definition FF_real_fflush : Z := 0x8e660.

Definition FF_got_strchr : Z := 0x9b010.
Definition FF_got_fwrite : Z := 0x9b040.

Definition FF_got_fflush : Z := 0x9b0a8.

Definition FF_meta_ptr : Z := 0xa0b80.
Definition FF_meta_mem : Z := 0xa0b88.
Definition FF_got_cflags : Z := 0x992d8.
Definition FF_cflags : Z := 0x132e68.
Definition FF_got_shadow : Z := 0x992e8.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f49c8.
Definition A_ofl_head : Z := 0x5f49d0.
Definition A_threaded : Z := 0x5f4569.
Definition A_need_locks : Z := 0x5f456b.
Definition A_stdio_read : Z := 0x8e1f0.
Definition A_stdio_write : Z := 0x8e310.
Definition A_stdio_seek : Z := 0x8e308.
Definition A_stdio_close : Z := 0x8e1c4.
Definition FF_got_canary : Z := 0x99f88.
Definition FF_canary : Z := 0x5f4318.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103b8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_decode writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
