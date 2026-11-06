(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_scene.asan-ubsan holds none of them (it links no fopen or fclose and writes no file), so tfib_K's four string fields are 0; FF_got_fflush is real_fflush's cell in that build (__interception::real_fflush + 0); and tfib_owned is the sink's own static cells (ak_owned). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x44330.
Definition FF_pc_wrap_fwrite : Z := 0x44348.
Definition FF_pc_wrap_fflush : Z := 0x44384.
Definition FF_real_strchr : Z := 0x9526c.
Definition FF_real_fwrite : Z := 0x91324.
Definition FF_real_fflush : Z := 0x90db8.
Definition FF_got_strchr : Z := 0x9d758.
Definition FF_got_fwrite : Z := 0x9d788.
Definition FF_got_fflush : Z := 0x9d7f0.
Definition FF_meta_ptr : Z := 0xa3340.
Definition FF_meta_mem : Z := 0xa3348.
Definition FF_got_cflags : Z := 0x9ba30.
Definition FF_cflags : Z := 0x135628.
Definition FF_got_shadow : Z := 0x9ba40.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f7188.
Definition A_ofl_head : Z := 0x5f7190.
Definition A_threaded : Z := 0x5f6d29.
Definition A_need_locks : Z := 0x5f6d2b.
Definition A_stdio_read : Z := 0x90948.
Definition A_stdio_write : Z := 0x90a68.
Definition A_stdio_seek : Z := 0x90a60.
Definition A_stdio_close : Z := 0x9091c.
Definition FF_got_canary : Z := 0x9c6d0.
Definition FF_canary : Z := 0x5f6ad8.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
(* FF_mask / FF_mask_val re-measured on scene's pins: the 8 bytes at 0x103a0 are 0xafffff00000fffff in both images, an anonymous .rodata constant that scene's own code loads (a Theorem Labs lane 13:55Z; a Theorem Labs lane 14:27Z: 39 ld in 38 functions). *)
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_scene writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
