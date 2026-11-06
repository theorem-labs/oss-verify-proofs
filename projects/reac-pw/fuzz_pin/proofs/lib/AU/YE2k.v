(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build; the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_scene.asan holds none of them (it links no fopen or fclose and writes no file), so tfib_K's four string fields are 0; FF_got_fflush is real_fflush's cell in that build (__interception::real_fflush + 0); FF_got_canary and FF_got_shadow are that build's .got cells of __stack_chk_guard and __asan_shadow_memory_dynamic_address; and tfib_owned is the sink's own static cells (ak_owned). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE2k.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AE2k.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AE2k.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x41918.
Definition FF_pc_wrap_fwrite : Z := 0x41934.
Definition FF_pc_wrap_fflush : Z := 0x41970.
Definition FF_real_strchr : Z := 0x9181c.
Definition FF_real_fwrite : Z := 0x8d8d4.
Definition FF_real_fflush : Z := 0x8d368.
Definition FF_got_strchr : Z := 0x9ae88.
Definition FF_got_fwrite : Z := 0x9aec0.
Definition FF_got_fflush : Z := 0x9af28.
Definition FF_meta_ptr : Z := 0xa0f40.
Definition FF_meta_mem : Z := 0xa0f48.
Definition FF_got_cflags : Z := 0x99160.
Definition FF_cflags : Z := 0x133228.
Definition FF_got_shadow : Z := 0x99170.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f4d88.
Definition A_ofl_head : Z := 0x5f4d90.
Definition A_threaded : Z := 0x5f4929.
Definition A_need_locks : Z := 0x5f492b.
Definition A_stdio_read : Z := 0x8cef8.
Definition A_stdio_write : Z := 0x8d018.
Definition A_stdio_seek : Z := 0x8d010.
Definition A_stdio_close : Z := 0x8cecc.
Definition FF_got_canary : Z := 0x99df8.
Definition FF_canary : Z := 0x5f46d8.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
(* FF_mask / FF_mask_val re-measured on scene's pins: the 8 bytes at 0x103a0 are 0xafffff00000fffff in both images, an anonymous .rodata constant that scene's own code loads (h-rw-pre-6 13:55Z; h-rw-kno-3 14:27Z: 39 ld in 38 functions). *)
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
