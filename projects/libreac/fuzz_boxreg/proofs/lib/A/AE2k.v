(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan, index/binaries.tsv at c8557374ad2e: eacfa205...); the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_boxreg.asan holds none of them (no fopen or fclose function or interceptor; the driver writes no file, see A/AD2k.v), so tfib_K's four string fields are 0; and tfib_owned is the sink's own static cells (ak_owned), as in libreac/fuzz_grant's copy (a working branch 4d244de18f0). *)
(* Sources: fuzz_boxreg.nm.txt for the addresses; the image's bytes for the cell values.
   FF_pc_wrap_<f> = __interceptor_trampoline_<f> (= __wrap_<f>); FF_real_<f> = musl's <f>; FF_got_<f> =
   _ZN14__interception11real_<f>E, a .data cell whose image value is FF_real_<f> (read by __interceptor_strchr+0x48,
   __interceptor_fwrite+0x40, __interceptor_fflush+0x20).
   FF_meta_ptr / FF_meta_mem = _ZL24interceptor_metadata_map / _ZZL28InitializeCommonInterceptorsvE12metadata_mem (.bss;
   the start-up stores are in A/AD2k.v). FF_got_cflags = the .got word whose image value is
   &__sanitizer::common_flags_dont_use (FF_cflags). FF_got_shadow = the .got word whose image value is
   &__asan_shadow_memory_dynamic_address (0xa0f78); __asan::SealedReserveShadow stores FF_SB through it (0x59964-0x5996c).
   FF_got_canary = the .got word whose image value is &__stack_chk_guard (FF_canary).
   A_ofl_lock / A_ofl_head = ofl_lock / ofl_head; A_threaded / A_need_locks = __libc + 1 / __libc + 3; A_stdio_<f> =
   __stdio_<f>. FF_mask = the .rodata word at 0x103a0, image value FF_mask_val, read by
   __sanitizer::AddrHashMap<CommonInterceptorMetadata, 31051>::acquire / release (0x4771c, 0x47f10, 0x480f8). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x413fc.
Definition FF_pc_wrap_fwrite : Z := 0x41414.
Definition FF_pc_wrap_fflush : Z := 0x41450.
Definition FF_real_strchr : Z := 0x92680.
Definition FF_real_fwrite : Z := 0x8e738.
Definition FF_real_fflush : Z := 0x8e1cc.
Definition FF_got_strchr : Z := 0x9abd0.
Definition FF_got_fwrite : Z := 0x9ac00.
Definition FF_got_fflush : Z := 0x9ac68.
Definition FF_meta_ptr : Z := 0xa07c0.
Definition FF_meta_mem : Z := 0xa07c8.
Definition FF_got_cflags : Z := 0x98ea8.
Definition FF_cflags : Z := 0x132aa8.
Definition FF_got_shadow : Z := 0x98eb8.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f4600.
Definition A_ofl_head : Z := 0x5f4608.
Definition A_threaded : Z := 0x5f41a1.
Definition A_need_locks : Z := 0x5f41a3.
Definition A_stdio_read : Z := 0x8dd5c.
Definition A_stdio_write : Z := 0x8de7c.
Definition A_stdio_seek : Z := 0x8de74.
Definition A_stdio_close : Z := 0x8dd30.
Definition FF_got_canary : Z := 0x99b40.
Definition FF_canary : Z := 0x5f3f50.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_boxreg writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
