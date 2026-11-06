(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v, with its module paths changed (fuzz_boxreg's ASan+UBSan core is lib/B, under the A core's file names) and its addresses moved to libreac/fuzz_boxreg's ASan+UBSan build (fuzz_boxreg.asan-ubsan, index/binaries.tsv at c8557374ad2e: 7620eb05...); the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells (FF_pc_wrap_, FF_real_ and FF_got_ of both, and their two tfib_icells rows) are removed, as fuzz_boxreg.asan-ubsan holds none of them (no fopen or fclose function or interceptor; the driver writes no file, see the B twin of A/AD2k.v), so tfib_K's four string fields are 0; and tfib_owned is the sink's own static cells (ak_owned), as in libreac/fuzz_grant's copy of the ASan twin (a working branch 4d244de18f0, lib/A/AE2k.v). *)
(* Sources: fuzz_boxreg.nm.txt for the addresses; the image's bytes for the cell values.
   FF_pc_wrap_<f> = __interceptor_trampoline_<f> (= __wrap_<f>); FF_real_<f> = musl's <f>; FF_got_<f> =
   _ZN14__interception11real_<f>E, a .data cell whose image value is FF_real_<f> (read by __interceptor_strchr+0x48,
   __interceptor_fwrite+0x40, __interceptor_fflush+0x20).
   FF_meta_ptr / FF_meta_mem = _ZL24interceptor_metadata_map / _ZZL28InitializeCommonInterceptorsvE12metadata_mem (.bss;
   the start-up stores are in the B twin of A/AD2k.v). FF_got_cflags = the .got word whose image value is
   &__sanitizer::common_flags_dont_use (FF_cflags). FF_got_shadow = the .got word whose image value is
   &__asan_shadow_memory_dynamic_address (0xa13b8); __asan::SealedReserveShadow stores FF_SB through it (0x599c4-0x599cc).
   FF_got_canary = the .got word whose image value is &__stack_chk_guard (FF_canary).
   A_ofl_lock / A_ofl_head = ofl_lock / ofl_head; A_threaded / A_need_locks = __libc + 1 / __libc + 3; A_stdio_<f> =
   __stdio_<f>. FF_mask = the .rodata word at 0x103a0, image value FF_mask_val, read by
   __sanitizer::AddrHashMap<CommonInterceptorMetadata, 31051>::acquire / release (0x4777c, 0x47f70, 0x48158). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x4145c.
Definition FF_pc_wrap_fwrite : Z := 0x41474.
Definition FF_pc_wrap_fflush : Z := 0x414b0.
Definition FF_real_strchr : Z := 0x92aa4.
Definition FF_real_fwrite : Z := 0x8eb5c.
Definition FF_real_fflush : Z := 0x8e5f0.
Definition FF_got_strchr : Z := 0x9aff0.
Definition FF_got_fwrite : Z := 0x9b020.
Definition FF_got_fflush : Z := 0x9b088.
Definition FF_meta_ptr : Z := 0xa0c00.
Definition FF_meta_mem : Z := 0xa0c08.
Definition FF_got_cflags : Z := 0x992c8.
Definition FF_cflags : Z := 0x132ee8.
Definition FF_got_shadow : Z := 0x992d8.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f4a40.
Definition A_ofl_head : Z := 0x5f4a48.
Definition A_threaded : Z := 0x5f45e1.
Definition A_need_locks : Z := 0x5f45e3.
Definition A_stdio_read : Z := 0x8e180.
Definition A_stdio_write : Z := 0x8e2a0.
Definition A_stdio_seek : Z := 0x8e298.
Definition A_stdio_close : Z := 0x8e154.
Definition FF_got_canary : Z := 0x99f60.
Definition FF_canary : Z := 0x5f4390.
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
