(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_uci; only the definitions this unit's files use are kept, each value moved to fuzz_uci's image by symbol and offset (section bounds from its section headers); src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.reac_repacer.fuzz_uci.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x126c8.
Definition src0_A_target_run : Z := 0x12998.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12b68.
Definition src0_A_stack_chk_fail : Z := 0x13de8.
Definition src0_A_syscall_ret : Z := 0x13df0.
Definition src0_A_errno_location : Z := 0x13e28.
Definition src0_A_free : Z := 0x13e34.
Definition src0_A_malloc : Z := 0x13f74.
Definition src0_A_libc_free : Z := 0x13f78.
Definition src0_A_get_meta : Z := 0x14144.
Definition src0_A_nontrivial_free : Z := 0x14254.
Definition src0_A_alloc_meta : Z := 0x1462c.
Definition src0_A_libc_malloc_impl : Z := 0x14904.
Definition src0_A_alloc_slot : Z := 0x14c74.
Definition src0_A_enframe : Z := 0x15518.
Definition src0_A_malloc_allzerop : Z := 0x15668.
Definition src0_A_vm_wait : Z := 0x157e0.
Definition src0_A_mmap : Z := 0x157e4.
Definition src0_A_mprotect : Z := 0x158d0.
Definition src0_A_munmap : Z := 0x15918.
Definition src0_A_stdio_read : Z := 0x16074.
Definition src0_A_stdio_write : Z := 0x161b8.
Definition src0_A_stdio_seek : Z := 0x1631c.
Definition src0_A_stdio_close : Z := 0x1618c.
Definition src0_A_memcpy : Z := 0x1ae7c.
Definition src0_A_memset : Z := 0x1b280.
Definition src0_A_strnlen : Z := 0x1b378.
Definition src0_A_memchr : Z := 0x1adb0.
Definition src0_A_lock : Z := 0x1b3bc.
Definition src0_A_unlock : Z := 0x1b644.
Definition src0_A_syscall_cp_c : Z := 0x1b6b8.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_rwa : Z := 0x102ed.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10600.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10610.
Definition src0_D_debruijn32 : Z := 0x103f4.
Definition src0_D_size_classes : Z := 0x10414.
Definition src0_D_small_cnt_tab : Z := 0x10474.
Definition src0_D_med_cnt_tab : Z := 0x1048f.
Definition src0_D_got_stack_chk_guard : Z := 0x1c830.
Definition src0_D_read_stage : Z := 0x1daa9.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2dac0.
Definition src0_D_stack_chk_guard : Z := 0x4de20.
Definition src0_D_libc : Z := 0x4de40.
Definition src0_D_malloc_lock : Z := 0x4deb0.
Definition src0_D_malloc_context : Z := 0x4deb8.
Definition src0_D_ofl_lock : Z := 0x4e268.
Definition src0_D_ofl_head : Z := 0x4e270.
Definition src0_vmlock : option Z := None.
