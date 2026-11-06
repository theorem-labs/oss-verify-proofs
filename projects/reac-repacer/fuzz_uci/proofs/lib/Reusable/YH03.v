(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_uci; only the definitions this unit's files use are kept, each value moved to fuzz_uci's image by symbol and offset (section bounds from its section headers); src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.reac_repacer.fuzz_uci.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x126c4.
Definition src0_A_target_run : Z := 0x12994.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12b64.
Definition src0_A_stack_chk_fail : Z := 0x13cc4.
Definition src0_A_syscall_ret : Z := 0x13ccc.
Definition src0_A_errno_location : Z := 0x13d04.
Definition src0_A_free : Z := 0x13d10.
Definition src0_A_malloc : Z := 0x13e50.
Definition src0_A_libc_free : Z := 0x13e54.
Definition src0_A_get_meta : Z := 0x14020.
Definition src0_A_nontrivial_free : Z := 0x14130.
Definition src0_A_alloc_meta : Z := 0x14508.
Definition src0_A_libc_malloc_impl : Z := 0x147e0.
Definition src0_A_alloc_slot : Z := 0x14b50.
Definition src0_A_enframe : Z := 0x153f4.
Definition src0_A_malloc_allzerop : Z := 0x15544.
Definition src0_A_vm_wait : Z := 0x156bc.
Definition src0_A_mmap : Z := 0x156c0.
Definition src0_A_mprotect : Z := 0x157ac.
Definition src0_A_munmap : Z := 0x157f4.
Definition src0_A_stdio_read : Z := 0x15f50.
Definition src0_A_stdio_write : Z := 0x16094.
Definition src0_A_stdio_seek : Z := 0x161f8.
Definition src0_A_stdio_close : Z := 0x16068.
Definition src0_A_memcpy : Z := 0x1ad58.
Definition src0_A_memset : Z := 0x1b15c.
Definition src0_A_strnlen : Z := 0x1b254.
Definition src0_A_memchr : Z := 0x1ac8c.
Definition src0_A_lock : Z := 0x1b298.
Definition src0_A_unlock : Z := 0x1b520.
Definition src0_A_syscall_cp_c : Z := 0x1b594.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_rwa : Z := 0x102ed.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103a8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103b8.
Definition src0_D_debruijn32 : Z := 0x10444.
Definition src0_D_size_classes : Z := 0x10464.
Definition src0_D_small_cnt_tab : Z := 0x104c4.
Definition src0_D_med_cnt_tab : Z := 0x104df.
Definition src0_D_got_stack_chk_guard : Z := 0x1c708.
Definition src0_D_read_stage : Z := 0x1d979.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2d990.
Definition src0_D_stack_chk_guard : Z := 0x4dcf0.
Definition src0_D_libc : Z := 0x4dd10.
Definition src0_D_malloc_lock : Z := 0x4dd80.
Definition src0_D_malloc_context : Z := 0x4dd88.
Definition src0_D_ofl_lock : Z := 0x4e138.
Definition src0_D_ofl_head : Z := 0x4e140.
Definition src0_vmlock : option Z := None.
