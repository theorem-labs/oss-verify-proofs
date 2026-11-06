(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_egress; only the definitions this unit's files use are kept, each value moved to fuzz_egress's image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit's symtab; src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.reac_repacer.fuzz_egress.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x127c0.
Definition src0_A_target_run : Z := 0x12a90.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12c60.
Definition src0_A_stack_chk_fail : Z := 0x13da0.
Definition src0_A_syscall_ret : Z := 0x13e8c.
Definition src0_A_errno_location : Z := 0x13ec4.
Definition src0_A_free : Z := 0x13ed0.
Definition src0_A_malloc : Z := 0x14010.
Definition src0_A_libc_free : Z := 0x14014.
Definition src0_A_get_meta : Z := 0x141e0.
Definition src0_A_nontrivial_free : Z := 0x142f0.
Definition src0_A_alloc_meta : Z := 0x146c8.
Definition src0_A_libc_malloc_impl : Z := 0x149a0.
Definition src0_A_alloc_slot : Z := 0x14d10.
Definition src0_A_enframe : Z := 0x155b4.
Definition src0_A_malloc_allzerop : Z := 0x15704.
Definition src0_A_vm_wait : Z := 0x1587c.
Definition src0_A_mmap : Z := 0x15880.
Definition src0_A_mprotect : Z := 0x1596c.
Definition src0_A_munmap : Z := 0x159b4.
Definition src0_A_stdio_read : Z := 0x0. (* no such symbol in this image (no __stdio_read and no fopen are linked, so no sink FILE exists); unused (sink_none): 0 is the read slot of the image's FILE objects, __stdout_FILE + 64, measured *)
Definition src0_A_stdio_write : Z := 0x16254.
Definition src0_A_stdio_seek : Z := 0x163e4.
Definition src0_A_stdio_close : Z := 0x16228.
Definition src0_A_memcpy : Z := 0x1ae80.
Definition src0_A_memset : Z := 0x1b284.
Definition src0_A_strnlen : Z := 0x1b37c.
Definition src0_A_memchr : Z := 0x1b3c0.
Definition src0_A_lock : Z := 0x1b48c.
Definition src0_A_unlock : Z := 0x1b714.
Definition src0_A_syscall_cp_c : Z := 0x1b788.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_rwa : Z := 0x102ed.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103c0.
Definition src0_D_debruijn32 : Z := 0x10454.
Definition src0_D_size_classes : Z := 0x10474.
Definition src0_D_small_cnt_tab : Z := 0x104d4.
Definition src0_D_med_cnt_tab : Z := 0x104ef.
Definition src0_D_got_stack_chk_guard : Z := 0x1c900.
Definition src0_D_read_stage : Z := 0x1db79.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2db90.
Definition src0_D_stack_chk_guard : Z := 0x4def0.
Definition src0_D_libc : Z := 0x4df10.
Definition src0_D_malloc_lock : Z := 0x4df80.
Definition src0_D_malloc_context : Z := 0x4df88.
Definition src0_D_ofl_lock : Z := 0x4e338.
Definition src0_D_ofl_head : Z := 0x4e340.
Definition src0_vmlock : option Z := None.
