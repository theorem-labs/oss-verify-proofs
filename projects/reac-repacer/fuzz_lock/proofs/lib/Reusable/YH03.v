(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_lock; only the definitions this unit's files use are kept, each value moved to fuzz_lock's image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit's symtab; src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.reac_repacer.fuzz_lock.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x126d8.
Definition src0_A_target_run : Z := 0x129a8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12b78.
Definition src0_A_stack_chk_fail : Z := 0x13e50.
Definition src0_A_syscall_ret : Z := 0x13e58.
Definition src0_A_errno_location : Z := 0x13e90.
Definition src0_A_free : Z := 0x13e9c.
Definition src0_A_malloc : Z := 0x13fdc.
Definition src0_A_libc_free : Z := 0x13fe0.
Definition src0_A_get_meta : Z := 0x141ac.
Definition src0_A_nontrivial_free : Z := 0x142bc.
Definition src0_A_alloc_meta : Z := 0x14694.
Definition src0_A_libc_malloc_impl : Z := 0x1496c.
Definition src0_A_alloc_slot : Z := 0x14cdc.
Definition src0_A_enframe : Z := 0x15580.
Definition src0_A_malloc_allzerop : Z := 0x156d0.
Definition src0_A_vm_wait : Z := 0x15848.
Definition src0_A_mmap : Z := 0x1584c.
Definition src0_A_mprotect : Z := 0x15938.
Definition src0_A_munmap : Z := 0x15980.
Definition src0_A_stdio_read : Z := 0x0. (* no such symbol in this image (no __stdio_read and no fopen are linked, so no sink FILE exists); unused (sink_none): 0 is the read slot of the image's FILE objects, __stdout_FILE + 64, measured *)
Definition src0_A_stdio_write : Z := 0x16220.
Definition src0_A_stdio_seek : Z := 0x163b0.
Definition src0_A_stdio_close : Z := 0x161f4.
Definition src0_A_memcpy : Z := 0x1af18.
Definition src0_A_memset : Z := 0x1b31c.
Definition src0_A_strnlen : Z := 0x1b4a4.
Definition src0_A_memchr : Z := 0x1ae1c.
Definition src0_A_lock : Z := 0x1b4e8.
Definition src0_A_unlock : Z := 0x1b770.
Definition src0_A_syscall_cp_c : Z := 0x1b7e4.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_rwa : Z := 0x102ed.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10620.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10630.
Definition src0_D_debruijn32 : Z := 0x10414.
Definition src0_D_size_classes : Z := 0x10434.
Definition src0_D_small_cnt_tab : Z := 0x10494.
Definition src0_D_med_cnt_tab : Z := 0x104af.
Definition src0_D_got_stack_chk_guard : Z := 0x1c958.
Definition src0_D_read_stage : Z := 0x1dbc9.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2dbe0.
Definition src0_D_stack_chk_guard : Z := 0x4df40.
Definition src0_D_libc : Z := 0x4df60.
Definition src0_D_malloc_lock : Z := 0x4dfd0.
Definition src0_D_malloc_context : Z := 0x4dfd8.
Definition src0_D_ofl_lock : Z := 0x4e388.
Definition src0_D_ofl_head : Z := 0x4e390.
Definition src0_vmlock : option Z := None.
