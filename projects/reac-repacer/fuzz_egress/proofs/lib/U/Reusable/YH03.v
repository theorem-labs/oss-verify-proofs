(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_egress; only the definitions this unit's files use are kept, each value moved to fuzz_egress's image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit's symtab; src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.reac_repacer.fuzz_egress.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x127cc.
Definition src0_A_target_run : Z := 0x12a9c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12c6c.
Definition src0_A_stack_chk_fail : Z := 0x13fd0.
Definition src0_A_syscall_ret : Z := 0x140bc.
Definition src0_A_errno_location : Z := 0x140f4.
Definition src0_A_free : Z := 0x14100.
Definition src0_A_malloc : Z := 0x14240.
Definition src0_A_libc_free : Z := 0x14244.
Definition src0_A_get_meta : Z := 0x14410.
Definition src0_A_nontrivial_free : Z := 0x14520.
Definition src0_A_alloc_meta : Z := 0x148f8.
Definition src0_A_libc_malloc_impl : Z := 0x14bd0.
Definition src0_A_alloc_slot : Z := 0x14f40.
Definition src0_A_enframe : Z := 0x157e4.
Definition src0_A_malloc_allzerop : Z := 0x15934.
Definition src0_A_vm_wait : Z := 0x15aac.
Definition src0_A_mmap : Z := 0x15ab0.
Definition src0_A_mprotect : Z := 0x15b9c.
Definition src0_A_munmap : Z := 0x15be4.
Definition src0_A_stdio_read : Z := 0x0. (* no such symbol in this image (no __stdio_read and no fopen are linked, so no sink FILE exists); unused (sink_none): 0 is the read slot of the image's FILE objects, __stdout_FILE + 64, measured *)
Definition src0_A_stdio_write : Z := 0x16484.
Definition src0_A_stdio_seek : Z := 0x16614.
Definition src0_A_stdio_close : Z := 0x16458.
Definition src0_A_memcpy : Z := 0x1b0b0.
Definition src0_A_memset : Z := 0x1b4b4.
Definition src0_A_strnlen : Z := 0x1b5ac.
Definition src0_A_memchr : Z := 0x1b5f0.
Definition src0_A_lock : Z := 0x1b6bc.
Definition src0_A_unlock : Z := 0x1b944.
Definition src0_A_syscall_cp_c : Z := 0x1b9b8.
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
Definition src0_D_got_stack_chk_guard : Z := 0x1cb30.
Definition src0_D_read_stage : Z := 0x1dda9.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2ddc0.
Definition src0_D_stack_chk_guard : Z := 0x4e120.
Definition src0_D_libc : Z := 0x4e140.
Definition src0_D_malloc_lock : Z := 0x4e1b0.
Definition src0_D_malloc_context : Z := 0x4e1b8.
Definition src0_D_ofl_lock : Z := 0x4e568.
Definition src0_D_ofl_head : Z := 0x4e570.
Definition src0_vmlock : option Z := None.
