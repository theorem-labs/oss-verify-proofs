(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* v1.9 port: definitions no file names were removed (a Theorem Labs lane, 2026-10-28); they carried cgif / v1.8 addresses. *)
(* YH03 address fix (a Theorem Labs lane, 2026-10-29): three used constants corrected for the v1.9 UBSAN PIN s/fuzz_pcap/fuzz_pcap.ubsan, sha256 83af59086893b560..., symbols read from its unstripped twin x/unstripped/fuzz_pcap/fuzz_pcap.ubsan, sha256 da555ced6d68... (twin and pin differ only in ELF section-header fields and the build-id note): src0_A_stdio_read 0x1a2a4 -> 0x1680c and src0_A_stdio_seek 0x1a754 -> 0x1a780 (the .symtab addresses of __stdio_read and __stdio_seek), src0_D_str_rwa 0x10388 -> 0x1038e (the only NUL-terminated "rwa" in .rodata). src0_D_str_tmp_out_gif, src0_D_str_wb and src0_D_str_3 keep their values: pcap's image has no counterpart string, so each carries a comment below. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x130a0.
Definition src0_A_target_run : Z := 0x13370.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13a30.
Definition src0_A_stack_chk_fail : Z := 0x17a90.
Definition src0_A_syscall_ret : Z := 0x17a98.
Definition src0_A_errno_location : Z := 0x17638.
Definition src0_A_free : Z := 0x17c08.
Definition src0_A_malloc : Z := 0x17d48.
Definition src0_A_libc_free : Z := 0x17d4c.
Definition src0_A_get_meta : Z := 0x17f18.
Definition src0_A_nontrivial_free : Z := 0x18028.
Definition src0_A_alloc_meta : Z := 0x18400.
Definition src0_A_libc_malloc_impl : Z := 0x186d8.
Definition src0_A_alloc_slot : Z := 0x18a48.
Definition src0_A_enframe : Z := 0x192ec.
Definition src0_A_vm_wait : Z := 0x195b4.
Definition src0_A_mmap : Z := 0x195b8.
Definition src0_A_mprotect : Z := 0x196a4.
Definition src0_A_munmap : Z := 0x196ec.
Definition src0_A_stdio_write : Z := 0x1a5f0.
Definition src0_A_stdio_seek : Z := 0x1a780.
Definition src0_A_stdio_close : Z := 0x1a5c4.
Definition src0_A_memcpy : Z := 0x1f490.
Definition src0_A_memset : Z := 0x1f894.
Definition src0_A_strnlen : Z := 0x1fbd0.
Definition src0_A_memchr : Z := 0x1f394.
Definition src0_A_lock : Z := 0x1fc14.
Definition src0_A_unlock : Z := 0x1fe9c.
Definition src0_A_syscall_cp_c : Z := 0x1ff10.
Definition src0_D_str_rwa : Z := 0x10592.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10660.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10670.
Definition src0_D_debruijn32 : Z := 0x10768.
Definition src0_D_size_classes : Z := 0x10788.
Definition src0_D_small_cnt_tab : Z := 0x107e8.
Definition src0_D_med_cnt_tab : Z := 0x10803.
Definition src0_D_got_stack_chk_guard : Z := 0x21110.
Definition src0_D_read_stage : Z := 0x22389.
Definition src0_D_aef_aligned_copy_empty : Z := 0x323a0.
Definition src0_D_stack_chk_guard : Z := 0x960b8.
Definition src0_D_libc : Z := 0x960d8.
Definition src0_D_malloc_lock : Z := 0x96148.
Definition src0_D_malloc_context : Z := 0x96150.
Definition src0_D_ofl_lock : Z := 0x96500.
Definition src0_D_ofl_head : Z := 0x96508.
Definition src0_vmlock : option Z := None.
