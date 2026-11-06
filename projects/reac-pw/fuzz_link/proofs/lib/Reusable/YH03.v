(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* v1.9 port: definitions no file names were removed (a Theorem Labs lane, 2026-10-28); they carried cgif / v1.8 addresses. *)
(* YH03 address fix (a Theorem Labs lane, 2026-10-29): three used constants corrected for the v1.9 PLAIN PIN s/fuzz_pcap/fuzz_pcap.plain, sha256 1e8e7da32456ca11..., symbols read from its unstripped twin x/unstripped/fuzz_pcap/fuzz_pcap.plain, sha256 89ec1ad3a6a6... (twin and pin differ only in ELF section-header fields and the build-id note): src0_A_stdio_read 0x19a70 -> 0x16778 and src0_A_stdio_seek 0x19f20 -> 0x19f4c (the .symtab addresses of __stdio_read and __stdio_seek), src0_D_str_rwa 0x10388 -> 0x1038e (the only NUL-terminated "rwa" in .rodata). src0_D_str_tmp_out_gif, src0_D_str_wb and src0_D_str_3 keep their values: pcap's image has no counterpart string, so each carries a comment below. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x13000.
Definition src0_A_target_run : Z := 0x132d0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x1384c.
Definition src0_A_stack_chk_fail : Z := 0x1725c.
Definition src0_A_syscall_ret : Z := 0x17264.
Definition src0_A_errno_location : Z := 0x16e04.
Definition src0_A_free : Z := 0x173d4.
Definition src0_A_malloc : Z := 0x17514.
Definition src0_A_libc_free : Z := 0x17518.
Definition src0_A_get_meta : Z := 0x176e4.
Definition src0_A_nontrivial_free : Z := 0x177f4.
Definition src0_A_alloc_meta : Z := 0x17bcc.
Definition src0_A_libc_malloc_impl : Z := 0x17ea4.
Definition src0_A_alloc_slot : Z := 0x18214.
Definition src0_A_enframe : Z := 0x18ab8.
Definition src0_A_vm_wait : Z := 0x18d80.
Definition src0_A_mmap : Z := 0x18d84.
Definition src0_A_mprotect : Z := 0x18e70.
Definition src0_A_munmap : Z := 0x18eb8.
Definition src0_A_stdio_write : Z := 0x19dbc.
Definition src0_A_stdio_seek : Z := 0x19f4c.
Definition src0_A_stdio_close : Z := 0x19d90.
Definition src0_A_memcpy : Z := 0x1ec5c.
Definition src0_A_memset : Z := 0x1f060.
Definition src0_A_strnlen : Z := 0x1f39c.
Definition src0_A_memchr : Z := 0x1eb60.
Definition src0_A_lock : Z := 0x1f3e0.
Definition src0_A_unlock : Z := 0x1f668.
Definition src0_A_syscall_cp_c : Z := 0x1f6dc.
Definition src0_D_str_rwa : Z := 0x10594.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10668.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10678.
Definition src0_D_debruijn32 : Z := 0x10778.
Definition src0_D_size_classes : Z := 0x10798.
Definition src0_D_small_cnt_tab : Z := 0x107f8.
Definition src0_D_med_cnt_tab : Z := 0x10813.
Definition src0_D_got_stack_chk_guard : Z := 0x208d8.
Definition src0_D_read_stage : Z := 0x21b49.
Definition src0_D_aef_aligned_copy_empty : Z := 0x31b60.
Definition src0_D_stack_chk_guard : Z := 0x95878.
Definition src0_D_libc : Z := 0x95898.
Definition src0_D_malloc_lock : Z := 0x95908.
Definition src0_D_malloc_context : Z := 0x95910.
Definition src0_D_ofl_lock : Z := 0x95cc0.
Definition src0_D_ofl_head : Z := 0x95cc8.
Definition src0_vmlock : option Z := None.
