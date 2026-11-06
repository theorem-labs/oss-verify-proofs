(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH03.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; only the definitions this unit's files use are kept, each value moved to fuzz_transport's image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit's symtab; src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x132c0.
Definition src0_A_target_run : Z := 0x13590.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13760.
Definition src0_A_stack_chk_fail : Z := 0x19444.
Definition src0_A_syscall_ret : Z := 0x1944c.
Definition src0_A_errno_location : Z := 0x19484.
Definition src0_A_free : Z := 0x19490.
Definition src0_A_malloc : Z := 0x195d0.
Definition src0_A_libc_free : Z := 0x195d4.
Definition src0_A_get_meta : Z := 0x197a0.
Definition src0_A_nontrivial_free : Z := 0x198b0.
Definition src0_A_alloc_meta : Z := 0x19c88.
Definition src0_A_libc_malloc_impl : Z := 0x19f60.
Definition src0_A_alloc_slot : Z := 0x1a2d0.
Definition src0_A_enframe : Z := 0x1ab74.
Definition src0_A_malloc_allzerop : Z := 0x1acc4.
Definition src0_A_vm_wait : Z := 0x1ae3c.
Definition src0_A_mmap : Z := 0x1ae40.
Definition src0_A_mprotect : Z := 0x1af2c.
Definition src0_A_munmap : Z := 0x1af74.
Definition src0_A_memcpy : Z := 0x20440.
Definition src0_A_memset : Z := 0x20844.
Definition src0_A_strnlen : Z := 0x20a04.
Definition src0_A_memchr : Z := 0x20a48.
Definition src0_A_lock : Z := 0x20b14.
Definition src0_A_unlock : Z := 0x20d9c.
Definition src0_A_syscall_cp_c : Z := 0x20e10.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103d0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103e0.
Definition src0_D_debruijn32 : Z := 0x10500.
Definition src0_D_size_classes : Z := 0x10520.
Definition src0_D_small_cnt_tab : Z := 0x10580.
Definition src0_D_med_cnt_tab : Z := 0x1059b.
Definition src0_D_got_stack_chk_guard : Z := 0x22050.
Definition src0_D_read_stage : Z := 0x232c9.
Definition src0_D_oft_aligned_copy_empty : Z := 0x332e0.
Definition src0_D_stack_chk_guard : Z := 0x63690.
Definition src0_D_libc : Z := 0x636b0.
Definition src0_D_malloc_lock : Z := 0x63720.
Definition src0_D_malloc_context : Z := 0x63728.
Definition src0_D_ofl_lock : Z := 0x63ad8.
Definition src0_D_ofl_head : Z := 0x63ae0.
Definition src0_vmlock : option Z := None.
