(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH03.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; only the definitions this unit's files use are kept, each value moved to fuzz_decode's image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit's symtab; src0_A_calloc is dropped (no calloc is linked); module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x1285c.
Definition src0_A_target_run : Z := 0x12b2c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12cfc.
Definition src0_A_stack_chk_fail : Z := 0x14e9c.
Definition src0_A_syscall_ret : Z := 0x14ea4.
Definition src0_A_errno_location : Z := 0x14edc.
Definition src0_A_free : Z := 0x14ee8.
Definition src0_A_malloc : Z := 0x15028.
Definition src0_A_libc_free : Z := 0x1502c.
Definition src0_A_get_meta : Z := 0x151f8.
Definition src0_A_nontrivial_free : Z := 0x15308.
Definition src0_A_alloc_meta : Z := 0x156e0.
Definition src0_A_libc_malloc_impl : Z := 0x159b8.
Definition src0_A_alloc_slot : Z := 0x15d28.
Definition src0_A_enframe : Z := 0x165cc.
Definition src0_A_malloc_allzerop : Z := 0x1671c.
Definition src0_A_vm_wait : Z := 0x16894.
Definition src0_A_mmap : Z := 0x16898.
Definition src0_A_mprotect : Z := 0x16984.
Definition src0_A_munmap : Z := 0x169cc.
Definition src0_A_memcpy : Z := 0x1be98.
Definition src0_A_memset : Z := 0x1c29c.
Definition src0_A_strnlen : Z := 0x1c394.
Definition src0_A_memchr : Z := 0x1c3d8.
Definition src0_A_lock : Z := 0x1c4a4.
Definition src0_A_unlock : Z := 0x1c72c.
Definition src0_A_syscall_cp_c : Z := 0x1c7a0.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10668.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10678.
Definition src0_D_debruijn32 : Z := 0x10460.
Definition src0_D_size_classes : Z := 0x10480.
Definition src0_D_small_cnt_tab : Z := 0x104e0.
Definition src0_D_med_cnt_tab : Z := 0x104fb.
Definition src0_D_got_stack_chk_guard : Z := 0x1d948.
Definition src0_D_read_stage : Z := 0x1ebb9.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2ebd0.
Definition src0_D_stack_chk_guard : Z := 0x4ef30.
Definition src0_D_libc : Z := 0x4ef50.
Definition src0_D_malloc_lock : Z := 0x4efc0.
Definition src0_D_malloc_context : Z := 0x4efc8.
Definition src0_D_ofl_lock : Z := 0x4f378.
Definition src0_D_ofl_head : Z := 0x4f380.
Definition src0_vmlock : option Z := None.
