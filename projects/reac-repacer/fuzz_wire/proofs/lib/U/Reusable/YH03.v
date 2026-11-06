(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YH03.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_wire; the definitions this unit's files use are kept; also kept, though no file of the unit reads them: src0_A_malloc_allzerop (the donor reads it only in its calloc walk, and the UBSan image has no symbol named `calloc` (musl's __libc_calloc is linked)) and src0_A_stdio_write / src0_A_stdio_seek / src0_A_stdio_close (musl's stdio FILE functions, which the sk_write / sk_seek / sk_close of a FILE sink would name; present and true in this image, which has no FILE sink); each address cell is set for fuzz_wire's image by the rule provenance/evidence/k2/k2-cells.tsv records for it: symbol and offset for most cells, by name for src0_A_stdio_seek (__stdio_seek), and port_addr_check's mapping for four data cells; every code cell (src0_A_) checked against the function it names in the UBSan image's symtab; src0_A_calloc is dropped (the UBSan image has no symbol named `calloc` (musl's __libc_calloc is linked)); module path OSSVerify.Proofs.reac_repacer.fuzz_wire.lib. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := 0x12920.
Definition src0_A_target_run : Z := 0x12bf0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12dc0.
Definition src0_A_stack_chk_fail : Z := 0x14628.
Definition src0_A_syscall_ret : Z := 0x14714.
Definition src0_A_errno_location : Z := 0x1474c.
Definition src0_A_free : Z := 0x14758.
Definition src0_A_malloc : Z := 0x14898.
Definition src0_A_libc_free : Z := 0x1489c.
Definition src0_A_get_meta : Z := 0x14a68.
Definition src0_A_nontrivial_free : Z := 0x14b78.
Definition src0_A_alloc_meta : Z := 0x14f50.
Definition src0_A_libc_malloc_impl : Z := 0x15228.
Definition src0_A_alloc_slot : Z := 0x15598.
Definition src0_A_enframe : Z := 0x15e3c.
Definition src0_A_malloc_allzerop : Z := 0x15f8c.
Definition src0_A_vm_wait : Z := 0x16104.
Definition src0_A_mmap : Z := 0x16108.
Definition src0_A_mprotect : Z := 0x161f4.
Definition src0_A_munmap : Z := 0x1623c.
Definition src0_A_stdio_write : Z := 0x16adc.
Definition src0_A_stdio_seek : Z := 0x16c6c.
Definition src0_A_stdio_close : Z := 0x16ab0.
Definition src0_A_memcpy : Z := 0x1b708.
Definition src0_A_memset : Z := 0x1bc88.
Definition src0_A_strnlen : Z := 0x1bd80.
Definition src0_A_memchr : Z := 0x1bdc4.
Definition src0_A_lock : Z := 0x1be90.
Definition src0_A_unlock : Z := 0x1c118.
Definition src0_A_syscall_cp_c : Z := 0x1c18c.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103c0.
Definition src0_D_debruijn32 : Z := 0x10454.
Definition src0_D_size_classes : Z := 0x10474.
Definition src0_D_small_cnt_tab : Z := 0x104d4.
Definition src0_D_med_cnt_tab : Z := 0x104ef.
Definition src0_D_got_stack_chk_guard : Z := 0x1d300.
Definition src0_D_read_stage : Z := 0x1e579.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2e590.
Definition src0_D_stack_chk_guard : Z := 0x4e8f0.
Definition src0_D_libc : Z := 0x4e910.
Definition src0_D_malloc_lock : Z := 0x4e980.
Definition src0_D_malloc_context : Z := 0x4e988.
Definition src0_D_ofl_lock : Z := 0x4ed38.
Definition src0_D_ofl_head : Z := 0x4ed40.
Definition src0_vmlock : option Z := None.
