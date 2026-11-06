From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* v1.9 port: definitions no file names were removed (a Theorem Labs lane, 2026-10-28); they carried cgif / v1.8 addresses. See yh03-check.md (sha256 f82c7576099d; internal record). *)
(* YH03 address fix (a Theorem Labs lane, 2026-10-29): three constants corrected for the v1.9 UBSAN PIN fuzz_pcap.ubsan, sha256 83af59086893b560..., symbols read from its unstripped twin fuzz_pcap.ubsan, sha256 da555ced6d68... (twin and pin differ only in ELF section-header fields and the build-id note): src0_A_stdio_read 0x16dec -> 0x1680c and src0_A_stdio_seek 0x16a88 -> 0x16ab4 (the .symtab addresses of __stdio_read and __stdio_seek), src0_D_str_rwa 0x102ed -> 0x1038e (the only NUL-terminated "rwa" in .rodata). src0_D_str_rwa was later deleted from this file, because no code reads it. src0_D_str_tmp_out_gif, src0_D_str_wb and src0_D_str_3 are not defined in this file: pcap's image has no counterpart string. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_A_main : Z := (symaddr Symbols.Ubsan.s_main).
Definition src0_A_target_run : Z := (symaddr Symbols.Ubsan.s_target_run).
Definition src0_A_LLVMFuzzerTestOneInput : Z := (symaddr Symbols.Ubsan.s_LLVMFuzzerTestOneInput).
Definition src0_A_stack_chk_fail : Z := (symaddr Symbols.Ubsan.s___stack_chk_fail_local).
Definition src0_A_syscall_ret : Z := (symaddr Symbols.Ubsan.s___syscall_ret).
Definition src0_A_errno_location : Z := (symaddr Symbols.Ubsan.s___errno_location).
Definition src0_A_free : Z := (symaddr Symbols.Ubsan.s_free).
Definition src0_A_malloc : Z := (symaddr Symbols.Ubsan.s_malloc).
Definition src0_A_libc_free : Z := (symaddr Symbols.Ubsan.s___libc_free).
Definition src0_A_get_meta : Z := (symaddr Symbols.Ubsan.s_get_meta).
Definition src0_A_nontrivial_free : Z := (symaddr Symbols.Ubsan.s_nontrivial_free).
Definition src0_A_alloc_meta : Z := (symaddr Symbols.Ubsan.s___malloc_alloc_meta).
Definition src0_A_libc_malloc_impl : Z := (symaddr Symbols.Ubsan.s___libc_malloc_impl).
Definition src0_A_alloc_slot : Z := (symaddr Symbols.Ubsan.s_alloc_slot).
Definition src0_A_enframe : Z := (symaddr Symbols.Ubsan.s_enframe).
Definition src0_A_vm_wait : Z := (symaddr Symbols.Ubsan.s___vm_wait).
Definition src0_A_mmap : Z := (symaddr Symbols.Ubsan.s_mmap).
Definition src0_A_mprotect : Z := (symaddr Symbols.Ubsan.s_mprotect).
Definition src0_A_munmap : Z := (symaddr Symbols.Ubsan.s_munmap).
Definition src0_A_stdio_read : Z := (symaddr Symbols.Ubsan.s___stdio_read).
Definition src0_A_stdio_write : Z := (symaddr Symbols.Ubsan.s___stdio_write).
Definition src0_A_stdio_seek : Z := (symaddr Symbols.Ubsan.s___stdio_seek).
Definition src0_A_stdio_close : Z := (symaddr Symbols.Ubsan.s___stdio_close).
Definition src0_A_memcpy : Z := (symaddr Symbols.Ubsan.s_memcpy).
Definition src0_A_memset : Z := (symaddr Symbols.Ubsan.s_memset).
Definition src0_A_strnlen : Z := (symaddr Symbols.Ubsan.s_strnlen).
Definition src0_A_memchr : Z := (symaddr Symbols.Ubsan.s_memchr).
Definition src0_A_lock : Z := (symaddr Symbols.Ubsan.s___lock).
Definition src0_A_unlock : Z := (symaddr Symbols.Ubsan.s___unlock).
Definition src0_A_syscall_cp_c : Z := (symaddr Symbols.Ubsan.s_sccp).
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x120)%Z).
Definition src0_D_const_ONES_0x0101010101010100 : Z := (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x130)%Z).
Definition src0_D_debruijn32 : Z := (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x1c4)%Z).
Definition src0_D_size_classes : Z := (symaddr Symbols.Ubsan.s___malloc_size_classes).
Definition src0_D_small_cnt_tab : Z := (symaddr Symbols.Ubsan.s_small_cnt_tab).
Definition src0_D_med_cnt_tab : Z := (symaddr Symbols.Ubsan.s_med_cnt_tab).
Definition src0_D_got_stack_chk_guard : Z := (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z).
Definition src0_D_read_stage : Z := (symaddr Symbols.Ubsan.s_read_stage).
Definition src0_D_aef_aligned_copy_empty : Z := (symaddr Symbols.Ubsan.s_oft_aligned_copy_empty).
Definition src0_D_stack_chk_guard : Z := (symaddr Symbols.Ubsan.s___stack_chk_guard).
Definition src0_D_libc : Z := (symaddr Symbols.Ubsan.s___libc).
Definition src0_D_malloc_lock : Z := (symaddr Symbols.Ubsan.s___malloc_lock).
Definition src0_D_malloc_context : Z := (symaddr Symbols.Ubsan.s___malloc_context).
Definition src0_D_ofl_lock : Z := (symaddr Symbols.Ubsan.s_ofl_lock).
Definition src0_D_ofl_head : Z := (symaddr Symbols.Ubsan.s_ofl_head).
Definition src0_vmlock : option Z := None.
