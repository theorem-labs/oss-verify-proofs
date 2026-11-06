(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module A3Syms.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_img_lo : Z := 0x10000%Z.
Definition A_img_hi : Z := 0x603000%Z.
Definition A_rw_lo : Z := 0xa4000%Z.
Definition A_rw_len : Z := 0x55f000%Z.
Definition A_rodata_lo : Z := 0x102e0%Z.
Definition A_text_lo : Z := 0x329c4%Z.
Definition A_text_hi : Z := 0x9eebc%Z.

(* [comment removed for export] *)
Definition A_entry : Z := 0x329c4%Z.         (* [comment removed for export] *)
Definition A_main : Z := 0x84120%Z.          (* [comment removed for export] *)
Definition A_libc_start_main : Z := 0x94020%Z.
Definition A_stage2 : Z := 0x94080%Z.        (* [comment removed for export] *)
Definition A_stage2_ret : Z := 0x940c4%Z.    (* [comment removed for export] *)
Definition A_exit : Z := 0x947c4%Z.          (* [comment removed for export] *)
Definition A_Exit : Z := 0x94594%Z.          (* [comment removed for export] *)
Definition A_ec_exit_group : Z := 0x9459c%Z. (* [comment removed for export] *)
Definition A_open : Z := 0x94a38%Z.          (* [comment removed for export] *)
Definition A_close : Z := 0xa3dc8%Z.         (* [comment removed for export] *)
Definition A_syscall_ret : Z := 0x94b1c%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_malloc : Z := 0x56178%Z.        (* [comment removed for export] *)
Definition A_free : Z := 0x56174%Z.          (* [comment removed for export] *)
Definition A_memcpy : Z := 0x54960%Z.        (* [comment removed for export] *)
Definition A_memset : Z := 0x54958%Z.        (* [comment removed for export] *)
Definition A_fwrite : Z := 0x44490%Z.        (* [comment removed for export] *)
Definition A_fprintf : Z := 0x444ac%Z.       (* [comment removed for export] *)
Definition A_strnlen : Z := 0x4446c%Z.       (* [comment removed for export] *)
Definition A_memchr : Z := 0x44480%Z.        (* [comment removed for export] *)
Definition A_icpt_malloc : Z := 0x56354%Z.
Definition A_icpt_free : Z := 0x56184%Z.
Definition A_icpt_memcpy : Z := 0x557f0%Z.
Definition A_icpt_memset : Z := 0x55040%Z.
Definition A_icpt_read : Z := 0x463c4%Z.
Definition A_icpt_fwrite : Z := 0x468a8%Z.
Definition A_icpt_fprintf : Z := 0x4820c%Z.
Definition A_icpt_strnlen : Z := 0x447a0%Z.
Definition A_icpt_memchr : Z := 0x45e7c%Z.

(* [comment removed for export] *)
Definition A_spin_sizeclass_map : Z := 0x36d10%Z.
Definition A_spin_quarantine : Z := 0x38334%Z.
Definition A_spin_poison_remap : Z := 0x57a40%Z.
Definition A_spin_shadow0 : Z := 0x5e048%Z.
Definition A_spin_shadow1 : Z := 0x5e05c%Z.
Definition A_spin_shadow2 : Z := 0x5e070%Z.
Definition A_spin_mmap_die0 : Z := 0x63b14%Z.
Definition A_spin_mmap_die1 : Z := 0x63be4%Z.
Definition A_spin_70f98 : Z := 0x71110%Z.
Definition A_spin_mmap_fixed : Z := 0x7201c%Z.
Definition A_spin_mmap_noaccess : Z := 0x721ac%Z.
Definition A_spin_7bc50 : Z := 0x7bf04%Z.

(* [comment removed for export] *)
Definition A_stderr : Z := 0xa9ab0%Z.         (* [comment removed for export] *)
Definition A_stdin : Z := 0xa9ba0%Z.          (* [comment removed for export] *)
Definition A_stdout : Z := 0xa9c90%Z.         (* [comment removed for export] *)
Definition A_stderr_buf : Z := 0x601cc0%Z.     (* [comment removed for export] *)
Definition A_asan_globals : Z := 0xa9db0%Z.   (* [comment removed for export] *)
Definition A_asan_globals_end : Z := 0xaaf30%Z.
Definition A_bss : Z := 0xaaf40%Z.            (* [comment removed for export] *)
Definition A_elf_globals_flag : Z := 0xaaf40%Z.   (* [comment removed for export] *)
Definition A_crt_completed : Z := 0xaaf90%Z.      (* [comment removed for export] *)
Definition A_asan_flags : Z := 0xabdf8%Z.         (* [comment removed for export] *)
Definition A_globals_mu : Z := 0xabeb0%Z.         (* [comment removed for export] *)
Definition A_can_poison : Z := 0xade5c%Z.         (* [comment removed for export] *)
Definition A_shadow_base_cell : Z := 0xae5f8%Z.   (* [comment removed for export] *)
Definition A_asan_inited : Z := 0xaf2d8%Z.        (* [comment removed for export] *)
Definition A_common_flags : Z := 0x140128%Z.      (* [comment removed for export] *)
Definition A_stats_flag : Z := 0x1404a0%Z.        (* [comment removed for export] *)
Definition A_odr_byte : Z := 0x5e0ca0%Z.          (* [comment removed for export] *)
Definition A_stack_chk_guard : Z := 0x6015f8%Z. (* [comment removed for export] *)
Definition A_atexit_blob : Z := 0x601608%Z.       (* [comment removed for export] *)
Definition A_atexit_builtin : Z := 0x601620%Z.    (* [comment removed for export] *)
Definition A_exit_lock : Z := 0x601828%Z.         (* [comment removed for export] *)
Definition A_libc : Z := 0x601848%Z.              (* [comment removed for export] *)
Definition A_ofl_head : Z := 0x601cb0%Z.          (* [comment removed for export] *)
Definition A_atexit_stub : Z := 0x73b80%Z.        (* [comment removed for export] *)
Definition A_atexit_call : Z := 0x94770%Z.        (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_img_lo : Z := 0x10000%Z.
Definition A_img_hi : Z := 0x604000%Z.
Definition A_rw_lo : Z := 0xa5000%Z.
Definition A_rw_len : Z := 0x55f000%Z.
Definition A_rodata_lo : Z := 0x102e0%Z.
Definition A_text_lo : Z := 0x32a2c%Z.
Definition A_text_hi : Z := 0x9f2a0%Z.

(* [comment removed for export] *)
Definition A_entry : Z := 0x32a2c%Z.         (* [comment removed for export] *)
Definition A_main : Z := 0x84188%Z.          (* [comment removed for export] *)
Definition A_libc_start_main : Z := 0x94404%Z.
Definition A_stage2 : Z := 0x94464%Z.        (* [comment removed for export] *)
Definition A_stage2_ret : Z := 0x944a8%Z.    (* [comment removed for export] *)
Definition A_exit : Z := 0x94ba8%Z.          (* [comment removed for export] *)
Definition A_Exit : Z := 0x94978%Z.          (* [comment removed for export] *)
Definition A_ec_exit_group : Z := 0x94980%Z. (* [comment removed for export] *)
Definition A_open : Z := 0x94e1c%Z.          (* [comment removed for export] *)
Definition A_close : Z := 0xa41ac%Z.         (* [comment removed for export] *)
Definition A_syscall_ret : Z := 0x94f00%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_malloc : Z := 0x561e0%Z.        (* [comment removed for export] *)
Definition A_free : Z := 0x561dc%Z.          (* [comment removed for export] *)
Definition A_memcpy : Z := 0x549c8%Z.        (* [comment removed for export] *)
Definition A_memset : Z := 0x549c0%Z.        (* [comment removed for export] *)
Definition A_fwrite : Z := 0x444f8%Z.        (* [comment removed for export] *)
Definition A_fprintf : Z := 0x44514%Z.       (* [comment removed for export] *)
Definition A_strnlen : Z := 0x444d4%Z.       (* [comment removed for export] *)
Definition A_memchr : Z := 0x444e8%Z.        (* [comment removed for export] *)
Definition A_icpt_malloc : Z := 0x563bc%Z.
Definition A_icpt_free : Z := 0x561ec%Z.
Definition A_icpt_memcpy : Z := 0x55858%Z.
Definition A_icpt_memset : Z := 0x550a8%Z.
Definition A_icpt_read : Z := 0x4642c%Z.
Definition A_icpt_fwrite : Z := 0x46910%Z.
Definition A_icpt_fprintf : Z := 0x48274%Z.
Definition A_icpt_strnlen : Z := 0x44808%Z.
Definition A_icpt_memchr : Z := 0x45ee4%Z.

(* [comment removed for export] *)
Definition A_spin_sizeclass_map : Z := 0x36d78%Z.
Definition A_spin_quarantine : Z := 0x3839c%Z.
Definition A_spin_poison_remap : Z := 0x57aa8%Z.
Definition A_spin_shadow0 : Z := 0x5e0b0%Z.
Definition A_spin_shadow1 : Z := 0x5e0c4%Z.
Definition A_spin_shadow2 : Z := 0x5e0d8%Z.
Definition A_spin_mmap_die0 : Z := 0x63b7c%Z.
Definition A_spin_mmap_die1 : Z := 0x63c4c%Z.
Definition A_spin_70f98 : Z := 0x71178%Z.
Definition A_spin_mmap_fixed : Z := 0x72084%Z.
Definition A_spin_mmap_noaccess : Z := 0x72214%Z.
Definition A_spin_7bc50 : Z := 0x7bf6c%Z.

(* [comment removed for export] *)
Definition A_stderr : Z := 0xa9e90%Z.         (* [comment removed for export] *)
Definition A_stdin : Z := 0xa9f80%Z.          (* [comment removed for export] *)
Definition A_stdout : Z := 0xaa070%Z.         (* [comment removed for export] *)
Definition A_stderr_buf : Z := 0x6020c0%Z.     (* [comment removed for export] *)
Definition A_asan_globals : Z := 0xaa190%Z.   (* [comment removed for export] *)
Definition A_asan_globals_end : Z := 0xab310%Z.
Definition A_bss : Z := 0xab340%Z.            (* [comment removed for export] *)
Definition A_elf_globals_flag : Z := 0xab340%Z.   (* [comment removed for export] *)
Definition A_crt_completed : Z := 0xab390%Z.      (* [comment removed for export] *)
Definition A_asan_flags : Z := 0xac1f8%Z.         (* [comment removed for export] *)
Definition A_globals_mu : Z := 0xac2b0%Z.         (* [comment removed for export] *)
Definition A_can_poison : Z := 0xae25c%Z.         (* [comment removed for export] *)
Definition A_shadow_base_cell : Z := 0xae9f8%Z.   (* [comment removed for export] *)
Definition A_asan_inited : Z := 0xaf6d8%Z.        (* [comment removed for export] *)
Definition A_common_flags : Z := 0x140528%Z.      (* [comment removed for export] *)
Definition A_stats_flag : Z := 0x1408a0%Z.        (* [comment removed for export] *)
Definition A_odr_byte : Z := 0x5e10a0%Z.          (* [comment removed for export] *)
Definition A_stack_chk_guard : Z := 0x6019f8%Z. (* [comment removed for export] *)
Definition A_atexit_blob : Z := 0x601a08%Z.       (* [comment removed for export] *)
Definition A_atexit_builtin : Z := 0x601a20%Z.    (* [comment removed for export] *)
Definition A_exit_lock : Z := 0x601c28%Z.         (* [comment removed for export] *)
Definition A_libc : Z := 0x601c48%Z.              (* [comment removed for export] *)
Definition A_ofl_head : Z := 0x6020b0%Z.          (* [comment removed for export] *)
Definition A_atexit_stub : Z := 0x73be8%Z.        (* [comment removed for export] *)
Definition A_atexit_call : Z := 0x94b54%Z.        (* [comment removed for export] *)
End TwB.
End A3Syms.

(* [comment removed for export] *)
Module A3SymsBoot.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_musl_memset : Z := 0x9ead4%Z.     (* [comment removed for export] *)
Definition A_musl_memcpy : Z := 0x9e6a0%Z.     (* [comment removed for export] *)
Definition A_musl_memchr : Z := 0x9e5a4%Z.
Definition A_musl_strnlen : Z := 0x9eff4%Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_imemset : Z := 0x67a98%Z.         (* [comment removed for export] *)
Definition A_imemcpy : Z := 0x67a1c%Z.         (* [comment removed for export] *)
Definition A_mem_is_zero : Z := 0x67fc8%Z.     (* [comment removed for export] *)
Definition A_istrncpy : Z := 0x67ec4%Z.        (* [comment removed for export] *)
Definition A_istrlen : Z := 0x67bec%Z.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_asan_init : Z := 0x5d874%Z.       (* [comment removed for export] *)
Definition A_module_ctor : Z := 0x84bd8%Z.     (* [comment removed for export] *)
Definition A_init_libc : Z := 0x93da8%Z.       (* [comment removed for export] *)
Definition A_internal_mmap_ecall : Z := 0x6829c%Z.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_start : Z := 0x329c4%Z.            (* [comment removed for export] *)
Definition A_gp : Z := 0x10800%Z.
Definition A_envloop : Z := 0x93de0%Z.
Definition A_envloop_exit : Z := 0x93dec%Z.
Definition A_pn_stores : Z := 0x93e88%Z.
Definition A_pnloop : Z := 0x93ea4%Z.
Definition A_pnloop_exit : Z := 0x93eb0%Z.
Definition A_builtin_tls : Z := 0x5e14f0%Z.
Definition A_set_tid_ecall : Z := 0x943fc%Z.
Definition A_set_tid_ret : Z := 0x94400%Z.
Definition A_ssp_sb : Z := 0x94494%Z.
Definition A_ssp_ld : Z := 0x94498%Z.
Definition A_ssp_after_ld : Z := 0x9449c%Z.
(* [comment removed for export] *)
Definition A_environ : Z := 0x5e14e8%Z.          (* [comment removed for export] *)
Definition A_thread_list_lock : Z := 0x6015c0%Z. (* [comment removed for export] *)
Definition A_stack_chk_guard : Z := 0x6015f8%Z.  (* [comment removed for export] *)
Definition A_sysinfo : Z := 0x601830%Z.
Definition A_progname : Z := 0x601838%Z.         (* [comment removed for export] *)
Definition A_progname_full : Z := 0x601840%Z.    (* [comment removed for export] *)
Definition A_hwcap : Z := 0x6018b0%Z.
Definition A_default_stacksize : Z := 0xa9d80%Z.
Definition A_init_array : Z := 0xa4f10%Z.       (* [comment removed for export] *)
Definition A_fini_array : Z := 0xa4f30%Z.
Definition A_preinit_array : Z := 0xa4f40%Z.    (* [comment removed for export] *)
Definition A_got : Z := 0xa5450%Z.
Definition A_got_dynamic : Z := 0xa5458%Z.       (* [comment removed for export] *)
Definition A_got_stack_chk_guard : Z := 0xa6160%Z.
(* [comment removed for export] *)
Definition A_maxva_smeared : Z := 0x69150%Z.    (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_musl_memset : Z := 0x9eeb8%Z.     (* [comment removed for export] *)
Definition A_musl_memcpy : Z := 0x9ea84%Z.     (* [comment removed for export] *)
Definition A_musl_memchr : Z := 0x9e988%Z.
Definition A_musl_strnlen : Z := 0x9f3d8%Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_imemset : Z := 0x67b00%Z.         (* [comment removed for export] *)
Definition A_imemcpy : Z := 0x67a84%Z.         (* [comment removed for export] *)
Definition A_mem_is_zero : Z := 0x68030%Z.     (* [comment removed for export] *)
Definition A_istrncpy : Z := 0x67f2c%Z.        (* [comment removed for export] *)
Definition A_istrlen : Z := 0x67c54%Z.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_asan_init : Z := 0x5d8dc%Z.       (* [comment removed for export] *)
Definition A_module_ctor : Z := 0x84c64%Z.     (* [comment removed for export] *)
Definition A_init_libc : Z := 0x9418c%Z.       (* [comment removed for export] *)
Definition A_internal_mmap_ecall : Z := 0x68304%Z.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_start : Z := 0x32a2c%Z.            (* [comment removed for export] *)
Definition A_gp : Z := 0x10800%Z.
Definition A_envloop : Z := 0x941c4%Z.
Definition A_envloop_exit : Z := 0x941d0%Z.
Definition A_pn_stores : Z := 0x9426c%Z.
Definition A_pnloop : Z := 0x94288%Z.
Definition A_pnloop_exit : Z := 0x94294%Z.
Definition A_builtin_tls : Z := 0x5e18f0%Z.
Definition A_set_tid_ecall : Z := 0x947e0%Z.
Definition A_set_tid_ret : Z := 0x947e4%Z.
Definition A_ssp_sb : Z := 0x94878%Z.
Definition A_ssp_ld : Z := 0x9487c%Z.
Definition A_ssp_after_ld : Z := 0x94880%Z.
(* [comment removed for export] *)
Definition A_environ : Z := 0x5e18e8%Z.          (* [comment removed for export] *)
Definition A_thread_list_lock : Z := 0x6019c0%Z. (* [comment removed for export] *)
Definition A_stack_chk_guard : Z := 0x6019f8%Z.  (* [comment removed for export] *)
Definition A_sysinfo : Z := 0x601c30%Z.
Definition A_progname : Z := 0x601c38%Z.         (* [comment removed for export] *)
Definition A_progname_full : Z := 0x601c40%Z.    (* [comment removed for export] *)
Definition A_hwcap : Z := 0x601cb0%Z.
Definition A_default_stacksize : Z := 0xaa160%Z.
Definition A_init_array : Z := 0xa52f0%Z.       (* [comment removed for export] *)
Definition A_fini_array : Z := 0xa5310%Z.
Definition A_preinit_array : Z := 0xa5320%Z.    (* [comment removed for export] *)
Definition A_got : Z := 0xa5830%Z.
Definition A_got_dynamic : Z := 0xa5838%Z.       (* [comment removed for export] *)
Definition A_got_stack_chk_guard : Z := 0xa6540%Z.
(* [comment removed for export] *)
Definition A_maxva_smeared : Z := 0x691b8%Z.    (* [comment removed for export] *)
End TwB.
End A3SymsBoot.

(* [comment removed for export] *)
Module A3SymsBootW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_internal_mmap_ret : Z := 0x682a0%Z.   (* [comment removed for export] *)
Definition A_cbn_mid : Z := 0x644a0%Z.             (* [comment removed for export] *)
Definition A_init_after_cbn : Z := 0x5d3e8%Z.      (* [comment removed for export] *)
Definition A_binary_name_cache : Z := 0x13f0c0%Z.  (* [comment removed for export] *)
Definition A_process_name_cache : Z := 0x13e0c0%Z. (* [comment removed for export] *)
Definition A_sealed_str : Z := 0x11854%Z.          (* [comment removed for export] *)
Definition SEALED_U64 : Z := 4495829844187509564%Z. (* [comment removed for export] *)
Definition A_spin_mmapordie : Z := 0x63b14%Z.   (* [comment removed for export] *)
Definition A_spin_noreserve : Z := 0x721ac%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_internal_mmap_ret : Z := 0x68308%Z.   (* [comment removed for export] *)
Definition A_cbn_mid : Z := 0x64508%Z.             (* [comment removed for export] *)
Definition A_init_after_cbn : Z := 0x5d450%Z.      (* [comment removed for export] *)
Definition A_binary_name_cache : Z := 0x13f4c0%Z.  (* [comment removed for export] *)
Definition A_process_name_cache : Z := 0x13e4c0%Z. (* [comment removed for export] *)
Definition A_sealed_str : Z := 0x11854%Z.          (* [comment removed for export] *)
Definition SEALED_U64 : Z := 4495829844187509564%Z. (* [comment removed for export] *)
Definition A_spin_mmapordie : Z := 0x63b7c%Z.   (* [comment removed for export] *)
Definition A_spin_noreserve : Z := 0x72214%Z.   (* [comment removed for export] *)
End TwB.
End A3SymsBootW.

(* [comment removed for export] *)
Module A3SymsBootW2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_init_aligned_sb : Z := 0x6ff10%Z.  (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_init_aligned_sb : Z := 0x6ff78%Z.  (* [comment removed for export] *)
End TwB.
End A3SymsBootW2.

(* [comment removed for export] *)
Module A3SymsBootW3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_getblockbegin_xcmp : Z := 0x34fd4%Z.    (* [comment removed for export] *)
Definition A_internal_munmap_ecall : Z := 0x682a8%Z. (* [comment removed for export] *)
Definition A_internal_munmap_ret : Z := 0x682ac%Z.   (* [comment removed for export] *)
Definition A_tlsvec_ld : Z := 0x7098c%Z.            (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_getblockbegin_xcmp : Z := 0x3503c%Z.    (* [comment removed for export] *)
Definition A_internal_munmap_ecall : Z := 0x68310%Z. (* [comment removed for export] *)
Definition A_internal_munmap_ret : Z := 0x68314%Z.   (* [comment removed for export] *)
Definition A_tlsvec_ld : Z := 0x709f4%Z.            (* [comment removed for export] *)
End TwB.
End A3SymsBootW3.

(* [comment removed for export] *)
Module A3SymsBootW4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_stacktop_site : Z := 0x7043c%Z.   (* [comment removed for export] *)
Definition A_fps_pagecmp : Z := 0x578a0%Z.     (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_stacktop_site : Z := 0x704a4%Z.   (* [comment removed for export] *)
Definition A_fps_pagecmp : Z := 0x57908%Z.     (* [comment removed for export] *)
End TwB.
End A3SymsBootW4.

(* [comment removed for export] *)
Module A3SymsBootW5.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_mcq_src : Z := 0x5588c%Z.   (* [comment removed for export] *)
Definition A_mcq_dst : Z := 0x558d4%Z.   (* [comment removed for export] *)
Definition A_mcq_call : Z := 0x558ec%Z.  (* [comment removed for export] *)
Definition A_mcq_ret : Z := 0x558f0%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition A_mcq_src : Z := 0x558f4%Z.   (* [comment removed for export] *)
Definition A_mcq_dst : Z := 0x5593c%Z.   (* [comment removed for export] *)
Definition A_mcq_call : Z := 0x55954%Z.  (* [comment removed for export] *)
Definition A_mcq_ret : Z := 0x55958%Z.   (* [comment removed for export] *)
End TwB.
End A3SymsBootW5.
