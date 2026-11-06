(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: 38 names that no proof reads are deleted: 31 whose value is not the address of the symbol they name in this image, and 7 that only the cgif FILE sink used (src0_A_stdio_read, src0_A_stdio_write, src0_A_stdio_seek, src0_A_stdio_close and the tmp_out.gif, wb and ';' strings). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12a34.  Definition src0_text_hi : Z := 0x1d1b0.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1130c.
Definition src0_eh_frame_lo : Z := 0x11470.  Definition src0_eh_frame_hi : Z := 0x11a34.
Definition src0_init_array_lo : Z := 0x1e1b0.  Definition src0_init_array_hi : Z := 0x1e1b8.
Definition src0_fini_array_lo : Z := 0x1e1b8.  Definition src0_fini_array_hi : Z := 0x1e1c0.
Definition src0_data_rel_ro_lo : Z := 0x1e1c0.  Definition src0_data_rel_ro_hi : Z := 0x1e2d8.
Definition src0_got_lo : Z := 0x1e2d8.  Definition src0_got_hi : Z := 0x1e370.
Definition src0_data_lo : Z := 0x1f370.  Definition src0_data_hi : Z := 0x1f57c.
Definition src0_bss_lo : Z := 0x1f580.  Definition src0_bss_hi : Z := 0x501a8.
Definition src0_A_do_init : Z := 0x12a7c.  Definition src0_E_do_init : Z := 0x12af0.
Definition src0_A_do_fini : Z := 0x12af0.  Definition src0_E_do_fini : Z := 0x12b80.
Definition src0_A_main : Z := 0x12b80.  Definition src0_E_main : Z := 0x12e44.
Definition src0_A_target_alloc_init : Z := 0x12e44.  Definition src0_E_target_alloc_init : Z := 0x12e48.
Definition src0_A_target_alloc_count : Z := 0x12e48.  Definition src0_E_target_alloc_count : Z := 0x12e50.
Definition src0_A_target_run : Z := 0x12e50.  Definition src0_E_target_run : Z := 0x12fa8.
Definition src0_A_aef_exit_guard : Z := 0x12fa8.  Definition src0_E_aef_exit_guard : Z := 0x12fd8.
Definition src0_A_emit_printf : Z := 0x12fd8.  Definition src0_E_emit_printf : Z := 0x13020.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13020.
Definition src0_A_init : Z := 0x14db8.  Definition src0_E_init : Z := 0x14dbc.
Definition src0_A_init_libc : Z := 0x14dbc.  Definition src0_E_init_libc : Z := 0x14fe8.
Definition src0_A_libc_start_init : Z := 0x14fe8.  Definition src0_E_libc_start_init : Z := 0x15034.
Definition src0_A_libc_start_main : Z := 0x15034.  Definition src0_E_libc_start_main : Z := 0x15094.
Definition src0_A_libc_start_main_stage2 : Z := 0x15094.  Definition src0_E_libc_start_main_stage2 : Z := 0x150dc.
Definition src0_A_init_tls : Z := 0x150dc.
Definition src0_A_funcs_on_exit : Z := 0x1543c.  Definition src0_E_funcs_on_exit : Z := 0x15504.
Definition src0_A_cxa_finalize : Z := 0x15504.  Definition src0_E_cxa_finalize : Z := 0x15508.
Definition src0_A_atexit : Z := 0x15508.  Definition src0_E_atexit : Z := 0x155cc.
Definition src0_A_atexit_call : Z := 0x155cc.  Definition src0_E_atexit_call : Z := 0x155d0.
Definition src0_A_fini : Z := 0x155d0.  Definition src0_E_fini : Z := 0x155d4.
Definition src0_A_libc_exit_fini : Z := 0x155d4.  Definition src0_E_libc_exit_fini : Z := 0x15620.
Definition src0_A_exit : Z := 0x15620.
Definition src0_A_Exit : Z := 0x15420.
Definition src0_A_open : Z := 0x15694.  Definition src0_E_open : Z := 0x15778.
Definition src0_A_init_ssp : Z := 0x15778.  Definition src0_E_init_ssp : Z := 0x157d8.
Definition src0_A_stack_chk_fail : Z := 0x157d8.  Definition src0_E_stack_chk_fail : Z := 0x157e0.
Definition src0_A_syscall_ret : Z := 0x157e0.  Definition src0_E_syscall_ret : Z := 0x15818.
Definition src0_A_errno_location : Z := 0x15818.  Definition src0_E_errno_location : Z := 0x15824.
Definition src0_A_free : Z := 0x15824.  Definition src0_E_free : Z := 0x15828.
Definition src0_A_libc_calloc : Z := 0x15828.  Definition src0_E_libc_calloc : Z := 0x15960.
Definition src0_A_libc_malloc : Z := 0x15960.  Definition src0_E_libc_malloc : Z := 0x15964.
Definition src0_A_malloc : Z := 0x15964.  Definition src0_E_malloc : Z := 0x15968.
Definition src0_A_libc_free : Z := 0x15968.  Definition src0_E_libc_free : Z := 0x15b34.
Definition src0_A_get_meta : Z := 0x15b34.  Definition src0_E_get_meta : Z := 0x15c44.
Definition src0_A_nontrivial_free : Z := 0x15c44.  Definition src0_E_nontrivial_free : Z := 0x1601c.
Definition src0_A_alloc_meta : Z := 0x1601c.  Definition src0_E_alloc_meta : Z := 0x162f4.
Definition src0_A_libc_malloc_impl : Z := 0x162f4.  Definition src0_E_libc_malloc_impl : Z := 0x16664.
Definition src0_A_alloc_slot : Z := 0x16664.  Definition src0_E_alloc_slot : Z := 0x16f08.
Definition src0_A_enframe : Z := 0x16f08.  Definition src0_E_enframe : Z := 0x17058.
Definition src0_A_malloc_allzerop : Z := 0x17058.  Definition src0_E_malloc_allzerop : Z := 0x171d0.
Definition src0_A_vm_wait : Z := 0x171d0.  Definition src0_E_vm_wait : Z := 0x171d4.
Definition src0_A_mmap : Z := 0x171d4.  Definition src0_E_mmap : Z := 0x172c0.
Definition src0_A_mprotect : Z := 0x172c0.  Definition src0_E_mprotect : Z := 0x17308.
Definition src0_A_munmap : Z := 0x17308.
Definition src0_A_fflush : Z := 0x17424.  Definition src0_E_fflush : Z := 0x17594.
Definition src0_A_lockfile : Z := 0x17594.  Definition src0_E_lockfile : Z := 0x17690.
Definition src0_A_unlockfile : Z := 0x17690.
Definition src0_A_aio_close : Z := 0x17b78.  Definition src0_E_aio_close : Z := 0x17b7c.
Definition src0_A_fprintf : Z := 0x176f0.  Definition src0_E_fprintf : Z := 0x17754.
Definition src0_A_fwritex : Z := 0x17754.  Definition src0_E_fwritex : Z := 0x1788c.
Definition src0_A_fwrite : Z := 0x1788c.  Definition src0_E_fwrite : Z := 0x17944.
Definition src0_A_towrite : Z := 0x17944.  Definition src0_E_towrite : Z := 0x17998.
Definition src0_A_stdio_exit : Z := 0x17998.  Definition src0_E_stdio_exit : Z := 0x17b3c.
Definition src0_A_ofl_lock : Z := 0x17b3c.  Definition src0_E_ofl_lock : Z := 0x17b6c.
Definition src0_A_ofl_unlock : Z := 0x17b6c.
Definition src0_A_stdout_write : Z := 0x17d40.  Definition src0_E_stdout_write : Z := 0x17de0.
Definition src0_A_vfprintf : Z := 0x17de0.  Definition src0_E_vfprintf : Z := 0x17f90.
Definition src0_A_printf_core : Z := 0x17f90.  Definition src0_E_printf_core : Z := 0x18dc0.
Definition src0_A_pop_arg : Z := 0x18dc0.  Definition src0_E_pop_arg : Z := 0x18ef4.
Definition src0_A_pad : Z := 0x18ef4.  Definition src0_E_pad : Z := 0x18fc8.
Definition src0_A_fmt_fp : Z := 0x18fc8.  Definition src0_E_fmt_fp : Z := 0x1a690.
Definition src0_A_strerror : Z := 0x1a690.
Definition src0_E_lctrans_impl : Z := 0x1a6d0.
Definition src0_A_lctrans : Z := 0x1a6d0.  Definition src0_E_lctrans : Z := 0x1a6d4.
Definition src0_A_wctomb : Z := 0x1a6d4.  Definition src0_E_wctomb : Z := 0x1a6f8.
Definition src0_A_wcrtomb : Z := 0x1a6f8.  Definition src0_E_wcrtomb : Z := 0x1a824.
Definition src0_A_extenddftf2 : Z := 0x1a824.
Definition src0_E_signbitl : Z := 0x1a9bc.
Definition src0_A_fpclassifyl : Z := 0x1a9bc.
Definition src0_E_frexpl : Z := 0x1aad8.
Definition src0_A_letf2 : Z := 0x1aad8.  Definition src0_E_letf2 : Z := 0x1aba0.
Definition src0_A_multf3 : Z := 0x1aba0.  Definition src0_E_multf3 : Z := 0x1b2a0.
Definition src0_A_floatsitf : Z := 0x1b2a0.
Definition src0_E_scalbn : Z := 0x1b440.
Definition src0_A_subtf3 : Z := 0x1b440.  Definition src0_E_subtf3 : Z := 0x1b450.
Definition src0_A_addtf3 : Z := 0x1b450.  Definition src0_E_addtf3 : Z := 0x1bc1c.
Definition src0_A_fe_getround : Z := 0x1bc1c.  Definition src0_E_fe_getround : Z := 0x1bc4c.
Definition src0_A_fe_raise_inexact : Z := 0x1bc4c.  Definition src0_E_fe_raise_inexact : Z := 0x1bc58.
Definition src0_A_fixunstfsi : Z := 0x1bc58.  Definition src0_E_fixunstfsi : Z := 0x1bcec.
Definition src0_A_floatunsitf : Z := 0x1bcec.  Definition src0_E_floatunsitf : Z := 0x1bdd8.
Definition src0_A_fixtfsi : Z := 0x1bdd8.  Definition src0_E_fixtfsi : Z := 0x1be80.
Definition src0_A_divtf3 : Z := 0x1be80.  Definition src0_E_divtf3 : Z := 0x1c784.
Definition src0_A_vprintf : Z := 0x1c784.
Definition src0_E_memcmp : Z := 0x1c7d4.
Definition src0_A_memcpy : Z := 0x1c7d4.  Definition src0_E_memcpy : Z := 0x1cbd8.
Definition src0_A_memset : Z := 0x1cbd8.
Definition src0_A_strnlen : Z := 0x1ccd0.  Definition src0_E_strnlen : Z := 0x1cd14.
Definition src0_A_memchr : Z := 0x1cd14.  Definition src0_E_memchr : Z := 0x1cde0.
Definition src0_A_lock : Z := 0x1cde0.  Definition src0_E_lock : Z := 0x1d068.
Definition src0_A_unlock : Z := 0x1d068.  Definition src0_E_unlock : Z := 0x1d0dc.
Definition src0_A_syscall_cp_c : Z := 0x1d0dc.  Definition src0_E_syscall_cp_c : Z := 0x1d100.
Definition src0_A_syscall_cp : Z := 0x1d100.  Definition src0_E_syscall_cp : Z := 0x1d104.
Definition src0_A_unistd_exit : Z := 0x1d110.  Definition src0_E_unistd_exit : Z := 0x1d11c.
Definition src0_A_close : Z := 0x1d11c.  Definition src0_E_close : Z := 0x1d170.
Definition src0_A_lseek : Z := 0x1d170.  Definition src0_E_lseek : Z := 0x1d17c.
Definition src0_A_read : Z := 0x1d17c.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b5.
Definition src0_D_str_d_n : Z := 0x102c9.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d0.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e1.
Definition src0_D_str_inf : Z := 0x10301.
Definition src0_D_str_INF : Z := 0x10305.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10309.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1032a.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x1033f.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10365.
Definition src0_D_str_dev_null : Z := 0x10385.
Definition src0_D_str_null : Z := 0x1038f.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103a8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103b8.
Definition src0_D_debruijn32 : Z := 0x1061c.
Definition src0_D_size_classes : Z := 0x10698.
Definition src0_D_small_cnt_tab : Z := 0x106f8.
Definition src0_D_med_cnt_tab : Z := 0x10713.
Definition src0_D_states : Z := 0x10870.
Definition src0_D_xdigits : Z := 0x10a40.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x111f8.
Definition src0_D_fe_getround : Z := 0x11300.
Definition src0_D_EH_FRAME_LIST : Z := 0x11470.
Definition src0_D_init_array_start : Z := 0x1e1b0.
Definition src0_D_fini_array_start : Z := 0x1e1b8.
Definition src0_D_stdout : Z := 0x1e2d0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1e2d8.
Definition src0_D_got_DYNAMIC : Z := 0x1e2e0.
Definition src0_D_got_main : Z := 0x1e2e8.
Definition src0_D_got_init : Z := 0x1e2f0.
Definition src0_D_got_fini : Z := 0x1e2f8.
Definition src0_D_got_register_frame_info : Z := 0x1e300.
Definition src0_D_got_cxa_finalize : Z := 0x1e308.
Definition src0_D_got_deregister_frame_info : Z := 0x1e310.
Definition src0_D_got_stderr : Z := 0x1e318.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e320.
Definition src0_D_got_stdout : Z := 0x1e328.
Definition src0_D_got_environ : Z := 0x1e330.
Definition src0_D_got_progname_full : Z := 0x1e338.
Definition src0_D_got_progname : Z := 0x1e340.
Definition src0_D_got_init_array_end : Z := 0x1e348.
Definition src0_D_got_init_array_start : Z := 0x1e350.
Definition src0_D_got_stack_chk_guard : Z := 0x1e358.
Definition src0_D_got_fini_array_end : Z := 0x1e360.
Definition src0_D_got_fini_array_start : Z := 0x1e368.
Definition src0_D_dso_handle : Z := 0x1f370.
Definition src0_D_aef_argc : Z := 0x1f380.
Definition src0_D_stderr_FILE : Z := 0x1f398.
Definition src0_D_stderr_used : Z := 0x1f480.
Definition src0_D_stdout_FILE : Z := 0x1f488.
Definition src0_D_stdout_used : Z := 0x1f570.
Definition src0_D_default_stacksize : Z := 0x1f578.
Definition src0_D_do_init_initialized : Z := 0x1f580.
Definition src0_D_do_init_object : Z := 0x1f588.
Definition src0_D_do_fini_finalized : Z := 0x1f5c8.
Definition src0_D_read_stage : Z := 0x1f5c9.
Definition src0_D_target_run_initialized : Z := 0x2f5d0.
Definition src0_D_aef_in_callback : Z := 0x2f5d4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f5e0.
Definition src0_D_environ : Z := 0x2f600.
Definition src0_D_thread_list_lock : Z := 0x4f6d8.
Definition src0_D_main_tls : Z := 0x4f6e0.
Definition src0_D_builtin_tls : Z := 0x2f608.
Definition src0_D_finished_atexit : Z := 0x4f718.
Definition src0_D_atexit_lock : Z := 0x4f71c.
Definition src0_D_atexit_slot : Z := 0x4f720.
Definition src0_D_atexit_head : Z := 0x4f728.
Definition src0_D_atexit_builtin : Z := 0x4f730.
Definition src0_D_exit_exit_lock : Z := 0x4f938.
Definition src0_D_stack_chk_guard : Z := 0x4f940.
Definition src0_D_sysinfo : Z := 0x4f948.
Definition src0_D_progname : Z := 0x4f950.
Definition src0_D_progname_full : Z := 0x4f958.
Definition src0_D_libc : Z := 0x4f960.
Definition src0_D_hwcap : Z := 0x4f9c8.
Definition src0_D_malloc_lock : Z := 0x4f9d0.
Definition src0_D_malloc_context : Z := 0x4f9d8.
Definition src0_D_malloc_replaced : Z := 0x4fd78.
Definition src0_D_stdin_used : Z := 0x4fd80.
Definition src0_D_ofl_lock : Z := 0x4fd88.
Definition src0_D_ofl_head : Z := 0x4fd90.
Definition src0_D_stderr_buf : Z := 0x4fd98.
Definition src0_D_stdout_buf : Z := 0x4fda0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 124.
