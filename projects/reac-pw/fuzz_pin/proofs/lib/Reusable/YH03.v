(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x126c0.  Definition src0_text_hi : Z := 0x1b71c.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1122c.
Definition src0_eh_frame_lo : Z := 0x11310.  Definition src0_eh_frame_hi : Z := 0x116c0.
Definition src0_init_array_lo : Z := 0x1c720.  Definition src0_init_array_hi : Z := 0x1c728.
Definition src0_fini_array_lo : Z := 0x1c728.  Definition src0_fini_array_hi : Z := 0x1c730.
Definition src0_data_rel_ro_lo : Z := 0x1c730.  Definition src0_data_rel_ro_hi : Z := 0x1d3f8.
Definition src0_got_lo : Z := 0x1d3f8.  Definition src0_got_hi : Z := 0x1d490.
Definition src0_data_lo : Z := 0x1e490.  Definition src0_data_hi : Z := 0x1e69c.
Definition src0_bss_lo : Z := 0x1e6a0.  Definition src0_bss_hi : Z := 0x4f2c8.
Definition src0_A_start : Z := 0x126c0.  Definition src0_E_start : Z := 0x12708.
Definition src0_A_do_init : Z := 0x12708.  Definition src0_E_do_init : Z := 0x1277c.
Definition src0_A_do_fini : Z := 0x1277c.  Definition src0_E_do_fini : Z := 0x1280c.
Definition src0_A_main : Z := 0x1280c.  Definition src0_E_main : Z := 0x12ad0.
Definition src0_A_target_alloc_init : Z := 0x12ad0.  Definition src0_E_target_alloc_init : Z := 0x12ad4.
Definition src0_A_target_alloc_count : Z := 0x12ad4.  Definition src0_E_target_alloc_count : Z := 0x12adc.
Definition src0_A_target_run : Z := 0x12adc.  Definition src0_E_target_run : Z := 0x12c34.
Definition src0_A_aef_exit_guard : Z := 0x12c34.  Definition src0_E_aef_exit_guard : Z := 0x12c64.
Definition src0_A_emit_printf : Z := 0x12c64.  Definition src0_E_emit_printf : Z := 0x12cac.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12cac.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x12e4c.
Definition src0_A_read_frameconfig : Z := 0x132d4.  Definition src0_E_read_frameconfig : Z := 0x1353c.
Definition src0_A_cgif_newgif : Z := 0x1353c.  Definition src0_E_cgif_newgif : Z := 0x136f4.
Definition src0_A_cgif_writecb : Z := 0x136f4.  Definition src0_E_cgif_writecb : Z := 0x13768.
Definition src0_A_freeCGIF : Z := 0x13768.  Definition src0_E_freeCGIF : Z := 0x137a0.
Definition src0_A_cgif_addframe : Z := 0x137a0.  Definition src0_E_cgif_addframe : Z := 0x13b0c.
Definition src0_A_cmpPixel : Z := 0x13b0c.  Definition src0_E_cmpPixel : Z := 0x13bc0.
Definition src0_A_flushFrame : Z := 0x13bc0.  Definition src0_E_flushFrame : Z := 0x144bc.
Definition src0_A_freeFrame : Z := 0x144bc.  Definition src0_E_freeFrame : Z := 0x14504.
Definition src0_A_cgif_close : Z := 0x14504.  Definition src0_E_cgif_close : Z := 0x145cc.
Definition src0_A_cgif_raw_newgif : Z := 0x145cc.  Definition src0_E_cgif_raw_newgif : Z := 0x14880.
Definition src0_A_cgif_raw_addframe : Z := 0x14880.  Definition src0_E_cgif_raw_addframe : Z := 0x14cfc.
Definition src0_A_LZW_GenerateStream : Z := 0x14cfc.  Definition src0_E_LZW_GenerateStream : Z := 0x1529c.
Definition src0_A_cgif_raw_close : Z := 0x1529c.  Definition src0_E_cgif_raw_close : Z := 0x152fc.
Definition src0_A_create_byte_list : Z := 0x152fc.  Definition src0_E_create_byte_list : Z := 0x15478.
Definition src0_A_create_byte_list_block : Z := 0x15478.  Definition src0_E_create_byte_list_block : Z := 0x1303c.
Definition src0_A_init : Z := 0x1303c.  Definition src0_E_init : Z := 0x13040.
Definition src0_A_init_libc : Z := 0x13040.  Definition src0_E_init_libc : Z := 0x1326c.
Definition src0_A_libc_start_init : Z := 0x1326c.  Definition src0_E_libc_start_init : Z := 0x132b8.
Definition src0_A_libc_start_main : Z := 0x132b8.  Definition src0_E_libc_start_main : Z := 0x13318.
Definition src0_A_libc_start_main_stage2 : Z := 0x13318.  Definition src0_E_libc_start_main_stage2 : Z := 0x13360.
Definition src0_A_init_tls : Z := 0x13360.  Definition src0_E_init_tls : Z := 0x13610.
Definition src0_A_funcs_on_exit : Z := 0x136c0.  Definition src0_E_funcs_on_exit : Z := 0x13788.
Definition src0_A_cxa_finalize : Z := 0x13788.  Definition src0_E_cxa_finalize : Z := 0x1378c.
Definition src0_A_atexit : Z := 0x1378c.  Definition src0_E_atexit : Z := 0x13850.
Definition src0_A_atexit_call : Z := 0x13850.  Definition src0_E_atexit_call : Z := 0x13854.
Definition src0_A_fini : Z := 0x13854.  Definition src0_E_fini : Z := 0x13858.
Definition src0_A_libc_exit_fini : Z := 0x13858.  Definition src0_E_libc_exit_fini : Z := 0x138a4.
Definition src0_A_exit : Z := 0x138a4.  Definition src0_E_exit : Z := 0x13918.
Definition src0_A_Exit : Z := 0x136a4.  Definition src0_E_Exit : Z := 0x136c0.
Definition src0_A_open : Z := 0x13918.  Definition src0_E_open : Z := 0x139fc.
Definition src0_A_init_ssp : Z := 0x139fc.  Definition src0_E_init_ssp : Z := 0x13a5c.
Definition src0_A_stack_chk_fail : Z := 0x13a5c.  Definition src0_E_stack_chk_fail : Z := 0x13a64.
Definition src0_A_syscall_ret : Z := 0x13a64.  Definition src0_E_syscall_ret : Z := 0x13a9c.
Definition src0_A_errno_location : Z := 0x13a9c.  Definition src0_E_errno_location : Z := 0x13aa8.
Definition src0_A_free : Z := 0x13aa8.  Definition src0_E_free : Z := 0x13aac.
Definition src0_A_libc_calloc : Z := 0x13aac.  Definition src0_E_libc_calloc : Z := 0x13be4.
Definition src0_A_libc_malloc : Z := 0x13be4.  Definition src0_E_libc_malloc : Z := 0x13be8.
Definition src0_A_malloc : Z := 0x13be8.  Definition src0_E_malloc : Z := 0x13bec.
Definition src0_A_libc_free : Z := 0x13bec.  Definition src0_E_libc_free : Z := 0x13db8.
Definition src0_A_get_meta : Z := 0x13db8.  Definition src0_E_get_meta : Z := 0x13ec8.
Definition src0_A_nontrivial_free : Z := 0x13ec8.  Definition src0_E_nontrivial_free : Z := 0x142a0.
Definition src0_A_alloc_meta : Z := 0x142a0.  Definition src0_E_alloc_meta : Z := 0x14578.
Definition src0_A_libc_malloc_impl : Z := 0x14578.  Definition src0_E_libc_malloc_impl : Z := 0x148e8.
Definition src0_A_alloc_slot : Z := 0x148e8.  Definition src0_E_alloc_slot : Z := 0x1518c.
Definition src0_A_enframe : Z := 0x1518c.  Definition src0_E_enframe : Z := 0x152dc.
Definition src0_A_malloc_allzerop : Z := 0x152dc.  Definition src0_E_malloc_allzerop : Z := 0x15454.
Definition src0_A_vm_wait : Z := 0x15454.  Definition src0_E_vm_wait : Z := 0x15458.
Definition src0_A_mmap : Z := 0x15458.  Definition src0_E_mmap : Z := 0x15544.
Definition src0_A_mprotect : Z := 0x15544.  Definition src0_E_mprotect : Z := 0x1558c.
Definition src0_A_munmap : Z := 0x1558c.  Definition src0_E_munmap : Z := 0x155d4.
Definition src0_A_unlist_locked_file : Z := 0x155e4.  Definition src0_E_unlist_locked_file : Z := 0x155e8.
Definition src0_A_fclose : Z := 0x155e8.  Definition src0_E_fclose : Z := 0x156a8.
Definition src0_A_fflush : Z := 0x156a8.  Definition src0_E_fflush : Z := 0x15818.
Definition src0_A_lockfile : Z := 0x15818.  Definition src0_E_lockfile : Z := 0x15914.
Definition src0_A_unlockfile : Z := 0x15914.  Definition src0_E_unlockfile : Z := 0x15974.
Definition src0_A_fopen : Z := 0x15980.  Definition src0_E_fopen : Z := 0x15a5c.
Definition src0_A_fmodeflags : Z := 0x15a5c.  Definition src0_E_fmodeflags : Z := 0x15b10.
Definition src0_A_fdopen : Z := 0x15b10.  Definition src0_E_fdopen : Z := 0x15ce8.
Definition src0_A_stdio_write : Z := 0x15e2c.  Definition src0_E_stdio_write : Z := 0x15fbc.
Definition src0_A_aio_close : Z := 0x15dfc.  Definition src0_E_aio_close : Z := 0x15e00.
Definition src0_A_stdio_close : Z := 0x15e00.  Definition src0_E_stdio_close : Z := 0x15e2c.
Definition src0_A_fprintf : Z := 0x15974.  Definition src0_E_fprintf : Z := 0x159d8.
Definition src0_A_fwritex : Z := 0x159d8.  Definition src0_E_fwritex : Z := 0x15b10.
Definition src0_A_fwrite : Z := 0x15b10.  Definition src0_E_fwrite : Z := 0x15bc8.
Definition src0_A_towrite : Z := 0x15bc8.  Definition src0_E_towrite : Z := 0x15c1c.
Definition src0_A_stdio_exit : Z := 0x15c1c.  Definition src0_E_stdio_exit : Z := 0x15dc0.
Definition src0_A_ofl_lock : Z := 0x15dc0.  Definition src0_E_ofl_lock : Z := 0x15df0.
Definition src0_A_ofl_unlock : Z := 0x15df0.  Definition src0_E_ofl_unlock : Z := 0x15dfc.
Definition src0_A_ofl_add : Z := 0x16450.  Definition src0_E_ofl_add : Z := 0x15fc4.
Definition src0_A_stdout_write : Z := 0x15fc4.  Definition src0_E_stdout_write : Z := 0x16064.
Definition src0_A_vfprintf : Z := 0x16064.  Definition src0_E_vfprintf : Z := 0x16214.
Definition src0_A_printf_core : Z := 0x16214.  Definition src0_E_printf_core : Z := 0x17044.
Definition src0_A_pop_arg : Z := 0x17044.  Definition src0_E_pop_arg : Z := 0x17178.
Definition src0_A_pad : Z := 0x17178.  Definition src0_E_pad : Z := 0x1724c.
Definition src0_A_fmt_fp : Z := 0x1724c.  Definition src0_E_fmt_fp : Z := 0x18914.
Definition src0_A_strerror : Z := 0x18914.  Definition src0_E_strerror : Z := 0x18950.
Definition src0_A_lctrans_impl : Z := 0x18950.  Definition src0_E_lctrans_impl : Z := 0x18954.
Definition src0_A_lctrans : Z := 0x18954.  Definition src0_E_lctrans : Z := 0x18958.
Definition src0_A_wctomb : Z := 0x18958.  Definition src0_E_wctomb : Z := 0x1897c.
Definition src0_A_wcrtomb : Z := 0x1897c.  Definition src0_E_wcrtomb : Z := 0x18aa8.
Definition src0_A_extenddftf2 : Z := 0x18aa8.  Definition src0_E_extenddftf2 : Z := 0x18c38.
Definition src0_A_signbitl : Z := 0x18c38.  Definition src0_E_signbitl : Z := 0x18c40.
Definition src0_A_fpclassifyl : Z := 0x18c40.  Definition src0_E_fpclassifyl : Z := 0x18c84.
Definition src0_A_frexpl : Z := 0x18c84.  Definition src0_E_frexpl : Z := 0x18d5c.
Definition src0_A_letf2 : Z := 0x18d5c.  Definition src0_E_letf2 : Z := 0x18e24.
Definition src0_A_multf3 : Z := 0x18e24.  Definition src0_E_multf3 : Z := 0x19524.
Definition src0_A_floatsitf : Z := 0x19524.  Definition src0_E_floatsitf : Z := 0x1962c.
Definition src0_A_scalbn : Z := 0x1962c.  Definition src0_E_scalbn : Z := 0x196c4.
Definition src0_A_subtf3 : Z := 0x196c4.  Definition src0_E_subtf3 : Z := 0x196d4.
Definition src0_A_addtf3 : Z := 0x196d4.  Definition src0_E_addtf3 : Z := 0x19ea0.
Definition src0_A_fe_getround : Z := 0x19ea0.  Definition src0_E_fe_getround : Z := 0x19ed0.
Definition src0_A_fe_raise_inexact : Z := 0x19ed0.  Definition src0_E_fe_raise_inexact : Z := 0x19edc.
Definition src0_A_fixunstfsi : Z := 0x19edc.  Definition src0_E_fixunstfsi : Z := 0x19f70.
Definition src0_A_floatunsitf : Z := 0x19f70.  Definition src0_E_floatunsitf : Z := 0x1a05c.
Definition src0_A_fixtfsi : Z := 0x1a05c.  Definition src0_E_fixtfsi : Z := 0x1a104.
Definition src0_A_divtf3 : Z := 0x1a104.  Definition src0_E_divtf3 : Z := 0x1aa08.
Definition src0_A_vprintf : Z := 0x1aa08.  Definition src0_E_vprintf : Z := 0x1aa24.
Definition src0_A_bcmp : Z := 0x1aa24.  Definition src0_E_bcmp : Z := 0x1aa28.
Definition src0_A_memcmp : Z := 0x1aaf4.  Definition src0_E_memcmp : Z := 0x1ab24.
Definition src0_A_memcpy : Z := 0x1ab24.  Definition src0_E_memcpy : Z := 0x1af28.
Definition src0_A_memset : Z := 0x1af28.  Definition src0_E_memset : Z := 0x1b020.
Definition src0_A_strchr : Z := 0x1e8a4.  Definition src0_E_strchr : Z := 0x1e8e0.
Definition src0_A_strchrnul : Z := 0x1b138.  Definition src0_E_strchrnul : Z := 0x1b218.
Definition src0_A_strlen : Z := 0x1b218.  Definition src0_E_strlen : Z := 0x1b2a8.
Definition src0_A_strnlen : Z := 0x1b308.  Definition src0_E_strnlen : Z := 0x1b34c.
Definition src0_A_memchr : Z := 0x1aa28.  Definition src0_E_memchr : Z := 0x1aaf4.
Definition src0_A_lock : Z := 0x1b34c.  Definition src0_E_lock : Z := 0x1b5d4.
Definition src0_A_unlock : Z := 0x1b5d4.  Definition src0_E_unlock : Z := 0x1b648.
Definition src0_A_syscall_cp_c : Z := 0x1b648.  Definition src0_E_syscall_cp_c : Z := 0x1b66c.
Definition src0_A_syscall_cp : Z := 0x1b66c.  Definition src0_E_syscall_cp : Z := 0x1b670.
Definition src0_A_set_thread_area : Z := 0x1b670.  Definition src0_E_set_thread_area : Z := 0x1b67c.
Definition src0_A_unistd_exit : Z := 0x1b67c.  Definition src0_E_unistd_exit : Z := 0x1b688.
Definition src0_A_close : Z := 0x1b688.  Definition src0_E_close : Z := 0x1b6dc.
Definition src0_A_lseek : Z := 0x1b6dc.  Definition src0_E_lseek : Z := 0x1b6e8.
Definition src0_A_read : Z := 0x1b6e8.  Definition src0_E_read : Z := 0x1b71c.
Definition src0_A_unlink : Z := 0x1ef30.  Definition src0_E_unlink : Z := 0x1ef60.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x1030d.
Definition src0_D_str_d_n : Z := 0x10321.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x1032e.
Definition src0_D_str_cli_config_len_overruns : Z := 0x1033f.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x103da.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10473.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10488.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x104ad.
Definition src0_D_str_dev_null : Z := 0x104da.
Definition src0_D_str_null : Z := 0x104e4.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10750.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10760.
Definition src0_D_debruijn32 : Z := 0x10547.
Definition src0_D_size_classes : Z := 0x10568.
Definition src0_D_small_cnt_tab : Z := 0x105c8.
Definition src0_D_med_cnt_tab : Z := 0x105e3.
Definition src0_D_states : Z := 0x10790.
Definition src0_D_xdigits : Z := 0x10960.
Definition src0_D_errmsgstr : Z := 0x10970.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11118.
Definition src0_D_fe_getround : Z := 0x11220.
Definition src0_D_EH_FRAME_LIST : Z := 0x11310.
Definition src0_D_init_array_start : Z := 0x1c720.
Definition src0_D_fini_array_start : Z := 0x1c728.
Definition src0_D_stderr : Z := 0x1d3e8.
Definition src0_D_stdout : Z := 0x1d3f0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1d3f8.
Definition src0_D_got_DYNAMIC : Z := 0x1d400.
Definition src0_D_got_main : Z := 0x1d408.
Definition src0_D_got_init : Z := 0x1d410.
Definition src0_D_got_fini : Z := 0x1d418.
Definition src0_D_got_register_frame_info : Z := 0x1d420.
Definition src0_D_got_cxa_finalize : Z := 0x1d428.
Definition src0_D_got_deregister_frame_info : Z := 0x1d430.
Definition src0_D_got_stderr : Z := 0x1d438.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1d440.
Definition src0_D_got_stdout : Z := 0x1d448.
Definition src0_D_got_environ : Z := 0x1d450.
Definition src0_D_got_progname_full : Z := 0x1d458.
Definition src0_D_got_progname : Z := 0x1d460.
Definition src0_D_got_init_array_end : Z := 0x1d468.
Definition src0_D_got_init_array_start : Z := 0x1d470.
Definition src0_D_got_stack_chk_guard : Z := 0x1d478.
Definition src0_D_got_fini_array_end : Z := 0x1d480.
Definition src0_D_got_fini_array_start : Z := 0x1d488.
Definition src0_D_dso_handle : Z := 0x1e490.
Definition src0_D_aef_argc : Z := 0x1e4a0.
Definition src0_D_stderr_FILE : Z := 0x1e4b8.
Definition src0_D_stderr_used : Z := 0x1e5a0.
Definition src0_D_stdout_FILE : Z := 0x1e5a8.
Definition src0_D_stdout_used : Z := 0x1e690.
Definition src0_D_default_stacksize : Z := 0x1e698.
Definition src0_D_do_init_initialized : Z := 0x1e6a0.
Definition src0_D_do_init_object : Z := 0x1e6a8.
Definition src0_D_do_fini_finalized : Z := 0x1e6e8.
Definition src0_D_read_stage : Z := 0x1e6e9.
Definition src0_D_target_run_initialized : Z := 0x2e6f0.
Definition src0_D_aef_in_callback : Z := 0x2e6f4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2e700.
Definition src0_D_environ : Z := 0x2e720.
Definition src0_D_thread_list_lock : Z := 0x4e7f8.
Definition src0_D_main_tls : Z := 0x4e800.
Definition src0_D_builtin_tls : Z := 0x2e728.
Definition src0_D_finished_atexit : Z := 0x4e838.
Definition src0_D_atexit_lock : Z := 0x4e83c.
Definition src0_D_atexit_slot : Z := 0x4e840.
Definition src0_D_atexit_head : Z := 0x4e848.
Definition src0_D_atexit_builtin : Z := 0x4e850.
Definition src0_D_exit_exit_lock : Z := 0x4ea58.
Definition src0_D_stack_chk_guard : Z := 0x4ea60.
Definition src0_D_sysinfo : Z := 0x4ea68.
Definition src0_D_progname : Z := 0x4ea70.
Definition src0_D_progname_full : Z := 0x4ea78.
Definition src0_D_libc : Z := 0x4ea80.
Definition src0_D_hwcap : Z := 0x4eae8.
Definition src0_D_malloc_lock : Z := 0x4eaf0.
Definition src0_D_malloc_context : Z := 0x4eaf8.
Definition src0_D_malloc_replaced : Z := 0x4ee98.
Definition src0_D_stdin_used : Z := 0x4eea0.
Definition src0_D_ofl_lock : Z := 0x4eea8.
Definition src0_D_ofl_head : Z := 0x4eeb0.
Definition src0_D_stderr_buf : Z := 0x4eeb8.
Definition src0_D_stdout_buf : Z := 0x4eec0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 33.
