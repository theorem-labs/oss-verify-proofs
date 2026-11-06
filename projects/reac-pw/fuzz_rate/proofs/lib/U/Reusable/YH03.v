(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x129f4.  Definition src0_text_hi : Z := 0x1dcb8.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11340.
Definition src0_eh_frame_lo : Z := 0x11490.  Definition src0_eh_frame_hi : Z := 0x119f4.
Definition src0_init_array_lo : Z := 0x1ecb8.  Definition src0_init_array_hi : Z := 0x1ecc0.
Definition src0_fini_array_lo : Z := 0x1ecc0.  Definition src0_fini_array_hi : Z := 0x1ecc8.
Definition src0_data_rel_ro_lo : Z := 0x1ecc8.  Definition src0_data_rel_ro_hi : Z := 0x1edf8.
Definition src0_got_lo : Z := 0x1edf8.  Definition src0_got_hi : Z := 0x1ee90.
Definition src0_data_lo : Z := 0x1fe90.  Definition src0_data_hi : Z := 0x2009c.
Definition src0_bss_lo : Z := 0x200a0.  Definition src0_bss_hi : Z := 0x50cc8.
Definition src0_A_start : Z := 0x129f4.  Definition src0_E_start : Z := 0x12a3c.
Definition src0_A_do_init : Z := 0x12a3c.  Definition src0_E_do_init : Z := 0x12ab0.
Definition src0_A_do_fini : Z := 0x12ab0.  Definition src0_E_do_fini : Z := 0x12b40.
Definition src0_A_main : Z := 0x12b40.  Definition src0_E_main : Z := 0x12e04.
Definition src0_A_target_alloc_init : Z := 0x12e04.  Definition src0_E_target_alloc_init : Z := 0x12e08.
Definition src0_A_target_alloc_count : Z := 0x12e08.  Definition src0_E_target_alloc_count : Z := 0x12e10.
Definition src0_A_target_run : Z := 0x12e10.  Definition src0_E_target_run : Z := 0x12f68.
Definition src0_A_aef_exit_guard : Z := 0x12f68.  Definition src0_E_aef_exit_guard : Z := 0x12f98.
Definition src0_A_emit_printf : Z := 0x12f98.  Definition src0_E_emit_printf : Z := 0x12fe0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12fe0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x160f8.
Definition src0_A_read_frameconfig : Z := 0x160f8.  Definition src0_E_read_frameconfig : Z := 0x16360.
Definition src0_A_cgif_newgif : Z := 0x16360.  Definition src0_E_cgif_newgif : Z := 0x16518.
Definition src0_A_cgif_writecb : Z := 0x16518.  Definition src0_E_cgif_writecb : Z := 0x1658c.
Definition src0_A_freeCGIF : Z := 0x1658c.  Definition src0_E_freeCGIF : Z := 0x165c4.
Definition src0_A_cgif_addframe : Z := 0x165c4.  Definition src0_E_cgif_addframe : Z := 0x16930.
Definition src0_A_cmpPixel : Z := 0x16930.  Definition src0_E_cmpPixel : Z := 0x169e4.
Definition src0_A_flushFrame : Z := 0x169e4.  Definition src0_E_flushFrame : Z := 0x172e0.
Definition src0_A_freeFrame : Z := 0x172e0.  Definition src0_E_freeFrame : Z := 0x17328.
Definition src0_A_cgif_close : Z := 0x17328.  Definition src0_E_cgif_close : Z := 0x173f0.
Definition src0_A_cgif_raw_newgif : Z := 0x173f0.  Definition src0_E_cgif_raw_newgif : Z := 0x176a4.
Definition src0_A_cgif_raw_addframe : Z := 0x176a4.  Definition src0_E_cgif_raw_addframe : Z := 0x17b20.
Definition src0_A_LZW_GenerateStream : Z := 0x17b20.  Definition src0_E_LZW_GenerateStream : Z := 0x180c0.
Definition src0_A_cgif_raw_close : Z := 0x180c0.  Definition src0_E_cgif_raw_close : Z := 0x18120.
Definition src0_A_create_byte_list : Z := 0x18120.  Definition src0_E_create_byte_list : Z := 0x1829c.
Definition src0_A_create_byte_list_block : Z := 0x1829c.  Definition src0_E_create_byte_list_block : Z := 0x15ed0.
Definition src0_A_init : Z := 0x15ed0.  Definition src0_E_init : Z := 0x15ed4.
Definition src0_A_init_libc : Z := 0x15ed4.  Definition src0_E_init_libc : Z := 0x16100.
Definition src0_A_libc_start_init : Z := 0x16100.  Definition src0_E_libc_start_init : Z := 0x1614c.
Definition src0_A_libc_start_main : Z := 0x1614c.  Definition src0_E_libc_start_main : Z := 0x161ac.
Definition src0_A_libc_start_main_stage2 : Z := 0x161ac.  Definition src0_E_libc_start_main_stage2 : Z := 0x161f4.
Definition src0_A_init_tls : Z := 0x161f4.  Definition src0_E_init_tls : Z := 0x16554.
Definition src0_A_funcs_on_exit : Z := 0x16554.  Definition src0_E_funcs_on_exit : Z := 0x1661c.
Definition src0_A_cxa_finalize : Z := 0x1661c.  Definition src0_E_cxa_finalize : Z := 0x16620.
Definition src0_A_atexit : Z := 0x16620.  Definition src0_E_atexit : Z := 0x166e4.
Definition src0_A_atexit_call : Z := 0x166e4.  Definition src0_E_atexit_call : Z := 0x166e8.
Definition src0_A_fini : Z := 0x166e8.  Definition src0_E_fini : Z := 0x166ec.
Definition src0_A_libc_exit_fini : Z := 0x166ec.  Definition src0_E_libc_exit_fini : Z := 0x16738.
Definition src0_A_exit : Z := 0x16738.  Definition src0_E_exit : Z := 0x16538.
Definition src0_A_Exit : Z := 0x16538.  Definition src0_E_Exit : Z := 0x167ac.
Definition src0_A_open : Z := 0x167ac.  Definition src0_E_open : Z := 0x16890.
Definition src0_A_init_ssp : Z := 0x16890.  Definition src0_E_init_ssp : Z := 0x168f0.
Definition src0_A_stack_chk_fail : Z := 0x168f0.  Definition src0_E_stack_chk_fail : Z := 0x168f8.
Definition src0_A_syscall_ret : Z := 0x168f8.  Definition src0_E_syscall_ret : Z := 0x16930.
Definition src0_A_errno_location : Z := 0x16930.  Definition src0_E_errno_location : Z := 0x1693c.
Definition src0_A_free : Z := 0x1693c.  Definition src0_E_free : Z := 0x16940.
Definition src0_A_libc_calloc : Z := 0x16940.  Definition src0_E_libc_calloc : Z := 0x16a78.
Definition src0_A_libc_malloc : Z := 0x16a78.  Definition src0_E_libc_malloc : Z := 0x16a7c.
Definition src0_A_malloc : Z := 0x16a7c.  Definition src0_E_malloc : Z := 0x16a80.
Definition src0_A_libc_free : Z := 0x16a80.  Definition src0_E_libc_free : Z := 0x16c4c.
Definition src0_A_get_meta : Z := 0x16c4c.  Definition src0_E_get_meta : Z := 0x16d5c.
Definition src0_A_nontrivial_free : Z := 0x16d5c.  Definition src0_E_nontrivial_free : Z := 0x17134.
Definition src0_A_alloc_meta : Z := 0x17134.  Definition src0_E_alloc_meta : Z := 0x1740c.
Definition src0_A_libc_malloc_impl : Z := 0x1740c.  Definition src0_E_libc_malloc_impl : Z := 0x1777c.
Definition src0_A_alloc_slot : Z := 0x1777c.  Definition src0_E_alloc_slot : Z := 0x18020.
Definition src0_A_enframe : Z := 0x18020.  Definition src0_E_enframe : Z := 0x18170.
Definition src0_A_malloc_allzerop : Z := 0x18170.  Definition src0_E_malloc_allzerop : Z := 0x182e8.
Definition src0_A_vm_wait : Z := 0x182e8.  Definition src0_E_vm_wait : Z := 0x182ec.
Definition src0_A_mmap : Z := 0x182ec.  Definition src0_E_mmap : Z := 0x183d8.
Definition src0_A_mprotect : Z := 0x183d8.  Definition src0_E_mprotect : Z := 0x18420.
Definition src0_A_munmap : Z := 0x18420.  Definition src0_E_munmap : Z := 0x18478.
Definition src0_A_unlist_locked_file : Z := 0x18478.  Definition src0_E_unlist_locked_file : Z := 0x1847c.
Definition src0_A_fclose : Z := 0x1847c.  Definition src0_E_fclose : Z := 0x1853c.
Definition src0_A_fflush : Z := 0x1853c.  Definition src0_E_fflush : Z := 0x186ac.
Definition src0_A_lockfile : Z := 0x186ac.  Definition src0_E_lockfile : Z := 0x187a8.
Definition src0_A_unlockfile : Z := 0x187a8.  Definition src0_E_unlockfile : Z := 0x18814.
Definition src0_A_fopen : Z := 0x18814.  Definition src0_E_fopen : Z := 0x188f0.
Definition src0_A_fmodeflags : Z := 0x188f0.  Definition src0_E_fmodeflags : Z := 0x189a4.
Definition src0_A_fdopen : Z := 0x189a4.  Definition src0_E_fdopen : Z := 0x18b7c.
Definition src0_A_stdio_read : Z := 0x18b7c.  Definition src0_E_stdio_read : Z := 0x18d20.
Definition src0_A_stdio_write : Z := 0x18d20.  Definition src0_E_stdio_write : Z := 0x18e84.
Definition src0_A_stdio_seek : Z := 0x18e84.  Definition src0_E_stdio_seek : Z := 0x18cf0.
Definition src0_A_aio_close : Z := 0x18cf0.  Definition src0_E_aio_close : Z := 0x18cf4.
Definition src0_A_stdio_close : Z := 0x18cf4.  Definition src0_E_stdio_close : Z := 0x18808.
Definition src0_A_fprintf : Z := 0x18808.  Definition src0_E_fprintf : Z := 0x1886c.
Definition src0_A_fwritex : Z := 0x1886c.  Definition src0_E_fwritex : Z := 0x189a4.
Definition src0_A_fwrite : Z := 0x189a4.  Definition src0_E_fwrite : Z := 0x18a5c.
Definition src0_A_towrite : Z := 0x18a5c.  Definition src0_E_towrite : Z := 0x18ab0.
Definition src0_A_stdio_exit : Z := 0x18ab0.  Definition src0_E_stdio_exit : Z := 0x18c54.
Definition src0_A_ofl_lock : Z := 0x18c54.  Definition src0_E_ofl_lock : Z := 0x18c84.
Definition src0_A_ofl_unlock : Z := 0x18c84.  Definition src0_E_ofl_unlock : Z := 0x19344.
Definition src0_A_ofl_add : Z := 0x19344.  Definition src0_E_ofl_add : Z := 0x18eb8.
Definition src0_A_stdout_write : Z := 0x18eb8.  Definition src0_E_stdout_write : Z := 0x18f58.
Definition src0_A_vfprintf : Z := 0x18f58.  Definition src0_E_vfprintf : Z := 0x19108.
Definition src0_A_printf_core : Z := 0x19108.  Definition src0_E_printf_core : Z := 0x19f38.
Definition src0_A_pop_arg : Z := 0x19f38.  Definition src0_E_pop_arg : Z := 0x1a06c.
Definition src0_A_pad : Z := 0x1a06c.  Definition src0_E_pad : Z := 0x1a140.
Definition src0_A_fmt_fp : Z := 0x1a140.  Definition src0_E_fmt_fp : Z := 0x1b808.
Definition src0_A_strerror : Z := 0x1b808.  Definition src0_E_strerror : Z := 0x15374.
Definition src0_A_lctrans_impl : Z := 0x15374.  Definition src0_E_lctrans_impl : Z := 0x1b848.
Definition src0_A_lctrans : Z := 0x1b848.  Definition src0_E_lctrans : Z := 0x1b84c.
Definition src0_A_wctomb : Z := 0x1b84c.  Definition src0_E_wctomb : Z := 0x1b870.
Definition src0_A_wcrtomb : Z := 0x1b870.  Definition src0_E_wcrtomb : Z := 0x1b99c.
Definition src0_A_extenddftf2 : Z := 0x1b99c.  Definition src0_E_extenddftf2 : Z := 0x1bf30.
Definition src0_A_signbitl : Z := 0x1bf30.  Definition src0_E_signbitl : Z := 0x1bb34.
Definition src0_A_fpclassifyl : Z := 0x1bb34.  Definition src0_E_fpclassifyl : Z := 0x1bf7c.
Definition src0_A_frexpl : Z := 0x1bf7c.  Definition src0_E_frexpl : Z := 0x1bc50.
Definition src0_A_letf2 : Z := 0x152b4.  Definition src0_E_letf2 : Z := 0x1537c.
Definition src0_A_multf3 : Z := 0x1bc50.  Definition src0_E_multf3 : Z := 0x1c350.
Definition src0_A_floatsitf : Z := 0x1c350.  Definition src0_E_floatsitf : Z := 0x15aec.
Definition src0_A_scalbn : Z := 0x15aec.  Definition src0_E_scalbn : Z := 0x1c4f0.
Definition src0_A_subtf3 : Z := 0x156b8.  Definition src0_E_subtf3 : Z := 0x156c8.
Definition src0_A_addtf3 : Z := 0x156c8.  Definition src0_E_addtf3 : Z := 0x15e94.
Definition src0_A_fe_getround : Z := 0x15e94.  Definition src0_E_fe_getround : Z := 0x15ec4.
Definition src0_A_fe_raise_inexact : Z := 0x15ec4.  Definition src0_E_fe_raise_inexact : Z := 0x15ed0.
Definition src0_A_fixunstfsi : Z := 0x1c4f0.  Definition src0_E_fixunstfsi : Z := 0x1c584.
Definition src0_A_floatunsitf : Z := 0x1c584.  Definition src0_E_floatunsitf : Z := 0x1c670.
Definition src0_A_fixtfsi : Z := 0x1c670.  Definition src0_E_fixtfsi : Z := 0x1c718.
Definition src0_A_divtf3 : Z := 0x1c718.  Definition src0_E_divtf3 : Z := 0x1d01c.
Definition src0_A_vprintf : Z := 0x1d01c.  Definition src0_E_vprintf : Z := 0x1d6e0.
Definition src0_A_bcmp : Z := 0x1d6e0.  Definition src0_E_bcmp : Z := 0x1d6e4.
Definition src0_A_memcmp : Z := 0x1d6e4.  Definition src0_E_memcmp : Z := 0x1d214.
Definition src0_A_memcpy : Z := 0x1d214.  Definition src0_E_memcpy : Z := 0x1d618.
Definition src0_A_memset : Z := 0x1d618.  Definition src0_E_memset : Z := 0x20234.
Definition src0_A_strchr : Z := 0x20234.  Definition src0_E_strchr : Z := 0x20270.
Definition src0_A_strchrnul : Z := 0x20270.  Definition src0_E_strchrnul : Z := 0x20350.
Definition src0_A_strlen : Z := 0x20350.  Definition src0_E_strlen : Z := 0x1d7d8.
Definition src0_A_strnlen : Z := 0x1d7d8.  Definition src0_E_strnlen : Z := 0x1d81c.
Definition src0_A_memchr : Z := 0x1d81c.  Definition src0_E_memchr : Z := 0x1d8e8.
Definition src0_A_lock : Z := 0x1d8e8.  Definition src0_E_lock : Z := 0x1db70.
Definition src0_A_unlock : Z := 0x1db70.  Definition src0_E_unlock : Z := 0x1dbe4.
Definition src0_A_syscall_cp_c : Z := 0x1dbe4.  Definition src0_E_syscall_cp_c : Z := 0x1dc08.
Definition src0_A_syscall_cp : Z := 0x1dc08.  Definition src0_E_syscall_cp : Z := 0x1dc0c.
Definition src0_A_set_thread_area : Z := 0x1dc0c.  Definition src0_E_set_thread_area : Z := 0x1dc18.
Definition src0_A_unistd_exit : Z := 0x1dc18.  Definition src0_E_unistd_exit : Z := 0x1dc24.
Definition src0_A_close : Z := 0x1dc24.  Definition src0_E_close : Z := 0x1dc78.
Definition src0_A_lseek : Z := 0x1dc78.  Definition src0_E_lseek : Z := 0x1dc84.
Definition src0_A_read : Z := 0x1dc84.  Definition src0_E_read : Z := 0x208c0.
Definition src0_A_unlink : Z := 0x208c0.  Definition src0_E_unlink : Z := 0x208f0.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_wb : Z := 0x102f5.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102f8.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10308.
Definition src0_D_str_d_n : Z := 0x1031c.
Definition src0_D_str : Z := 0x1032e.
Definition src0_D_str_2 : Z := 0x10343.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10342.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10353.
Definition src0_D_str_tmp_out_gif : Z := 0x10385.
Definition src0_D_str_3 : Z := 0x103a2.
Definition src0_D_str_inf : Z := 0x103a4.
Definition src0_D_str_INF : Z := 0x103a8.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1039a.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10418.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x1042d.
Definition src0_D_str_NAN : Z := 0x10318.
Definition src0_D_str_nan : Z := 0x1031c.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10475.
Definition src0_D_str_rwa : Z := 0x1035f.
Definition src0_D_str_dev_null : Z := 0x104b2.
Definition src0_D_str_null : Z := 0x104bc.
Definition src0_D_const_double_0x1p28 : Z := 0x10675.
Definition src0_D_const_double_1_0 : Z := 0x1067d.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10500.
Definition src0_D_const_double_0_5 : Z := 0x1068d.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10510.
Definition src0_D_const_double_0x1p1023 : Z := 0x1069d.
Definition src0_D_const_double_1_5 : Z := 0x106a5.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x106ad.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x106b5.
Definition src0_D_const_u64_0x0101010101010102 : Z := 0x106bd.
Definition src0_D_const_double_0x1p120 : Z := 0x106c5.
Definition src0_D_debruijn32 : Z := 0x106b8.
Definition src0_D_size_classes : Z := 0x106d8.
Definition src0_D_small_cnt_tab : Z := 0x10738.
Definition src0_D_med_cnt_tab : Z := 0x10753.
Definition src0_D_jt_printf_core_1 : Z := 0x11b40.
Definition src0_D_jt_printf_core_2 : Z := 0x11c20.
Definition src0_D_jt_pop_arg : Z := 0x11c40.
Definition src0_D_states : Z := 0x108b0.
Definition src0_D_xdigits : Z := 0x10a80.
Definition src0_D_errmsgstr : Z := 0x10a90.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11238.
Definition src0_D_fe_getround : Z := 0x10650.
Definition src0_D_EH_FRAME_LIST : Z := 0x11490.
Definition src0_D_init_array_start : Z := 0x1ecb8.
Definition src0_D_fini_array_start : Z := 0x1ecc0.
Definition src0_D_stderr : Z := 0x1ede8.
Definition src0_D_stdout : Z := 0x1edf0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x21910.
Definition src0_D_got_DYNAMIC : Z := 0x1ee00.
Definition src0_D_got_main : Z := 0x1ee08.
Definition src0_D_got_init : Z := 0x1ee10.
Definition src0_D_got_fini : Z := 0x1ee18.
Definition src0_D_got_register_frame_info : Z := 0x1ee20.
Definition src0_D_got_cxa_finalize : Z := 0x1ee28.
Definition src0_D_got_deregister_frame_info : Z := 0x1ee30.
Definition src0_D_got_stderr : Z := 0x1ee38.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1ee40.
Definition src0_D_got_stdout : Z := 0x1ee48.
Definition src0_D_got_environ : Z := 0x1ee50.
Definition src0_D_got_progname_full : Z := 0x1ee58.
Definition src0_D_got_progname : Z := 0x1ee60.
Definition src0_D_got_init_array_end : Z := 0x1ee68.
Definition src0_D_got_init_array_start : Z := 0x1ee70.
Definition src0_D_got_stack_chk_guard : Z := 0x1ee78.
Definition src0_D_got_fini_array_end : Z := 0x1ee80.
Definition src0_D_got_fini_array_start : Z := 0x1ee88.
Definition src0_D_dso_handle : Z := 0x1fe90.
Definition src0_D_aef_arg0 : Z := 0x20570.
Definition src0_D_aef_argc : Z := 0x1fea0.
Definition src0_D_aef_argv : Z := 0x20580.
Definition src0_D_stderr_FILE : Z := 0x1feb8.
Definition src0_D_stderr_used : Z := 0x1ffa0.
Definition src0_D_stdout_FILE : Z := 0x1ffa8.
Definition src0_D_stdout_used : Z := 0x20090.
Definition src0_D_default_stacksize : Z := 0x20098.
Definition src0_D_do_init_initialized : Z := 0x200a0.
Definition src0_D_do_init_object : Z := 0x200a8.
Definition src0_D_do_fini_finalized : Z := 0x200e8.
Definition src0_D_read_stage : Z := 0x200e9.
Definition src0_D_target_run_initialized : Z := 0x300f0.
Definition src0_D_aef_in_callback : Z := 0x300f4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30100.
Definition src0_D_environ : Z := 0x30120.
Definition src0_D_thread_list_lock : Z := 0x501f8.
Definition src0_D_main_tls : Z := 0x50200.
Definition src0_D_builtin_tls : Z := 0x30128.
Definition src0_D_finished_atexit : Z := 0x50238.
Definition src0_D_atexit_lock : Z := 0x5023c.
Definition src0_D_atexit_slot : Z := 0x50240.
Definition src0_D_atexit_head : Z := 0x50248.
Definition src0_D_atexit_builtin : Z := 0x50250.
Definition src0_D_exit_exit_lock : Z := 0x50458.
Definition src0_D_stack_chk_guard : Z := 0x50460.
Definition src0_D_sysinfo : Z := 0x50468.
Definition src0_D_progname : Z := 0x50470.
Definition src0_D_progname_full : Z := 0x50478.
Definition src0_D_libc : Z := 0x50480.
Definition src0_D_hwcap : Z := 0x504e8.
Definition src0_D_malloc_lock : Z := 0x504f0.
Definition src0_D_malloc_context : Z := 0x504f8.
Definition src0_D_malloc_replaced : Z := 0x50898.
Definition src0_D_stdin_used : Z := 0x508a0.
Definition src0_D_ofl_lock : Z := 0x508a8.
Definition src0_D_ofl_head : Z := 0x508b0.
Definition src0_D_stderr_buf : Z := 0x508b8.
Definition src0_D_stdout_buf : Z := 0x508c0.
Definition src0_vmlock : option Z := None.
(** The de Bruijn table's length is the image's: the table runs up to __malloc_size_classes (32 bytes in both builds of rate,
    no pad byte; a donor with a pad byte gets 33 the same way). *)
Definition src0_debruijn_len : Z := src0_D_size_classes - src0_D_debruijn32.
