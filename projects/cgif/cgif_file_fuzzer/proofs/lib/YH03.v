(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x127e4.  Definition src0_text_hi : Z := 0x1dd70.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x110e0.
Definition src0_eh_frame_lo : Z := 0x11210.  Definition src0_eh_frame_hi : Z := 0x117e4.
Definition src0_init_array_lo : Z := 0x1ed70.  Definition src0_init_array_hi : Z := 0x1ed78.
Definition src0_fini_array_lo : Z := 0x1ed78.  Definition src0_fini_array_hi : Z := 0x1ed80.
Definition src0_data_rel_ro_lo : Z := 0x1ed80.  Definition src0_data_rel_ro_hi : Z := 0x1ed90.
Definition src0_got_lo : Z := 0x1ed90.  Definition src0_got_hi : Z := 0x1ee28.
Definition src0_data_lo : Z := 0x1fe28.  Definition src0_data_hi : Z := 0x20034.
Definition src0_bss_lo : Z := 0x20040.  Definition src0_bss_hi : Z := 0x50c60.
Definition src0_A_start : Z := 0x127e4.  Definition src0_E_start : Z := 0x1282c.
Definition src0_A_do_init : Z := 0x1282c.  Definition src0_E_do_init : Z := 0x128a0.
Definition src0_A_do_fini : Z := 0x128a0.  Definition src0_E_do_fini : Z := 0x12930.
Definition src0_A_main : Z := 0x12930.  Definition src0_E_main : Z := 0x12bf4.
Definition src0_A_target_alloc_init : Z := 0x12bf4.  Definition src0_E_target_alloc_init : Z := 0x12bf8.
Definition src0_A_target_alloc_count : Z := 0x12bf8.  Definition src0_E_target_alloc_count : Z := 0x12c00.
Definition src0_A_target_run : Z := 0x12c00.  Definition src0_E_target_run : Z := 0x12d58.
Definition src0_A_aef_exit_guard : Z := 0x12d58.  Definition src0_E_aef_exit_guard : Z := 0x12d88.
Definition src0_A_emit_printf : Z := 0x12d88.  Definition src0_E_emit_printf : Z := 0x12dd0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12dd0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x130b0.
Definition src0_A_read_frameconfig : Z := 0x130b0.  Definition src0_E_read_frameconfig : Z := 0x13318.
Definition src0_A_cgif_newgif : Z := 0x13318.  Definition src0_E_cgif_newgif : Z := 0x134d0.
Definition src0_A_cgif_writecb : Z := 0x134d0.  Definition src0_E_cgif_writecb : Z := 0x13544.
Definition src0_A_freeCGIF : Z := 0x13544.  Definition src0_E_freeCGIF : Z := 0x1357c.
Definition src0_A_cgif_addframe : Z := 0x1357c.  Definition src0_E_cgif_addframe : Z := 0x138e8.
Definition src0_A_cmpPixel : Z := 0x138e8.  Definition src0_E_cmpPixel : Z := 0x1399c.
Definition src0_A_flushFrame : Z := 0x1399c.  Definition src0_E_flushFrame : Z := 0x14298.
Definition src0_A_freeFrame : Z := 0x14298.  Definition src0_E_freeFrame : Z := 0x142e0.
Definition src0_A_cgif_close : Z := 0x142e0.  Definition src0_E_cgif_close : Z := 0x143a8.
Definition src0_A_cgif_raw_newgif : Z := 0x143a8.  Definition src0_E_cgif_raw_newgif : Z := 0x1465c.
Definition src0_A_cgif_raw_addframe : Z := 0x1465c.  Definition src0_E_cgif_raw_addframe : Z := 0x14ad8.
Definition src0_A_LZW_GenerateStream : Z := 0x14ad8.  Definition src0_E_LZW_GenerateStream : Z := 0x15078.
Definition src0_A_cgif_raw_close : Z := 0x15078.  Definition src0_E_cgif_raw_close : Z := 0x150d8.
Definition src0_A_create_byte_list : Z := 0x150d8.  Definition src0_E_create_byte_list : Z := 0x15254.
Definition src0_A_create_byte_list_block : Z := 0x15254.  Definition src0_E_create_byte_list_block : Z := 0x15374.
Definition src0_A_init : Z := 0x15374.  Definition src0_E_init : Z := 0x15378.
Definition src0_A_init_libc : Z := 0x15378.  Definition src0_E_init_libc : Z := 0x155a4.
Definition src0_A_libc_start_init : Z := 0x155a4.  Definition src0_E_libc_start_init : Z := 0x155f0.
Definition src0_A_libc_start_main : Z := 0x155f0.  Definition src0_E_libc_start_main : Z := 0x15650.
Definition src0_A_libc_start_main_stage2 : Z := 0x15650.  Definition src0_E_libc_start_main_stage2 : Z := 0x15698.
Definition src0_A_init_tls : Z := 0x15698.  Definition src0_E_init_tls : Z := 0x15948.
Definition src0_A_funcs_on_exit : Z := 0x15948.  Definition src0_E_funcs_on_exit : Z := 0x15a10.
Definition src0_A_cxa_finalize : Z := 0x15a10.  Definition src0_E_cxa_finalize : Z := 0x15a14.
Definition src0_A_atexit : Z := 0x15a14.  Definition src0_E_atexit : Z := 0x15ad8.
Definition src0_A_atexit_call : Z := 0x15ad8.  Definition src0_E_atexit_call : Z := 0x15adc.
Definition src0_A_fini : Z := 0x15adc.  Definition src0_E_fini : Z := 0x15ae0.
Definition src0_A_libc_exit_fini : Z := 0x15ae0.  Definition src0_E_libc_exit_fini : Z := 0x15b2c.
Definition src0_A_exit : Z := 0x15b2c.  Definition src0_E_exit : Z := 0x15ba0.
Definition src0_A_Exit : Z := 0x15ba0.  Definition src0_E_Exit : Z := 0x15bbc.
Definition src0_A_open : Z := 0x15bbc.  Definition src0_E_open : Z := 0x15ca0.
Definition src0_A_init_ssp : Z := 0x15ca0.  Definition src0_E_init_ssp : Z := 0x15d00.
Definition src0_A_stack_chk_fail : Z := 0x15d00.  Definition src0_E_stack_chk_fail : Z := 0x15d08.
Definition src0_A_syscall_ret : Z := 0x15d08.  Definition src0_E_syscall_ret : Z := 0x15d40.
Definition src0_A_errno_location : Z := 0x15d40.  Definition src0_E_errno_location : Z := 0x15d4c.
Definition src0_A_free : Z := 0x15d4c.  Definition src0_E_free : Z := 0x15d50.
Definition src0_A_libc_calloc : Z := 0x15d50.  Definition src0_E_libc_calloc : Z := 0x15e88.
Definition src0_A_libc_malloc : Z := 0x15e88.  Definition src0_E_libc_malloc : Z := 0x15e8c.
Definition src0_A_malloc : Z := 0x15e8c.  Definition src0_E_malloc : Z := 0x15e90.
Definition src0_A_libc_free : Z := 0x15e90.  Definition src0_E_libc_free : Z := 0x1605c.
Definition src0_A_get_meta : Z := 0x1605c.  Definition src0_E_get_meta : Z := 0x1616c.
Definition src0_A_nontrivial_free : Z := 0x1616c.  Definition src0_E_nontrivial_free : Z := 0x16544.
Definition src0_A_alloc_meta : Z := 0x16544.  Definition src0_E_alloc_meta : Z := 0x1681c.
Definition src0_A_libc_malloc_impl : Z := 0x1681c.  Definition src0_E_libc_malloc_impl : Z := 0x16b8c.
Definition src0_A_alloc_slot : Z := 0x16b8c.  Definition src0_E_alloc_slot : Z := 0x17430.
Definition src0_A_enframe : Z := 0x17430.  Definition src0_E_enframe : Z := 0x17580.
Definition src0_A_malloc_allzerop : Z := 0x17580.  Definition src0_E_malloc_allzerop : Z := 0x176f8.
Definition src0_A_vm_wait : Z := 0x176f8.  Definition src0_E_vm_wait : Z := 0x176fc.
Definition src0_A_mmap : Z := 0x176fc.  Definition src0_E_mmap : Z := 0x177e8.
Definition src0_A_mprotect : Z := 0x177e8.  Definition src0_E_mprotect : Z := 0x17830.
Definition src0_A_munmap : Z := 0x17830.  Definition src0_E_munmap : Z := 0x17878.
Definition src0_A_unlist_locked_file : Z := 0x17878.  Definition src0_E_unlist_locked_file : Z := 0x1787c.
Definition src0_A_fclose : Z := 0x1787c.  Definition src0_E_fclose : Z := 0x17948.
Definition src0_A_fflush : Z := 0x17948.  Definition src0_E_fflush : Z := 0x17ab8.
Definition src0_A_lockfile : Z := 0x17ab8.  Definition src0_E_lockfile : Z := 0x17bb4.
Definition src0_A_unlockfile : Z := 0x17bb4.  Definition src0_E_unlockfile : Z := 0x17c14.
Definition src0_A_fopen : Z := 0x17c14.  Definition src0_E_fopen : Z := 0x17cf0.
Definition src0_A_fmodeflags : Z := 0x17cf0.  Definition src0_E_fmodeflags : Z := 0x17da4.
Definition src0_A_fdopen : Z := 0x17da4.  Definition src0_E_fdopen : Z := 0x17f7c.
Definition src0_A_stdio_read : Z := 0x17f7c.  Definition src0_E_stdio_read : Z := 0x18094.
Definition src0_A_stdio_write : Z := 0x18094.  Definition src0_E_stdio_write : Z := 0x18224.
Definition src0_A_stdio_seek : Z := 0x18224.  Definition src0_E_stdio_seek : Z := 0x1822c.
Definition src0_A_aio_close : Z := 0x1822c.  Definition src0_E_aio_close : Z := 0x18230.
Definition src0_A_stdio_close : Z := 0x18230.  Definition src0_E_stdio_close : Z := 0x1825c.
Definition src0_A_fprintf : Z := 0x1825c.  Definition src0_E_fprintf : Z := 0x182c0.
Definition src0_A_fwritex : Z := 0x182c0.  Definition src0_E_fwritex : Z := 0x183f8.
Definition src0_A_fwrite : Z := 0x183f8.  Definition src0_E_fwrite : Z := 0x184b0.
Definition src0_A_towrite : Z := 0x184b0.  Definition src0_E_towrite : Z := 0x18504.
Definition src0_A_stdio_exit : Z := 0x18504.  Definition src0_E_stdio_exit : Z := 0x186a8.
Definition src0_A_ofl_lock : Z := 0x186a8.  Definition src0_E_ofl_lock : Z := 0x186d8.
Definition src0_A_ofl_unlock : Z := 0x186d8.  Definition src0_E_ofl_unlock : Z := 0x186e4.
Definition src0_A_ofl_add : Z := 0x186e4.  Definition src0_E_ofl_add : Z := 0x18724.
Definition src0_A_stdout_write : Z := 0x18724.  Definition src0_E_stdout_write : Z := 0x187c4.
Definition src0_A_vfprintf : Z := 0x187c4.  Definition src0_E_vfprintf : Z := 0x18974.
Definition src0_A_printf_core : Z := 0x18974.  Definition src0_E_printf_core : Z := 0x197a4.
Definition src0_A_pop_arg : Z := 0x197a4.  Definition src0_E_pop_arg : Z := 0x198d8.
Definition src0_A_pad : Z := 0x198d8.  Definition src0_E_pad : Z := 0x199ac.
Definition src0_A_fmt_fp : Z := 0x199ac.  Definition src0_E_fmt_fp : Z := 0x1b074.
Definition src0_A_strerror : Z := 0x1b074.  Definition src0_E_strerror : Z := 0x1b0b0.
Definition src0_A_lctrans_impl : Z := 0x1b0b0.  Definition src0_E_lctrans_impl : Z := 0x1b0b4.
Definition src0_A_lctrans : Z := 0x1b0b4.  Definition src0_E_lctrans : Z := 0x1b0b8.
Definition src0_A_wctomb : Z := 0x1b0b8.  Definition src0_E_wctomb : Z := 0x1b0dc.
Definition src0_A_wcrtomb : Z := 0x1b0dc.  Definition src0_E_wcrtomb : Z := 0x1b208.
Definition src0_A_extenddftf2 : Z := 0x1b208.  Definition src0_E_extenddftf2 : Z := 0x1b398.
Definition src0_A_signbitl : Z := 0x1b398.  Definition src0_E_signbitl : Z := 0x1b3a0.
Definition src0_A_fpclassifyl : Z := 0x1b3a0.  Definition src0_E_fpclassifyl : Z := 0x1b3e4.
Definition src0_A_frexpl : Z := 0x1b3e4.  Definition src0_E_frexpl : Z := 0x1b4bc.
Definition src0_A_letf2 : Z := 0x1b4bc.  Definition src0_E_letf2 : Z := 0x1b584.
Definition src0_A_multf3 : Z := 0x1b584.  Definition src0_E_multf3 : Z := 0x1bc84.
Definition src0_A_floatsitf : Z := 0x1bc84.  Definition src0_E_floatsitf : Z := 0x1bd8c.
Definition src0_A_scalbn : Z := 0x1bd8c.  Definition src0_E_scalbn : Z := 0x1be24.
Definition src0_A_subtf3 : Z := 0x1be24.  Definition src0_E_subtf3 : Z := 0x1be34.
Definition src0_A_addtf3 : Z := 0x1be34.  Definition src0_E_addtf3 : Z := 0x1c600.
Definition src0_A_fe_getround : Z := 0x1c600.  Definition src0_E_fe_getround : Z := 0x1c630.
Definition src0_A_fe_raise_inexact : Z := 0x1c630.  Definition src0_E_fe_raise_inexact : Z := 0x1c63c.
Definition src0_A_fixunstfsi : Z := 0x1c63c.  Definition src0_E_fixunstfsi : Z := 0x1c6d0.
Definition src0_A_floatunsitf : Z := 0x1c6d0.  Definition src0_E_floatunsitf : Z := 0x1c7bc.
Definition src0_A_fixtfsi : Z := 0x1c7bc.  Definition src0_E_fixtfsi : Z := 0x1c864.
Definition src0_A_divtf3 : Z := 0x1c864.  Definition src0_E_divtf3 : Z := 0x1d168.
Definition src0_A_vprintf : Z := 0x1d168.  Definition src0_E_vprintf : Z := 0x1d184.
Definition src0_A_bcmp : Z := 0x1d184.  Definition src0_E_bcmp : Z := 0x1d188.
Definition src0_A_memcmp : Z := 0x1d188.  Definition src0_E_memcmp : Z := 0x1d1b8.
Definition src0_A_memcpy : Z := 0x1d1b8.  Definition src0_E_memcpy : Z := 0x1d5bc.
Definition src0_A_memset : Z := 0x1d5bc.  Definition src0_E_memset : Z := 0x1d6b4.
Definition src0_A_strchr : Z := 0x1d6b4.  Definition src0_E_strchr : Z := 0x1d6f0.
Definition src0_A_strchrnul : Z := 0x1d6f0.  Definition src0_E_strchrnul : Z := 0x1d7d0.
Definition src0_A_strlen : Z := 0x1d7d0.  Definition src0_E_strlen : Z := 0x1d860.
Definition src0_A_strnlen : Z := 0x1d860.  Definition src0_E_strnlen : Z := 0x1d8a4.
Definition src0_A_memchr : Z := 0x1d8a4.  Definition src0_E_memchr : Z := 0x1d970.
Definition src0_A_lock : Z := 0x1d970.  Definition src0_E_lock : Z := 0x1dbf8.
Definition src0_A_unlock : Z := 0x1dbf8.  Definition src0_E_unlock : Z := 0x1dc6c.
Definition src0_A_syscall_cp_c : Z := 0x1dc6c.  Definition src0_E_syscall_cp_c : Z := 0x1dc90.
Definition src0_A_syscall_cp : Z := 0x1dc90.  Definition src0_E_syscall_cp : Z := 0x1dc94.
Definition src0_A_set_thread_area : Z := 0x1dc94.  Definition src0_E_set_thread_area : Z := 0x1dca0.
Definition src0_A_unistd_exit : Z := 0x1dca0.  Definition src0_E_unistd_exit : Z := 0x1dcac.
Definition src0_A_close : Z := 0x1dcac.  Definition src0_E_close : Z := 0x1dd00.
Definition src0_A_lseek : Z := 0x1dd00.  Definition src0_E_lseek : Z := 0x1dd0c.
Definition src0_A_read : Z := 0x1dd0c.  Definition src0_E_read : Z := 0x1dd40.
Definition src0_A_unlink : Z := 0x1dd40.  Definition src0_E_unlink : Z := 0x1dd70.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b8.
Definition src0_D_str_d_n : Z := 0x102cc.
Definition src0_D_str : Z := 0x102d0.
Definition src0_D_str_2 : Z := 0x102d1.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d3.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e4.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_inf : Z := 0x10313.
Definition src0_D_str_INF : Z := 0x10317.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1031b.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1033c.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10351.
Definition src0_D_str_NAN : Z := 0x10368.
Definition src0_D_str_nan : Z := 0x1036c.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10370.
Definition src0_D_str_rwa : Z := 0x10390.
Definition src0_D_str_dev_null : Z := 0x10394.
Definition src0_D_str_null : Z := 0x1039e.
Definition src0_D_const_double_0x1p28 : Z := 0x103a8.
Definition src0_D_const_double_1_0 : Z := 0x103b0.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b8.
Definition src0_D_const_double_0_5 : Z := 0x103c0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103c8.
Definition src0_D_const_double_0x1p1023 : Z := 0x103d0.
Definition src0_D_const_double_1_5 : Z := 0x103d8.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103e0.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e8.
Definition src0_D_const_u64_0x0101010101010102 : Z := 0x103f0.
Definition src0_D_const_double_0x1p120 : Z := 0x103f8.
Definition src0_D_debruijn32 : Z := 0x1045c.
Definition src0_D_size_classes : Z := 0x1047c.
Definition src0_D_small_cnt_tab : Z := 0x104dc.
Definition src0_D_med_cnt_tab : Z := 0x104f7.
Definition src0_D_jt_printf_core_1 : Z := 0x104fc.
Definition src0_D_jt_printf_core_2 : Z := 0x105dc.
Definition src0_D_jt_pop_arg : Z := 0x105fc.
Definition src0_D_states : Z := 0x10644.
Definition src0_D_xdigits : Z := 0x10814.
Definition src0_D_errmsgstr : Z := 0x10824.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x10fcc.
Definition src0_D_fe_getround : Z := 0x110d4.
Definition src0_D_EH_FRAME_LIST : Z := 0x11210.
Definition src0_D_init_array_start : Z := 0x1ed70.
Definition src0_D_fini_array_start : Z := 0x1ed78.
Definition src0_D_stderr : Z := 0x1ed80.
Definition src0_D_stdout : Z := 0x1ed88.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1ed90.
Definition src0_D_got_DYNAMIC : Z := 0x1ed98.
Definition src0_D_got_main : Z := 0x1eda0.
Definition src0_D_got_init : Z := 0x1eda8.
Definition src0_D_got_fini : Z := 0x1edb0.
Definition src0_D_got_register_frame_info : Z := 0x1edb8.
Definition src0_D_got_cxa_finalize : Z := 0x1edc0.
Definition src0_D_got_deregister_frame_info : Z := 0x1edc8.
Definition src0_D_got_stderr : Z := 0x1edd0.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1edd8.
Definition src0_D_got_stdout : Z := 0x1ede0.
Definition src0_D_got_environ : Z := 0x1ede8.
Definition src0_D_got_progname_full : Z := 0x1edf0.
Definition src0_D_got_progname : Z := 0x1edf8.
Definition src0_D_got_init_array_end : Z := 0x1ee00.
Definition src0_D_got_init_array_start : Z := 0x1ee08.
Definition src0_D_got_stack_chk_guard : Z := 0x1ee10.
Definition src0_D_got_fini_array_end : Z := 0x1ee18.
Definition src0_D_got_fini_array_start : Z := 0x1ee20.
Definition src0_D_dso_handle : Z := 0x1fe28.
Definition src0_D_aef_arg0 : Z := 0x1fe30.
Definition src0_D_aef_argc : Z := 0x1fe38.
Definition src0_D_aef_argv : Z := 0x1fe40.
Definition src0_D_stderr_FILE : Z := 0x1fe50.
Definition src0_D_stderr_used : Z := 0x1ff38.
Definition src0_D_stdout_FILE : Z := 0x1ff40.
Definition src0_D_stdout_used : Z := 0x20028.
Definition src0_D_default_stacksize : Z := 0x20030.
Definition src0_D_do_init_initialized : Z := 0x20040.
Definition src0_D_do_init_object : Z := 0x20048.
Definition src0_D_do_fini_finalized : Z := 0x20088.
Definition src0_D_read_stage : Z := 0x20089.
Definition src0_D_target_run_initialized : Z := 0x30090.
Definition src0_D_aef_in_callback : Z := 0x30094.
Definition src0_D_aef_aligned_copy_empty : Z := 0x300a0.
Definition src0_D_environ : Z := 0x300c0.
Definition src0_D_thread_list_lock : Z := 0x50198.
Definition src0_D_main_tls : Z := 0x501a0.
Definition src0_D_builtin_tls : Z := 0x300c8.
Definition src0_D_finished_atexit : Z := 0x501d0.
Definition src0_D_atexit_lock : Z := 0x501d4.
Definition src0_D_atexit_slot : Z := 0x501d8.
Definition src0_D_atexit_head : Z := 0x501e0.
Definition src0_D_atexit_builtin : Z := 0x501e8.
Definition src0_D_exit_exit_lock : Z := 0x503f0.
Definition src0_D_stack_chk_guard : Z := 0x503f8.
Definition src0_D_sysinfo : Z := 0x50400.
Definition src0_D_progname : Z := 0x50408.
Definition src0_D_progname_full : Z := 0x50410.
Definition src0_D_libc : Z := 0x50418.
Definition src0_D_hwcap : Z := 0x50480.
Definition src0_D_malloc_lock : Z := 0x50488.
Definition src0_D_malloc_context : Z := 0x50490.
Definition src0_D_malloc_replaced : Z := 0x50830.
Definition src0_D_stdin_used : Z := 0x50838.
Definition src0_D_ofl_lock : Z := 0x50840.
Definition src0_D_ofl_head : Z := 0x50848.
Definition src0_D_stderr_buf : Z := 0x50850.
Definition src0_D_stdout_buf : Z := 0x50858.
