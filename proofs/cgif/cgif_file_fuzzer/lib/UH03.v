(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ubs0_text_lo : Z := 0x12864.  Definition ubs0_text_hi : Z := 0x1e694.
Definition ubs0_rodata_lo : Z := 0x10298.  Definition ubs0_rodata_hi : Z := 0x110e0.
Definition ubs0_eh_frame_lo : Z := 0x11220.  Definition ubs0_eh_frame_hi : Z := 0x11864.
Definition ubs0_init_array_lo : Z := 0x1f698.  Definition ubs0_init_array_hi : Z := 0x1f6a0.
Definition ubs0_fini_array_lo : Z := 0x1f6a0.  Definition ubs0_fini_array_hi : Z := 0x1f6a8.
Definition ubs0_data_rel_ro_lo : Z := 0x1f6a8.  Definition ubs0_data_rel_ro_hi : Z := 0x1f6b8.
Definition ubs0_got_lo : Z := 0x1f6b8.  Definition ubs0_got_hi : Z := 0x1f750.
Definition ubs0_data_lo : Z := 0x20750.  Definition ubs0_data_hi : Z := 0x2095c.
Definition ubs0_bss_lo : Z := 0x20960.  Definition ubs0_bss_hi : Z := 0x51580.
Definition ubs0_A_start : Z := 0x12864.  Definition ubs0_E_start : Z := 0x128ac.
Definition ubs0_A_do_init : Z := 0x128ac.  Definition ubs0_E_do_init : Z := 0x12920.
Definition ubs0_A_do_fini : Z := 0x12920.  Definition ubs0_E_do_fini : Z := 0x129b0.
Definition ubs0_A_main : Z := 0x129b0.  Definition ubs0_E_main : Z := 0x12c74.
Definition ubs0_A_target_alloc_init : Z := 0x12c74.  Definition ubs0_E_target_alloc_init : Z := 0x12c78.
Definition ubs0_A_target_alloc_count : Z := 0x12c78.  Definition ubs0_E_target_alloc_count : Z := 0x12c80.
Definition ubs0_A_target_run : Z := 0x12c80.  Definition ubs0_E_target_run : Z := 0x12dd8.
Definition ubs0_A_aef_exit_guard : Z := 0x12dd8.  Definition ubs0_E_aef_exit_guard : Z := 0x12e08.
Definition ubs0_A_emit_printf : Z := 0x12e08.  Definition ubs0_E_emit_printf : Z := 0x12e50.
Definition ubs0_A_LLVMFuzzerTestOneInput : Z := 0x12e50.  Definition ubs0_E_LLVMFuzzerTestOneInput : Z := 0x13004.
Definition ubs0_A_read_frameconfig : Z := 0x13004.  Definition ubs0_E_read_frameconfig : Z := 0x1315c.
Definition ubs0_A_readdata : Z := 0x1315c.  Definition ubs0_E_readdata : Z := 0x131e8.
Definition ubs0_A_cgif_newgif : Z := 0x131e8.  Definition ubs0_E_cgif_newgif : Z := 0x133b8.
Definition ubs0_A_cgif_writecb : Z := 0x133b8.  Definition ubs0_E_cgif_writecb : Z := 0x1343c.
Definition ubs0_A_freeCGIF : Z := 0x1343c.  Definition ubs0_E_freeCGIF : Z := 0x13480.
Definition ubs0_A_cgif_addframe : Z := 0x13480.  Definition ubs0_E_cgif_addframe : Z := 0x13948.
Definition ubs0_A_cmpPixel : Z := 0x13948.  Definition ubs0_E_cmpPixel : Z := 0x13a58.
Definition ubs0_A_flushFrame : Z := 0x13a58.  Definition ubs0_E_flushFrame : Z := 0x14570.
Definition ubs0_A_freeFrame : Z := 0x14570.  Definition ubs0_E_freeFrame : Z := 0x145d0.
Definition ubs0_A_cgif_close : Z := 0x145d0.  Definition ubs0_E_cgif_close : Z := 0x146cc.
Definition ubs0_A_cgif_raw_newgif : Z := 0x146cc.  Definition ubs0_E_cgif_raw_newgif : Z := 0x14aa8.
Definition ubs0_A_cgif_raw_addframe : Z := 0x14aa8.  Definition ubs0_E_cgif_raw_addframe : Z := 0x15074.
Definition ubs0_A_LZW_GenerateStream : Z := 0x15074.  Definition ubs0_E_LZW_GenerateStream : Z := 0x157d8.
Definition ubs0_A_cgif_raw_close : Z := 0x157d8.  Definition ubs0_E_cgif_raw_close : Z := 0x15844.
Definition ubs0_A_create_byte_list : Z := 0x15844.  Definition ubs0_E_create_byte_list : Z := 0x15a70.
Definition ubs0_A_create_byte_list_block : Z := 0x15a70.  Definition ubs0_E_create_byte_list_block : Z := 0x15be0.
Definition ubs0_A_resetDict : Z := 0x15be0.  Definition ubs0_E_resetDict : Z := 0x15c98.
Definition ubs0_A_init : Z := 0x15c98.  Definition ubs0_E_init : Z := 0x15c9c.
Definition ubs0_A_init_libc : Z := 0x15c9c.  Definition ubs0_E_init_libc : Z := 0x15ec8.
Definition ubs0_A_libc_start_init : Z := 0x15ec8.  Definition ubs0_E_libc_start_init : Z := 0x15f14.
Definition ubs0_A_libc_start_main : Z := 0x15f14.  Definition ubs0_E_libc_start_main : Z := 0x15f74.
Definition ubs0_A_libc_start_main_stage2 : Z := 0x15f74.  Definition ubs0_E_libc_start_main_stage2 : Z := 0x15fbc.
Definition ubs0_A_init_tls : Z := 0x15fbc.  Definition ubs0_E_init_tls : Z := 0x1626c.
Definition ubs0_A_funcs_on_exit : Z := 0x1626c.  Definition ubs0_E_funcs_on_exit : Z := 0x16334.
Definition ubs0_A_cxa_finalize : Z := 0x16334.  Definition ubs0_E_cxa_finalize : Z := 0x16338.
Definition ubs0_A_atexit : Z := 0x16338.  Definition ubs0_E_atexit : Z := 0x163fc.
Definition ubs0_A_atexit_call : Z := 0x163fc.  Definition ubs0_E_atexit_call : Z := 0x16400.
Definition ubs0_A_fini : Z := 0x16400.  Definition ubs0_E_fini : Z := 0x16404.
Definition ubs0_A_libc_exit_fini : Z := 0x16404.  Definition ubs0_E_libc_exit_fini : Z := 0x16450.
Definition ubs0_A_exit : Z := 0x16450.  Definition ubs0_E_exit : Z := 0x164c4.
Definition ubs0_A_Exit : Z := 0x164c4.  Definition ubs0_E_Exit : Z := 0x164e0.
Definition ubs0_A_open : Z := 0x164e0.  Definition ubs0_E_open : Z := 0x165c4.
Definition ubs0_A_init_ssp : Z := 0x165c4.  Definition ubs0_E_init_ssp : Z := 0x16624.
Definition ubs0_A_stack_chk_fail : Z := 0x16624.  Definition ubs0_E_stack_chk_fail : Z := 0x1662c.
Definition ubs0_A_syscall_ret : Z := 0x1662c.  Definition ubs0_E_syscall_ret : Z := 0x16664.
Definition ubs0_A_errno_location : Z := 0x16664.  Definition ubs0_E_errno_location : Z := 0x16670.
Definition ubs0_A_free : Z := 0x16670.  Definition ubs0_E_free : Z := 0x16674.
Definition ubs0_A_libc_calloc : Z := 0x16674.  Definition ubs0_E_libc_calloc : Z := 0x167ac.
Definition ubs0_A_libc_malloc : Z := 0x167ac.  Definition ubs0_E_libc_malloc : Z := 0x167b0.
Definition ubs0_A_malloc : Z := 0x167b0.  Definition ubs0_E_malloc : Z := 0x167b4.
Definition ubs0_A_libc_free : Z := 0x167b4.  Definition ubs0_E_libc_free : Z := 0x16980.
Definition ubs0_A_get_meta : Z := 0x16980.  Definition ubs0_E_get_meta : Z := 0x16a90.
Definition ubs0_A_nontrivial_free : Z := 0x16a90.  Definition ubs0_E_nontrivial_free : Z := 0x16e68.
Definition ubs0_A_alloc_meta : Z := 0x16e68.  Definition ubs0_E_alloc_meta : Z := 0x17140.
Definition ubs0_A_libc_malloc_impl : Z := 0x17140.  Definition ubs0_E_libc_malloc_impl : Z := 0x174b0.
Definition ubs0_A_alloc_slot : Z := 0x174b0.  Definition ubs0_E_alloc_slot : Z := 0x17d54.
Definition ubs0_A_enframe : Z := 0x17d54.  Definition ubs0_E_enframe : Z := 0x17ea4.
Definition ubs0_A_malloc_allzerop : Z := 0x17ea4.  Definition ubs0_E_malloc_allzerop : Z := 0x1801c.
Definition ubs0_A_vm_wait : Z := 0x1801c.  Definition ubs0_E_vm_wait : Z := 0x18020.
Definition ubs0_A_mmap : Z := 0x18020.  Definition ubs0_E_mmap : Z := 0x1810c.
Definition ubs0_A_mprotect : Z := 0x1810c.  Definition ubs0_E_mprotect : Z := 0x18154.
Definition ubs0_A_munmap : Z := 0x18154.  Definition ubs0_E_munmap : Z := 0x1819c.
Definition ubs0_A_unlist_locked_file : Z := 0x1819c.  Definition ubs0_E_unlist_locked_file : Z := 0x181a0.
Definition ubs0_A_fclose : Z := 0x181a0.  Definition ubs0_E_fclose : Z := 0x1826c.
Definition ubs0_A_fflush : Z := 0x1826c.  Definition ubs0_E_fflush : Z := 0x183dc.
Definition ubs0_A_lockfile : Z := 0x183dc.  Definition ubs0_E_lockfile : Z := 0x184d8.
Definition ubs0_A_unlockfile : Z := 0x184d8.  Definition ubs0_E_unlockfile : Z := 0x18538.
Definition ubs0_A_fopen : Z := 0x18538.  Definition ubs0_E_fopen : Z := 0x18614.
Definition ubs0_A_fmodeflags : Z := 0x18614.  Definition ubs0_E_fmodeflags : Z := 0x186c8.
Definition ubs0_A_fdopen : Z := 0x186c8.  Definition ubs0_E_fdopen : Z := 0x188a0.
Definition ubs0_A_stdio_read : Z := 0x188a0.  Definition ubs0_E_stdio_read : Z := 0x189b8.
Definition ubs0_A_stdio_write : Z := 0x189b8.  Definition ubs0_E_stdio_write : Z := 0x18b48.
Definition ubs0_A_stdio_seek : Z := 0x18b48.  Definition ubs0_E_stdio_seek : Z := 0x18b50.
Definition ubs0_A_aio_close : Z := 0x18b50.  Definition ubs0_E_aio_close : Z := 0x18b54.
Definition ubs0_A_stdio_close : Z := 0x18b54.  Definition ubs0_E_stdio_close : Z := 0x18b80.
Definition ubs0_A_fprintf : Z := 0x18b80.  Definition ubs0_E_fprintf : Z := 0x18be4.
Definition ubs0_A_fwritex : Z := 0x18be4.  Definition ubs0_E_fwritex : Z := 0x18d1c.
Definition ubs0_A_fwrite : Z := 0x18d1c.  Definition ubs0_E_fwrite : Z := 0x18dd4.
Definition ubs0_A_towrite : Z := 0x18dd4.  Definition ubs0_E_towrite : Z := 0x18e28.
Definition ubs0_A_stdio_exit : Z := 0x18e28.  Definition ubs0_E_stdio_exit : Z := 0x18fcc.
Definition ubs0_A_ofl_lock : Z := 0x18fcc.  Definition ubs0_E_ofl_lock : Z := 0x18ffc.
Definition ubs0_A_ofl_unlock : Z := 0x18ffc.  Definition ubs0_E_ofl_unlock : Z := 0x19008.
Definition ubs0_A_ofl_add : Z := 0x19008.  Definition ubs0_E_ofl_add : Z := 0x19048.
Definition ubs0_A_stdout_write : Z := 0x19048.  Definition ubs0_E_stdout_write : Z := 0x190e8.
Definition ubs0_A_vfprintf : Z := 0x190e8.  Definition ubs0_E_vfprintf : Z := 0x19298.
Definition ubs0_A_printf_core : Z := 0x19298.  Definition ubs0_E_printf_core : Z := 0x1a0c8.
Definition ubs0_A_pop_arg : Z := 0x1a0c8.  Definition ubs0_E_pop_arg : Z := 0x1a1fc.
Definition ubs0_A_pad : Z := 0x1a1fc.  Definition ubs0_E_pad : Z := 0x1a2d0.
Definition ubs0_A_fmt_fp : Z := 0x1a2d0.  Definition ubs0_E_fmt_fp : Z := 0x1b998.
Definition ubs0_A_strerror : Z := 0x1b998.  Definition ubs0_E_strerror : Z := 0x1b9d4.
Definition ubs0_A_lctrans_impl : Z := 0x1b9d4.  Definition ubs0_E_lctrans_impl : Z := 0x1b9d8.
Definition ubs0_A_lctrans : Z := 0x1b9d8.  Definition ubs0_E_lctrans : Z := 0x1b9dc.
Definition ubs0_A_wctomb : Z := 0x1b9dc.  Definition ubs0_E_wctomb : Z := 0x1ba00.
Definition ubs0_A_wcrtomb : Z := 0x1ba00.  Definition ubs0_E_wcrtomb : Z := 0x1bb2c.
Definition ubs0_A_extenddftf2 : Z := 0x1bb2c.  Definition ubs0_E_extenddftf2 : Z := 0x1bcbc.
Definition ubs0_A_signbitl : Z := 0x1bcbc.  Definition ubs0_E_signbitl : Z := 0x1bcc4.
Definition ubs0_A_fpclassifyl : Z := 0x1bcc4.  Definition ubs0_E_fpclassifyl : Z := 0x1bd08.
Definition ubs0_A_frexpl : Z := 0x1bd08.  Definition ubs0_E_frexpl : Z := 0x1bde0.
Definition ubs0_A_letf2 : Z := 0x1bde0.  Definition ubs0_E_letf2 : Z := 0x1bea8.
Definition ubs0_A_multf3 : Z := 0x1bea8.  Definition ubs0_E_multf3 : Z := 0x1c5a8.
Definition ubs0_A_floatsitf : Z := 0x1c5a8.  Definition ubs0_E_floatsitf : Z := 0x1c6b0.
Definition ubs0_A_scalbn : Z := 0x1c6b0.  Definition ubs0_E_scalbn : Z := 0x1c748.
Definition ubs0_A_subtf3 : Z := 0x1c748.  Definition ubs0_E_subtf3 : Z := 0x1c758.
Definition ubs0_A_addtf3 : Z := 0x1c758.  Definition ubs0_E_addtf3 : Z := 0x1cf24.
Definition ubs0_A_fe_getround : Z := 0x1cf24.  Definition ubs0_E_fe_getround : Z := 0x1cf54.
Definition ubs0_A_fe_raise_inexact : Z := 0x1cf54.  Definition ubs0_E_fe_raise_inexact : Z := 0x1cf60.
Definition ubs0_A_fixunstfsi : Z := 0x1cf60.  Definition ubs0_E_fixunstfsi : Z := 0x1cff4.
Definition ubs0_A_floatunsitf : Z := 0x1cff4.  Definition ubs0_E_floatunsitf : Z := 0x1d0e0.
Definition ubs0_A_fixtfsi : Z := 0x1d0e0.  Definition ubs0_E_fixtfsi : Z := 0x1d188.
Definition ubs0_A_divtf3 : Z := 0x1d188.  Definition ubs0_E_divtf3 : Z := 0x1da8c.
Definition ubs0_A_vprintf : Z := 0x1da8c.  Definition ubs0_E_vprintf : Z := 0x1daa8.
Definition ubs0_A_bcmp : Z := 0x1daa8.  Definition ubs0_E_bcmp : Z := 0x1daac.
Definition ubs0_A_memcmp : Z := 0x1daac.  Definition ubs0_E_memcmp : Z := 0x1dadc.
Definition ubs0_A_memcpy : Z := 0x1dadc.  Definition ubs0_E_memcpy : Z := 0x1dee0.
Definition ubs0_A_memset : Z := 0x1dee0.  Definition ubs0_E_memset : Z := 0x1dfd8.
Definition ubs0_A_strchr : Z := 0x1dfd8.  Definition ubs0_E_strchr : Z := 0x1e014.
Definition ubs0_A_strchrnul : Z := 0x1e014.  Definition ubs0_E_strchrnul : Z := 0x1e0f4.
Definition ubs0_A_strlen : Z := 0x1e0f4.  Definition ubs0_E_strlen : Z := 0x1e184.
Definition ubs0_A_strnlen : Z := 0x1e184.  Definition ubs0_E_strnlen : Z := 0x1e1c8.
Definition ubs0_A_memchr : Z := 0x1e1c8.  Definition ubs0_E_memchr : Z := 0x1e294.
Definition ubs0_A_lock : Z := 0x1e294.  Definition ubs0_E_lock : Z := 0x1e51c.
Definition ubs0_A_unlock : Z := 0x1e51c.  Definition ubs0_E_unlock : Z := 0x1e590.
Definition ubs0_A_syscall_cp_c : Z := 0x1e590.  Definition ubs0_E_syscall_cp_c : Z := 0x1e5b4.
Definition ubs0_A_syscall_cp : Z := 0x1e5b4.  Definition ubs0_E_syscall_cp : Z := 0x1e5b8.
Definition ubs0_A_set_thread_area : Z := 0x1e5b8.  Definition ubs0_E_set_thread_area : Z := 0x1e5c4.
Definition ubs0_A_unistd_exit : Z := 0x1e5c4.  Definition ubs0_E_unistd_exit : Z := 0x1e5d0.
Definition ubs0_A_close : Z := 0x1e5d0.  Definition ubs0_E_close : Z := 0x1e624.
Definition ubs0_A_lseek : Z := 0x1e624.  Definition ubs0_E_lseek : Z := 0x1e630.
Definition ubs0_A_read : Z := 0x1e630.  Definition ubs0_E_read : Z := 0x1e664.
Definition ubs0_A_unlink : Z := 0x1e664.  Definition ubs0_E_unlink : Z := 0x1e694.
Definition ubs0_D_str_n0X0x : Z := 0x10298.
Definition ubs0_D_str_wb : Z := 0x102a2.
Definition ubs0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition ubs0_D_str_cli_out_of_memory_n : Z := 0x102b8.
Definition ubs0_D_str_d_n : Z := 0x102cc.
Definition ubs0_D_str : Z := 0x102d0.
Definition ubs0_D_str_2 : Z := 0x102d1.
Definition ubs0_D_str_usage_s_INPUT_n : Z := 0x102d3.
Definition ubs0_D_str_cli_config_len_overruns : Z := 0x102e4.
Definition ubs0_D_str_tmp_out_gif : Z := 0x10304.
Definition ubs0_D_str_3 : Z := 0x10311.
Definition ubs0_D_str_inf : Z := 0x10313.
Definition ubs0_D_str_INF : Z := 0x10317.
Definition ubs0_D_str_cli_input_u_bytes_refuse : Z := 0x1031b.
Definition ubs0_D_str_cli_cannot_open_s_n : Z := 0x1033c.
Definition ubs0_D_str_cli_read_error_on_s_n : Z := 0x10351.
Definition ubs0_D_str_NAN : Z := 0x10368.
Definition ubs0_D_str_nan : Z := 0x1036c.
Definition ubs0_D_str_cli_input_shorter_than_h : Z := 0x10370.
Definition ubs0_D_str_rwa : Z := 0x10390.
Definition ubs0_D_str_dev_null : Z := 0x10394.
Definition ubs0_D_str_null : Z := 0x1039e.
Definition ubs0_D_const_double_0x1p28 : Z := 0x103a8.
Definition ubs0_D_const_double_1_0 : Z := 0x103b0.
Definition ubs0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b8.
Definition ubs0_D_const_double_0_5 : Z := 0x103c0.
Definition ubs0_D_const_ONES_0x0101010101010100 : Z := 0x103c8.
Definition ubs0_D_const_double_0x1p1023 : Z := 0x103d0.
Definition ubs0_D_const_double_1_5 : Z := 0x103d8.
Definition ubs0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103e0.
Definition ubs0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e8.
Definition ubs0_D_const_u64_0x0101010101010102 : Z := 0x103f0.
Definition ubs0_D_const_double_0x1p120 : Z := 0x103f8.
Definition ubs0_D_debruijn32 : Z := 0x1045c.
Definition ubs0_D_size_classes : Z := 0x1047c.
Definition ubs0_D_small_cnt_tab : Z := 0x104dc.
Definition ubs0_D_med_cnt_tab : Z := 0x104f7.
Definition ubs0_D_jt_printf_core_1 : Z := 0x104fc.
Definition ubs0_D_jt_printf_core_2 : Z := 0x105dc.
Definition ubs0_D_jt_pop_arg : Z := 0x105fc.
Definition ubs0_D_states : Z := 0x10644.
Definition ubs0_D_xdigits : Z := 0x10814.
Definition ubs0_D_errmsgstr : Z := 0x10824.
Definition ubs0_D_global_pointer : Z := 0x10800.
Definition ubs0_D_errmsgidx : Z := 0x10fcc.
Definition ubs0_D_fe_getround : Z := 0x110d4.
Definition ubs0_D_EH_FRAME_LIST : Z := 0x11220.
Definition ubs0_D_init_array_start : Z := 0x1f698.
Definition ubs0_D_fini_array_start : Z := 0x1f6a0.
Definition ubs0_D_stderr : Z := 0x1f6a8.
Definition ubs0_D_stdout : Z := 0x1f6b0.
Definition ubs0_D_got_DYNAMIC_reserved : Z := 0x1f6b8.
Definition ubs0_D_got_DYNAMIC : Z := 0x1f6c0.
Definition ubs0_D_got_main : Z := 0x1f6c8.
Definition ubs0_D_got_init : Z := 0x1f6d0.
Definition ubs0_D_got_fini : Z := 0x1f6d8.
Definition ubs0_D_got_register_frame_info : Z := 0x1f6e0.
Definition ubs0_D_got_cxa_finalize : Z := 0x1f6e8.
Definition ubs0_D_got_deregister_frame_info : Z := 0x1f6f0.
Definition ubs0_D_got_stderr : Z := 0x1f6f8.
Definition ubs0_D_got_LLVMFuzzerInitialize : Z := 0x1f700.
Definition ubs0_D_got_stdout : Z := 0x1f708.
Definition ubs0_D_got_environ : Z := 0x1f710.
Definition ubs0_D_got_progname_full : Z := 0x1f718.
Definition ubs0_D_got_progname : Z := 0x1f720.
Definition ubs0_D_got_init_array_end : Z := 0x1f728.
Definition ubs0_D_got_init_array_start : Z := 0x1f730.
Definition ubs0_D_got_stack_chk_guard : Z := 0x1f738.
Definition ubs0_D_got_fini_array_end : Z := 0x1f740.
Definition ubs0_D_got_fini_array_start : Z := 0x1f748.
Definition ubs0_D_dso_handle : Z := 0x20750.
Definition ubs0_D_aef_arg0 : Z := 0x20758.
Definition ubs0_D_aef_argc : Z := 0x20760.
Definition ubs0_D_aef_argv : Z := 0x20768.
Definition ubs0_D_stderr_FILE : Z := 0x20778.
Definition ubs0_D_stderr_used : Z := 0x20860.
Definition ubs0_D_stdout_FILE : Z := 0x20868.
Definition ubs0_D_stdout_used : Z := 0x20950.
Definition ubs0_D_default_stacksize : Z := 0x20958.
Definition ubs0_D_do_init_initialized : Z := 0x20960.
Definition ubs0_D_do_init_object : Z := 0x20968.
Definition ubs0_D_do_fini_finalized : Z := 0x209a8.
Definition ubs0_D_read_stage : Z := 0x209a9.
Definition ubs0_D_target_run_initialized : Z := 0x309b0.
Definition ubs0_D_aef_in_callback : Z := 0x309b4.
Definition ubs0_D_aef_aligned_copy_empty : Z := 0x309c0.
Definition ubs0_D_environ : Z := 0x309e0.
Definition ubs0_D_thread_list_lock : Z := 0x50ab8.
Definition ubs0_D_main_tls : Z := 0x50ac0.
Definition ubs0_D_builtin_tls : Z := 0x309e8.
Definition ubs0_D_finished_atexit : Z := 0x50af0.
Definition ubs0_D_atexit_lock : Z := 0x50af4.
Definition ubs0_D_atexit_slot : Z := 0x50af8.
Definition ubs0_D_atexit_head : Z := 0x50b00.
Definition ubs0_D_atexit_builtin : Z := 0x50b08.
Definition ubs0_D_exit_exit_lock : Z := 0x50d10.
Definition ubs0_D_stack_chk_guard : Z := 0x50d18.
Definition ubs0_D_sysinfo : Z := 0x50d20.
Definition ubs0_D_progname : Z := 0x50d28.
Definition ubs0_D_progname_full : Z := 0x50d30.
Definition ubs0_D_libc : Z := 0x50d38.
Definition ubs0_D_hwcap : Z := 0x50da0.
Definition ubs0_D_malloc_lock : Z := 0x50da8.
Definition ubs0_D_malloc_context : Z := 0x50db0.
Definition ubs0_D_malloc_replaced : Z := 0x51150.
Definition ubs0_D_stdin_used : Z := 0x51158.
Definition ubs0_D_ofl_lock : Z := 0x51160.
Definition ubs0_D_ofl_head : Z := 0x51168.
Definition ubs0_D_stderr_buf : Z := 0x51170.
Definition ubs0_D_stdout_buf : Z := 0x51178.
