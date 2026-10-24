(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x13c04.  Definition src0_text_hi : Z := 0x1d694.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x12724.
Definition src0_eh_frame_lo : Z := 0x12818.  Definition src0_eh_frame_hi : Z := 0x12c04.
Definition src0_init_array_lo : Z := 0x1e698.  Definition src0_init_array_hi : Z := 0x1e6a0.
Definition src0_fini_array_lo : Z := 0x1e6a0.  Definition src0_fini_array_hi : Z := 0x1e6a8.
Definition src0_data_rel_ro_lo : Z := 0x1e6a8.  Definition src0_data_rel_ro_hi : Z := 0x1e6b8.
Definition src0_got_lo : Z := 0x1e6b8.  Definition src0_got_hi : Z := 0x1e750.
Definition src0_data_lo : Z := 0x1f750.  Definition src0_data_hi : Z := 0x1f95c.
Definition src0_bss_lo : Z := 0x1f960.  Definition src0_bss_hi : Z := 0x50588.
Definition src0_A_start : Z := 0x13c04.  Definition src0_E_start : Z := 0x13c4c.
Definition src0_A_do_init : Z := 0x13c4c.  Definition src0_E_do_init : Z := 0x13cc0.
Definition src0_A_do_fini : Z := 0x13cc0.  Definition src0_E_do_fini : Z := 0x13d50.
Definition src0_A_main : Z := 0x13d50.  Definition src0_E_main : Z := 0x14014.
Definition src0_A_target_alloc_init : Z := 0x14014.  Definition src0_E_target_alloc_init : Z := 0x14018.
Definition src0_A_target_alloc_count : Z := 0x14018.  Definition src0_E_target_alloc_count : Z := 0x14020.
Definition src0_A_target_run : Z := 0x14020.  Definition src0_E_target_run : Z := 0x14178.
Definition src0_A_aef_exit_guard : Z := 0x14178.  Definition src0_E_aef_exit_guard : Z := 0x141a8.
Definition src0_A_emit_printf : Z := 0x141a8.  Definition src0_E_emit_printf : Z := 0x141f0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x141f0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x130b0.
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
Definition src0_A_create_byte_list_block : Z := 0x15254.  Definition src0_E_create_byte_list_block : Z := 0x152a0.
Definition src0_A_init : Z := 0x152a0.  Definition src0_E_init : Z := 0x152a4.
Definition src0_A_init_libc : Z := 0x152a4.  Definition src0_E_init_libc : Z := 0x154d0.
Definition src0_A_libc_start_init : Z := 0x154d0.  Definition src0_E_libc_start_init : Z := 0x1551c.
Definition src0_A_libc_start_main : Z := 0x1551c.  Definition src0_E_libc_start_main : Z := 0x1557c.
Definition src0_A_libc_start_main_stage2 : Z := 0x1557c.  Definition src0_E_libc_start_main_stage2 : Z := 0x155c4.
Definition src0_A_init_tls : Z := 0x155c4.  Definition src0_E_init_tls : Z := 0x15954.
Definition src0_A_funcs_on_exit : Z := 0x15954.  Definition src0_E_funcs_on_exit : Z := 0x15a1c.
Definition src0_A_cxa_finalize : Z := 0x15a1c.  Definition src0_E_cxa_finalize : Z := 0x15a20.
Definition src0_A_atexit : Z := 0x15a20.  Definition src0_E_atexit : Z := 0x15ae4.
Definition src0_A_atexit_call : Z := 0x15ae4.  Definition src0_E_atexit_call : Z := 0x15ae8.
Definition src0_A_fini : Z := 0x15ae8.  Definition src0_E_fini : Z := 0x15aec.
Definition src0_A_libc_exit_fini : Z := 0x15aec.  Definition src0_E_libc_exit_fini : Z := 0x15b38.
Definition src0_A_exit : Z := 0x15b38.  Definition src0_E_exit : Z := 0x15938.
Definition src0_A_Exit : Z := 0x15938.  Definition src0_E_Exit : Z := 0x15bac.
Definition src0_A_open : Z := 0x15bac.  Definition src0_E_open : Z := 0x15c90.
Definition src0_A_init_ssp : Z := 0x15c90.  Definition src0_E_init_ssp : Z := 0x15cf0.
Definition src0_A_stack_chk_fail : Z := 0x15cf0.  Definition src0_E_stack_chk_fail : Z := 0x15cf8.
Definition src0_A_syscall_ret : Z := 0x15cf8.  Definition src0_E_syscall_ret : Z := 0x15d30.
Definition src0_A_errno_location : Z := 0x15d30.  Definition src0_E_errno_location : Z := 0x15d3c.
Definition src0_A_free : Z := 0x15d3c.  Definition src0_E_free : Z := 0x15d40.
Definition src0_A_libc_calloc : Z := 0x15d40.  Definition src0_E_libc_calloc : Z := 0x15e78.
Definition src0_A_libc_malloc : Z := 0x15e78.  Definition src0_E_libc_malloc : Z := 0x15e7c.
Definition src0_A_malloc : Z := 0x15e7c.  Definition src0_E_malloc : Z := 0x15e80.
Definition src0_A_libc_free : Z := 0x15e80.  Definition src0_E_libc_free : Z := 0x1604c.
Definition src0_A_get_meta : Z := 0x1604c.  Definition src0_E_get_meta : Z := 0x1615c.
Definition src0_A_nontrivial_free : Z := 0x1615c.  Definition src0_E_nontrivial_free : Z := 0x16534.
Definition src0_A_alloc_meta : Z := 0x16534.  Definition src0_E_alloc_meta : Z := 0x1680c.
Definition src0_A_libc_malloc_impl : Z := 0x1680c.  Definition src0_E_libc_malloc_impl : Z := 0x16b7c.
Definition src0_A_alloc_slot : Z := 0x16b7c.  Definition src0_E_alloc_slot : Z := 0x17420.
Definition src0_A_enframe : Z := 0x17420.  Definition src0_E_enframe : Z := 0x17570.
Definition src0_A_malloc_allzerop : Z := 0x17570.  Definition src0_E_malloc_allzerop : Z := 0x176e8.
Definition src0_A_vm_wait : Z := 0x176e8.  Definition src0_E_vm_wait : Z := 0x176ec.
Definition src0_A_mmap : Z := 0x176ec.  Definition src0_E_mmap : Z := 0x177d8.
Definition src0_A_mprotect : Z := 0x177d8.  Definition src0_E_mprotect : Z := 0x17820.
Definition src0_A_munmap : Z := 0x17820.  Definition src0_E_munmap : Z := 0x17878.
Definition src0_A_unlist_locked_file : Z := 0x17878.  Definition src0_E_unlist_locked_file : Z := 0x1787c.
Definition src0_A_fclose : Z := 0x1787c.  Definition src0_E_fclose : Z := 0x1793c.
Definition src0_A_fflush : Z := 0x1793c.  Definition src0_E_fflush : Z := 0x17aac.
Definition src0_A_lockfile : Z := 0x17aac.  Definition src0_E_lockfile : Z := 0x17ba8.
Definition src0_A_unlockfile : Z := 0x17ba8.  Definition src0_E_unlockfile : Z := 0x17c14.
Definition src0_A_fopen : Z := 0x17c14.  Definition src0_E_fopen : Z := 0x17cf0.
Definition src0_A_fmodeflags : Z := 0x17cf0.  Definition src0_E_fmodeflags : Z := 0x17da4.
Definition src0_A_fdopen : Z := 0x17da4.  Definition src0_E_fdopen : Z := 0x17f7c.
Definition src0_A_stdio_read : Z := 0x17f7c.  Definition src0_E_stdio_read : Z := 0x180c0.
Definition src0_A_stdio_write : Z := 0x180c0.  Definition src0_E_stdio_write : Z := 0x18224.
Definition src0_A_stdio_seek : Z := 0x18224.  Definition src0_E_stdio_seek : Z := 0x18090.
Definition src0_A_aio_close : Z := 0x18090.  Definition src0_E_aio_close : Z := 0x18094.
Definition src0_A_stdio_close : Z := 0x18094.  Definition src0_E_stdio_close : Z := 0x17c08.
Definition src0_A_fprintf : Z := 0x17c08.  Definition src0_E_fprintf : Z := 0x17c6c.
Definition src0_A_fwritex : Z := 0x17c6c.  Definition src0_E_fwritex : Z := 0x17da4.
Definition src0_A_fwrite : Z := 0x17da4.  Definition src0_E_fwrite : Z := 0x17e5c.
Definition src0_A_towrite : Z := 0x17e5c.  Definition src0_E_towrite : Z := 0x17eb0.
Definition src0_A_stdio_exit : Z := 0x17eb0.  Definition src0_E_stdio_exit : Z := 0x18054.
Definition src0_A_ofl_lock : Z := 0x18054.  Definition src0_E_ofl_lock : Z := 0x18084.
Definition src0_A_ofl_unlock : Z := 0x18084.  Definition src0_E_ofl_unlock : Z := 0x186e4.
Definition src0_A_ofl_add : Z := 0x186e4.  Definition src0_E_ofl_add : Z := 0x18258.
Definition src0_A_stdout_write : Z := 0x18258.  Definition src0_E_stdout_write : Z := 0x182f8.
Definition src0_A_vfprintf : Z := 0x182f8.  Definition src0_E_vfprintf : Z := 0x184a8.
Definition src0_A_printf_core : Z := 0x184a8.  Definition src0_E_printf_core : Z := 0x192d8.
Definition src0_A_pop_arg : Z := 0x192d8.  Definition src0_E_pop_arg : Z := 0x1940c.
Definition src0_A_pad : Z := 0x1940c.  Definition src0_E_pad : Z := 0x194e0.
Definition src0_A_fmt_fp : Z := 0x194e0.  Definition src0_E_fmt_fp : Z := 0x1aba8.
Definition src0_A_strerror : Z := 0x1aba8.  Definition src0_E_strerror : Z := 0x1b0b0.
Definition src0_A_lctrans_impl : Z := 0x1b0b0.  Definition src0_E_lctrans_impl : Z := 0x1abe8.
Definition src0_A_lctrans : Z := 0x1abe8.  Definition src0_E_lctrans : Z := 0x1abec.
Definition src0_A_wctomb : Z := 0x1abec.  Definition src0_E_wctomb : Z := 0x1ac10.
Definition src0_A_wcrtomb : Z := 0x1ac10.  Definition src0_E_wcrtomb : Z := 0x1ad3c.
Definition src0_A_extenddftf2 : Z := 0x1ad3c.  Definition src0_E_extenddftf2 : Z := 0x1b398.
Definition src0_A_signbitl : Z := 0x1b398.  Definition src0_E_signbitl : Z := 0x1aed4.
Definition src0_A_fpclassifyl : Z := 0x1aed4.  Definition src0_E_fpclassifyl : Z := 0x1b3e4.
Definition src0_A_frexpl : Z := 0x1b3e4.  Definition src0_E_frexpl : Z := 0x1aff0.
Definition src0_A_letf2 : Z := 0x1aff0.  Definition src0_E_letf2 : Z := 0x1b0b8.
Definition src0_A_multf3 : Z := 0x1b0b8.  Definition src0_E_multf3 : Z := 0x1b7b8.
Definition src0_A_floatsitf : Z := 0x1b7b8.  Definition src0_E_floatsitf : Z := 0x1bd8c.
Definition src0_A_scalbn : Z := 0x1bd8c.  Definition src0_E_scalbn : Z := 0x1b958.
Definition src0_A_subtf3 : Z := 0x1b958.  Definition src0_E_subtf3 : Z := 0x1b968.
Definition src0_A_addtf3 : Z := 0x1b968.  Definition src0_E_addtf3 : Z := 0x1c134.
Definition src0_A_fe_getround : Z := 0x1c134.  Definition src0_E_fe_getround : Z := 0x1c164.
Definition src0_A_fe_raise_inexact : Z := 0x1c164.  Definition src0_E_fe_raise_inexact : Z := 0x1c170.
Definition src0_A_fixunstfsi : Z := 0x1c170.  Definition src0_E_fixunstfsi : Z := 0x1c204.
Definition src0_A_floatunsitf : Z := 0x1c204.  Definition src0_E_floatunsitf : Z := 0x1c2f0.
Definition src0_A_fixtfsi : Z := 0x1c2f0.  Definition src0_E_fixtfsi : Z := 0x1c398.
Definition src0_A_divtf3 : Z := 0x1c398.  Definition src0_E_divtf3 : Z := 0x1cc9c.
Definition src0_A_vprintf : Z := 0x1cc9c.  Definition src0_E_vprintf : Z := 0x1d184.
Definition src0_A_bcmp : Z := 0x1d184.  Definition src0_E_bcmp : Z := 0x1d188.
Definition src0_A_memcmp : Z := 0x1d188.  Definition src0_E_memcmp : Z := 0x1ccb8.
Definition src0_A_memcpy : Z := 0x1ccb8.  Definition src0_E_memcpy : Z := 0x1d0bc.
Definition src0_A_memset : Z := 0x1d0bc.  Definition src0_E_memset : Z := 0x1d6b4.
Definition src0_A_strchr : Z := 0x1d6b4.  Definition src0_E_strchr : Z := 0x1d6f0.
Definition src0_A_strchrnul : Z := 0x1d6f0.  Definition src0_E_strchrnul : Z := 0x1d7d0.
Definition src0_A_strlen : Z := 0x1d7d0.  Definition src0_E_strlen : Z := 0x1d1b4.
Definition src0_A_strnlen : Z := 0x1d1b4.  Definition src0_E_strnlen : Z := 0x1d1f8.
Definition src0_A_memchr : Z := 0x1d1f8.  Definition src0_E_memchr : Z := 0x1d2c4.
Definition src0_A_lock : Z := 0x1d2c4.  Definition src0_E_lock : Z := 0x1d54c.
Definition src0_A_unlock : Z := 0x1d54c.  Definition src0_E_unlock : Z := 0x1d5c0.
Definition src0_A_syscall_cp_c : Z := 0x1d5c0.  Definition src0_E_syscall_cp_c : Z := 0x1d5e4.
Definition src0_A_syscall_cp : Z := 0x1d5e4.  Definition src0_E_syscall_cp : Z := 0x1d5e8.
Definition src0_A_set_thread_area : Z := 0x1d5e8.  Definition src0_E_set_thread_area : Z := 0x1d5f4.
Definition src0_A_unistd_exit : Z := 0x1d5f4.  Definition src0_E_unistd_exit : Z := 0x1d600.
Definition src0_A_close : Z := 0x1d600.  Definition src0_E_close : Z := 0x1d654.
Definition src0_A_lseek : Z := 0x1d654.  Definition src0_E_lseek : Z := 0x1d660.
Definition src0_A_read : Z := 0x1d660.  Definition src0_E_read : Z := 0x1dd40.
Definition src0_A_unlink : Z := 0x1dd40.  Definition src0_E_unlink : Z := 0x1dd70.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_wb : Z := 0x102a2.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10358.
Definition src0_D_str_d_n : Z := 0x1036c.
Definition src0_D_str : Z := 0x10370.
Definition src0_D_str_2 : Z := 0x102d1.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10373.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10384.
Definition src0_D_str_tmp_out_gif : Z := 0x10304.
Definition src0_D_str_3 : Z := 0x10311.
Definition src0_D_str_inf : Z := 0x10313.
Definition src0_D_str_INF : Z := 0x10317.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x104bb.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x104dc.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x104f1.
Definition src0_D_str_NAN : Z := 0x10368.
Definition src0_D_str_nan : Z := 0x1036c.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10521.
Definition src0_D_str_rwa : Z := 0x10390.
Definition src0_D_str_dev_null : Z := 0x10541.
Definition src0_D_str_null : Z := 0x1054b.
Definition src0_D_const_double_0x1p28 : Z := 0x103a8.
Definition src0_D_const_double_1_0 : Z := 0x103b0.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x119f0.
Definition src0_D_const_double_0_5 : Z := 0x103c0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x11a00.
Definition src0_D_const_double_0x1p1023 : Z := 0x103d0.
Definition src0_D_const_double_1_5 : Z := 0x103d8.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103e0.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e8.
Definition src0_D_const_u64_0x0101010101010102 : Z := 0x103f0.
Definition src0_D_const_double_0x1p120 : Z := 0x103f8.
Definition src0_D_debruijn32 : Z := 0x11a8c.
Definition src0_D_size_classes : Z := 0x11aac.
Definition src0_D_small_cnt_tab : Z := 0x11b0c.
Definition src0_D_med_cnt_tab : Z := 0x11b27.
Definition src0_D_jt_printf_core_1 : Z := 0x11b40.
Definition src0_D_jt_printf_core_2 : Z := 0x11c20.
Definition src0_D_jt_pop_arg : Z := 0x11c40.
Definition src0_D_states : Z := 0x11c88.
Definition src0_D_xdigits : Z := 0x11e58.
Definition src0_D_errmsgstr : Z := 0x11e68.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x12610.
Definition src0_D_fe_getround : Z := 0x12718.
Definition src0_D_EH_FRAME_LIST : Z := 0x12818.
Definition src0_D_init_array_start : Z := 0x1e698.
Definition src0_D_fini_array_start : Z := 0x1e6a0.
Definition src0_D_stderr : Z := 0x1e6a8.
Definition src0_D_stdout : Z := 0x1e6b0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1ed90.
Definition src0_D_got_DYNAMIC : Z := 0x1e6c0.
Definition src0_D_got_main : Z := 0x1e6c8.
Definition src0_D_got_init : Z := 0x1e6d0.
Definition src0_D_got_fini : Z := 0x1e6d8.
Definition src0_D_got_register_frame_info : Z := 0x1e6e0.
Definition src0_D_got_cxa_finalize : Z := 0x1e6e8.
Definition src0_D_got_deregister_frame_info : Z := 0x1e6f0.
Definition src0_D_got_stderr : Z := 0x1e6f8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e700.
Definition src0_D_got_stdout : Z := 0x1e708.
Definition src0_D_got_environ : Z := 0x1e710.
Definition src0_D_got_progname_full : Z := 0x1e718.
Definition src0_D_got_progname : Z := 0x1e720.
Definition src0_D_got_init_array_end : Z := 0x1e728.
Definition src0_D_got_init_array_start : Z := 0x1e730.
Definition src0_D_got_stack_chk_guard : Z := 0x1e738.
Definition src0_D_got_fini_array_end : Z := 0x1e740.
Definition src0_D_got_fini_array_start : Z := 0x1e748.
Definition src0_D_dso_handle : Z := 0x1f750.
Definition src0_D_aef_arg0 : Z := 0x1fe30.
Definition src0_D_aef_argc : Z := 0x1f760.
Definition src0_D_aef_argv : Z := 0x1fe40.
Definition src0_D_stderr_FILE : Z := 0x1f778.
Definition src0_D_stderr_used : Z := 0x1f860.
Definition src0_D_stdout_FILE : Z := 0x1f868.
Definition src0_D_stdout_used : Z := 0x1f950.
Definition src0_D_default_stacksize : Z := 0x1f958.
Definition src0_D_do_init_initialized : Z := 0x1f960.
Definition src0_D_do_init_object : Z := 0x1f968.
Definition src0_D_do_fini_finalized : Z := 0x1f9a8.
Definition src0_D_read_stage : Z := 0x1f9a9.
Definition src0_D_target_run_initialized : Z := 0x2f9b0.
Definition src0_D_aef_in_callback : Z := 0x2f9b4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f9c0.
Definition src0_D_environ : Z := 0x2f9e0.
Definition src0_D_thread_list_lock : Z := 0x4fab8.
Definition src0_D_main_tls : Z := 0x4fac0.
Definition src0_D_builtin_tls : Z := 0x2f9e8.
Definition src0_D_finished_atexit : Z := 0x4faf8.
Definition src0_D_atexit_lock : Z := 0x4fafc.
Definition src0_D_atexit_slot : Z := 0x4fb00.
Definition src0_D_atexit_head : Z := 0x4fb08.
Definition src0_D_atexit_builtin : Z := 0x4fb10.
Definition src0_D_exit_exit_lock : Z := 0x4fd18.
Definition src0_D_stack_chk_guard : Z := 0x4fd20.
Definition src0_D_sysinfo : Z := 0x4fd28.
Definition src0_D_progname : Z := 0x4fd30.
Definition src0_D_progname_full : Z := 0x4fd38.
Definition src0_D_libc : Z := 0x4fd40.
Definition src0_D_hwcap : Z := 0x4fda8.
Definition src0_D_malloc_lock : Z := 0x4fdb0.
Definition src0_D_malloc_context : Z := 0x4fdb8.
Definition src0_D_malloc_replaced : Z := 0x50158.
Definition src0_D_stdin_used : Z := 0x50160.
Definition src0_D_ofl_lock : Z := 0x50168.
Definition src0_D_ofl_head : Z := 0x50170.
Definition src0_D_stderr_buf : Z := 0x50178.
Definition src0_D_stdout_buf : Z := 0x50180.
