(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x129d4.  Definition src0_text_hi : Z := 0x1d8d0.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11368.
Definition src0_eh_frame_lo : Z := 0x114b0.  Definition src0_eh_frame_hi : Z := 0x119d4.
Definition src0_init_array_lo : Z := 0x1e8d0.  Definition src0_init_array_hi : Z := 0x1e8d8.
Definition src0_fini_array_lo : Z := 0x1e8d8.  Definition src0_fini_array_hi : Z := 0x1e8e0.
Definition src0_data_rel_ro_lo : Z := 0x1e8e0.  Definition src0_data_rel_ro_hi : Z := 0x1e9a8.
Definition src0_got_lo : Z := 0x1e9a8.  Definition src0_got_hi : Z := 0x1ea40.
Definition src0_data_lo : Z := 0x1fa40.  Definition src0_data_hi : Z := 0x1fc4c.
Definition src0_bss_lo : Z := 0x1fc50.  Definition src0_bss_hi : Z := 0x50878.
Definition src0_A_start : Z := 0x129d4.  Definition src0_E_start : Z := 0x12a1c.
Definition src0_A_do_init : Z := 0x12a1c.  Definition src0_E_do_init : Z := 0x12a90.
Definition src0_A_do_fini : Z := 0x12a90.  Definition src0_E_do_fini : Z := 0x12b20.
Definition src0_A_main : Z := 0x12b20.  Definition src0_E_main : Z := 0x12de4.
Definition src0_A_target_alloc_init : Z := 0x12de4.  Definition src0_E_target_alloc_init : Z := 0x12de8.
Definition src0_A_target_alloc_count : Z := 0x12de8.  Definition src0_E_target_alloc_count : Z := 0x12df0.
Definition src0_A_target_run : Z := 0x12df0.  Definition src0_E_target_run : Z := 0x12f48.
Definition src0_A_aef_exit_guard : Z := 0x12f48.  Definition src0_E_aef_exit_guard : Z := 0x12f78.
Definition src0_A_emit_printf : Z := 0x12f78.  Definition src0_E_emit_printf : Z := 0x12fc0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12fc0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x15d80.
Definition src0_A_read_frameconfig : Z := 0x15d80.  Definition src0_E_read_frameconfig : Z := 0x15fe8.
Definition src0_A_cgif_newgif : Z := 0x15fe8.  Definition src0_E_cgif_newgif : Z := 0x161a0.
Definition src0_A_cgif_writecb : Z := 0x161a0.  Definition src0_E_cgif_writecb : Z := 0x16214.
Definition src0_A_freeCGIF : Z := 0x16214.  Definition src0_E_freeCGIF : Z := 0x1624c.
Definition src0_A_cgif_addframe : Z := 0x1624c.  Definition src0_E_cgif_addframe : Z := 0x165b8.
Definition src0_A_cmpPixel : Z := 0x165b8.  Definition src0_E_cmpPixel : Z := 0x1666c.
Definition src0_A_flushFrame : Z := 0x1666c.  Definition src0_E_flushFrame : Z := 0x16f68.
Definition src0_A_freeFrame : Z := 0x16f68.  Definition src0_E_freeFrame : Z := 0x16fb0.
Definition src0_A_cgif_close : Z := 0x16fb0.  Definition src0_E_cgif_close : Z := 0x17078.
Definition src0_A_cgif_raw_newgif : Z := 0x17078.  Definition src0_E_cgif_raw_newgif : Z := 0x1732c.
Definition src0_A_cgif_raw_addframe : Z := 0x1732c.  Definition src0_E_cgif_raw_addframe : Z := 0x177a8.
Definition src0_A_LZW_GenerateStream : Z := 0x177a8.  Definition src0_E_LZW_GenerateStream : Z := 0x17d48.
Definition src0_A_cgif_raw_close : Z := 0x17d48.  Definition src0_E_cgif_raw_close : Z := 0x17da8.
Definition src0_A_create_byte_list : Z := 0x17da8.  Definition src0_E_create_byte_list : Z := 0x17f24.
Definition src0_A_create_byte_list_block : Z := 0x17f24.  Definition src0_E_create_byte_list_block : Z := 0x15ae8.
Definition src0_A_init : Z := 0x15ae8.  Definition src0_E_init : Z := 0x15aec.
Definition src0_A_init_libc : Z := 0x15aec.  Definition src0_E_init_libc : Z := 0x15d18.
Definition src0_A_libc_start_init : Z := 0x15d18.  Definition src0_E_libc_start_init : Z := 0x15d64.
Definition src0_A_libc_start_main : Z := 0x15d64.  Definition src0_E_libc_start_main : Z := 0x15dc4.
Definition src0_A_libc_start_main_stage2 : Z := 0x15dc4.  Definition src0_E_libc_start_main_stage2 : Z := 0x15e0c.
Definition src0_A_init_tls : Z := 0x15e0c.  Definition src0_E_init_tls : Z := 0x1616c.
Definition src0_A_funcs_on_exit : Z := 0x1616c.  Definition src0_E_funcs_on_exit : Z := 0x16234.
Definition src0_A_cxa_finalize : Z := 0x16234.  Definition src0_E_cxa_finalize : Z := 0x16238.
Definition src0_A_atexit : Z := 0x16238.  Definition src0_E_atexit : Z := 0x162fc.
Definition src0_A_atexit_call : Z := 0x162fc.  Definition src0_E_atexit_call : Z := 0x16300.
Definition src0_A_fini : Z := 0x16300.  Definition src0_E_fini : Z := 0x16304.
Definition src0_A_libc_exit_fini : Z := 0x16304.  Definition src0_E_libc_exit_fini : Z := 0x16350.
Definition src0_A_exit : Z := 0x16350.  Definition src0_E_exit : Z := 0x16150.
Definition src0_A_Exit : Z := 0x16150.  Definition src0_E_Exit : Z := 0x163c4.
Definition src0_A_open : Z := 0x163c4.  Definition src0_E_open : Z := 0x164a8.
Definition src0_A_init_ssp : Z := 0x164a8.  Definition src0_E_init_ssp : Z := 0x16508.
Definition src0_A_stack_chk_fail : Z := 0x16508.  Definition src0_E_stack_chk_fail : Z := 0x16510.
Definition src0_A_syscall_ret : Z := 0x16510.  Definition src0_E_syscall_ret : Z := 0x16548.
Definition src0_A_errno_location : Z := 0x16548.  Definition src0_E_errno_location : Z := 0x16554.
Definition src0_A_free : Z := 0x16554.  Definition src0_E_free : Z := 0x16558.
Definition src0_A_libc_calloc : Z := 0x16558.  Definition src0_E_libc_calloc : Z := 0x16690.
Definition src0_A_libc_malloc : Z := 0x16690.  Definition src0_E_libc_malloc : Z := 0x16694.
Definition src0_A_malloc : Z := 0x16694.  Definition src0_E_malloc : Z := 0x16698.
Definition src0_A_libc_free : Z := 0x16698.  Definition src0_E_libc_free : Z := 0x16864.
Definition src0_A_get_meta : Z := 0x16864.  Definition src0_E_get_meta : Z := 0x16974.
Definition src0_A_nontrivial_free : Z := 0x16974.  Definition src0_E_nontrivial_free : Z := 0x16d4c.
Definition src0_A_alloc_meta : Z := 0x16d4c.  Definition src0_E_alloc_meta : Z := 0x17024.
Definition src0_A_libc_malloc_impl : Z := 0x17024.  Definition src0_E_libc_malloc_impl : Z := 0x17394.
Definition src0_A_alloc_slot : Z := 0x17394.  Definition src0_E_alloc_slot : Z := 0x17c38.
Definition src0_A_enframe : Z := 0x17c38.  Definition src0_E_enframe : Z := 0x17d88.
Definition src0_A_malloc_allzerop : Z := 0x17d88.  Definition src0_E_malloc_allzerop : Z := 0x17f00.
Definition src0_A_vm_wait : Z := 0x17f00.  Definition src0_E_vm_wait : Z := 0x17f04.
Definition src0_A_mmap : Z := 0x17f04.  Definition src0_E_mmap : Z := 0x17ff0.
Definition src0_A_mprotect : Z := 0x17ff0.  Definition src0_E_mprotect : Z := 0x18038.
Definition src0_A_munmap : Z := 0x18038.  Definition src0_E_munmap : Z := 0x18090.
Definition src0_A_unlist_locked_file : Z := 0x18090.  Definition src0_E_unlist_locked_file : Z := 0x18094.
Definition src0_A_fclose : Z := 0x18094.  Definition src0_E_fclose : Z := 0x18154.
Definition src0_A_fflush : Z := 0x18154.  Definition src0_E_fflush : Z := 0x182c4.
Definition src0_A_lockfile : Z := 0x182c4.  Definition src0_E_lockfile : Z := 0x183c0.
Definition src0_A_unlockfile : Z := 0x183c0.  Definition src0_E_unlockfile : Z := 0x1842c.
Definition src0_A_fopen : Z := 0x1842c.  Definition src0_E_fopen : Z := 0x18508.
Definition src0_A_fmodeflags : Z := 0x18508.  Definition src0_E_fmodeflags : Z := 0x185bc.
Definition src0_A_fdopen : Z := 0x185bc.  Definition src0_E_fdopen : Z := 0x18794.
Definition src0_A_stdio_read : Z := 0x18794.  Definition src0_E_stdio_read : Z := 0x18938.
Definition src0_A_stdio_write : Z := 0x18938.  Definition src0_E_stdio_write : Z := 0x18a9c.
Definition src0_A_stdio_seek : Z := 0x18a9c.  Definition src0_E_stdio_seek : Z := 0x18908.
Definition src0_A_aio_close : Z := 0x18908.  Definition src0_E_aio_close : Z := 0x1890c.
Definition src0_A_stdio_close : Z := 0x1890c.  Definition src0_E_stdio_close : Z := 0x18420.
Definition src0_A_fprintf : Z := 0x18420.  Definition src0_E_fprintf : Z := 0x18484.
Definition src0_A_fwritex : Z := 0x18484.  Definition src0_E_fwritex : Z := 0x185bc.
Definition src0_A_fwrite : Z := 0x185bc.  Definition src0_E_fwrite : Z := 0x18674.
Definition src0_A_towrite : Z := 0x18674.  Definition src0_E_towrite : Z := 0x186c8.
Definition src0_A_stdio_exit : Z := 0x186c8.  Definition src0_E_stdio_exit : Z := 0x1886c.
Definition src0_A_ofl_lock : Z := 0x1886c.  Definition src0_E_ofl_lock : Z := 0x1889c.
Definition src0_A_ofl_unlock : Z := 0x1889c.  Definition src0_E_ofl_unlock : Z := 0x18f5c.
Definition src0_A_ofl_add : Z := 0x18f5c.  Definition src0_E_ofl_add : Z := 0x18ad0.
Definition src0_A_stdout_write : Z := 0x18ad0.  Definition src0_E_stdout_write : Z := 0x18b70.
Definition src0_A_vfprintf : Z := 0x18b70.  Definition src0_E_vfprintf : Z := 0x18d20.
Definition src0_A_printf_core : Z := 0x18d20.  Definition src0_E_printf_core : Z := 0x19b50.
Definition src0_A_pop_arg : Z := 0x19b50.  Definition src0_E_pop_arg : Z := 0x19c84.
Definition src0_A_pad : Z := 0x19c84.  Definition src0_E_pad : Z := 0x19d58.
Definition src0_A_fmt_fp : Z := 0x19d58.  Definition src0_E_fmt_fp : Z := 0x1b420.
Definition src0_A_strerror : Z := 0x1b420.  Definition src0_E_strerror : Z := 0x14f8c.
Definition src0_A_lctrans_impl : Z := 0x14f8c.  Definition src0_E_lctrans_impl : Z := 0x1b460.
Definition src0_A_lctrans : Z := 0x1b460.  Definition src0_E_lctrans : Z := 0x1b464.
Definition src0_A_wctomb : Z := 0x1b464.  Definition src0_E_wctomb : Z := 0x1b488.
Definition src0_A_wcrtomb : Z := 0x1b488.  Definition src0_E_wcrtomb : Z := 0x1b5b4.
Definition src0_A_extenddftf2 : Z := 0x1b5b4.  Definition src0_E_extenddftf2 : Z := 0x1bb48.
Definition src0_A_signbitl : Z := 0x1bb48.  Definition src0_E_signbitl : Z := 0x1b74c.
Definition src0_A_fpclassifyl : Z := 0x1b74c.  Definition src0_E_fpclassifyl : Z := 0x1bb94.
Definition src0_A_frexpl : Z := 0x1bb94.  Definition src0_E_frexpl : Z := 0x1b868.
Definition src0_A_letf2 : Z := 0x14ecc.  Definition src0_E_letf2 : Z := 0x14f94.
Definition src0_A_multf3 : Z := 0x1b868.  Definition src0_E_multf3 : Z := 0x1bf68.
Definition src0_A_floatsitf : Z := 0x1bf68.  Definition src0_E_floatsitf : Z := 0x15704.
Definition src0_A_scalbn : Z := 0x15704.  Definition src0_E_scalbn : Z := 0x1c108.
Definition src0_A_subtf3 : Z := 0x152d0.  Definition src0_E_subtf3 : Z := 0x152e0.
Definition src0_A_addtf3 : Z := 0x152e0.  Definition src0_E_addtf3 : Z := 0x15aac.
Definition src0_A_fe_getround : Z := 0x15aac.  Definition src0_E_fe_getround : Z := 0x15adc.
Definition src0_A_fe_raise_inexact : Z := 0x15adc.  Definition src0_E_fe_raise_inexact : Z := 0x15ae8.
Definition src0_A_fixunstfsi : Z := 0x1c108.  Definition src0_E_fixunstfsi : Z := 0x1c19c.
Definition src0_A_floatunsitf : Z := 0x1c19c.  Definition src0_E_floatunsitf : Z := 0x1c288.
Definition src0_A_fixtfsi : Z := 0x1c288.  Definition src0_E_fixtfsi : Z := 0x1c330.
Definition src0_A_divtf3 : Z := 0x1c330.  Definition src0_E_divtf3 : Z := 0x1cc34.
Definition src0_A_vprintf : Z := 0x1cc34.  Definition src0_E_vprintf : Z := 0x1d2f8.
Definition src0_A_bcmp : Z := 0x1d2f8.  Definition src0_E_bcmp : Z := 0x1d2fc.
Definition src0_A_memcmp : Z := 0x1d2fc.  Definition src0_E_memcmp : Z := 0x1ce2c.
Definition src0_A_memcpy : Z := 0x1ce2c.  Definition src0_E_memcpy : Z := 0x1d230.
Definition src0_A_memset : Z := 0x1d230.  Definition src0_E_memset : Z := 0x1fe54.
Definition src0_A_strchr : Z := 0x1fe54.  Definition src0_E_strchr : Z := 0x1fe90.
Definition src0_A_strchrnul : Z := 0x1fe90.  Definition src0_E_strchrnul : Z := 0x1ff70.
Definition src0_A_strlen : Z := 0x1ff70.  Definition src0_E_strlen : Z := 0x1d3f0.
Definition src0_A_strnlen : Z := 0x1d3f0.  Definition src0_E_strnlen : Z := 0x1d434.
Definition src0_A_memchr : Z := 0x1d434.  Definition src0_E_memchr : Z := 0x1d500.
Definition src0_A_lock : Z := 0x1d500.  Definition src0_E_lock : Z := 0x1d788.
Definition src0_A_unlock : Z := 0x1d788.  Definition src0_E_unlock : Z := 0x1d7fc.
Definition src0_A_syscall_cp_c : Z := 0x1d7fc.  Definition src0_E_syscall_cp_c : Z := 0x1d820.
Definition src0_A_syscall_cp : Z := 0x1d820.  Definition src0_E_syscall_cp : Z := 0x1d824.
Definition src0_A_set_thread_area : Z := 0x1d824.  Definition src0_E_set_thread_area : Z := 0x1d830.
Definition src0_A_unistd_exit : Z := 0x1d830.  Definition src0_E_unistd_exit : Z := 0x1d83c.
Definition src0_A_close : Z := 0x1d83c.  Definition src0_E_close : Z := 0x1d890.
Definition src0_A_lseek : Z := 0x1d890.  Definition src0_E_lseek : Z := 0x1d89c.
Definition src0_A_read : Z := 0x1d89c.  Definition src0_E_read : Z := 0x204e0.
Definition src0_A_unlink : Z := 0x204e0.  Definition src0_E_unlink : Z := 0x20510.
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
Definition src0_D_const_double_0x1p28 : Z := 0x106a9.
Definition src0_D_const_double_1_0 : Z := 0x106b1.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x104f8.
Definition src0_D_const_double_0_5 : Z := 0x106c1.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10508.
Definition src0_D_const_double_0x1p1023 : Z := 0x106d1.
Definition src0_D_const_double_1_5 : Z := 0x106d9.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x106e1.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x106e9.
Definition src0_D_const_u64_0x0101010101010102 : Z := 0x106f1.
Definition src0_D_const_double_0x1p120 : Z := 0x106f9.
Definition src0_D_debruijn32 : Z := 0x106ec.
Definition src0_D_size_classes : Z := 0x1070c.
Definition src0_D_small_cnt_tab : Z := 0x1076c.
Definition src0_D_med_cnt_tab : Z := 0x10787.
Definition src0_D_jt_printf_core_1 : Z := 0x11b40.
Definition src0_D_jt_printf_core_2 : Z := 0x11c20.
Definition src0_D_jt_pop_arg : Z := 0x11c40.
Definition src0_D_states : Z := 0x108e8.
Definition src0_D_xdigits : Z := 0x105f8.
Definition src0_D_errmsgstr : Z := 0x10ab8.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11260.
Definition src0_D_fe_getround : Z := 0x10684.
Definition src0_D_EH_FRAME_LIST : Z := 0x114b0.
Definition src0_D_init_array_start : Z := 0x1e8d0.
Definition src0_D_fini_array_start : Z := 0x1e8d8.
Definition src0_D_stderr : Z := 0x1e998.
Definition src0_D_stdout : Z := 0x1e9a0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x21530.
Definition src0_D_got_DYNAMIC : Z := 0x1e9b0.
Definition src0_D_got_main : Z := 0x1e9b8.
Definition src0_D_got_init : Z := 0x1e9c0.
Definition src0_D_got_fini : Z := 0x1e9c8.
Definition src0_D_got_register_frame_info : Z := 0x1e9d0.
Definition src0_D_got_cxa_finalize : Z := 0x1e9d8.
Definition src0_D_got_deregister_frame_info : Z := 0x1e9e0.
Definition src0_D_got_stderr : Z := 0x1e9e8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e9f0.
Definition src0_D_got_stdout : Z := 0x1e9f8.
Definition src0_D_got_environ : Z := 0x1ea00.
Definition src0_D_got_progname_full : Z := 0x1ea08.
Definition src0_D_got_progname : Z := 0x1ea10.
Definition src0_D_got_init_array_end : Z := 0x1ea18.
Definition src0_D_got_init_array_start : Z := 0x1ea20.
Definition src0_D_got_stack_chk_guard : Z := 0x1ea28.
Definition src0_D_got_fini_array_end : Z := 0x1ea30.
Definition src0_D_got_fini_array_start : Z := 0x1ea38.
Definition src0_D_dso_handle : Z := 0x1fa40.
Definition src0_D_aef_arg0 : Z := 0x20120.
Definition src0_D_aef_argc : Z := 0x1fa50.
Definition src0_D_aef_argv : Z := 0x20130.
Definition src0_D_stderr_FILE : Z := 0x1fa68.
Definition src0_D_stderr_used : Z := 0x1fb50.
Definition src0_D_stdout_FILE : Z := 0x1fb58.
Definition src0_D_stdout_used : Z := 0x1fc40.
Definition src0_D_default_stacksize : Z := 0x1fc48.
Definition src0_D_do_init_initialized : Z := 0x1fc50.
Definition src0_D_do_init_object : Z := 0x1fc58.
Definition src0_D_do_fini_finalized : Z := 0x1fc98.
Definition src0_D_read_stage : Z := 0x1fc99.
Definition src0_D_target_run_initialized : Z := 0x2fca0.
Definition src0_D_aef_in_callback : Z := 0x2fca4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2fcb0.
Definition src0_D_environ : Z := 0x2fcd0.
Definition src0_D_thread_list_lock : Z := 0x4fda8.
Definition src0_D_main_tls : Z := 0x4fdb0.
Definition src0_D_builtin_tls : Z := 0x2fcd8.
Definition src0_D_finished_atexit : Z := 0x4fde8.
Definition src0_D_atexit_lock : Z := 0x4fdec.
Definition src0_D_atexit_slot : Z := 0x4fdf0.
Definition src0_D_atexit_head : Z := 0x4fdf8.
Definition src0_D_atexit_builtin : Z := 0x4fe00.
Definition src0_D_exit_exit_lock : Z := 0x50008.
Definition src0_D_stack_chk_guard : Z := 0x50010.
Definition src0_D_sysinfo : Z := 0x50018.
Definition src0_D_progname : Z := 0x50020.
Definition src0_D_progname_full : Z := 0x50028.
Definition src0_D_libc : Z := 0x50030.
Definition src0_D_hwcap : Z := 0x50098.
Definition src0_D_malloc_lock : Z := 0x500a0.
Definition src0_D_malloc_context : Z := 0x500a8.
Definition src0_D_malloc_replaced : Z := 0x50448.
Definition src0_D_stdin_used : Z := 0x50450.
Definition src0_D_ofl_lock : Z := 0x50458.
Definition src0_D_ofl_head : Z := 0x50460.
Definition src0_D_stderr_buf : Z := 0x50468.
Definition src0_D_stdout_buf : Z := 0x50470.
Definition src0_vmlock : option Z := None.
(** The de Bruijn table's length is the image's: the table runs up to __malloc_size_classes (32 bytes in both builds of rate,
    no pad byte; a donor with a pad byte gets 33 the same way). *)
Definition src0_debruijn_len : Z := src0_D_size_classes - src0_D_debruijn32.
