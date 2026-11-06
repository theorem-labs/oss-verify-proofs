(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src2_text_lo : Z := 0x12988.  Definition src2_text_hi : Z := 0x1f904.
Definition src2_rodata_lo : Z := 0x10298.  Definition src2_rodata_hi : Z := 0x110d8.
Definition src2_eh_frame_lo : Z := 0x11250.  Definition src2_eh_frame_hi : Z := 0x11988.
Definition src2_init_array_lo : Z := 0x20908.  Definition src2_init_array_hi : Z := 0x20910.
Definition src2_fini_array_lo : Z := 0x20910.  Definition src2_fini_array_hi : Z := 0x20918.
Definition src2_data_rel_ro_lo : Z := 0x20918.  Definition src2_data_rel_ro_hi : Z := 0x20928.
Definition src2_got_lo : Z := 0x20928.  Definition src2_got_hi : Z := 0x209c0.
Definition src2_data_lo : Z := 0x219c0.  Definition src2_data_hi : Z := 0x21bcc.
Definition src2_bss_lo : Z := 0x21bd0.  Definition src2_bss_hi : Z := 0x527f0.
Definition src2_A_start : Z := 0x12988.  Definition src2_E_start : Z := 0x129d0.
Definition src2_A_do_init : Z := 0x129d0.  Definition src2_E_do_init : Z := 0x12a44.
Definition src2_A_do_fini : Z := 0x12a44.  Definition src2_E_do_fini : Z := 0x12ad4.
Definition src2_A_main : Z := 0x12ad4.  Definition src2_E_main : Z := 0x12d98.
Definition src2_A_target_alloc_init : Z := 0x12d98.  Definition src2_E_target_alloc_init : Z := 0x12d9c.
Definition src2_A_target_alloc_count : Z := 0x12d9c.  Definition src2_E_target_alloc_count : Z := 0x12da4.
Definition src2_A_target_run : Z := 0x12da4.  Definition src2_E_target_run : Z := 0x12efc.
Definition src2_A_aef_exit_guard : Z := 0x12efc.  Definition src2_E_aef_exit_guard : Z := 0x12f2c.
Definition src2_A_emit_printf : Z := 0x12f2c.  Definition src2_E_emit_printf : Z := 0x12f74.
Definition src2_A_LLVMFuzzerTestOneInput : Z := 0x12f74.  Definition src2_E_LLVMFuzzerTestOneInput : Z := 0x13180.
Definition src2_A_writecb : Z := 0x13180.  Definition src2_E_writecb : Z := 0x13188.
Definition src2_A_read_frameconfig : Z := 0x13188.  Definition src2_E_read_frameconfig : Z := 0x13348.
Definition src2_A_cgif_rgb_newgif : Z := 0x13348.  Definition src2_E_cgif_rgb_newgif : Z := 0x13414.
Definition src2_A_cgif_rgb_addframe : Z := 0x13414.  Definition src2_E_cgif_rgb_addframe : Z := 0x14504.
Definition src2_A_free_col_hash_table : Z := 0x14504.  Definition src2_E_free_col_hash_table : Z := 0x14550.
Definition src2_A_cgif_rgb_close : Z := 0x14550.  Definition src2_E_cgif_rgb_close : Z := 0x1459c.
Definition src2_A_col_hash : Z := 0x1459c.  Definition src2_E_col_hash : Z := 0x1467c.
Definition src2_A_free_decision_tree : Z := 0x1467c.  Definition src2_E_free_decision_tree : Z := 0x146c0.
Definition src2_A_new_tree_node : Z := 0x146c0.  Definition src2_E_new_tree_node : Z := 0x14924.
Definition src2_A_get_palette_from_decision_tree : Z := 0x14924.  Definition src2_E_get_palette_from_decision_tree : Z := 0x149c4.
Definition src2_A_cgif_newgif : Z := 0x149c4.  Definition src2_E_cgif_newgif : Z := 0x14b7c.
Definition src2_A_cgif_writecb : Z := 0x14b7c.  Definition src2_E_cgif_writecb : Z := 0x14bf0.
Definition src2_A_freeCGIF : Z := 0x14bf0.  Definition src2_E_freeCGIF : Z := 0x14c28.
Definition src2_A_cgif_addframe : Z := 0x14c28.  Definition src2_E_cgif_addframe : Z := 0x14f94.
Definition src2_A_cmpPixel : Z := 0x14f94.  Definition src2_E_cmpPixel : Z := 0x15048.
Definition src2_A_flushFrame : Z := 0x15048.  Definition src2_E_flushFrame : Z := 0x15944.
Definition src2_A_freeFrame : Z := 0x15944.  Definition src2_E_freeFrame : Z := 0x1598c.
Definition src2_A_cgif_close : Z := 0x1598c.  Definition src2_E_cgif_close : Z := 0x15a54.
Definition src2_A_cgif_raw_newgif : Z := 0x15a54.  Definition src2_E_cgif_raw_newgif : Z := 0x15d08.
Definition src2_A_cgif_raw_addframe : Z := 0x15d08.  Definition src2_E_cgif_raw_addframe : Z := 0x16184.
Definition src2_A_LZW_GenerateStream : Z := 0x16184.  Definition src2_E_LZW_GenerateStream : Z := 0x16724.
Definition src2_A_cgif_raw_close : Z := 0x16724.  Definition src2_E_cgif_raw_close : Z := 0x16784.
Definition src2_A_create_byte_list : Z := 0x16784.  Definition src2_E_create_byte_list : Z := 0x16900.
Definition src2_A_create_byte_list_block : Z := 0x16900.  Definition src2_E_create_byte_list_block : Z := 0x16a20.
Definition src2_A_init : Z := 0x16a20.  Definition src2_E_init : Z := 0x16a24.
Definition src2_A_init_libc : Z := 0x16a24.  Definition src2_E_init_libc : Z := 0x16c50.
Definition src2_A_libc_start_init : Z := 0x16c50.  Definition src2_E_libc_start_init : Z := 0x16c9c.
Definition src2_A_libc_start_main : Z := 0x16c9c.  Definition src2_E_libc_start_main : Z := 0x16cfc.
Definition src2_A_libc_start_main_stage2 : Z := 0x16cfc.  Definition src2_E_libc_start_main_stage2 : Z := 0x16d44.
Definition src2_A_init_tls : Z := 0x16d44.  Definition src2_E_init_tls : Z := 0x16ff4.
Definition src2_A_funcs_on_exit : Z := 0x16ff4.  Definition src2_E_funcs_on_exit : Z := 0x170bc.
Definition src2_A_cxa_finalize : Z := 0x170bc.  Definition src2_E_cxa_finalize : Z := 0x170c0.
Definition src2_A_atexit : Z := 0x170c0.  Definition src2_E_atexit : Z := 0x17184.
Definition src2_A_atexit_call : Z := 0x17184.  Definition src2_E_atexit_call : Z := 0x17188.
Definition src2_A_fini : Z := 0x17188.  Definition src2_E_fini : Z := 0x1718c.
Definition src2_A_libc_exit_fini : Z := 0x1718c.  Definition src2_E_libc_exit_fini : Z := 0x171d8.
Definition src2_A_exit : Z := 0x171d8.  Definition src2_E_exit : Z := 0x1724c.
Definition src2_A_Exit : Z := 0x1724c.  Definition src2_E_Exit : Z := 0x17268.
Definition src2_A_open : Z := 0x17268.  Definition src2_E_open : Z := 0x1734c.
Definition src2_A_init_ssp : Z := 0x1734c.  Definition src2_E_init_ssp : Z := 0x173ac.
Definition src2_A_stack_chk_fail : Z := 0x173ac.  Definition src2_E_stack_chk_fail : Z := 0x173b4.
Definition src2_A_syscall_ret : Z := 0x173b4.  Definition src2_E_syscall_ret : Z := 0x173ec.
Definition src2_A_errno_location : Z := 0x173ec.  Definition src2_E_errno_location : Z := 0x173f8.
Definition src2_A_free : Z := 0x173f8.  Definition src2_E_free : Z := 0x173fc.
Definition src2_A_libc_calloc : Z := 0x173fc.  Definition src2_E_libc_calloc : Z := 0x17534.
Definition src2_A_libc_malloc : Z := 0x17534.  Definition src2_E_libc_malloc : Z := 0x17538.
Definition src2_A_malloc : Z := 0x17538.  Definition src2_E_malloc : Z := 0x1753c.
Definition src2_A_libc_free : Z := 0x1753c.  Definition src2_E_libc_free : Z := 0x17708.
Definition src2_A_get_meta : Z := 0x17708.  Definition src2_E_get_meta : Z := 0x17818.
Definition src2_A_nontrivial_free : Z := 0x17818.  Definition src2_E_nontrivial_free : Z := 0x17bf0.
Definition src2_A_alloc_meta : Z := 0x17bf0.  Definition src2_E_alloc_meta : Z := 0x17ec8.
Definition src2_A_libc_malloc_impl : Z := 0x17ec8.  Definition src2_E_libc_malloc_impl : Z := 0x18238.
Definition src2_A_alloc_slot : Z := 0x18238.  Definition src2_E_alloc_slot : Z := 0x18adc.
Definition src2_A_enframe : Z := 0x18adc.  Definition src2_E_enframe : Z := 0x18c2c.
Definition src2_A_malloc_allzerop : Z := 0x18c2c.  Definition src2_E_malloc_allzerop : Z := 0x18da4.
Definition src2_A_realloc : Z := 0x18da4.  Definition src2_E_realloc : Z := 0x191e8.
Definition src2_A_vm_wait : Z := 0x191e8.  Definition src2_E_vm_wait : Z := 0x191ec.
Definition src2_A_mmap : Z := 0x191ec.  Definition src2_E_mmap : Z := 0x192d8.
Definition src2_A_mprotect : Z := 0x192d8.  Definition src2_E_mprotect : Z := 0x19320.
Definition src2_A_mremap : Z := 0x19320.  Definition src2_E_mremap : Z := 0x193f4.
Definition src2_A_munmap : Z := 0x193f4.  Definition src2_E_munmap : Z := 0x1943c.
Definition src2_A_unlist_locked_file : Z := 0x1943c.  Definition src2_E_unlist_locked_file : Z := 0x19440.
Definition src2_A_fclose : Z := 0x19440.  Definition src2_E_fclose : Z := 0x1950c.
Definition src2_A_fflush : Z := 0x1950c.  Definition src2_E_fflush : Z := 0x1967c.
Definition src2_A_lockfile : Z := 0x1967c.  Definition src2_E_lockfile : Z := 0x19778.
Definition src2_A_unlockfile : Z := 0x19778.  Definition src2_E_unlockfile : Z := 0x197d8.
Definition src2_A_fopen : Z := 0x197d8.  Definition src2_E_fopen : Z := 0x198b4.
Definition src2_A_fmodeflags : Z := 0x198b4.  Definition src2_E_fmodeflags : Z := 0x19968.
Definition src2_A_fdopen : Z := 0x19968.  Definition src2_E_fdopen : Z := 0x19b40.
Definition src2_A_stdio_read : Z := 0x19b40.  Definition src2_E_stdio_read : Z := 0x19c58.
Definition src2_A_stdio_write : Z := 0x19c58.  Definition src2_E_stdio_write : Z := 0x19de8.
Definition src2_A_stdio_seek : Z := 0x19de8.  Definition src2_E_stdio_seek : Z := 0x19df0.
Definition src2_A_aio_close : Z := 0x19df0.  Definition src2_E_aio_close : Z := 0x19df4.
Definition src2_A_stdio_close : Z := 0x19df4.  Definition src2_E_stdio_close : Z := 0x19e20.
Definition src2_A_fprintf : Z := 0x19e20.  Definition src2_E_fprintf : Z := 0x19e84.
Definition src2_A_fwritex : Z := 0x19e84.  Definition src2_E_fwritex : Z := 0x19fbc.
Definition src2_A_fwrite : Z := 0x19fbc.  Definition src2_E_fwrite : Z := 0x1a074.
Definition src2_A_towrite : Z := 0x1a074.  Definition src2_E_towrite : Z := 0x1a0c8.
Definition src2_A_stdio_exit : Z := 0x1a0c8.  Definition src2_E_stdio_exit : Z := 0x1a26c.
Definition src2_A_ofl_lock : Z := 0x1a26c.  Definition src2_E_ofl_lock : Z := 0x1a29c.
Definition src2_A_ofl_unlock : Z := 0x1a29c.  Definition src2_E_ofl_unlock : Z := 0x1a2a8.
Definition src2_A_ofl_add : Z := 0x1a2a8.  Definition src2_E_ofl_add : Z := 0x1a2e8.
Definition src2_A_stdout_write : Z := 0x1a2e8.  Definition src2_E_stdout_write : Z := 0x1a388.
Definition src2_A_vfprintf : Z := 0x1a388.  Definition src2_E_vfprintf : Z := 0x1a538.
Definition src2_A_printf_core : Z := 0x1a538.  Definition src2_E_printf_core : Z := 0x1b368.
Definition src2_A_pop_arg : Z := 0x1b368.  Definition src2_E_pop_arg : Z := 0x1b49c.
Definition src2_A_pad : Z := 0x1b49c.  Definition src2_E_pad : Z := 0x1b570.
Definition src2_A_fmt_fp : Z := 0x1b570.  Definition src2_E_fmt_fp : Z := 0x1cc38.
Definition src2_A_strerror : Z := 0x1cc38.  Definition src2_E_strerror : Z := 0x1cc74.
Definition src2_A_lctrans_impl : Z := 0x1cc74.  Definition src2_E_lctrans_impl : Z := 0x1cc78.
Definition src2_A_lctrans : Z := 0x1cc78.  Definition src2_E_lctrans : Z := 0x1cc7c.
Definition src2_A_wctomb : Z := 0x1cc7c.  Definition src2_E_wctomb : Z := 0x1cca0.
Definition src2_A_wcrtomb : Z := 0x1cca0.  Definition src2_E_wcrtomb : Z := 0x1cdcc.
Definition src2_A_extenddftf2 : Z := 0x1cdcc.  Definition src2_E_extenddftf2 : Z := 0x1cf5c.
Definition src2_A_signbitl : Z := 0x1cf5c.  Definition src2_E_signbitl : Z := 0x1cf64.
Definition src2_A_fpclassifyl : Z := 0x1cf64.  Definition src2_E_fpclassifyl : Z := 0x1cfa8.
Definition src2_A_frexpl : Z := 0x1cfa8.  Definition src2_E_frexpl : Z := 0x1d080.
Definition src2_A_letf2 : Z := 0x1d080.  Definition src2_E_letf2 : Z := 0x1d148.
Definition src2_A_multf3 : Z := 0x1d148.  Definition src2_E_multf3 : Z := 0x1d848.
Definition src2_A_floatsitf : Z := 0x1d848.  Definition src2_E_floatsitf : Z := 0x1d950.
Definition src2_A_scalbn : Z := 0x1d950.  Definition src2_E_scalbn : Z := 0x1d9e8.
Definition src2_A_subtf3 : Z := 0x1d9e8.  Definition src2_E_subtf3 : Z := 0x1d9f8.
Definition src2_A_addtf3 : Z := 0x1d9f8.  Definition src2_E_addtf3 : Z := 0x1e1c4.
Definition src2_A_fe_getround : Z := 0x1e1c4.  Definition src2_E_fe_getround : Z := 0x1e1f4.
Definition src2_A_fe_raise_inexact : Z := 0x1e1f4.  Definition src2_E_fe_raise_inexact : Z := 0x1e200.
Definition src2_A_fixunstfsi : Z := 0x1e200.  Definition src2_E_fixunstfsi : Z := 0x1e294.
Definition src2_A_floatunsitf : Z := 0x1e294.  Definition src2_E_floatunsitf : Z := 0x1e380.
Definition src2_A_fixtfsi : Z := 0x1e380.  Definition src2_E_fixtfsi : Z := 0x1e428.
Definition src2_A_divtf3 : Z := 0x1e428.  Definition src2_E_divtf3 : Z := 0x1ed2c.
Definition src2_A_vprintf : Z := 0x1ed2c.  Definition src2_E_vprintf : Z := 0x1ed48.
Definition src2_A_bcmp : Z := 0x1ed48.  Definition src2_E_bcmp : Z := 0x1ed4c.
Definition src2_A_memcmp : Z := 0x1ed4c.  Definition src2_E_memcmp : Z := 0x1ed7c.
Definition src2_A_memcpy : Z := 0x1ed7c.  Definition src2_E_memcpy : Z := 0x1f180.
Definition src2_A_memset : Z := 0x1f180.  Definition src2_E_memset : Z := 0x1f278.
Definition src2_A_strchr : Z := 0x1f278.  Definition src2_E_strchr : Z := 0x1f2b4.
Definition src2_A_strchrnul : Z := 0x1f2b4.  Definition src2_E_strchrnul : Z := 0x1f394.
Definition src2_A_strlen : Z := 0x1f394.  Definition src2_E_strlen : Z := 0x1f424.
Definition src2_A_strnlen : Z := 0x1f424.  Definition src2_E_strnlen : Z := 0x1f468.
Definition src2_A_memchr : Z := 0x1f468.  Definition src2_E_memchr : Z := 0x1f534.
Definition src2_A_lock : Z := 0x1f534.  Definition src2_E_lock : Z := 0x1f7bc.
Definition src2_A_unlock : Z := 0x1f7bc.  Definition src2_E_unlock : Z := 0x1f830.
Definition src2_A_syscall_cp_c : Z := 0x1f830.  Definition src2_E_syscall_cp_c : Z := 0x1f854.
Definition src2_A_syscall_cp : Z := 0x1f854.  Definition src2_E_syscall_cp : Z := 0x1f858.
Definition src2_A_set_thread_area : Z := 0x1f858.  Definition src2_E_set_thread_area : Z := 0x1f864.
Definition src2_A_unistd_exit : Z := 0x1f864.  Definition src2_E_unistd_exit : Z := 0x1f870.
Definition src2_A_close : Z := 0x1f870.  Definition src2_E_close : Z := 0x1f8c4.
Definition src2_A_lseek : Z := 0x1f8c4.  Definition src2_E_lseek : Z := 0x1f8d0.
Definition src2_A_read : Z := 0x1f8d0.  Definition src2_E_read : Z := 0x1f904.
Definition src2_D_str_n0X0x : Z := 0x10298.
Definition src2_D_str_wb : Z := 0x102a2.
Definition src2_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition src2_D_str_cli_out_of_memory_n : Z := 0x102b8.
Definition src2_D_str_d_n : Z := 0x102cc.
Definition src2_D_str : Z := 0x102d0.
Definition src2_D_str_2 : Z := 0x102d1.
Definition src2_D_str_usage_s_INPUT_n : Z := 0x102d3.
Definition src2_D_str_cli_config_len_overruns : Z := 0x102e4.
Definition src2_D_str_3 : Z := 0x10304.
Definition src2_D_str_inf : Z := 0x10306.
Definition src2_D_str_INF : Z := 0x1030a.
Definition src2_D_str_cli_input_u_bytes_refuse : Z := 0x1030e.
Definition src2_D_str_cli_cannot_open_s_n : Z := 0x1032f.
Definition src2_D_str_cli_read_error_on_s_n : Z := 0x10344.
Definition src2_D_str_NAN : Z := 0x1035b.
Definition src2_D_str_nan : Z := 0x1035f.
Definition src2_D_str_cli_input_shorter_than_h : Z := 0x10363.
Definition src2_D_str_rwa : Z := 0x10383.
Definition src2_D_str_dev_null : Z := 0x10387.
Definition src2_D_str_null : Z := 0x10391.
Definition src2_D_const_double_0x1p28 : Z := 0x10398.
Definition src2_D_const_double_1_0 : Z := 0x103a0.
Definition src2_D_const_HIGHS_0x8080808080808080 : Z := 0x103a8.
Definition src2_D_const_double_0_5 : Z := 0x103b0.
Definition src2_D_const_ONES_0x0101010101010100 : Z := 0x103b8.
Definition src2_D_const_double_0x1p1023 : Z := 0x103c0.
Definition src2_D_const_double_1_5 : Z := 0x103c8.
Definition src2_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103d0.
Definition src2_D_d_103d8 : Z := 0x103d8.
Definition src2_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e0.
Definition src2_D_const_u64_0x0101010101010102 : Z := 0x103e8.
Definition src2_D_const_double_0x1p120 : Z := 0x103f0.
Definition src2_D_debruijn32 : Z := 0x10454.
Definition src2_D_size_classes : Z := 0x10474.
Definition src2_D_small_cnt_tab : Z := 0x104d4.
Definition src2_D_med_cnt_tab : Z := 0x104ef.
Definition src2_D_jt_printf_core_1 : Z := 0x104f4.
Definition src2_D_jt_printf_core_2 : Z := 0x105d4.
Definition src2_D_jt_pop_arg : Z := 0x105f4.
Definition src2_D_states : Z := 0x1063c.
Definition src2_D_xdigits : Z := 0x1080c.
Definition src2_D_errmsgstr : Z := 0x1081c.
Definition src2_D_global_pointer : Z := 0x10864.
Definition src2_D_errmsgidx : Z := 0x10fc4.
Definition src2_D_fe_getround : Z := 0x110cc.
Definition src2_D_EH_FRAME_LIST : Z := 0x11250.
Definition src2_D_init_array_start : Z := 0x20908.
Definition src2_D_fini_array_start : Z := 0x20910.
Definition src2_D_stderr : Z := 0x20918.
Definition src2_D_stdout : Z := 0x20920.
Definition src2_D_got_DYNAMIC : Z := 0x20930.
Definition src2_D_got_main : Z := 0x20938.
Definition src2_D_got_init : Z := 0x20940.
Definition src2_D_got_fini : Z := 0x20948.
Definition src2_D_got_register_frame_info : Z := 0x20950.
Definition src2_D_got_cxa_finalize : Z := 0x20958.
Definition src2_D_got_deregister_frame_info : Z := 0x20960.
Definition src2_D_got_stderr : Z := 0x20968.
Definition src2_D_got_LLVMFuzzerInitialize : Z := 0x20970.
Definition src2_D_got_stdout : Z := 0x20978.
Definition src2_D_got_environ : Z := 0x20980.
Definition src2_D_got_progname_full : Z := 0x20988.
Definition src2_D_got_progname : Z := 0x20990.
Definition src2_D_got_init_array_end : Z := 0x20998.
Definition src2_D_got_init_array_start : Z := 0x209a0.
Definition src2_D_got_stack_chk_guard : Z := 0x209a8.
Definition src2_D_got_fini_array_end : Z := 0x209b0.
Definition src2_D_got_fini_array_start : Z := 0x209b8.
Definition src2_D_dso_handle : Z := 0x219c0.
Definition src2_D_aef_arg0 : Z := 0x219c8.
Definition src2_D_aef_argc : Z := 0x219d0.
Definition src2_D_aef_argv : Z := 0x219d8.
Definition src2_D_stderr_FILE : Z := 0x219e8.
Definition src2_D_stderr_used : Z := 0x21ad0.
Definition src2_D_stdout_FILE : Z := 0x21ad8.
Definition src2_D_stdout_used : Z := 0x21bc0.
Definition src2_D_default_stacksize : Z := 0x21bc8.
Definition src2_D_do_init_initialized : Z := 0x21bd0.
Definition src2_D_do_init_object : Z := 0x21bd8.
Definition src2_D_do_fini_finalized : Z := 0x21c18.
Definition src2_D_read_stage : Z := 0x21c19.
Definition src2_D_target_run_initialized : Z := 0x31c20.
Definition src2_D_aef_in_callback : Z := 0x31c24.
Definition src2_D_aef_aligned_copy_empty : Z := 0x31c30.
Definition src2_D_environ : Z := 0x31c50.
Definition src2_D_thread_list_lock : Z := 0x51d28.
Definition src2_D_main_tls : Z := 0x51d30.
Definition src2_D_builtin_tls : Z := 0x31c58.
Definition src2_D_finished_atexit : Z := 0x51d60.
Definition src2_D_atexit_lock : Z := 0x51d64.
Definition src2_D_atexit_slot : Z := 0x51d68.
Definition src2_D_atexit_head : Z := 0x51d70.
Definition src2_D_atexit_builtin : Z := 0x51d78.
Definition src2_D_exit_exit_lock : Z := 0x51f80.
Definition src2_D_stack_chk_guard : Z := 0x51f88.
Definition src2_D_sysinfo : Z := 0x51f90.
Definition src2_D_progname : Z := 0x51f98.
Definition src2_D_progname_full : Z := 0x51fa0.
Definition src2_D_libc : Z := 0x51fa8.
Definition src2_D_hwcap : Z := 0x52010.
Definition src2_D_malloc_lock : Z := 0x52018.
Definition src2_D_malloc_context : Z := 0x52020.
Definition src2_D_malloc_replaced : Z := 0x523c0.
Definition src2_D_stdin_used : Z := 0x523c8.
Definition src2_D_ofl_lock : Z := 0x523d0.
Definition src2_D_ofl_head : Z := 0x523d8.
Definition src2_D_stderr_buf : Z := 0x523e0.
Definition src2_D_stdout_buf : Z := 0x523e8.
