(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ubs2_text_lo : Z := 0x12aa8.  Definition ubs2_text_hi : Z := 0x20c54.
Definition ubs2_rodata_lo : Z := 0x10298.  Definition ubs2_rodata_hi : Z := 0x110fc.
Definition ubs2_eh_frame_lo : Z := 0x11290.  Definition ubs2_eh_frame_hi : Z := 0x11aa8.
Definition ubs2_init_array_lo : Z := 0x21c58.  Definition ubs2_init_array_hi : Z := 0x21c60.
Definition ubs2_fini_array_lo : Z := 0x21c60.  Definition ubs2_fini_array_hi : Z := 0x21c68.
Definition ubs2_data_rel_ro_lo : Z := 0x21c68.  Definition ubs2_data_rel_ro_hi : Z := 0x21c78.
Definition ubs2_got_lo : Z := 0x21c78.  Definition ubs2_got_hi : Z := 0x21d10.
Definition ubs2_data_lo : Z := 0x22d10.  Definition ubs2_data_hi : Z := 0x22f1c.
Definition ubs2_bss_lo : Z := 0x22f20.  Definition ubs2_bss_hi : Z := 0x53b40.
Definition ubs2_A_start : Z := 0x12aa8.  Definition ubs2_E_start : Z := 0x12af0.
Definition ubs2_A_do_init : Z := 0x12af0.  Definition ubs2_E_do_init : Z := 0x12b64.
Definition ubs2_A_do_fini : Z := 0x12b64.  Definition ubs2_E_do_fini : Z := 0x12bf4.
Definition ubs2_A_main : Z := 0x12bf4.  Definition ubs2_E_main : Z := 0x12eb8.
Definition ubs2_A_target_alloc_init : Z := 0x12eb8.  Definition ubs2_E_target_alloc_init : Z := 0x12ebc.
Definition ubs2_A_target_alloc_count : Z := 0x12ebc.  Definition ubs2_E_target_alloc_count : Z := 0x12ec4.
Definition ubs2_A_target_run : Z := 0x12ec4.  Definition ubs2_E_target_run : Z := 0x1301c.
Definition ubs2_A_aef_exit_guard : Z := 0x1301c.  Definition ubs2_E_aef_exit_guard : Z := 0x1304c.
Definition ubs2_A_emit_printf : Z := 0x1304c.  Definition ubs2_E_emit_printf : Z := 0x13094.
Definition ubs2_A_LLVMFuzzerTestOneInput : Z := 0x13094.  Definition ubs2_E_LLVMFuzzerTestOneInput : Z := 0x131d4.
Definition ubs2_A_writecb : Z := 0x131d4.  Definition ubs2_E_writecb : Z := 0x131dc.
Definition ubs2_A_read_frameconfig : Z := 0x131dc.  Definition ubs2_E_read_frameconfig : Z := 0x13300.
Definition ubs2_A_cgif_rgb_newgif : Z := 0x1338c.  Definition ubs2_E_cgif_rgb_newgif : Z := 0x1346c.
Definition ubs2_A_cgif_rgb_addframe : Z := 0x1346c.  Definition ubs2_E_cgif_rgb_addframe : Z := 0x14ac8.
Definition ubs2_A_free_col_hash_table : Z := 0x14ac8.  Definition ubs2_E_free_col_hash_table : Z := 0x14b20.
Definition ubs2_A_cgif_rgb_close : Z := 0x14b20.  Definition ubs2_E_cgif_rgb_close : Z := 0x14b7c.
Definition ubs2_A_col_hash : Z := 0x14bdc.  Definition ubs2_E_col_hash : Z := 0x14d08.
Definition ubs2_A_free_decision_tree : Z := 0x14d08.  Definition ubs2_E_free_decision_tree : Z := 0x14d6c.
Definition ubs2_A_new_tree_node : Z := 0x14d6c.  Definition ubs2_E_new_tree_node : Z := 0x15044.
Definition ubs2_A_get_palette_from_decision_tree : Z := 0x15044.  Definition ubs2_E_get_palette_from_decision_tree : Z := 0x15194.
Definition ubs2_A_cgif_newgif : Z := 0x15220.  Definition ubs2_E_cgif_newgif : Z := 0x153f0.
Definition ubs2_A_cgif_writecb : Z := 0x153f0.  Definition ubs2_E_cgif_writecb : Z := 0x15474.
Definition ubs2_A_freeCGIF : Z := 0x15474.  Definition ubs2_E_freeCGIF : Z := 0x154b8.
Definition ubs2_A_cgif_addframe : Z := 0x154b8.  Definition ubs2_E_cgif_addframe : Z := 0x15980.
Definition ubs2_A_cmpPixel : Z := 0x15980.  Definition ubs2_E_cmpPixel : Z := 0x15a90.
Definition ubs2_A_flushFrame : Z := 0x15a90.  Definition ubs2_E_flushFrame : Z := 0x165a8.
Definition ubs2_A_freeFrame : Z := 0x165a8.  Definition ubs2_E_freeFrame : Z := 0x16608.
Definition ubs2_A_cgif_close : Z := 0x16608.  Definition ubs2_E_cgif_close : Z := 0x16704.
Definition ubs2_A_cgif_raw_newgif : Z := 0x16704.  Definition ubs2_E_cgif_raw_newgif : Z := 0x16ae0.
Definition ubs2_A_cgif_raw_addframe : Z := 0x16ae0.  Definition ubs2_E_cgif_raw_addframe : Z := 0x170ac.
Definition ubs2_A_LZW_GenerateStream : Z := 0x170ac.  Definition ubs2_E_LZW_GenerateStream : Z := 0x17810.
Definition ubs2_A_cgif_raw_close : Z := 0x17810.  Definition ubs2_E_cgif_raw_close : Z := 0x1787c.
Definition ubs2_A_create_byte_list : Z := 0x1787c.  Definition ubs2_E_create_byte_list : Z := 0x17aa8.
Definition ubs2_A_create_byte_list_block : Z := 0x17aa8.  Definition ubs2_E_create_byte_list_block : Z := 0x17c18.
Definition ubs2_A_readdata : Z := 0x13300.  Definition ubs2_E_readdata : Z := 0x1338c.
Definition ubs2_A_getPixelVal : Z := 0x14b7c.  Definition ubs2_E_getPixelVal : Z := 0x14bdc.
Definition ubs2_A_get_leave_node_index : Z := 0x15194.  Definition ubs2_E_get_leave_node_index : Z := 0x15220.
Definition ubs2_A_resetDict : Z := 0x17c18.  Definition ubs2_E_resetDict : Z := 0x17cd0.
Definition ubs2_A_round : Z := 0x1a498.  Definition ubs2_E_round : Z := 0x1a538.
Definition ubs2_A_init : Z := 0x17cd0.  Definition ubs2_E_init : Z := 0x17f4c.
Definition ubs2_A_init_libc : Z := 0x17cd4.  Definition ubs2_E_init_libc : Z := 0x17f00.
Definition ubs2_A_libc_start_init : Z := 0x17f00.  Definition ubs2_E_libc_start_init : Z := 0x17f4c.
Definition ubs2_A_libc_start_main : Z := 0x17f4c.  Definition ubs2_E_libc_start_main : Z := 0x1836c.
Definition ubs2_A_libc_start_main_stage2 : Z := 0x17fac.  Definition ubs2_E_libc_start_main_stage2 : Z := 0x17ff4.
Definition ubs2_A_init_tls : Z := 0x17ff4.  Definition ubs2_E_init_tls : Z := 0x182a4.
Definition ubs2_A_funcs_on_exit : Z := 0x182a4.  Definition ubs2_E_funcs_on_exit : Z := 0x1836c.
Definition ubs2_A_cxa_finalize : Z := 0x1836c.  Definition ubs2_E_cxa_finalize : Z := 0x18370.
Definition ubs2_A_atexit : Z := 0x18370.  Definition ubs2_E_atexit : Z := 0x18488.
Definition ubs2_A_atexit_call : Z := 0x18434.  Definition ubs2_E_atexit_call : Z := 0x18438.
Definition ubs2_A_fini : Z := 0x18438.  Definition ubs2_E_fini : Z := 0x1843c.
Definition ubs2_A_libc_exit_fini : Z := 0x1843c.  Definition ubs2_E_libc_exit_fini : Z := 0x18488.
Definition ubs2_A_exit : Z := 0x18488.  Definition ubs2_E_exit : Z := 0x184fc.
Definition ubs2_A_Exit : Z := 0x184fc.  Definition ubs2_E_Exit : Z := 0x18518.
Definition ubs2_A_open : Z := 0x18518.  Definition ubs2_E_open : Z := 0x18664.
Definition ubs2_A_init_ssp : Z := 0x185fc.  Definition ubs2_E_init_ssp : Z := 0x1865c.
Definition ubs2_A_stack_chk_fail : Z := 0x1865c.  Definition ubs2_E_stack_chk_fail : Z := 0x18664.
Definition ubs2_A_syscall_ret : Z := 0x18664.  Definition ubs2_E_syscall_ret : Z := 0x186a8.
Definition ubs2_A_errno_location : Z := 0x1869c.  Definition ubs2_E_errno_location : Z := 0x186a8.
Definition ubs2_A_free : Z := 0x186a8.  Definition ubs2_E_free : Z := 0x187e8.
Definition ubs2_A_libc_calloc : Z := 0x186ac.  Definition ubs2_E_libc_calloc : Z := 0x187e4.
Definition ubs2_A_libc_malloc : Z := 0x187e4.  Definition ubs2_E_libc_malloc : Z := 0x187e8.
Definition ubs2_A_malloc : Z := 0x187e8.  Definition ubs2_E_malloc : Z := 0x1a054.
Definition ubs2_A_libc_free : Z := 0x187ec.  Definition ubs2_E_libc_free : Z := 0x189b8.
Definition ubs2_A_get_meta : Z := 0x189b8.  Definition ubs2_E_get_meta : Z := 0x18ac8.
Definition ubs2_A_nontrivial_free : Z := 0x18ac8.  Definition ubs2_E_nontrivial_free : Z := 0x18ea0.
Definition ubs2_A_alloc_meta : Z := 0x18ea0.  Definition ubs2_E_alloc_meta : Z := 0x19178.
Definition ubs2_A_libc_malloc_impl : Z := 0x19178.  Definition ubs2_E_libc_malloc_impl : Z := 0x194e8.
Definition ubs2_A_alloc_slot : Z := 0x194e8.  Definition ubs2_E_alloc_slot : Z := 0x19d8c.
Definition ubs2_A_enframe : Z := 0x19d8c.  Definition ubs2_E_enframe : Z := 0x19edc.
Definition ubs2_A_malloc_allzerop : Z := 0x19edc.  Definition ubs2_E_malloc_allzerop : Z := 0x1a054.
Definition ubs2_A_realloc : Z := 0x1a054.  Definition ubs2_E_realloc : Z := 0x1a498.
Definition ubs2_A_vm_wait : Z := 0x1a538.  Definition ubs2_E_vm_wait : Z := 0x1a53c.
Definition ubs2_A_mmap : Z := 0x1a53c.  Definition ubs2_E_mmap : Z := 0x1a628.
Definition ubs2_A_mprotect : Z := 0x1a628.  Definition ubs2_E_mprotect : Z := 0x1a670.
Definition ubs2_A_mremap : Z := 0x1a670.  Definition ubs2_E_mremap : Z := 0x1a744.
Definition ubs2_A_munmap : Z := 0x1a744.  Definition ubs2_E_munmap : Z := 0x1a78c.
Definition ubs2_A_unlist_locked_file : Z := 0x1a78c.  Definition ubs2_E_unlist_locked_file : Z := 0x1a790.
Definition ubs2_A_fclose : Z := 0x1a790.  Definition ubs2_E_fclose : Z := 0x1a85c.
Definition ubs2_A_fflush : Z := 0x1a85c.  Definition ubs2_E_fflush : Z := 0x1ab28.
Definition ubs2_A_lockfile : Z := 0x1a9cc.  Definition ubs2_E_lockfile : Z := 0x1aac8.
Definition ubs2_A_unlockfile : Z := 0x1aac8.  Definition ubs2_E_unlockfile : Z := 0x1ab28.
Definition ubs2_A_fopen : Z := 0x1ab28.  Definition ubs2_E_fopen : Z := 0x1b140.
Definition ubs2_A_fmodeflags : Z := 0x1ac04.  Definition ubs2_E_fmodeflags : Z := 0x1acb8.
Definition ubs2_A_fdopen : Z := 0x1acb8.  Definition ubs2_E_fdopen : Z := 0x1ae90.
Definition ubs2_A_stdio_read : Z := 0x1ae90.  Definition ubs2_E_stdio_read : Z := 0x1afa8.
Definition ubs2_A_stdio_write : Z := 0x1afa8.  Definition ubs2_E_stdio_write : Z := 0x1b138.
Definition ubs2_A_stdio_seek : Z := 0x1b138.  Definition ubs2_E_stdio_seek : Z := 0x1b140.
Definition ubs2_A_aio_close : Z := 0x1b140.  Definition ubs2_E_aio_close : Z := 0x1b170.
Definition ubs2_A_stdio_close : Z := 0x1b144.  Definition ubs2_E_stdio_close : Z := 0x1b170.
Definition ubs2_A_fprintf : Z := 0x1b170.  Definition ubs2_E_fprintf : Z := 0x1b30c.
Definition ubs2_A_fwritex : Z := 0x1b1d4.  Definition ubs2_E_fwritex : Z := 0x1b30c.
Definition ubs2_A_fwrite : Z := 0x1b30c.  Definition ubs2_E_fwrite : Z := 0x1b6d8.
Definition ubs2_A_towrite : Z := 0x1b3c4.  Definition ubs2_E_towrite : Z := 0x1b418.
Definition ubs2_A_stdio_exit : Z := 0x1b418.  Definition ubs2_E_stdio_exit : Z := 0x1b5bc.
Definition ubs2_A_ofl_lock : Z := 0x1b5bc.  Definition ubs2_E_ofl_lock : Z := 0x1b5ec.
Definition ubs2_A_ofl_unlock : Z := 0x1b5ec.  Definition ubs2_E_ofl_unlock : Z := 0x1b5f8.
Definition ubs2_A_ofl_add : Z := 0x1b5f8.  Definition ubs2_E_ofl_add : Z := 0x1b638.
Definition ubs2_A_stdout_write : Z := 0x1b638.  Definition ubs2_E_stdout_write : Z := 0x1b6d8.
Definition ubs2_A_vfprintf : Z := 0x1b6d8.  Definition ubs2_E_vfprintf : Z := 0x1e11c.
Definition ubs2_A_printf_core : Z := 0x1b888.  Definition ubs2_E_printf_core : Z := 0x1c6b8.
Definition ubs2_A_pop_arg : Z := 0x1c6b8.  Definition ubs2_E_pop_arg : Z := 0x1c7ec.
Definition ubs2_A_pad : Z := 0x1c7ec.  Definition ubs2_E_pad : Z := 0x1c8c0.
Definition ubs2_A_fmt_fp : Z := 0x1c8c0.  Definition ubs2_E_fmt_fp : Z := 0x1df88.
Definition ubs2_A_strerror : Z := 0x1df88.  Definition ubs2_E_strerror : Z := 0x1dfc4.
Definition ubs2_A_lctrans_impl : Z := 0x1dfc4.  Definition ubs2_E_lctrans_impl : Z := 0x1dfc8.
Definition ubs2_A_lctrans : Z := 0x1dfc8.  Definition ubs2_E_lctrans : Z := 0x1dfcc.
Definition ubs2_A_wctomb : Z := 0x1dfcc.  Definition ubs2_E_wctomb : Z := 0x1dff0.
Definition ubs2_A_wcrtomb : Z := 0x1dff0.  Definition ubs2_E_wcrtomb : Z := 0x1e11c.
Definition ubs2_A_extenddftf2 : Z := 0x1e11c.  Definition ubs2_E_extenddftf2 : Z := 0x1e2ac.
Definition ubs2_A_signbitl : Z := 0x1e2ac.  Definition ubs2_E_signbitl : Z := 0x1e2b4.
Definition ubs2_A_fpclassifyl : Z := 0x1e2b4.  Definition ubs2_E_fpclassifyl : Z := 0x1e2f8.
Definition ubs2_A_frexpl : Z := 0x1e2f8.  Definition ubs2_E_frexpl : Z := 0x1e3d0.
Definition ubs2_A_letf2 : Z := 0x1e3d0.  Definition ubs2_E_letf2 : Z := 0x1e498.
Definition ubs2_A_multf3 : Z := 0x1e498.  Definition ubs2_E_multf3 : Z := 0x1eb98.
Definition ubs2_A_floatsitf : Z := 0x1eb98.  Definition ubs2_E_floatsitf : Z := 0x1eca0.
Definition ubs2_A_scalbn : Z := 0x1eca0.  Definition ubs2_E_scalbn : Z := 0x1ed38.
Definition ubs2_A_subtf3 : Z := 0x1ed38.  Definition ubs2_E_subtf3 : Z := 0x1ed48.
Definition ubs2_A_addtf3 : Z := 0x1ed48.  Definition ubs2_E_addtf3 : Z := 0x1f514.
Definition ubs2_A_fe_getround : Z := 0x1f514.  Definition ubs2_E_fe_getround : Z := 0x1f544.
Definition ubs2_A_fe_raise_inexact : Z := 0x1f544.  Definition ubs2_E_fe_raise_inexact : Z := 0x1f550.
Definition ubs2_A_fixunstfsi : Z := 0x1f550.  Definition ubs2_E_fixunstfsi : Z := 0x1f5e4.
Definition ubs2_A_floatunsitf : Z := 0x1f5e4.  Definition ubs2_E_floatunsitf : Z := 0x1f6d0.
Definition ubs2_A_fixtfsi : Z := 0x1f6d0.  Definition ubs2_E_fixtfsi : Z := 0x1f778.
Definition ubs2_A_divtf3 : Z := 0x1f778.  Definition ubs2_E_divtf3 : Z := 0x2007c.
Definition ubs2_A_vprintf : Z := 0x2007c.  Definition ubs2_E_vprintf : Z := 0x20098.
Definition ubs2_A_bcmp : Z := 0x20098.  Definition ubs2_E_bcmp : Z := 0x2009c.
Definition ubs2_A_memcmp : Z := 0x2009c.  Definition ubs2_E_memcmp : Z := 0x200cc.
Definition ubs2_A_memcpy : Z := 0x200cc.  Definition ubs2_E_memcpy : Z := 0x204d0.
Definition ubs2_A_memset : Z := 0x204d0.  Definition ubs2_E_memset : Z := 0x205c8.
Definition ubs2_A_strchr : Z := 0x205c8.  Definition ubs2_E_strchr : Z := 0x20774.
Definition ubs2_A_strchrnul : Z := 0x20604.  Definition ubs2_E_strchrnul : Z := 0x206e4.
Definition ubs2_A_strlen : Z := 0x206e4.  Definition ubs2_E_strlen : Z := 0x20774.
Definition ubs2_A_strnlen : Z := 0x20774.  Definition ubs2_E_strnlen : Z := 0x20884.
Definition ubs2_A_memchr : Z := 0x207b8.  Definition ubs2_E_memchr : Z := 0x20884.
Definition ubs2_A_lock : Z := 0x20884.  Definition ubs2_E_lock : Z := 0x20b0c.
Definition ubs2_A_unlock : Z := 0x20b0c.  Definition ubs2_E_unlock : Z := 0x20ba4.
Definition ubs2_A_syscall_cp_c : Z := 0x20b80.  Definition ubs2_E_syscall_cp_c : Z := 0x20ba4.
Definition ubs2_A_syscall_cp : Z := 0x20ba4.  Definition ubs2_E_syscall_cp : Z := 0x20ba8.
Definition ubs2_A_set_thread_area : Z := 0x20ba8.  Definition ubs2_E_set_thread_area : Z := 0x20bb4.
Definition ubs2_A_unistd_exit : Z := 0x20bb4.  Definition ubs2_E_unistd_exit : Z := 0x20bc0.
Definition ubs2_A_close : Z := 0x20bc0.  Definition ubs2_E_close : Z := 0x20c14.
Definition ubs2_A_lseek : Z := 0x20c14.  Definition ubs2_E_lseek : Z := 0x20c20.
Definition ubs2_A_read : Z := 0x20c20.  Definition ubs2_E_read : Z := 0x20c54.
Definition ubs2_D_str_n0X0x : Z := 0x10298.
Definition ubs2_D_str_wb : Z := 0x102a2.
Definition ubs2_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition ubs2_D_str_cli_out_of_memory_n : Z := 0x102b8.
Definition ubs2_D_str_d_n : Z := 0x102cc.
Definition ubs2_D_str : Z := 0x102d0.
Definition ubs2_D_str_2 : Z := 0x102d1.
Definition ubs2_D_str_usage_s_INPUT_n : Z := 0x102d3.
Definition ubs2_D_str_cli_config_len_overruns : Z := 0x102e4.
Definition ubs2_D_str_3 : Z := 0x10304.
Definition ubs2_D_str_inf : Z := 0x10306.
Definition ubs2_D_str_INF : Z := 0x1030a.
Definition ubs2_D_str_cli_input_u_bytes_refuse : Z := 0x1030e.
Definition ubs2_D_str_cli_cannot_open_s_n : Z := 0x1032f.
Definition ubs2_D_str_cli_read_error_on_s_n : Z := 0x10344.
Definition ubs2_D_str_NAN : Z := 0x1035b.
Definition ubs2_D_str_nan : Z := 0x1035f.
Definition ubs2_D_str_cli_input_shorter_than_h : Z := 0x10363.
Definition ubs2_D_str_rwa : Z := 0x10383.
Definition ubs2_D_str_dev_null : Z := 0x10387.
Definition ubs2_D_str_null : Z := 0x10391.
Definition ubs2_D_const_double_0x1p28 : Z := 0x103a0.
Definition ubs2_D_const_double_m1_0 : Z := 0x103a8.
Definition ubs2_D_const_double_0x1p52 : Z := 0x103b0.
Definition ubs2_D_const_double_256_0 : Z := 0x103b8.
Definition ubs2_D_const_double_1_0 : Z := 0x103c0.
Definition ubs2_D_const_double_m0_5 : Z := 0x103c8.
Definition ubs2_D_const_HIGHS_0x8080808080808080 : Z := 0x103d0.
Definition ubs2_D_const_double_0_5 : Z := 0x103d8.
Definition ubs2_D_const_ONES_0x0101010101010100 : Z := 0x103e0.
Definition ubs2_D_const_double_0x1p1023 : Z := 0x103e8.
Definition ubs2_D_const_double_1_5 : Z := 0x103f0.
Definition ubs2_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103f8.
Definition ubs2_D_d_103d8 : Z := 0x10400.
Definition ubs2_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x10408.
Definition ubs2_D_const_u64_0x0101010101010102 : Z := 0x10410.
Definition ubs2_D_const_double_0x1p120 : Z := 0x10418.
Definition ubs2_D_debruijn32 : Z := 0x1047c.
Definition ubs2_D_size_classes : Z := 0x1049c.
Definition ubs2_D_small_cnt_tab : Z := 0x104fc.
Definition ubs2_D_med_cnt_tab : Z := 0x10398.
Definition ubs2_D_const_float_m2147483904 : Z := 0x1039c.
Definition ubs2_D_jt_printf_core_1 : Z := 0x10518.
Definition ubs2_D_jt_printf_core_2 : Z := 0x105f8.
Definition ubs2_D_jt_pop_arg : Z := 0x10618.
Definition ubs2_D_states : Z := 0x10660.
Definition ubs2_D_xdigits : Z := 0x10830.
Definition ubs2_D_errmsgstr : Z := 0x10840.
Definition ubs2_D_global_pointer : Z := 0x10888.
Definition ubs2_D_errmsgidx : Z := 0x10fe8.
Definition ubs2_D_fe_getround : Z := 0x110f0.
Definition ubs2_D_EH_FRAME_LIST : Z := 0x11290.
Definition ubs2_D_init_array_start : Z := 0x21c58.
Definition ubs2_D_fini_array_start : Z := 0x21c60.
Definition ubs2_D_stderr : Z := 0x21c68.
Definition ubs2_D_stdout : Z := 0x21c70.
Definition ubs2_D_got_DYNAMIC : Z := 0x21c80.
Definition ubs2_D_got_main : Z := 0x21c88.
Definition ubs2_D_got_init : Z := 0x21c90.
Definition ubs2_D_got_fini : Z := 0x21c98.
Definition ubs2_D_got_register_frame_info : Z := 0x21ca0.
Definition ubs2_D_got_cxa_finalize : Z := 0x21ca8.
Definition ubs2_D_got_deregister_frame_info : Z := 0x21cb0.
Definition ubs2_D_got_stderr : Z := 0x21cb8.
Definition ubs2_D_got_LLVMFuzzerInitialize : Z := 0x21cc0.
Definition ubs2_D_got_stdout : Z := 0x21cc8.
Definition ubs2_D_got_environ : Z := 0x21cd0.
Definition ubs2_D_got_progname_full : Z := 0x21cd8.
Definition ubs2_D_got_progname : Z := 0x21ce0.
Definition ubs2_D_got_init_array_end : Z := 0x21ce8.
Definition ubs2_D_got_init_array_start : Z := 0x21cf0.
Definition ubs2_D_got_stack_chk_guard : Z := 0x21cf8.
Definition ubs2_D_got_fini_array_end : Z := 0x21d00.
Definition ubs2_D_got_fini_array_start : Z := 0x21d08.
Definition ubs2_D_dso_handle : Z := 0x22d10.
Definition ubs2_D_aef_arg0 : Z := 0x22d18.
Definition ubs2_D_aef_argc : Z := 0x22d20.
Definition ubs2_D_aef_argv : Z := 0x22d28.
Definition ubs2_D_stderr_FILE : Z := 0x22d38.
Definition ubs2_D_stderr_used : Z := 0x22e20.
Definition ubs2_D_stdout_FILE : Z := 0x22e28.
Definition ubs2_D_stdout_used : Z := 0x22f10.
Definition ubs2_D_default_stacksize : Z := 0x22f18.
Definition ubs2_D_do_init_initialized : Z := 0x22f20.
Definition ubs2_D_do_init_object : Z := 0x22f28.
Definition ubs2_D_do_fini_finalized : Z := 0x22f68.
Definition ubs2_D_read_stage : Z := 0x22f69.
Definition ubs2_D_target_run_initialized : Z := 0x32f70.
Definition ubs2_D_aef_in_callback : Z := 0x32f74.
Definition ubs2_D_aef_aligned_copy_empty : Z := 0x32f80.
Definition ubs2_D_environ : Z := 0x32fa0.
Definition ubs2_D_thread_list_lock : Z := 0x53078.
Definition ubs2_D_main_tls : Z := 0x53080.
Definition ubs2_D_builtin_tls : Z := 0x32fa8.
Definition ubs2_D_finished_atexit : Z := 0x530b0.
Definition ubs2_D_atexit_lock : Z := 0x530b4.
Definition ubs2_D_atexit_slot : Z := 0x530b8.
Definition ubs2_D_atexit_head : Z := 0x530c0.
Definition ubs2_D_atexit_builtin : Z := 0x530c8.
Definition ubs2_D_exit_exit_lock : Z := 0x532d0.
Definition ubs2_D_stack_chk_guard : Z := 0x532d8.
Definition ubs2_D_sysinfo : Z := 0x532e0.
Definition ubs2_D_progname : Z := 0x532e8.
Definition ubs2_D_progname_full : Z := 0x532f0.
Definition ubs2_D_libc : Z := 0x532f8.
Definition ubs2_D_hwcap : Z := 0x53360.
Definition ubs2_D_malloc_lock : Z := 0x53368.
Definition ubs2_D_malloc_context : Z := 0x53370.
Definition ubs2_D_malloc_replaced : Z := 0x53710.
Definition ubs2_D_stdin_used : Z := 0x53718.
Definition ubs2_D_ofl_lock : Z := 0x53720.
Definition ubs2_D_ofl_head : Z := 0x53728.
Definition ubs2_D_stderr_buf : Z := 0x53730.
Definition ubs2_D_stdout_buf : Z := 0x53738.
