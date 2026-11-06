(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x128d4.  Definition src0_text_hi : Z := 0x1d0ec.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11308.
Definition src0_eh_frame_lo : Z := 0x11430.  Definition src0_eh_frame_hi : Z := 0x118d4.
Definition src0_init_array_lo : Z := 0x1e0f0.  Definition src0_init_array_hi : Z := 0x1e0f8.
Definition src0_fini_array_lo : Z := 0x1e0f8.  Definition src0_fini_array_hi : Z := 0x1e100.
Definition src0_data_rel_ro_lo : Z := 0x1e100.  Definition src0_data_rel_ro_hi : Z := 0x1e218.
Definition src0_got_lo : Z := 0x1e218.  Definition src0_got_hi : Z := 0x1e2b0.
Definition src0_data_lo : Z := 0x1f2b0.  Definition src0_data_hi : Z := 0x1f4bc.
Definition src0_bss_lo : Z := 0x1f4c0.  Definition src0_bss_hi : Z := 0x500e8.
Definition src0_A_start : Z := 0x128d4.  Definition src0_E_start : Z := 0x1291c.
Definition src0_A_do_init : Z := 0x1291c.  Definition src0_E_do_init : Z := 0x12990.
Definition src0_A_do_fini : Z := 0x12990.  Definition src0_E_do_fini : Z := 0x12a20.
Definition src0_A_main : Z := 0x12a20.  Definition src0_E_main : Z := 0x12ce4.
Definition src0_A_target_alloc_init : Z := 0x12ce4.  Definition src0_E_target_alloc_init : Z := 0x12ce8.
Definition src0_A_target_alloc_count : Z := 0x12ce8.  Definition src0_E_target_alloc_count : Z := 0x12cf0.
Definition src0_A_target_run : Z := 0x12cf0.  Definition src0_E_target_run : Z := 0x12e48.
Definition src0_A_aef_exit_guard : Z := 0x12e48.  Definition src0_E_aef_exit_guard : Z := 0x12e78.
Definition src0_A_emit_printf : Z := 0x12e78.  Definition src0_E_emit_printf : Z := 0x12ec0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ec0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14224.
Definition src0_A_read_frameconfig : Z := 0x15768.  Definition src0_E_read_frameconfig : Z := 0x159d0.
Definition src0_A_cgif_newgif : Z := 0x159d0.  Definition src0_E_cgif_newgif : Z := 0x15b88.
Definition src0_A_cgif_writecb : Z := 0x15b88.  Definition src0_E_cgif_writecb : Z := 0x15bfc.
Definition src0_A_freeCGIF : Z := 0x15bfc.  Definition src0_E_freeCGIF : Z := 0x15c34.
Definition src0_A_cgif_addframe : Z := 0x15c34.  Definition src0_E_cgif_addframe : Z := 0x15fa0.
Definition src0_A_cmpPixel : Z := 0x15fa0.  Definition src0_E_cmpPixel : Z := 0x16054.
Definition src0_A_flushFrame : Z := 0x16054.  Definition src0_E_flushFrame : Z := 0x16950.
Definition src0_A_freeFrame : Z := 0x16950.  Definition src0_E_freeFrame : Z := 0x16998.
Definition src0_A_cgif_close : Z := 0x16998.  Definition src0_E_cgif_close : Z := 0x16a60.
Definition src0_A_cgif_raw_newgif : Z := 0x16a60.  Definition src0_E_cgif_raw_newgif : Z := 0x16d14.
Definition src0_A_cgif_raw_addframe : Z := 0x16d14.  Definition src0_E_cgif_raw_addframe : Z := 0x17190.
Definition src0_A_LZW_GenerateStream : Z := 0x17190.  Definition src0_E_LZW_GenerateStream : Z := 0x17730.
Definition src0_A_cgif_raw_close : Z := 0x17730.  Definition src0_E_cgif_raw_close : Z := 0x17790.
Definition src0_A_create_byte_list : Z := 0x17790.  Definition src0_E_create_byte_list : Z := 0x1790c.
Definition src0_A_create_byte_list_block : Z := 0x1790c.  Definition src0_E_create_byte_list_block : Z := 0x15540.
Definition src0_A_init : Z := 0x15540.  Definition src0_E_init : Z := 0x15544.
Definition src0_A_init_libc : Z := 0x15544.  Definition src0_E_init_libc : Z := 0x15770.
Definition src0_A_libc_start_init : Z := 0x15770.  Definition src0_E_libc_start_init : Z := 0x157bc.
Definition src0_A_libc_start_main : Z := 0x157bc.  Definition src0_E_libc_start_main : Z := 0x1581c.
Definition src0_A_libc_start_main_stage2 : Z := 0x1581c.  Definition src0_E_libc_start_main_stage2 : Z := 0x15864.
Definition src0_A_init_tls : Z := 0x15864.  Definition src0_E_init_tls : Z := 0x15b14.
Definition src0_A_funcs_on_exit : Z := 0x15bc4.  Definition src0_E_funcs_on_exit : Z := 0x15c8c.
Definition src0_A_cxa_finalize : Z := 0x15c8c.  Definition src0_E_cxa_finalize : Z := 0x15c90.
Definition src0_A_atexit : Z := 0x15c90.  Definition src0_E_atexit : Z := 0x15d54.
Definition src0_A_atexit_call : Z := 0x15d54.  Definition src0_E_atexit_call : Z := 0x15d58.
Definition src0_A_fini : Z := 0x15d58.  Definition src0_E_fini : Z := 0x15d5c.
Definition src0_A_libc_exit_fini : Z := 0x15d5c.  Definition src0_E_libc_exit_fini : Z := 0x15da8.
Definition src0_A_exit : Z := 0x15da8.  Definition src0_E_exit : Z := 0x15e1c.
Definition src0_A_Exit : Z := 0x15ba8.  Definition src0_E_Exit : Z := 0x15bc4.
Definition src0_A_open : Z := 0x15e1c.  Definition src0_E_open : Z := 0x15f00.
Definition src0_A_init_ssp : Z := 0x15f00.  Definition src0_E_init_ssp : Z := 0x15f60.
Definition src0_A_stack_chk_fail : Z := 0x15f60.  Definition src0_E_stack_chk_fail : Z := 0x15f68.
Definition src0_A_syscall_ret : Z := 0x15f68.  Definition src0_E_syscall_ret : Z := 0x15fa0.
Definition src0_A_errno_location : Z := 0x15fa0.  Definition src0_E_errno_location : Z := 0x15fac.
Definition src0_A_free : Z := 0x15fac.  Definition src0_E_free : Z := 0x15fb0.
Definition src0_A_libc_calloc : Z := 0x15fb0.  Definition src0_E_libc_calloc : Z := 0x160e8.
Definition src0_A_libc_malloc : Z := 0x160e8.  Definition src0_E_libc_malloc : Z := 0x160ec.
Definition src0_A_malloc : Z := 0x160ec.  Definition src0_E_malloc : Z := 0x160f0.
Definition src0_A_libc_free : Z := 0x160f0.  Definition src0_E_libc_free : Z := 0x162bc.
Definition src0_A_get_meta : Z := 0x162bc.  Definition src0_E_get_meta : Z := 0x163cc.
Definition src0_A_nontrivial_free : Z := 0x163cc.  Definition src0_E_nontrivial_free : Z := 0x167a4.
Definition src0_A_alloc_meta : Z := 0x167a4.  Definition src0_E_alloc_meta : Z := 0x16a7c.
Definition src0_A_libc_malloc_impl : Z := 0x16a7c.  Definition src0_E_libc_malloc_impl : Z := 0x16dec.
Definition src0_A_alloc_slot : Z := 0x16dec.  Definition src0_E_alloc_slot : Z := 0x17690.
Definition src0_A_enframe : Z := 0x17690.  Definition src0_E_enframe : Z := 0x177e0.
Definition src0_A_malloc_allzerop : Z := 0x177e0.  Definition src0_E_malloc_allzerop : Z := 0x17958.
Definition src0_A_vm_wait : Z := 0x17958.  Definition src0_E_vm_wait : Z := 0x1795c.
Definition src0_A_mmap : Z := 0x1795c.  Definition src0_E_mmap : Z := 0x17a48.
Definition src0_A_mprotect : Z := 0x17a48.  Definition src0_E_mprotect : Z := 0x17a90.
Definition src0_A_munmap : Z := 0x17a90.  Definition src0_E_munmap : Z := 0x17ad8.
Definition src0_A_unlist_locked_file : Z := 0x17ae8.  Definition src0_E_unlist_locked_file : Z := 0x17aec.
Definition src0_A_fclose : Z := 0x17aec.  Definition src0_E_fclose : Z := 0x17bac.
Definition src0_A_fflush : Z := 0x17bac.  Definition src0_E_fflush : Z := 0x17d1c.
Definition src0_A_lockfile : Z := 0x17d1c.  Definition src0_E_lockfile : Z := 0x17e18.
Definition src0_A_unlockfile : Z := 0x17e18.  Definition src0_E_unlockfile : Z := 0x17e78.
Definition src0_A_fopen : Z := 0x17e84.  Definition src0_E_fopen : Z := 0x17f60.
Definition src0_A_fmodeflags : Z := 0x17f60.  Definition src0_E_fmodeflags : Z := 0x18014.
Definition src0_A_fdopen : Z := 0x18014.  Definition src0_E_fdopen : Z := 0x181ec.
Definition src0_A_stdio_write : Z := 0x18330.  Definition src0_E_stdio_write : Z := 0x184c0.
Definition src0_A_aio_close : Z := 0x18300.  Definition src0_E_aio_close : Z := 0x18304.
Definition src0_A_stdio_close : Z := 0x18304.  Definition src0_E_stdio_close : Z := 0x18330.
Definition src0_A_fprintf : Z := 0x17e78.  Definition src0_E_fprintf : Z := 0x17edc.
Definition src0_A_fwritex : Z := 0x17edc.  Definition src0_E_fwritex : Z := 0x18014.
Definition src0_A_fwrite : Z := 0x18014.  Definition src0_E_fwrite : Z := 0x180cc.
Definition src0_A_towrite : Z := 0x180cc.  Definition src0_E_towrite : Z := 0x18120.
Definition src0_A_stdio_exit : Z := 0x18120.  Definition src0_E_stdio_exit : Z := 0x182c4.
Definition src0_A_ofl_lock : Z := 0x182c4.  Definition src0_E_ofl_lock : Z := 0x182f4.
Definition src0_A_ofl_unlock : Z := 0x182f4.  Definition src0_E_ofl_unlock : Z := 0x18300.
Definition src0_A_ofl_add : Z := 0x18954.  Definition src0_E_ofl_add : Z := 0x184c8.
Definition src0_A_stdout_write : Z := 0x184c8.  Definition src0_E_stdout_write : Z := 0x18568.
Definition src0_A_vfprintf : Z := 0x18568.  Definition src0_E_vfprintf : Z := 0x18718.
Definition src0_A_printf_core : Z := 0x18718.  Definition src0_E_printf_core : Z := 0x19548.
Definition src0_A_pop_arg : Z := 0x19548.  Definition src0_E_pop_arg : Z := 0x1967c.
Definition src0_A_pad : Z := 0x1967c.  Definition src0_E_pad : Z := 0x19750.
Definition src0_A_fmt_fp : Z := 0x19750.  Definition src0_E_fmt_fp : Z := 0x1ae18.
Definition src0_A_strerror : Z := 0x1ae18.  Definition src0_E_strerror : Z := 0x1ae54.
Definition src0_A_lctrans_impl : Z := 0x1ae54.  Definition src0_E_lctrans_impl : Z := 0x1ae58.
Definition src0_A_lctrans : Z := 0x1ae58.  Definition src0_E_lctrans : Z := 0x1ae5c.
Definition src0_A_wctomb : Z := 0x1ae5c.  Definition src0_E_wctomb : Z := 0x1ae80.
Definition src0_A_wcrtomb : Z := 0x1ae80.  Definition src0_E_wcrtomb : Z := 0x1afac.
Definition src0_A_extenddftf2 : Z := 0x1afac.  Definition src0_E_extenddftf2 : Z := 0x1b13c.
Definition src0_A_signbitl : Z := 0x1b13c.  Definition src0_E_signbitl : Z := 0x1b144.
Definition src0_A_fpclassifyl : Z := 0x1b144.  Definition src0_E_fpclassifyl : Z := 0x1b188.
Definition src0_A_frexpl : Z := 0x1b188.  Definition src0_E_frexpl : Z := 0x1b260.
Definition src0_A_letf2 : Z := 0x14924.  Definition src0_E_letf2 : Z := 0x149ec.
Definition src0_A_multf3 : Z := 0x1b260.  Definition src0_E_multf3 : Z := 0x1b960.
Definition src0_A_floatsitf : Z := 0x1b960.  Definition src0_E_floatsitf : Z := 0x1ba68.
Definition src0_A_scalbn : Z := 0x1ba68.  Definition src0_E_scalbn : Z := 0x1bb00.
Definition src0_A_subtf3 : Z := 0x14d28.  Definition src0_E_subtf3 : Z := 0x14d38.
Definition src0_A_addtf3 : Z := 0x14d38.  Definition src0_E_addtf3 : Z := 0x15504.
Definition src0_A_fe_getround : Z := 0x15504.  Definition src0_E_fe_getround : Z := 0x15534.
Definition src0_A_fe_raise_inexact : Z := 0x15534.  Definition src0_E_fe_raise_inexact : Z := 0x15540.
Definition src0_A_fixunstfsi : Z := 0x1bb00.  Definition src0_E_fixunstfsi : Z := 0x1bb94.
Definition src0_A_floatunsitf : Z := 0x1bb94.  Definition src0_E_floatunsitf : Z := 0x1bc80.
Definition src0_A_fixtfsi : Z := 0x1bc80.  Definition src0_E_fixtfsi : Z := 0x1bd28.
Definition src0_A_divtf3 : Z := 0x1bd28.  Definition src0_E_divtf3 : Z := 0x1c62c.
Definition src0_A_vprintf : Z := 0x1c62c.  Definition src0_E_vprintf : Z := 0x1c648.
Definition src0_A_bcmp : Z := 0x1cb14.  Definition src0_E_bcmp : Z := 0x1cb18.
Definition src0_A_memcmp : Z := 0x1cb18.  Definition src0_E_memcmp : Z := 0x1c648.
Definition src0_A_memcpy : Z := 0x1c648.  Definition src0_E_memcpy : Z := 0x1ca4c.
Definition src0_A_memset : Z := 0x1ca4c.  Definition src0_E_memset : Z := 0x1cb44.
Definition src0_A_strchr : Z := 0x1f654.  Definition src0_E_strchr : Z := 0x1f690.
Definition src0_A_strchrnul : Z := 0x1f690.  Definition src0_E_strchrnul : Z := 0x1f770.
Definition src0_A_strlen : Z := 0x1cb7c.  Definition src0_E_strlen : Z := 0x1cc0c.
Definition src0_A_strnlen : Z := 0x1cc0c.  Definition src0_E_strnlen : Z := 0x1cc50.
Definition src0_A_memchr : Z := 0x1cc50.  Definition src0_E_memchr : Z := 0x1cd1c.
Definition src0_A_lock : Z := 0x1cd1c.  Definition src0_E_lock : Z := 0x1cfa4.
Definition src0_A_unlock : Z := 0x1cfa4.  Definition src0_E_unlock : Z := 0x1d018.
Definition src0_A_syscall_cp_c : Z := 0x1d018.  Definition src0_E_syscall_cp_c : Z := 0x1d03c.
Definition src0_A_syscall_cp : Z := 0x1d03c.  Definition src0_E_syscall_cp : Z := 0x1d040.
Definition src0_A_set_thread_area : Z := 0x1d040.  Definition src0_E_set_thread_area : Z := 0x1d04c.
Definition src0_A_unistd_exit : Z := 0x1d04c.  Definition src0_E_unistd_exit : Z := 0x1d058.
Definition src0_A_close : Z := 0x1d058.  Definition src0_E_close : Z := 0x1d0ac.
Definition src0_A_lseek : Z := 0x1d0ac.  Definition src0_E_lseek : Z := 0x1d0b8.
Definition src0_A_read : Z := 0x1d0b8.  Definition src0_E_read : Z := 0x1d0ec.
Definition src0_A_unlink : Z := 0x1fce0.  Definition src0_E_unlink : Z := 0x1fd10.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10316.
Definition src0_D_str_d_n : Z := 0x1032a.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10350.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10361.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10399.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1040c.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10421.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10464.
Definition src0_D_str_dev_null : Z := 0x104a9.
Definition src0_D_str_null : Z := 0x104b3.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x104f0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10500.
Definition src0_D_debruijn32 : Z := 0x10680.
Definition src0_D_size_classes : Z := 0x106a0.
Definition src0_D_small_cnt_tab : Z := 0x10700.
Definition src0_D_med_cnt_tab : Z := 0x1071b.
Definition src0_D_states : Z := 0x10878.
Definition src0_D_xdigits : Z := 0x10a48.
Definition src0_D_errmsgstr : Z := 0x10a58.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11200.
Definition src0_D_fe_getround : Z := 0x10618.
Definition src0_D_EH_FRAME_LIST : Z := 0x11430.
Definition src0_D_init_array_start : Z := 0x1e0f0.
Definition src0_D_fini_array_start : Z := 0x1e0f8.
Definition src0_D_stderr : Z := 0x1e208.
Definition src0_D_stdout : Z := 0x1e210.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1e218.
Definition src0_D_got_DYNAMIC : Z := 0x1e220.
Definition src0_D_got_main : Z := 0x1e228.
Definition src0_D_got_init : Z := 0x1e230.
Definition src0_D_got_fini : Z := 0x1e238.
Definition src0_D_got_register_frame_info : Z := 0x1e240.
Definition src0_D_got_cxa_finalize : Z := 0x1e248.
Definition src0_D_got_deregister_frame_info : Z := 0x1e250.
Definition src0_D_got_stderr : Z := 0x1e258.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e260.
Definition src0_D_got_stdout : Z := 0x1e268.
Definition src0_D_got_environ : Z := 0x1e270.
Definition src0_D_got_progname_full : Z := 0x1e278.
Definition src0_D_got_progname : Z := 0x1e280.
Definition src0_D_got_init_array_end : Z := 0x1e288.
Definition src0_D_got_init_array_start : Z := 0x1e290.
Definition src0_D_got_stack_chk_guard : Z := 0x1e298.
Definition src0_D_got_fini_array_end : Z := 0x1e2a0.
Definition src0_D_got_fini_array_start : Z := 0x1e2a8.
Definition src0_D_dso_handle : Z := 0x1f2b0.
Definition src0_D_aef_argc : Z := 0x1f2c0.
Definition src0_D_stderr_FILE : Z := 0x1f2d8.
Definition src0_D_stderr_used : Z := 0x1f3c0.
Definition src0_D_stdout_FILE : Z := 0x1f3c8.
Definition src0_D_stdout_used : Z := 0x1f4b0.
Definition src0_D_default_stacksize : Z := 0x1f4b8.
Definition src0_D_do_init_initialized : Z := 0x1f4c0.
Definition src0_D_do_init_object : Z := 0x1f4c8.
Definition src0_D_do_fini_finalized : Z := 0x1f508.
Definition src0_D_read_stage : Z := 0x1f509.
Definition src0_D_target_run_initialized : Z := 0x2f510.
Definition src0_D_aef_in_callback : Z := 0x2f514.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f520.
Definition src0_D_environ : Z := 0x2f540.
Definition src0_D_thread_list_lock : Z := 0x4f618.
Definition src0_D_main_tls : Z := 0x4f620.
Definition src0_D_builtin_tls : Z := 0x2f548.
Definition src0_D_finished_atexit : Z := 0x4f658.
Definition src0_D_atexit_lock : Z := 0x4f65c.
Definition src0_D_atexit_slot : Z := 0x4f660.
Definition src0_D_atexit_head : Z := 0x4f668.
Definition src0_D_atexit_builtin : Z := 0x4f670.
Definition src0_D_exit_exit_lock : Z := 0x4f878.
Definition src0_D_stack_chk_guard : Z := 0x4f880.
Definition src0_D_sysinfo : Z := 0x4f888.
Definition src0_D_progname : Z := 0x4f890.
Definition src0_D_progname_full : Z := 0x4f898.
Definition src0_D_libc : Z := 0x4f8a0.
Definition src0_D_hwcap : Z := 0x4f908.
Definition src0_D_malloc_lock : Z := 0x4f910.
Definition src0_D_malloc_context : Z := 0x4f918.
Definition src0_D_malloc_replaced : Z := 0x4fcb8.
Definition src0_D_stdin_used : Z := 0x4fcc0.
Definition src0_D_ofl_lock : Z := 0x4fcc8.
Definition src0_D_ofl_head : Z := 0x4fcd0.
Definition src0_D_stderr_buf : Z := 0x4fcd8.
Definition src0_D_stdout_buf : Z := 0x4fce0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
