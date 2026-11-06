(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YH03.v, with its addresses changed; 6 of its 205 lines of code are new or changed and 51 lines of the source are left out. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x128b0.  Definition src0_text_hi : Z := 0x1ce94.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x112ec.
Definition src0_eh_frame_lo : Z := 0x11408.  Definition src0_eh_frame_hi : Z := 0x118b0.
Definition src0_init_array_lo : Z := 0x1de98.  Definition src0_init_array_hi : Z := 0x1dea0.
Definition src0_fini_array_lo : Z := 0x1dea0.  Definition src0_fini_array_hi : Z := 0x1dea8.
Definition src0_data_rel_ro_lo : Z := 0x1dea8.  Definition src0_data_rel_ro_hi : Z := 0x1eb88.
Definition src0_got_lo : Z := 0x1eb88.  Definition src0_got_hi : Z := 0x1ec20.
Definition src0_data_lo : Z := 0x1fc20.  Definition src0_data_hi : Z := 0x1fe2c.
Definition src0_bss_lo : Z := 0x1fe30.  Definition src0_bss_hi : Z := 0x50a58.
Definition src0_A_start : Z := 0x128b0.  Definition src0_E_start : Z := 0x128f8.
Definition src0_A_do_init : Z := 0x128f8.  Definition src0_E_do_init : Z := 0x1296c.
Definition src0_A_do_fini : Z := 0x1296c.  Definition src0_E_do_fini : Z := 0x129fc.
Definition src0_A_main : Z := 0x129fc.  Definition src0_E_main : Z := 0x12cc0.
Definition src0_A_target_alloc_init : Z := 0x12cc0.  Definition src0_E_target_alloc_init : Z := 0x12cc4.
Definition src0_A_target_alloc_count : Z := 0x12cc4.  Definition src0_E_target_alloc_count : Z := 0x12ccc.
Definition src0_A_target_run : Z := 0x12ccc.  Definition src0_E_target_run : Z := 0x12e24.
Definition src0_A_oft_exit_guard : Z := 0x12e24.  Definition src0_E_oft_exit_guard : Z := 0x12e54.
Definition src0_A_emit_printf : Z := 0x12e54.  Definition src0_E_emit_printf : Z := 0x12e9c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12e9c.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x13dc0.
Definition src0_A_init : Z := 0x149d4.  Definition src0_E_init : Z := 0x149d8.
Definition src0_A_init_libc : Z := 0x149d8.  Definition src0_E_init_libc : Z := 0x14c04.
Definition src0_A_libc_start_init : Z := 0x14c04.  Definition src0_E_libc_start_init : Z := 0x14c50.
Definition src0_A_libc_start_main : Z := 0x14c50.  Definition src0_E_libc_start_main : Z := 0x14cb0.
Definition src0_A_libc_start_main_stage2 : Z := 0x14cb0.  Definition src0_E_libc_start_main_stage2 : Z := 0x14cf8.
Definition src0_A_init_tls : Z := 0x14cf8.  Definition src0_E_init_tls : Z := 0x14fa8.
Definition src0_A_funcs_on_exit : Z := 0x15058.  Definition src0_E_funcs_on_exit : Z := 0x15120.
Definition src0_A_cxa_finalize : Z := 0x15120.  Definition src0_E_cxa_finalize : Z := 0x15124.
Definition src0_A_atexit : Z := 0x15124.  Definition src0_E_atexit : Z := 0x151e8.
Definition src0_A_atexit_call : Z := 0x151e8.  Definition src0_E_atexit_call : Z := 0x151ec.
Definition src0_A_fini : Z := 0x151ec.  Definition src0_E_fini : Z := 0x151f0.
Definition src0_A_libc_exit_fini : Z := 0x151f0.  Definition src0_E_libc_exit_fini : Z := 0x1523c.
Definition src0_A_exit : Z := 0x1523c.  Definition src0_E_exit : Z := 0x152b0.
Definition src0_A_Exit : Z := 0x1503c.  Definition src0_E_Exit : Z := 0x15058.
Definition src0_A_open : Z := 0x152b0.  Definition src0_E_open : Z := 0x15394.
Definition src0_A_init_ssp : Z := 0x15394.  Definition src0_E_init_ssp : Z := 0x153f4.
Definition src0_A_stack_chk_fail : Z := 0x153f4.  Definition src0_E_stack_chk_fail : Z := 0x153fc.
Definition src0_A_syscall_ret : Z := 0x153fc.  Definition src0_E_syscall_ret : Z := 0x15434.
Definition src0_A_errno_location : Z := 0x15434.  Definition src0_E_errno_location : Z := 0x15440.
Definition src0_A_free : Z := 0x15440.  Definition src0_E_free : Z := 0x15444.
Definition src0_A_libc_calloc : Z := 0x15444.  Definition src0_E_libc_calloc : Z := 0x1557c.
Definition src0_A_libc_malloc : Z := 0x1557c.  Definition src0_E_libc_malloc : Z := 0x15580.
Definition src0_A_malloc : Z := 0x15580.  Definition src0_E_malloc : Z := 0x15584.
Definition src0_A_libc_free : Z := 0x15584.  Definition src0_E_libc_free : Z := 0x15750.
Definition src0_A_get_meta : Z := 0x15750.  Definition src0_E_get_meta : Z := 0x15860.
Definition src0_A_nontrivial_free : Z := 0x15860.  Definition src0_E_nontrivial_free : Z := 0x15c38.
Definition src0_A_alloc_meta : Z := 0x15c38.  Definition src0_E_alloc_meta : Z := 0x15f10.
Definition src0_A_libc_malloc_impl : Z := 0x15f10.  Definition src0_E_libc_malloc_impl : Z := 0x16280.
Definition src0_A_alloc_slot : Z := 0x16280.  Definition src0_E_alloc_slot : Z := 0x16b24.
Definition src0_A_enframe : Z := 0x16b24.  Definition src0_E_enframe : Z := 0x16c74.
Definition src0_A_malloc_allzerop : Z := 0x16c74.  Definition src0_E_malloc_allzerop : Z := 0x16dec.
Definition src0_A_vm_wait : Z := 0x16dec.  Definition src0_E_vm_wait : Z := 0x16df0.
Definition src0_A_mmap : Z := 0x16df0.  Definition src0_E_mmap : Z := 0x16edc.
Definition src0_A_mprotect : Z := 0x16edc.  Definition src0_E_mprotect : Z := 0x16f24.
Definition src0_A_munmap : Z := 0x16f24.  Definition src0_E_munmap : Z := 0x16f6c.
Definition src0_A_fflush : Z := 0x17040.  Definition src0_E_fflush : Z := 0x171b0.
Definition src0_A_lockfile : Z := 0x171b0.  Definition src0_E_lockfile : Z := 0x172ac.
Definition src0_A_unlockfile : Z := 0x172ac.  Definition src0_E_unlockfile : Z := 0x1730c.
Definition src0_A_stdio_write : Z := 0x177c4.  Definition src0_E_stdio_write : Z := 0x17954.
Definition src0_A_stdio_seek : Z := 0x17954.  Definition src0_E_stdio_seek : Z := 0x1795c.
Definition src0_A_aio_close : Z := 0x17794.  Definition src0_E_aio_close : Z := 0x17798.
Definition src0_A_stdio_close : Z := 0x17798.  Definition src0_E_stdio_close : Z := 0x177c4.
Definition src0_A_fprintf : Z := 0x1730c.  Definition src0_E_fprintf : Z := 0x17370.
Definition src0_A_fwritex : Z := 0x17370.  Definition src0_E_fwritex : Z := 0x174a8.
Definition src0_A_fwrite : Z := 0x174a8.  Definition src0_E_fwrite : Z := 0x17560.
Definition src0_A_towrite : Z := 0x17560.  Definition src0_E_towrite : Z := 0x175b4.
Definition src0_A_stdio_exit : Z := 0x175b4.  Definition src0_E_stdio_exit : Z := 0x17758.
Definition src0_A_ofl_lock : Z := 0x17758.  Definition src0_E_ofl_lock : Z := 0x17788.
Definition src0_A_ofl_unlock : Z := 0x17788.  Definition src0_E_ofl_unlock : Z := 0x17794.
Definition src0_A_stdout_write : Z := 0x1795c.  Definition src0_E_stdout_write : Z := 0x179fc.
Definition src0_A_vfprintf : Z := 0x179fc.  Definition src0_E_vfprintf : Z := 0x17bac.
Definition src0_A_printf_core : Z := 0x17bac.  Definition src0_E_printf_core : Z := 0x189dc.
Definition src0_A_pop_arg : Z := 0x189dc.  Definition src0_E_pop_arg : Z := 0x18b10.
Definition src0_A_pad : Z := 0x18b10.  Definition src0_E_pad : Z := 0x18be4.
Definition src0_A_fmt_fp : Z := 0x18be4.  Definition src0_E_fmt_fp : Z := 0x1a2ac.
Definition src0_A_strerror : Z := 0x1a2ac.  Definition src0_E_strerror : Z := 0x1a2e8.
Definition src0_A_lctrans_impl : Z := 0x1a2e8.  Definition src0_E_lctrans_impl : Z := 0x1a2ec.
Definition src0_A_lctrans : Z := 0x1a2ec.  Definition src0_E_lctrans : Z := 0x1a2f0.
Definition src0_A_wctomb : Z := 0x1a2f0.  Definition src0_E_wctomb : Z := 0x1a314.
Definition src0_A_wcrtomb : Z := 0x1a314.  Definition src0_E_wcrtomb : Z := 0x1a440.
Definition src0_A_extenddftf2 : Z := 0x1a440.  Definition src0_E_extenddftf2 : Z := 0x1a5d0.
Definition src0_A_signbitl : Z := 0x1a5d0.  Definition src0_E_signbitl : Z := 0x1a5d8.
Definition src0_A_fpclassifyl : Z := 0x1a5d8.  Definition src0_E_fpclassifyl : Z := 0x1a61c.
Definition src0_A_frexpl : Z := 0x1a61c.  Definition src0_E_frexpl : Z := 0x1a6f4.
Definition src0_A_letf2 : Z := 0x1a6f4.  Definition src0_E_letf2 : Z := 0x1a7bc.
Definition src0_A_multf3 : Z := 0x1a7bc.  Definition src0_E_multf3 : Z := 0x1aebc.
Definition src0_A_floatsitf : Z := 0x1aebc.  Definition src0_E_floatsitf : Z := 0x1afc4.
Definition src0_A_scalbn : Z := 0x1afc4.  Definition src0_E_scalbn : Z := 0x1b05c.
Definition src0_A_subtf3 : Z := 0x1b05c.  Definition src0_E_subtf3 : Z := 0x1b06c.
Definition src0_A_addtf3 : Z := 0x1b06c.  Definition src0_E_addtf3 : Z := 0x1b838.
Definition src0_A_fe_getround : Z := 0x1b838.  Definition src0_E_fe_getround : Z := 0x1b868.
Definition src0_A_fe_raise_inexact : Z := 0x1b868.  Definition src0_E_fe_raise_inexact : Z := 0x1b874.
Definition src0_A_fixunstfsi : Z := 0x1b874.  Definition src0_E_fixunstfsi : Z := 0x1b908.
Definition src0_A_floatunsitf : Z := 0x1b908.  Definition src0_E_floatunsitf : Z := 0x1b9f4.
Definition src0_A_fixtfsi : Z := 0x1b9f4.  Definition src0_E_fixtfsi : Z := 0x1ba9c.
Definition src0_A_divtf3 : Z := 0x1ba9c.  Definition src0_E_divtf3 : Z := 0x1c3a0.
Definition src0_A_vprintf : Z := 0x1c3a0.  Definition src0_E_vprintf : Z := 0x1c3bc.
Definition src0_A_bcmp : Z := 0x1c3bc.  Definition src0_E_bcmp : Z := 0x1c3c0.
Definition src0_A_memcmp : Z := 0x1c48c.  Definition src0_E_memcmp : Z := 0x1c4bc.
Definition src0_A_memcpy : Z := 0x1c4bc.  Definition src0_E_memcpy : Z := 0x1c8c0.
Definition src0_A_memset : Z := 0x1c8c0.  Definition src0_E_memset : Z := 0x1c9b8.
Definition src0_A_strlen : Z := 0x1c9f0.  Definition src0_E_strlen : Z := 0x1ca80.
Definition src0_A_strnlen : Z := 0x1ca80.  Definition src0_E_strnlen : Z := 0x1cac4.
Definition src0_A_memchr : Z := 0x1c3c0.  Definition src0_E_memchr : Z := 0x1c48c.
Definition src0_A_lock : Z := 0x1cac4.  Definition src0_E_lock : Z := 0x1cd4c.
Definition src0_A_unlock : Z := 0x1cd4c.  Definition src0_E_unlock : Z := 0x1cdc0.
Definition src0_A_syscall_cp_c : Z := 0x1cdc0.  Definition src0_E_syscall_cp_c : Z := 0x1cde4.
Definition src0_A_syscall_cp : Z := 0x1cde4.  Definition src0_E_syscall_cp : Z := 0x1cde8.
Definition src0_A_set_thread_area : Z := 0x1cde8.  Definition src0_E_set_thread_area : Z := 0x1cdf4.
Definition src0_A_unistd_exit : Z := 0x1cdf4.  Definition src0_E_unistd_exit : Z := 0x1ce00.
Definition src0_A_close : Z := 0x1ce00.  Definition src0_E_close : Z := 0x1ce54.
Definition src0_A_lseek : Z := 0x1ce54.  Definition src0_E_lseek : Z := 0x1ce60.
Definition src0_A_read : Z := 0x1ce60.  Definition src0_E_read : Z := 0x1ce94.
Definition src0_D_str_n0X0x : Z := 0x102b7.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x10312.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10325.
Definition src0_D_str_d_n : Z := 0x10339.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10355.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10366.
Definition src0_D_str_inf : Z := 0x103b2.
Definition src0_D_str_INF : Z := 0x10407.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1040b.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x104bd.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x104d2.
Definition src0_D_str_NAN : Z := 0x104ff.
Definition src0_D_str_nan : Z := 0x10503.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1050d.
Definition src0_D_str_dev_null : Z := 0x1053f.
Definition src0_D_str_null : Z := 0x10549.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10560.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10570.
Definition src0_D_debruijn32 : Z := 0x10658.
Definition src0_D_size_classes : Z := 0x10678.
Definition src0_D_small_cnt_tab : Z := 0x106d8.
Definition src0_D_med_cnt_tab : Z := 0x106f3.
Definition src0_D_states : Z := 0x10850.
Definition src0_D_xdigits : Z := 0x10a20.
Definition src0_D_errmsgstr : Z := 0x10a30.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x111d8.
Definition src0_D_fe_getround : Z := 0x112e0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11408.
Definition src0_D_init_array_start : Z := 0x1de98.
Definition src0_D_fini_array_start : Z := 0x1dea0.
Definition src0_D_stdout : Z := 0x1eb80.
Definition src0_D_got_DYNAMIC : Z := 0x1eb90.
Definition src0_D_got_main : Z := 0x1eb98.
Definition src0_D_got_init : Z := 0x1eba0.
Definition src0_D_got_fini : Z := 0x1eba8.
Definition src0_D_got_register_frame_info : Z := 0x1ebb0.
Definition src0_D_got_cxa_finalize : Z := 0x1ebb8.
Definition src0_D_got_deregister_frame_info : Z := 0x1ebc0.
Definition src0_D_got_stderr : Z := 0x1ebc8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1ebd0.
Definition src0_D_got_stdout : Z := 0x1ebd8.
Definition src0_D_got_environ : Z := 0x1ebe0.
Definition src0_D_got_progname_full : Z := 0x1ebe8.
Definition src0_D_got_progname : Z := 0x1ebf0.
Definition src0_D_got_init_array_end : Z := 0x1ebf8.
Definition src0_D_got_init_array_start : Z := 0x1ec00.
Definition src0_D_got_stack_chk_guard : Z := 0x1ec08.
Definition src0_D_got_fini_array_end : Z := 0x1ec10.
Definition src0_D_got_fini_array_start : Z := 0x1ec18.
Definition src0_D_dso_handle : Z := 0x1fc20.
Definition src0_D_oft_argc : Z := 0x1fc30.
Definition src0_D_stderr_FILE : Z := 0x1fc48.
Definition src0_D_stderr_used : Z := 0x1fd30.
Definition src0_D_stdout_FILE : Z := 0x1fd38.
Definition src0_D_stdout_used : Z := 0x1fe20.
Definition src0_D_default_stacksize : Z := 0x1fe28.
Definition src0_D_do_init_initialized : Z := 0x1fe30.
Definition src0_D_do_init_object : Z := 0x1fe38.
Definition src0_D_do_fini_finalized : Z := 0x1fe78.
Definition src0_D_read_stage : Z := 0x1fe79.
Definition src0_D_target_run_initialized : Z := 0x2fe80.
Definition src0_D_oft_in_callback : Z := 0x2fe84.
Definition src0_D_oft_aligned_copy_empty : Z := 0x2fe90.
Definition src0_D_environ : Z := 0x2feb0.
Definition src0_D_thread_list_lock : Z := 0x4ff88.
Definition src0_D_main_tls : Z := 0x4ff90.
Definition src0_D_builtin_tls : Z := 0x2feb8.
Definition src0_D_finished_atexit : Z := 0x4ffc8.
Definition src0_D_atexit_lock : Z := 0x4ffcc.
Definition src0_D_atexit_slot : Z := 0x4ffd0.
Definition src0_D_atexit_head : Z := 0x4ffd8.
Definition src0_D_atexit_builtin : Z := 0x4ffe0.
Definition src0_D_exit_exit_lock : Z := 0x501e8.
Definition src0_D_stack_chk_guard : Z := 0x501f0.
Definition src0_D_sysinfo : Z := 0x501f8.
Definition src0_D_progname : Z := 0x50200.
Definition src0_D_progname_full : Z := 0x50208.
Definition src0_D_libc : Z := 0x50210.
Definition src0_D_hwcap : Z := 0x50278.
Definition src0_D_malloc_lock : Z := 0x50280.
Definition src0_D_malloc_context : Z := 0x50288.
Definition src0_D_malloc_replaced : Z := 0x50628.
Definition src0_D_stdin_used : Z := 0x50630.
Definition src0_D_ofl_lock : Z := 0x50638.
Definition src0_D_ofl_head : Z := 0x50640.
Definition src0_D_stderr_buf : Z := 0x50648.
Definition src0_D_stdout_buf : Z := 0x50650.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
