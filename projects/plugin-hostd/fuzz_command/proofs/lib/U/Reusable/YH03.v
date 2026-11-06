(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x13a74.  Definition src0_text_hi : Z := 0x216ac.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1197e.
Definition src0_eh_frame_lo : Z := 0x11c30.  Definition src0_eh_frame_hi : Z := 0x12a74.
Definition src0_init_array_lo : Z := 0x226b0.  Definition src0_init_array_hi : Z := 0x226b8.
Definition src0_fini_array_lo : Z := 0x226b8.  Definition src0_fini_array_hi : Z := 0x226c0.
Definition src0_data_rel_ro_lo : Z := 0x226c0.  Definition src0_data_rel_ro_hi : Z := 0x22ca0.
Definition src0_got_lo : Z := 0x22ca0.  Definition src0_got_hi : Z := 0x22d58.
Definition src0_data_lo : Z := 0x23d58.  Definition src0_data_hi : Z := 0x23f64.
Definition src0_bss_lo : Z := 0x23f70.  Definition src0_bss_hi : Z := 0x54f98.

Definition src0_A_do_init : Z := 0x13abc.  Definition src0_E_do_init : Z := 0x13b30.
Definition src0_A_do_fini : Z := 0x13b30.  Definition src0_E_do_fini : Z := 0x13bc0.
Definition src0_A_main : Z := 0x13bc0.  Definition src0_E_main : Z := 0x13e84.
Definition src0_A_target_alloc_init : Z := 0x13e84.  Definition src0_E_target_alloc_init : Z := 0x13e88.
Definition src0_A_target_alloc_count : Z := 0x13e88.  Definition src0_E_target_alloc_count : Z := 0x13e90.
Definition src0_A_target_run : Z := 0x13e90.  Definition src0_E_target_run : Z := 0x13fe8.
Definition src0_A_aef_exit_guard : Z := 0x13fe8.  Definition src0_E_aef_exit_guard : Z := 0x14018.
Definition src0_A_emit_printf : Z := 0x14018.  Definition src0_E_emit_printf : Z := 0x14060.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x14060.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14444.
Definition src0_A_init : Z := 0x18064.  Definition src0_E_init : Z := 0x18068.
Definition src0_A_init_libc : Z := 0x18068.  Definition src0_E_init_libc : Z := 0x18294.
Definition src0_A_libc_start_init : Z := 0x18294.  Definition src0_E_libc_start_init : Z := 0x182e0.
Definition src0_A_libc_start_main : Z := 0x182e0.  Definition src0_E_libc_start_main : Z := 0x18340.
Definition src0_A_libc_start_main_stage2 : Z := 0x18340.  Definition src0_E_libc_start_main_stage2 : Z := 0x18388.
Definition src0_A_init_tls : Z := 0x18388.  Definition src0_E_init_tls : Z := 0x18638.
Definition src0_A_funcs_on_exit : Z := 0x186e8.  Definition src0_E_funcs_on_exit : Z := 0x187b0.
Definition src0_A_cxa_finalize : Z := 0x187b0.  Definition src0_E_cxa_finalize : Z := 0x187b4.
Definition src0_A_atexit : Z := 0x187b4.  Definition src0_E_atexit : Z := 0x18878.
Definition src0_A_atexit_call : Z := 0x18878.  Definition src0_E_atexit_call : Z := 0x1887c.
Definition src0_A_fini : Z := 0x1887c.  Definition src0_E_fini : Z := 0x18880.
Definition src0_A_libc_exit_fini : Z := 0x18880.  Definition src0_E_libc_exit_fini : Z := 0x188cc.
Definition src0_A_exit : Z := 0x188cc.  Definition src0_E_exit : Z := 0x18940.
Definition src0_A_Exit : Z := 0x186cc.  Definition src0_E_Exit : Z := 0x186e8.
Definition src0_A_open : Z := 0x18940.  Definition src0_E_open : Z := 0x18a24.
Definition src0_A_init_ssp : Z := 0x18a24.  Definition src0_E_init_ssp : Z := 0x18a84.
Definition src0_A_stack_chk_fail : Z := 0x18a84.  Definition src0_E_stack_chk_fail : Z := 0x18a8c.
Definition src0_A_syscall_ret : Z := 0x18a8c.  Definition src0_E_syscall_ret : Z := 0x18ac4.
Definition src0_A_errno_location : Z := 0x18ac4.  Definition src0_E_errno_location : Z := 0x18ad0.
Definition src0_A_free : Z := 0x18ad0.  Definition src0_E_free : Z := 0x18ad4.
Definition src0_A_libc_calloc : Z := 0x18ad4.  Definition src0_E_libc_calloc : Z := 0x18c0c.
Definition src0_A_libc_malloc : Z := 0x18c0c.  Definition src0_E_libc_malloc : Z := 0x18c10.
Definition src0_A_malloc : Z := 0x18c10.  Definition src0_E_malloc : Z := 0x18c14.
Definition src0_A_libc_free : Z := 0x18c14.  Definition src0_E_libc_free : Z := 0x18de0.
Definition src0_A_get_meta : Z := 0x18de0.  Definition src0_E_get_meta : Z := 0x18ef0.
Definition src0_A_nontrivial_free : Z := 0x18ef0.  Definition src0_E_nontrivial_free : Z := 0x192c8.
Definition src0_A_alloc_meta : Z := 0x192c8.  Definition src0_E_alloc_meta : Z := 0x195a0.
Definition src0_A_libc_malloc_impl : Z := 0x195a0.  Definition src0_E_libc_malloc_impl : Z := 0x19910.
Definition src0_A_alloc_slot : Z := 0x19910.  Definition src0_E_alloc_slot : Z := 0x1a1b4.
Definition src0_A_enframe : Z := 0x1a1b4.  Definition src0_E_enframe : Z := 0x1a304.
Definition src0_A_malloc_allzerop : Z := 0x1a304.  Definition src0_E_malloc_allzerop : Z := 0x1a47c.
Definition src0_A_vm_wait : Z := 0x1a47c.  Definition src0_E_vm_wait : Z := 0x1a480.
Definition src0_A_mmap : Z := 0x1a480.  Definition src0_E_mmap : Z := 0x1a56c.
Definition src0_A_mprotect : Z := 0x1a56c.  Definition src0_E_mprotect : Z := 0x1a5b4.
Definition src0_A_munmap : Z := 0x1a5b4.  Definition src0_E_munmap : Z := 0x1a5fc.
Definition src0_A_fflush : Z := 0x1a6d0.  Definition src0_E_fflush : Z := 0x1a840.
Definition src0_A_lockfile : Z := 0x1a840.  Definition src0_E_lockfile : Z := 0x1a93c.
Definition src0_A_unlockfile : Z := 0x1a93c.  Definition src0_E_unlockfile : Z := 0x1a99c.
Definition src0_A_stdio_write : Z := 0x1af18.  Definition src0_E_stdio_write : Z := 0x1b0a8.
Definition src0_A_stdio_seek : Z := 0x1b0a8.  Definition src0_E_stdio_seek : Z := 0x1b0b0.
Definition src0_A_aio_close : Z := 0x1aee8.  Definition src0_E_aio_close : Z := 0x1aeec.
Definition src0_A_stdio_close : Z := 0x1aeec.  Definition src0_E_stdio_close : Z := 0x1af18.
Definition src0_A_fprintf : Z := 0x1a99c.  Definition src0_E_fprintf : Z := 0x1aa00.
Definition src0_A_fwritex : Z := 0x1aa00.  Definition src0_E_fwritex : Z := 0x1ab38.
Definition src0_A_fwrite : Z := 0x1ab38.  Definition src0_E_fwrite : Z := 0x1abf0.
Definition src0_A_towrite : Z := 0x1abf0.  Definition src0_E_towrite : Z := 0x1ac44.
Definition src0_A_stdio_exit : Z := 0x1ac44.  Definition src0_E_stdio_exit : Z := 0x1ade8.
Definition src0_A_ofl_lock : Z := 0x1ade8.  Definition src0_E_ofl_lock : Z := 0x1ae18.
Definition src0_A_ofl_unlock : Z := 0x1ae18.  Definition src0_E_ofl_unlock : Z := 0x1ae24.
Definition src0_A_stdout_write : Z := 0x1b0b0.  Definition src0_E_stdout_write : Z := 0x1b150.
Definition src0_A_vfprintf : Z := 0x1b150.  Definition src0_E_vfprintf : Z := 0x1b300.
Definition src0_A_printf_core : Z := 0x1b300.  Definition src0_E_printf_core : Z := 0x1c130.
Definition src0_A_pop_arg : Z := 0x1c130.  Definition src0_E_pop_arg : Z := 0x1c264.
Definition src0_A_pad : Z := 0x1c264.  Definition src0_E_pad : Z := 0x1c338.
Definition src0_A_fmt_fp : Z := 0x1c338.  Definition src0_E_fmt_fp : Z := 0x1da00.
Definition src0_A_strerror : Z := 0x1da00.  Definition src0_E_strerror : Z := 0x1da3c.
Definition src0_A_lctrans_impl : Z := 0x1da3c.  Definition src0_E_lctrans_impl : Z := 0x1da40.
Definition src0_A_lctrans : Z := 0x1da40.  Definition src0_E_lctrans : Z := 0x1da44.
Definition src0_A_wctomb : Z := 0x1da44.  Definition src0_E_wctomb : Z := 0x1da68.
Definition src0_A_wcrtomb : Z := 0x1da68.  Definition src0_E_wcrtomb : Z := 0x1db94.
Definition src0_A_extenddftf2 : Z := 0x1db94.  Definition src0_E_extenddftf2 : Z := 0x1dd24.
Definition src0_A_signbitl : Z := 0x1dd24.  Definition src0_E_signbitl : Z := 0x1dd2c.
Definition src0_A_fpclassifyl : Z := 0x1dd2c.  Definition src0_E_fpclassifyl : Z := 0x1dd70.
Definition src0_A_frexpl : Z := 0x1dd70.  Definition src0_E_frexpl : Z := 0x1de48.
Definition src0_A_letf2 : Z := 0x1de48.  Definition src0_E_letf2 : Z := 0x1df10.
Definition src0_A_multf3 : Z := 0x1df10.  Definition src0_E_multf3 : Z := 0x1e610.
Definition src0_A_floatsitf : Z := 0x1e610.  Definition src0_E_floatsitf : Z := 0x1e718.
Definition src0_A_scalbn : Z := 0x1e718.  Definition src0_E_scalbn : Z := 0x1e7b0.
Definition src0_A_subtf3 : Z := 0x1e7b0.  Definition src0_E_subtf3 : Z := 0x1e7c0.
Definition src0_A_addtf3 : Z := 0x1e7c0.  Definition src0_E_addtf3 : Z := 0x1ef8c.
Definition src0_A_fe_getround : Z := 0x1ef8c.  Definition src0_E_fe_getround : Z := 0x1efbc.
Definition src0_A_fe_raise_inexact : Z := 0x1efbc.  Definition src0_E_fe_raise_inexact : Z := 0x1efc8.
Definition src0_A_fixunstfsi : Z := 0x1efc8.  Definition src0_E_fixunstfsi : Z := 0x1f05c.
Definition src0_A_floatunsitf : Z := 0x1f05c.  Definition src0_E_floatunsitf : Z := 0x1f148.
Definition src0_A_fixtfsi : Z := 0x1f148.  Definition src0_E_fixtfsi : Z := 0x1f1f0.
Definition src0_A_divtf3 : Z := 0x1f1f0.  Definition src0_E_divtf3 : Z := 0x1faf4.
Definition src0_A_vprintf : Z := 0x1faf4.  Definition src0_E_vprintf : Z := 0x1fb10.
Definition src0_A_bcmp : Z := 0x20614.  Definition src0_E_bcmp : Z := 0x20618.
Definition src0_A_memcmp : Z := 0x206e4.  Definition src0_E_memcmp : Z := 0x20714.
Definition src0_A_memcpy : Z := 0x20714.  Definition src0_E_memcpy : Z := 0x20b18.
Definition src0_A_memset : Z := 0x20b18.  Definition src0_E_memset : Z := 0x20c10.
Definition src0_A_strchrnul : Z := 0x20e88.  Definition src0_E_strchrnul : Z := 0x20f68.
Definition src0_A_strlen : Z := 0x20fc0.  Definition src0_E_strlen : Z := 0x21050.
Definition src0_A_strnlen : Z := 0x21110.  Definition src0_E_strnlen : Z := 0x21154.
Definition src0_A_memchr : Z := 0x20618.  Definition src0_E_memchr : Z := 0x206e4.
Definition src0_A_lock : Z := 0x212dc.  Definition src0_E_lock : Z := 0x21564.
Definition src0_A_unlock : Z := 0x21564.  Definition src0_E_unlock : Z := 0x215d8.
Definition src0_A_syscall_cp_c : Z := 0x215d8.  Definition src0_E_syscall_cp_c : Z := 0x215fc.
Definition src0_A_syscall_cp : Z := 0x215fc.  Definition src0_E_syscall_cp : Z := 0x21600.

Definition src0_A_unistd_exit : Z := 0x2160c.  Definition src0_E_unistd_exit : Z := 0x21618.
Definition src0_A_close : Z := 0x21618.  Definition src0_E_close : Z := 0x2166c.
Definition src0_A_lseek : Z := 0x2166c.  Definition src0_E_lseek : Z := 0x21678.
Definition src0_A_read : Z := 0x21678.  Definition src0_E_read : Z := 0x216ac.
Definition src0_D_str_n0X0x : Z := 0x102f6.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x10404.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10443.
Definition src0_D_str_d_n : Z := 0x10457.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10558.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10569.
Definition src0_D_str_inf : Z := 0x10668.
Definition src0_D_str_INF : Z := 0x1075c.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10760.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10912.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10927.
Definition src0_D_str_NAN : Z := 0x1097e.
Definition src0_D_str_nan : Z := 0x109b8.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x109cf.
Definition src0_D_str_dev_null : Z := 0x10a2d.
Definition src0_D_str_null : Z := 0x10a19.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10a58.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10a68.
Definition src0_D_debruijn32 : Z := 0x10be0.
Definition src0_D_size_classes : Z := 0x10c00.
Definition src0_D_small_cnt_tab : Z := 0x10c60.
Definition src0_D_med_cnt_tab : Z := 0x10c7b.
Definition src0_D_states : Z := 0x10dd8.
Definition src0_D_xdigits : Z := 0x10fa8.
Definition src0_D_errmsgstr : Z := 0x10fb8.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11760.
Definition src0_D_fe_getround : Z := 0x11868.
Definition src0_D_EH_FRAME_LIST : Z := 0x11c30.
Definition src0_D_init_array_start : Z := 0x226b0.
Definition src0_D_fini_array_start : Z := 0x226b8.
Definition src0_D_stdout : Z := 0x22c98.
Definition src0_D_got_DYNAMIC : Z := 0x22ca8.
Definition src0_D_got_main : Z := 0x22cb0.
Definition src0_D_got_init : Z := 0x22cb8.
Definition src0_D_got_fini : Z := 0x22cc0.
Definition src0_D_got_register_frame_info : Z := 0x22cc8.
Definition src0_D_got_cxa_finalize : Z := 0x22cd0.
Definition src0_D_got_deregister_frame_info : Z := 0x22cd8.
Definition src0_D_got_stderr : Z := 0x22ce0.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x22ce8.
Definition src0_D_got_stdout : Z := 0x22cf0.
Definition src0_D_got_environ : Z := 0x22d18.
Definition src0_D_got_progname_full : Z := 0x22d20.
Definition src0_D_got_progname : Z := 0x22d28.
Definition src0_D_got_init_array_end : Z := 0x22d30.
Definition src0_D_got_init_array_start : Z := 0x22d38.
Definition src0_D_got_stack_chk_guard : Z := 0x22d40.
Definition src0_D_got_fini_array_end : Z := 0x22d48.
Definition src0_D_got_fini_array_start : Z := 0x22d50.
Definition src0_D_dso_handle : Z := 0x23d58.
Definition src0_D_aef_argc : Z := 0x23d68.
Definition src0_D_stderr_FILE : Z := 0x23d80.
Definition src0_D_stderr_used : Z := 0x23e68.
Definition src0_D_stdout_FILE : Z := 0x23e70.
Definition src0_D_stdout_used : Z := 0x23f58.
Definition src0_D_default_stacksize : Z := 0x23f60.
Definition src0_D_do_init_initialized : Z := 0x23f70.
Definition src0_D_do_init_object : Z := 0x23f78.
Definition src0_D_do_fini_finalized : Z := 0x23fb8.
Definition src0_D_read_stage : Z := 0x23fb9.
Definition src0_D_target_run_initialized : Z := 0x33fc0.
Definition src0_D_aef_in_callback : Z := 0x33fc4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x33fd0.
Definition src0_D_environ : Z := 0x343f0.
Definition src0_D_thread_list_lock : Z := 0x544c8.
Definition src0_D_main_tls : Z := 0x544d0.
Definition src0_D_builtin_tls : Z := 0x343f8.
Definition src0_D_finished_atexit : Z := 0x54508.
Definition src0_D_atexit_lock : Z := 0x5450c.
Definition src0_D_atexit_slot : Z := 0x54510.
Definition src0_D_atexit_head : Z := 0x54518.
Definition src0_D_atexit_builtin : Z := 0x54520.
Definition src0_D_exit_exit_lock : Z := 0x54728.
Definition src0_D_stack_chk_guard : Z := 0x54730.
Definition src0_D_sysinfo : Z := 0x54738.
Definition src0_D_progname : Z := 0x54740.
Definition src0_D_progname_full : Z := 0x54748.
Definition src0_D_libc : Z := 0x54750.
Definition src0_D_hwcap : Z := 0x547b8.
Definition src0_D_malloc_lock : Z := 0x547c0.
Definition src0_D_malloc_context : Z := 0x547c8.
Definition src0_D_malloc_replaced : Z := 0x54b68.
Definition src0_D_stdin_used : Z := 0x54b70.
Definition src0_D_ofl_lock : Z := 0x54b78.
Definition src0_D_ofl_head : Z := 0x54b80.
Definition src0_D_stderr_buf : Z := 0x54b88.
Definition src0_D_stdout_buf : Z := 0x54b90.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
