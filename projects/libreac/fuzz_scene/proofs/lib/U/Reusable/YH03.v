(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x148f8.  Definition src0_text_hi : Z := 0x1e2b4.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x133ec.
Definition src0_eh_frame_lo : Z := 0x134e0.  Definition src0_eh_frame_hi : Z := 0x138f8.
Definition src0_init_array_lo : Z := 0x1f2b8.  Definition src0_init_array_hi : Z := 0x1f2c0.
Definition src0_fini_array_lo : Z := 0x1f2c0.  Definition src0_fini_array_hi : Z := 0x1f2c8.
Definition src0_data_rel_ro_lo : Z := 0x1f2c8.  Definition src0_data_rel_ro_hi : Z := 0x1f2d8.
Definition src0_got_lo : Z := 0x1f2d8.  Definition src0_got_hi : Z := 0x1f378.
Definition src0_data_lo : Z := 0x20378.  Definition src0_data_hi : Z := 0x20584.
Definition src0_bss_lo : Z := 0x20590.  Definition src0_bss_hi : Z := 0x511b8.
Definition src0_A_do_init : Z := 0x14940.  Definition src0_E_do_init : Z := 0x149b4.
Definition src0_A_do_fini : Z := 0x149b4.  Definition src0_E_do_fini : Z := 0x14a44.
Definition src0_A_main : Z := 0x14a44.  Definition src0_E_main : Z := 0x14d08.
Definition src0_A_target_alloc_init : Z := 0x14d08.  Definition src0_E_target_alloc_init : Z := 0x14d0c.
Definition src0_A_target_alloc_count : Z := 0x14d0c.  Definition src0_E_target_alloc_count : Z := 0x14d14.
Definition src0_A_target_run : Z := 0x14d14.  Definition src0_E_target_run : Z := 0x14e6c.
Definition src0_A_aef_exit_guard : Z := 0x14e6c.  Definition src0_E_aef_exit_guard : Z := 0x14e9c.
Definition src0_A_emit_printf : Z := 0x14e9c.  Definition src0_E_emit_printf : Z := 0x14ee4.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x14ee4.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x15520.
Definition src0_A_init : Z := 0x15ebc.  Definition src0_E_init : Z := 0x15ec0.
Definition src0_A_init_libc : Z := 0x15ec0.  Definition src0_E_init_libc : Z := 0x160ec.
Definition src0_A_libc_start_init : Z := 0x160ec.  Definition src0_E_libc_start_init : Z := 0x16138.
Definition src0_A_libc_start_main : Z := 0x16138.  Definition src0_E_libc_start_main : Z := 0x16198.
Definition src0_A_libc_start_main_stage2 : Z := 0x16198.  Definition src0_E_libc_start_main_stage2 : Z := 0x161e0.
Definition src0_A_init_tls : Z := 0x161e0.  Definition src0_E_init_tls : Z := 0x16490.
Definition src0_A_funcs_on_exit : Z := 0x16540.  Definition src0_E_funcs_on_exit : Z := 0x16608.
Definition src0_A_cxa_finalize : Z := 0x16608.  Definition src0_E_cxa_finalize : Z := 0x1660c.
Definition src0_A_atexit : Z := 0x1660c.  Definition src0_E_atexit : Z := 0x166d0.
Definition src0_A_atexit_call : Z := 0x166d0.  Definition src0_E_atexit_call : Z := 0x166d4.
Definition src0_A_fini : Z := 0x166d4.  Definition src0_E_fini : Z := 0x166d8.
Definition src0_A_libc_exit_fini : Z := 0x166d8.  Definition src0_E_libc_exit_fini : Z := 0x16724.
Definition src0_A_exit : Z := 0x16724.  Definition src0_E_exit : Z := 0x16798.
Definition src0_A_Exit : Z := 0x16524.  Definition src0_E_Exit : Z := 0x16540.
Definition src0_A_open : Z := 0x16798.  Definition src0_E_open : Z := 0x1687c.
Definition src0_A_init_ssp : Z := 0x1687c.  Definition src0_E_init_ssp : Z := 0x168dc.
Definition src0_A_stack_chk_fail : Z := 0x168dc.  Definition src0_E_stack_chk_fail : Z := 0x168e4.
Definition src0_A_syscall_ret : Z := 0x168e4.  Definition src0_E_syscall_ret : Z := 0x1691c.
Definition src0_A_errno_location : Z := 0x1691c.  Definition src0_E_errno_location : Z := 0x16928.
Definition src0_A_free : Z := 0x16928.  Definition src0_E_free : Z := 0x1692c.
Definition src0_A_libc_calloc : Z := 0x1692c.  Definition src0_E_libc_calloc : Z := 0x16a64.
Definition src0_A_libc_malloc : Z := 0x16a64.  Definition src0_E_libc_malloc : Z := 0x16a68.
Definition src0_A_malloc : Z := 0x16a68.  Definition src0_E_malloc : Z := 0x16a6c.
Definition src0_A_libc_free : Z := 0x16a6c.  Definition src0_E_libc_free : Z := 0x16c38.
Definition src0_A_get_meta : Z := 0x16c38.  Definition src0_E_get_meta : Z := 0x16d48.
Definition src0_A_nontrivial_free : Z := 0x16d48.  Definition src0_E_nontrivial_free : Z := 0x17120.
Definition src0_A_alloc_meta : Z := 0x17120.  Definition src0_E_alloc_meta : Z := 0x173f8.
Definition src0_A_libc_malloc_impl : Z := 0x173f8.  Definition src0_E_libc_malloc_impl : Z := 0x17768.
Definition src0_A_alloc_slot : Z := 0x17768.  Definition src0_E_alloc_slot : Z := 0x1800c.
Definition src0_A_enframe : Z := 0x1800c.  Definition src0_E_enframe : Z := 0x1815c.
Definition src0_A_malloc_allzerop : Z := 0x1815c.  Definition src0_E_malloc_allzerop : Z := 0x182d4.
Definition src0_A_vm_wait : Z := 0x182d4.  Definition src0_E_vm_wait : Z := 0x182d8.
Definition src0_A_mmap : Z := 0x182d8.  Definition src0_E_mmap : Z := 0x183c4.
Definition src0_A_mprotect : Z := 0x183c4.  Definition src0_E_mprotect : Z := 0x1840c.
Definition src0_A_munmap : Z := 0x1840c.  Definition src0_E_munmap : Z := 0x18454.
Definition src0_A_fflush : Z := 0x18528.  Definition src0_E_fflush : Z := 0x18698.
Definition src0_A_lockfile : Z := 0x18698.  Definition src0_E_lockfile : Z := 0x18794.
Definition src0_A_unlockfile : Z := 0x18794.  Definition src0_E_unlockfile : Z := 0x187f4.
Definition src0_A_stdio_write : Z := 0x18cac.  Definition src0_E_stdio_write : Z := 0x18e3c.
Definition src0_A_stdio_seek : Z := 0x18e3c.  Definition src0_E_stdio_seek : Z := 0x18e44.
Definition src0_A_aio_close : Z := 0x18c7c.  Definition src0_E_aio_close : Z := 0x18c80.
Definition src0_A_stdio_close : Z := 0x18c80.  Definition src0_E_stdio_close : Z := 0x18cac.
Definition src0_A_fprintf : Z := 0x187f4.  Definition src0_E_fprintf : Z := 0x18858.
Definition src0_A_fwritex : Z := 0x18858.  Definition src0_E_fwritex : Z := 0x18990.
Definition src0_A_fwrite : Z := 0x18990.  Definition src0_E_fwrite : Z := 0x18a48.
Definition src0_A_towrite : Z := 0x18a48.  Definition src0_E_towrite : Z := 0x18a9c.
Definition src0_A_stdio_exit : Z := 0x18a9c.  Definition src0_E_stdio_exit : Z := 0x18c40.
Definition src0_A_ofl_lock : Z := 0x18c40.  Definition src0_E_ofl_lock : Z := 0x18c70.
Definition src0_A_ofl_unlock : Z := 0x18c70.  Definition src0_E_ofl_unlock : Z := 0x18c7c.
Definition src0_A_stdout_write : Z := 0x18e44.  Definition src0_E_stdout_write : Z := 0x18ee4.
Definition src0_A_vfprintf : Z := 0x18ee4.  Definition src0_E_vfprintf : Z := 0x19094.
Definition src0_A_printf_core : Z := 0x19094.  Definition src0_E_printf_core : Z := 0x19ec4.
Definition src0_A_pop_arg : Z := 0x19ec4.  Definition src0_E_pop_arg : Z := 0x19ff8.
Definition src0_A_pad : Z := 0x19ff8.  Definition src0_E_pad : Z := 0x1a0cc.
Definition src0_A_fmt_fp : Z := 0x1a0cc.  Definition src0_E_fmt_fp : Z := 0x1b794.
Definition src0_A_strerror : Z := 0x1b794.  Definition src0_E_strerror : Z := 0x1b7d0.
Definition src0_A_lctrans_impl : Z := 0x1b7d0.  Definition src0_E_lctrans_impl : Z := 0x1b7d4.
Definition src0_A_lctrans : Z := 0x1b7d4.  Definition src0_E_lctrans : Z := 0x1b7d8.
Definition src0_A_wctomb : Z := 0x1b7d8.  Definition src0_E_wctomb : Z := 0x1b7fc.
Definition src0_A_wcrtomb : Z := 0x1b7fc.  Definition src0_E_wcrtomb : Z := 0x1b928.
Definition src0_A_extenddftf2 : Z := 0x1b928.  Definition src0_E_extenddftf2 : Z := 0x1bab8.
Definition src0_A_signbitl : Z := 0x1bab8.  Definition src0_E_signbitl : Z := 0x1bac0.
Definition src0_A_fpclassifyl : Z := 0x1bac0.  Definition src0_E_fpclassifyl : Z := 0x1bb04.
Definition src0_A_frexpl : Z := 0x1bb04.  Definition src0_E_frexpl : Z := 0x1bbdc.
Definition src0_A_letf2 : Z := 0x1bbdc.  Definition src0_E_letf2 : Z := 0x1bca4.
Definition src0_A_multf3 : Z := 0x1bca4.  Definition src0_E_multf3 : Z := 0x1c3a4.
Definition src0_A_floatsitf : Z := 0x1c3a4.  Definition src0_E_floatsitf : Z := 0x1c4ac.
Definition src0_A_scalbn : Z := 0x1c4ac.  Definition src0_E_scalbn : Z := 0x1c544.
Definition src0_A_subtf3 : Z := 0x1c544.  Definition src0_E_subtf3 : Z := 0x1c554.
Definition src0_A_addtf3 : Z := 0x1c554.  Definition src0_E_addtf3 : Z := 0x1cd20.
Definition src0_A_fe_getround : Z := 0x1cd20.  Definition src0_E_fe_getround : Z := 0x1cd50.
Definition src0_A_fe_raise_inexact : Z := 0x1cd50.  Definition src0_E_fe_raise_inexact : Z := 0x1cd5c.
Definition src0_A_fixunstfsi : Z := 0x1cd5c.  Definition src0_E_fixunstfsi : Z := 0x1cdf0.
Definition src0_A_floatunsitf : Z := 0x1cdf0.  Definition src0_E_floatunsitf : Z := 0x1cedc.
Definition src0_A_fixtfsi : Z := 0x1cedc.  Definition src0_E_fixtfsi : Z := 0x1cf84.
Definition src0_A_divtf3 : Z := 0x1cf84.  Definition src0_E_divtf3 : Z := 0x1d888.
Definition src0_A_vprintf : Z := 0x1d888.  Definition src0_E_vprintf : Z := 0x1d8a4.
Definition src0_A_bcmp : Z := 0x1d8a4.  Definition src0_E_bcmp : Z := 0x1d8a8.
Definition src0_A_memcmp : Z := 0x1d8a8.  Definition src0_E_memcmp : Z := 0x1d8d8.
Definition src0_A_memcpy : Z := 0x1d8d8.  Definition src0_E_memcpy : Z := 0x1dcdc.
Definition src0_A_memset : Z := 0x1dcdc.  Definition src0_E_memset : Z := 0x1ddd4.
Definition src0_A_strnlen : Z := 0x1ddd4.  Definition src0_E_strnlen : Z := 0x1de18.
Definition src0_A_memchr : Z := 0x1de18.  Definition src0_E_memchr : Z := 0x1dee4.
Definition src0_A_lock : Z := 0x1dee4.  Definition src0_E_lock : Z := 0x1e16c.
Definition src0_A_unlock : Z := 0x1e16c.  Definition src0_E_unlock : Z := 0x1e1e0.
Definition src0_A_syscall_cp_c : Z := 0x1e1e0.  Definition src0_E_syscall_cp_c : Z := 0x1e204.
Definition src0_A_syscall_cp : Z := 0x1e204.  Definition src0_E_syscall_cp : Z := 0x1e208.
Definition src0_A_unistd_exit : Z := 0x1e214.  Definition src0_E_unistd_exit : Z := 0x1e220.
Definition src0_A_close : Z := 0x1e220.  Definition src0_E_close : Z := 0x1e274.
Definition src0_A_lseek : Z := 0x1e274.  Definition src0_E_lseek : Z := 0x1e280.
Definition src0_A_read : Z := 0x1e280.  Definition src0_E_read : Z := 0x1e2b4.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b5.
Definition src0_D_str_d_n : Z := 0x102c9.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d0.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e1.
Definition src0_D_str_inf : Z := 0x10301.
Definition src0_D_str_INF : Z := 0x10305.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10309.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1032a.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x1033f.
Definition src0_D_str_NAN : Z := 0x1035d.
Definition src0_D_str_nan : Z := 0x10361.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10365.
Definition src0_D_str_dev_null : Z := 0x10385.
Definition src0_D_str_null : Z := 0x1038f.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x12910.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x12920.
Definition src0_D_debruijn32 : Z := 0x12704.
Definition src0_D_size_classes : Z := 0x12724.
Definition src0_D_small_cnt_tab : Z := 0x12784.
Definition src0_D_med_cnt_tab : Z := 0x1279f.
Definition src0_D_states : Z := 0x12950.
Definition src0_D_xdigits : Z := 0x12b20.
Definition src0_D_errmsgstr : Z := 0x12b30.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x132d8.
Definition src0_D_fe_getround : Z := 0x133e0.
Definition src0_D_EH_FRAME_LIST : Z := 0x134e0.
Definition src0_D_init_array_start : Z := 0x1f2b8.
Definition src0_D_fini_array_start : Z := 0x1f2c0.
Definition src0_D_stderr : Z := 0x1f2c8.
Definition src0_D_stdout : Z := 0x1f2d0.
Definition src0_D_got_DYNAMIC : Z := 0x1f2e0.
Definition src0_D_got_main : Z := 0x1f2e8.
Definition src0_D_got_init : Z := 0x1f2f0.
Definition src0_D_got_fini : Z := 0x1f2f8.
Definition src0_D_got_register_frame_info : Z := 0x1f300.
Definition src0_D_got_cxa_finalize : Z := 0x1f308.
Definition src0_D_got_deregister_frame_info : Z := 0x1f310.
Definition src0_D_got_stderr : Z := 0x1f318.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1f320.
Definition src0_D_got_stdout : Z := 0x1f328.
Definition src0_D_got_environ : Z := 0x1f338.
Definition src0_D_got_progname_full : Z := 0x1f340.
Definition src0_D_got_progname : Z := 0x1f348.
Definition src0_D_got_init_array_end : Z := 0x1f350.
Definition src0_D_got_init_array_start : Z := 0x1f358.
Definition src0_D_got_stack_chk_guard : Z := 0x1f360.
Definition src0_D_got_fini_array_end : Z := 0x1f368.
Definition src0_D_got_fini_array_start : Z := 0x1f370.
Definition src0_D_dso_handle : Z := 0x20378.
Definition src0_D_aef_argc : Z := 0x20388.
Definition src0_D_stderr_FILE : Z := 0x203a0.
Definition src0_D_stderr_used : Z := 0x20488.
Definition src0_D_stdout_FILE : Z := 0x20490.
Definition src0_D_stdout_used : Z := 0x20578.
Definition src0_D_default_stacksize : Z := 0x20580.
Definition src0_D_do_init_initialized : Z := 0x20590.
Definition src0_D_do_init_object : Z := 0x20598.
Definition src0_D_do_fini_finalized : Z := 0x205d8.
Definition src0_D_read_stage : Z := 0x205d9.
Definition src0_D_target_run_initialized : Z := 0x305e0.
Definition src0_D_aef_in_callback : Z := 0x305e4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x305f0.
Definition src0_D_environ : Z := 0x30610.
Definition src0_D_thread_list_lock : Z := 0x506e8.
Definition src0_D_main_tls : Z := 0x506f0.
Definition src0_D_builtin_tls : Z := 0x30618.
Definition src0_D_finished_atexit : Z := 0x50728.
Definition src0_D_atexit_lock : Z := 0x5072c.
Definition src0_D_atexit_slot : Z := 0x50730.
Definition src0_D_atexit_head : Z := 0x50738.
Definition src0_D_atexit_builtin : Z := 0x50740.
Definition src0_D_exit_exit_lock : Z := 0x50948.
Definition src0_D_stack_chk_guard : Z := 0x50950.
Definition src0_D_sysinfo : Z := 0x50958.
Definition src0_D_progname : Z := 0x50960.
Definition src0_D_progname_full : Z := 0x50968.
Definition src0_D_libc : Z := 0x50970.
Definition src0_D_hwcap : Z := 0x509d8.
Definition src0_D_malloc_lock : Z := 0x509e0.
Definition src0_D_malloc_context : Z := 0x509e8.
Definition src0_D_malloc_replaced : Z := 0x50d88.
Definition src0_D_stdin_used : Z := 0x50d90.
Definition src0_D_ofl_lock : Z := 0x50d98.
Definition src0_D_ofl_head : Z := 0x50da0.
Definition src0_D_stderr_buf : Z := 0x50da8.
Definition src0_D_stdout_buf : Z := 0x50db0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
