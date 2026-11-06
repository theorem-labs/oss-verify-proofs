(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x1312c.  Definition src0_text_hi : Z := 0x22ef8.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11254.
Definition src0_eh_frame_lo : Z := 0x114c0.  Definition src0_eh_frame_hi : Z := 0x1212c.
Definition src0_init_array_lo : Z := 0x23ef8.  Definition src0_init_array_hi : Z := 0x23f00.
Definition src0_fini_array_lo : Z := 0x23f00.  Definition src0_fini_array_hi : Z := 0x23f08.
Definition src0_data_rel_ro_lo : Z := 0x23f08.  Definition src0_data_rel_ro_hi : Z := 0x23f18.
Definition src0_got_lo : Z := 0x23f18.  Definition src0_got_hi : Z := 0x23fb0.
Definition src0_data_lo : Z := 0x24fb0.  Definition src0_data_hi : Z := 0x251cc.
Definition src0_bss_lo : Z := 0x251d0.  Definition src0_bss_hi : Z := 0x55e20.
Definition src0_A_do_init : Z := 0x13174.  Definition src0_E_do_init : Z := 0x131e8.
Definition src0_A_do_fini : Z := 0x131e8.  Definition src0_E_do_fini : Z := 0x13278.
Definition src0_A_main : Z := 0x13278.  Definition src0_E_main : Z := 0x1353c.
Definition src0_A_target_alloc_init : Z := 0x1353c.  Definition src0_E_target_alloc_init : Z := 0x13540.
Definition src0_A_target_alloc_count : Z := 0x13540.  Definition src0_E_target_alloc_count : Z := 0x13548.
Definition src0_A_target_run : Z := 0x13548.  Definition src0_E_target_run : Z := 0x136a0.
Definition src0_A_emit_printf : Z := 0x136d0.  Definition src0_E_emit_printf : Z := 0x13718.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13718.
Definition src0_A_init : Z := 0x177e4.  Definition src0_E_init : Z := 0x177e8.
Definition src0_A_init_libc : Z := 0x177e8.  Definition src0_E_init_libc : Z := 0x17a14.
Definition src0_A_libc_start_init : Z := 0x17a14.  Definition src0_E_libc_start_init : Z := 0x17a60.
Definition src0_A_libc_start_main : Z := 0x17a60.  Definition src0_E_libc_start_main : Z := 0x17ac0.
Definition src0_A_libc_start_main_stage2 : Z := 0x17ac0.  Definition src0_E_libc_start_main_stage2 : Z := 0x17b08.
Definition src0_A_init_tls : Z := 0x17b08.  Definition src0_E_init_tls : Z := 0x17db8.
Definition src0_A_funcs_on_exit : Z := 0x17e68.  Definition src0_E_funcs_on_exit : Z := 0x17f30.
Definition src0_A_cxa_finalize : Z := 0x17f30.  Definition src0_E_cxa_finalize : Z := 0x17f34.
Definition src0_A_atexit : Z := 0x17f34.  Definition src0_E_atexit : Z := 0x17ff8.
Definition src0_A_fini : Z := 0x17ffc.  Definition src0_E_fini : Z := 0x18000.
Definition src0_A_libc_exit_fini : Z := 0x18000.  Definition src0_E_libc_exit_fini : Z := 0x1804c.
Definition src0_A_exit : Z := 0x1804c.  Definition src0_E_exit : Z := 0x180c0.
Definition src0_A_Exit : Z := 0x17e4c.  Definition src0_E_Exit : Z := 0x17e68.
Definition src0_A_open : Z := 0x180c0.  Definition src0_E_open : Z := 0x181a4.
Definition src0_A_init_ssp : Z := 0x181a4.  Definition src0_E_init_ssp : Z := 0x18204.
Definition src0_A_stack_chk_fail : Z := 0x18204.  Definition src0_E_stack_chk_fail : Z := 0x1820c.
Definition src0_A_syscall_ret : Z := 0x1820c.  Definition src0_E_syscall_ret : Z := 0x18244.
Definition src0_A_errno_location : Z := 0x18244.  Definition src0_E_errno_location : Z := 0x18250.
Definition src0_A_free : Z := 0x18250.  Definition src0_E_free : Z := 0x18254.
Definition src0_A_libc_calloc : Z := 0x18254.  Definition src0_E_libc_calloc : Z := 0x1838c.
Definition src0_A_libc_malloc : Z := 0x1838c.  Definition src0_E_libc_malloc : Z := 0x18390.
Definition src0_A_malloc : Z := 0x18390.  Definition src0_E_malloc : Z := 0x18394.
Definition src0_A_libc_free : Z := 0x18394.  Definition src0_E_libc_free : Z := 0x18560.
Definition src0_A_get_meta : Z := 0x18560.  Definition src0_E_get_meta : Z := 0x18670.
Definition src0_A_nontrivial_free : Z := 0x18670.  Definition src0_E_nontrivial_free : Z := 0x18a48.
Definition src0_A_alloc_meta : Z := 0x18a48.  Definition src0_E_alloc_meta : Z := 0x18d20.
Definition src0_A_libc_malloc_impl : Z := 0x18d20.  Definition src0_E_libc_malloc_impl : Z := 0x19090.
Definition src0_A_alloc_slot : Z := 0x19090.  Definition src0_E_alloc_slot : Z := 0x19934.
Definition src0_A_enframe : Z := 0x19934.  Definition src0_E_enframe : Z := 0x19a84.
Definition src0_A_malloc_allzerop : Z := 0x19a84.  Definition src0_E_malloc_allzerop : Z := 0x19bfc.
Definition src0_A_vm_wait : Z := 0x1a040.  Definition src0_E_vm_wait : Z := 0x1a044.
Definition src0_A_mmap : Z := 0x1a044.  Definition src0_E_mmap : Z := 0x1a130.
Definition src0_A_mprotect : Z := 0x1a130.  Definition src0_E_mprotect : Z := 0x1a178.
Definition src0_A_munmap : Z := 0x1a24c.  Definition src0_E_munmap : Z := 0x1a294.
Definition src0_A_fflush : Z := 0x1a4c4.  Definition src0_E_fflush : Z := 0x1a634.
Definition src0_A_lockfile : Z := 0x1a368.  Definition src0_E_lockfile : Z := 0x1a464.
Definition src0_A_unlockfile : Z := 0x1a464.  Definition src0_E_unlockfile : Z := 0x1a4c4.
Definition src0_A_aio_close : Z := 0x1a7cc.  Definition src0_E_aio_close : Z := 0x1a7d0.
Definition src0_A_fprintf : Z := 0x1a7fc.  Definition src0_E_fprintf : Z := 0x1a860.
Definition src0_A_fwritex : Z := 0x1aa98.  Definition src0_E_fwritex : Z := 0x1abd0.
Definition src0_A_fwrite : Z := 0x1abd0.  Definition src0_E_fwrite : Z := 0x1ac88.
Definition src0_A_towrite : Z := 0x1ac88.  Definition src0_E_towrite : Z := 0x1acdc.
Definition src0_A_stdio_exit : Z := 0x1a8f4.  Definition src0_E_stdio_exit : Z := 0x1aa98.
Definition src0_A_ofl_lock : Z := 0x1acdc.  Definition src0_E_ofl_lock : Z := 0x1ad0c.
Definition src0_A_ofl_unlock : Z := 0x1ad0c.  Definition src0_E_ofl_unlock : Z := 0x1ad18.
Definition src0_A_stdout_write : Z := 0x1ad78.  Definition src0_E_stdout_write : Z := 0x1ae18.
Definition src0_A_vfprintf : Z := 0x1ae18.  Definition src0_E_vfprintf : Z := 0x1afc8.
Definition src0_A_printf_core : Z := 0x1afc8.  Definition src0_E_printf_core : Z := 0x1bdf8.
Definition src0_A_pop_arg : Z := 0x1bdf8.  Definition src0_E_pop_arg : Z := 0x1bf2c.
Definition src0_A_pad : Z := 0x1bf2c.  Definition src0_E_pad : Z := 0x1c000.
Definition src0_A_fmt_fp : Z := 0x1c000.  Definition src0_E_fmt_fp : Z := 0x1d6c8.
Definition src0_A_strerror : Z := 0x1d6c8.  Definition src0_E_strerror : Z := 0x1d704.
Definition src0_A_lctrans_impl : Z := 0x1d704.  Definition src0_E_lctrans_impl : Z := 0x1d708.
Definition src0_A_lctrans : Z := 0x1d708.  Definition src0_E_lctrans : Z := 0x1d70c.
Definition src0_A_wctomb : Z := 0x1d70c.  Definition src0_E_wctomb : Z := 0x1d730.
Definition src0_A_wcrtomb : Z := 0x1d730.  Definition src0_E_wcrtomb : Z := 0x1d85c.
Definition src0_A_extenddftf2 : Z := 0x1d85c.  Definition src0_E_extenddftf2 : Z := 0x1d9ec.
Definition src0_A_signbitl : Z := 0x1d9ec.  Definition src0_E_signbitl : Z := 0x1d9f4.
Definition src0_A_fpclassifyl : Z := 0x1d9f4.  Definition src0_E_fpclassifyl : Z := 0x1da38.
Definition src0_A_frexpl : Z := 0x1da38.  Definition src0_E_frexpl : Z := 0x1db10.
Definition src0_A_letf2 : Z := 0x1db10.  Definition src0_E_letf2 : Z := 0x1dbd8.
Definition src0_A_multf3 : Z := 0x1dc94.  Definition src0_E_multf3 : Z := 0x1e394.
Definition src0_A_floatsitf : Z := 0x1e394.  Definition src0_E_floatsitf : Z := 0x1e49c.
Definition src0_A_scalbn : Z := 0x1e49c.  Definition src0_E_scalbn : Z := 0x1e534.
Definition src0_A_subtf3 : Z := 0x1e534.  Definition src0_E_subtf3 : Z := 0x1e544.
Definition src0_A_addtf3 : Z := 0x1e544.  Definition src0_E_addtf3 : Z := 0x1ed10.
Definition src0_A_fe_getround : Z := 0x1ed10.  Definition src0_E_fe_getround : Z := 0x1ed40.
Definition src0_A_fe_raise_inexact : Z := 0x1ed40.  Definition src0_E_fe_raise_inexact : Z := 0x1ed4c.
Definition src0_A_fixunstfsi : Z := 0x1ed4c.  Definition src0_E_fixunstfsi : Z := 0x1ede0.
Definition src0_A_floatunsitf : Z := 0x1ede0.  Definition src0_E_floatunsitf : Z := 0x1eecc.
Definition src0_A_fixtfsi : Z := 0x1eecc.  Definition src0_E_fixtfsi : Z := 0x1ef74.
Definition src0_A_divtf3 : Z := 0x1ef74.  Definition src0_E_divtf3 : Z := 0x1f878.
Definition src0_A_vprintf : Z := 0x1f878.  Definition src0_E_vprintf : Z := 0x1f894.
Definition src0_A_bcmp : Z := 0x22420.  Definition src0_E_bcmp : Z := 0x22424.
Definition src0_A_memcmp : Z := 0x224f0.  Definition src0_E_memcmp : Z := 0x22520.
Definition src0_A_memcpy : Z := 0x22520.  Definition src0_E_memcpy : Z := 0x22924.
Definition src0_A_memset : Z := 0x22924.  Definition src0_E_memset : Z := 0x22a1c.
Definition src0_A_strlen : Z := 0x22a54.  Definition src0_E_strlen : Z := 0x22ae4.
Definition src0_A_strnlen : Z := 0x22ae4.  Definition src0_E_strnlen : Z := 0x22b28.
Definition src0_A_memchr : Z := 0x22424.  Definition src0_E_memchr : Z := 0x224f0.
Definition src0_A_lock : Z := 0x22b28.  Definition src0_E_lock : Z := 0x22db0.
Definition src0_A_unlock : Z := 0x22db0.  Definition src0_E_unlock : Z := 0x22e24.
Definition src0_A_syscall_cp_c : Z := 0x22e24.  Definition src0_E_syscall_cp_c : Z := 0x22e48.
Definition src0_A_syscall_cp : Z := 0x22e48.  Definition src0_E_syscall_cp : Z := 0x22e4c.
Definition src0_A_close : Z := 0x22e64.  Definition src0_E_close : Z := 0x22eb8.
Definition src0_A_lseek : Z := 0x22eb8.  Definition src0_E_lseek : Z := 0x22ec4.
Definition src0_A_read : Z := 0x22ec4.  Definition src0_E_read : Z := 0x22ef8.
Definition src0_D_str_n0X0x : Z := 0x1029e.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102bd.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102d0.
Definition src0_D_str_d_n : Z := 0x102e4.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10302.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10313.
Definition src0_D_str_inf : Z := 0x10337.
Definition src0_D_str_INF : Z := 0x1035e.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10362.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103a7.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103bc.
Definition src0_D_str_NAN : Z := 0x103e8.
Definition src0_D_str_nan : Z := 0x103ec.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x103f3.
Definition src0_D_str_dev_null : Z := 0x10426.
Definition src0_D_str_null : Z := 0x10430.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10768.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10778.
Definition src0_D_debruijn32 : Z := 0x10554.
Definition src0_D_size_classes : Z := 0x10574.
Definition src0_D_small_cnt_tab : Z := 0x105d4.
Definition src0_D_med_cnt_tab : Z := 0x105ef.
Definition src0_D_jt_printf_core_1 : Z := 0x10608.
Definition src0_D_jt_printf_core_2 : Z := 0x106e8.
Definition src0_D_jt_pop_arg : Z := 0x10708.
Definition src0_D_states : Z := 0x107b8.
Definition src0_D_xdigits : Z := 0x10988.
Definition src0_D_errmsgstr : Z := 0x10998.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11140.
Definition src0_D_fe_getround : Z := 0x11248.
Definition src0_D_EH_FRAME_LIST : Z := 0x114c0.
Definition src0_D_init_array_start : Z := 0x23ef8.
Definition src0_D_fini_array_start : Z := 0x23f00.
Definition src0_D_stderr : Z := 0x23f08.
Definition src0_D_stdout : Z := 0x23f10.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x23f18.
Definition src0_D_got_DYNAMIC : Z := 0x23f20.
Definition src0_D_got_main : Z := 0x23f28.
Definition src0_D_got_init : Z := 0x23f30.
Definition src0_D_got_fini : Z := 0x23f38.
Definition src0_D_got_register_frame_info : Z := 0x23f40.
Definition src0_D_got_cxa_finalize : Z := 0x23f48.
Definition src0_D_got_deregister_frame_info : Z := 0x23f50.
Definition src0_D_got_stderr : Z := 0x23f58.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x23f60.
Definition src0_D_got_stdout : Z := 0x23f68.
Definition src0_D_got_environ : Z := 0x23f70.
Definition src0_D_got_progname_full : Z := 0x23f78.
Definition src0_D_got_progname : Z := 0x23f80.
Definition src0_D_got_init_array_end : Z := 0x23f88.
Definition src0_D_got_init_array_start : Z := 0x23f90.
Definition src0_D_got_stack_chk_guard : Z := 0x23f98.
Definition src0_D_got_fini_array_end : Z := 0x23fa0.
Definition src0_D_got_fini_array_start : Z := 0x23fa8.
Definition src0_D_dso_handle : Z := 0x24fb0.
Definition src0_D_aef_argc : Z := 0x24fc0.
Definition src0_D_stderr_FILE : Z := 0x24fe8.
Definition src0_D_stderr_used : Z := 0x250d0.
Definition src0_D_stdout_FILE : Z := 0x250d8.
Definition src0_D_stdout_used : Z := 0x251c0.
Definition src0_D_default_stacksize : Z := 0x251c8.
Definition src0_D_do_init_initialized : Z := 0x251d0.
Definition src0_D_do_init_object : Z := 0x251d8.
Definition src0_D_do_fini_finalized : Z := 0x25218.
Definition src0_D_read_stage : Z := 0x25219.
Definition src0_D_target_run_initialized : Z := 0x35220.
Definition src0_D_aef_in_callback : Z := 0x35224.
Definition src0_D_aef_aligned_copy_empty : Z := 0x35230.
Definition src0_D_environ : Z := 0x35278.
Definition src0_D_thread_list_lock : Z := 0x55350.
Definition src0_D_main_tls : Z := 0x55358.
Definition src0_D_builtin_tls : Z := 0x35280.
Definition src0_D_finished_atexit : Z := 0x55390.
Definition src0_D_atexit_lock : Z := 0x55394.
Definition src0_D_atexit_slot : Z := 0x55398.
Definition src0_D_atexit_head : Z := 0x553a0.
Definition src0_D_atexit_builtin : Z := 0x553a8.
Definition src0_D_exit_exit_lock : Z := 0x555b0.
Definition src0_D_stack_chk_guard : Z := 0x555b8.
Definition src0_D_sysinfo : Z := 0x555c0.
Definition src0_D_progname : Z := 0x555c8.
Definition src0_D_progname_full : Z := 0x555d0.
Definition src0_D_libc : Z := 0x555d8.
Definition src0_D_hwcap : Z := 0x55640.
Definition src0_D_malloc_lock : Z := 0x55648.
Definition src0_D_malloc_context : Z := 0x55650.
Definition src0_D_malloc_replaced : Z := 0x559f0.
Definition src0_D_stdin_used : Z := 0x559f8.
Definition src0_D_ofl_lock : Z := 0x55a00.
Definition src0_D_ofl_head : Z := 0x55a08.
Definition src0_D_stderr_buf : Z := 0x55a10.
Definition src0_D_stdout_buf : Z := 0x55a18.
Definition src0_A_realloc : Z := 0x19bfc.  Definition src0_E_realloc : Z := 0x19c00.
Definition src0_A_mremap : Z := 0x1a178.  Definition src0_E_mremap : Z := 0x1a24c.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
