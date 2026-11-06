(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x131d8.  Definition src0_text_hi : Z := 0x1fa94.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1181e.
Definition src0_eh_frame_lo : Z := 0x119e0.  Definition src0_eh_frame_hi : Z := 0x121d8.
Definition src0_init_array_lo : Z := 0x20a98.  Definition src0_init_array_hi : Z := 0x20aa0.
Definition src0_fini_array_lo : Z := 0x20aa0.  Definition src0_fini_array_hi : Z := 0x20aa8.
Definition src0_data_rel_ro_lo : Z := 0x20aa8.  Definition src0_data_rel_ro_hi : Z := 0x21798.
Definition src0_got_lo : Z := 0x21798.  Definition src0_got_hi : Z := 0x21830.
Definition src0_data_lo : Z := 0x22830.  Definition src0_data_hi : Z := 0x22a3c.
Definition src0_bss_lo : Z := 0x22a40.  Definition src0_bss_hi : Z := 0x536e8.
Definition src0_A_start : Z := 0x131d8.  Definition src0_E_start : Z := 0x13220.
Definition src0_A_do_init : Z := 0x13220.  Definition src0_E_do_init : Z := 0x13294.
Definition src0_A_do_fini : Z := 0x13294.  Definition src0_E_do_fini : Z := 0x13324.
Definition src0_A_main : Z := 0x13324.  Definition src0_E_main : Z := 0x135e8.
Definition src0_A_target_alloc_init : Z := 0x135e8.  Definition src0_E_target_alloc_init : Z := 0x135ec.
Definition src0_A_target_alloc_count : Z := 0x135ec.  Definition src0_E_target_alloc_count : Z := 0x135f4.
Definition src0_A_target_run : Z := 0x135f4.  Definition src0_E_target_run : Z := 0x1374c.
Definition src0_A_aef_exit_guard : Z := 0x1374c.  Definition src0_E_aef_exit_guard : Z := 0x1377c.
Definition src0_A_emit_printf : Z := 0x1377c.  Definition src0_E_emit_printf : Z := 0x137c4.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x137c4.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x13fb4.
Definition src0_A_init : Z := 0x15e54.  Definition src0_E_init : Z := 0x15e58.
Definition src0_A_init_libc : Z := 0x15e58.  Definition src0_E_init_libc : Z := 0x16084.
Definition src0_A_libc_start_init : Z := 0x16084.  Definition src0_E_libc_start_init : Z := 0x160d0.
Definition src0_A_libc_start_main : Z := 0x160d0.  Definition src0_E_libc_start_main : Z := 0x16130.
Definition src0_A_libc_start_main_stage2 : Z := 0x16130.  Definition src0_E_libc_start_main_stage2 : Z := 0x16178.
Definition src0_A_init_tls : Z := 0x16178.  Definition src0_E_init_tls : Z := 0x16428.
Definition src0_A_funcs_on_exit : Z := 0x16520.  Definition src0_E_funcs_on_exit : Z := 0x165e8.
Definition src0_A_cxa_finalize : Z := 0x165e8.  Definition src0_E_cxa_finalize : Z := 0x165ec.
Definition src0_A_atexit : Z := 0x165ec.  Definition src0_E_atexit : Z := 0x166b0.
Definition src0_A_atexit_call : Z := 0x166b0.  Definition src0_E_atexit_call : Z := 0x166b4.
Definition src0_A_fini : Z := 0x166b4.  Definition src0_E_fini : Z := 0x166b8.
Definition src0_A_libc_exit_fini : Z := 0x166b8.  Definition src0_E_libc_exit_fini : Z := 0x16704.
Definition src0_A_exit : Z := 0x16704.  Definition src0_E_exit : Z := 0x16778.
Definition src0_A_Exit : Z := 0x16504.  Definition src0_E_Exit : Z := 0x16520.
Definition src0_A_open : Z := 0x16778.  Definition src0_E_open : Z := 0x1685c.
Definition src0_A_init_ssp : Z := 0x1685c.  Definition src0_E_init_ssp : Z := 0x168bc.
Definition src0_A_stack_chk_fail : Z := 0x168bc.  Definition src0_E_stack_chk_fail : Z := 0x168c4.
Definition src0_A_syscall_ret : Z := 0x168c4.  Definition src0_E_syscall_ret : Z := 0x168fc.
Definition src0_A_errno_location : Z := 0x16428.  Definition src0_E_errno_location : Z := 0x16434.
Definition src0_A_free : Z := 0x16a3c.  Definition src0_E_free : Z := 0x16a40.
Definition src0_A_libc_calloc : Z := 0x16a40.  Definition src0_E_libc_calloc : Z := 0x16b78.
Definition src0_A_libc_malloc : Z := 0x16b78.  Definition src0_E_libc_malloc : Z := 0x16b7c.
Definition src0_A_malloc : Z := 0x16b7c.  Definition src0_E_malloc : Z := 0x16b80.
Definition src0_A_libc_free : Z := 0x16b80.  Definition src0_E_libc_free : Z := 0x16d4c.
Definition src0_A_get_meta : Z := 0x16d4c.  Definition src0_E_get_meta : Z := 0x16e5c.
Definition src0_A_nontrivial_free : Z := 0x16e5c.  Definition src0_E_nontrivial_free : Z := 0x17234.
Definition src0_A_alloc_meta : Z := 0x17234.  Definition src0_E_alloc_meta : Z := 0x1750c.
Definition src0_A_libc_malloc_impl : Z := 0x1750c.  Definition src0_E_libc_malloc_impl : Z := 0x1787c.
Definition src0_A_alloc_slot : Z := 0x1787c.  Definition src0_E_alloc_slot : Z := 0x18120.
Definition src0_A_enframe : Z := 0x18120.  Definition src0_E_enframe : Z := 0x18270.
Definition src0_A_malloc_allzerop : Z := 0x18270.  Definition src0_E_malloc_allzerop : Z := 0x183e8.
Definition src0_A_vm_wait : Z := 0x183e8.  Definition src0_E_vm_wait : Z := 0x183ec.
Definition src0_A_mmap : Z := 0x183ec.  Definition src0_E_mmap : Z := 0x184d8.
Definition src0_A_mprotect : Z := 0x184d8.  Definition src0_E_mprotect : Z := 0x18520.
Definition src0_A_munmap : Z := 0x18520.  Definition src0_E_munmap : Z := 0x18568.
Definition src0_A_fflush : Z := 0x1863c.  Definition src0_E_fflush : Z := 0x187ac.
Definition src0_A_lockfile : Z := 0x187ac.  Definition src0_E_lockfile : Z := 0x188a8.
Definition src0_A_unlockfile : Z := 0x188a8.  Definition src0_E_unlockfile : Z := 0x18908.
Definition src0_A_stdio_write : Z := 0x18bcc.  Definition src0_E_stdio_write : Z := 0x18d5c.
Definition src0_A_aio_close : Z := 0x18d64.  Definition src0_E_aio_close : Z := 0x18d68.
Definition src0_A_stdio_close : Z := 0x18d68.  Definition src0_E_stdio_close : Z := 0x18d94.
Definition src0_A_fprintf : Z := 0x18d94.  Definition src0_E_fprintf : Z := 0x18df8.
Definition src0_A_fwritex : Z := 0x18df8.  Definition src0_E_fwritex : Z := 0x18f30.
Definition src0_A_fwrite : Z := 0x18f30.  Definition src0_E_fwrite : Z := 0x18fe8.
Definition src0_A_towrite : Z := 0x18fe8.  Definition src0_E_towrite : Z := 0x1903c.
Definition src0_A_stdio_exit : Z := 0x18a28.  Definition src0_E_stdio_exit : Z := 0x18bcc.
Definition src0_A_ofl_lock : Z := 0x1903c.  Definition src0_E_ofl_lock : Z := 0x1906c.
Definition src0_A_ofl_unlock : Z := 0x1906c.  Definition src0_E_ofl_unlock : Z := 0x19078.
Definition src0_A_stdout_write : Z := 0x190d8.  Definition src0_E_stdout_write : Z := 0x19178.
Definition src0_A_vfprintf : Z := 0x19178.  Definition src0_E_vfprintf : Z := 0x19328.
Definition src0_A_printf_core : Z := 0x19328.  Definition src0_E_printf_core : Z := 0x1a158.
Definition src0_A_pop_arg : Z := 0x1a158.  Definition src0_E_pop_arg : Z := 0x1a28c.
Definition src0_A_pad : Z := 0x1a28c.  Definition src0_E_pad : Z := 0x1a360.
Definition src0_A_fmt_fp : Z := 0x1a360.  Definition src0_E_fmt_fp : Z := 0x1ba28.
Definition src0_A_strerror : Z := 0x16434.  Definition src0_E_strerror : Z := 0x16470.
Definition src0_A_lctrans_impl : Z := 0x168fc.  Definition src0_E_lctrans_impl : Z := 0x16900.
Definition src0_A_lctrans : Z := 0x16900.  Definition src0_E_lctrans : Z := 0x16904.
Definition src0_A_wctomb : Z := 0x1ba28.  Definition src0_E_wctomb : Z := 0x1ba4c.
Definition src0_A_wcrtomb : Z := 0x1ba4c.  Definition src0_E_wcrtomb : Z := 0x1bb78.
Definition src0_A_extenddftf2 : Z := 0x1bb78.  Definition src0_E_extenddftf2 : Z := 0x1bd08.
Definition src0_A_signbitl : Z := 0x1bd08.  Definition src0_E_signbitl : Z := 0x1bd10.
Definition src0_A_fpclassifyl : Z := 0x1bd10.  Definition src0_E_fpclassifyl : Z := 0x1bd54.
Definition src0_A_frexpl : Z := 0x1bd54.  Definition src0_E_frexpl : Z := 0x1be2c.
Definition src0_A_letf2 : Z := 0x1be2c.  Definition src0_E_letf2 : Z := 0x1bef4.
Definition src0_A_multf3 : Z := 0x1bef4.  Definition src0_E_multf3 : Z := 0x1c5f4.
Definition src0_A_floatsitf : Z := 0x1c5f4.  Definition src0_E_floatsitf : Z := 0x1c6fc.
Definition src0_A_scalbn : Z := 0x1c6fc.  Definition src0_E_scalbn : Z := 0x1c794.
Definition src0_A_subtf3 : Z := 0x1c794.  Definition src0_E_subtf3 : Z := 0x1c7a4.
Definition src0_A_addtf3 : Z := 0x1c7a4.  Definition src0_E_addtf3 : Z := 0x1cf70.
Definition src0_A_fe_getround : Z := 0x1cf70.  Definition src0_E_fe_getround : Z := 0x1cfa0.
Definition src0_A_fe_raise_inexact : Z := 0x1cfa0.  Definition src0_E_fe_raise_inexact : Z := 0x1cfac.
Definition src0_A_fixunstfsi : Z := 0x1cfac.  Definition src0_E_fixunstfsi : Z := 0x1d040.
Definition src0_A_floatunsitf : Z := 0x1d040.  Definition src0_E_floatunsitf : Z := 0x1d12c.
Definition src0_A_fixtfsi : Z := 0x1d12c.  Definition src0_E_fixtfsi : Z := 0x1d1d4.
Definition src0_A_divtf3 : Z := 0x1d1d4.  Definition src0_E_divtf3 : Z := 0x1dad8.
Definition src0_A_vprintf : Z := 0x1dad8.  Definition src0_E_vprintf : Z := 0x1daf4.
Definition src0_A_bcmp : Z := 0x1e42c.  Definition src0_E_bcmp : Z := 0x1e430.
Definition src0_A_memcmp : Z := 0x1e4fc.  Definition src0_E_memcmp : Z := 0x1e52c.
Definition src0_A_memcpy : Z := 0x1e52c.  Definition src0_E_memcpy : Z := 0x1e930.
Definition src0_A_memset : Z := 0x1e930.  Definition src0_E_memset : Z := 0x1ea28.
Definition src0_A_strchr : Z := 0x1eadc.  Definition src0_E_strchr : Z := 0x1eb18.
Definition src0_A_strchrnul : Z := 0x1eb18.  Definition src0_E_strchrnul : Z := 0x1ebf8.
Definition src0_A_strlen : Z := 0x1ec30.  Definition src0_E_strlen : Z := 0x1ecc0.
Definition src0_A_strnlen : Z := 0x1ef1c.  Definition src0_E_strnlen : Z := 0x1ef60.
Definition src0_A_memchr : Z := 0x1e430.  Definition src0_E_memchr : Z := 0x1e4fc.
Definition src0_A_lock : Z := 0x1f6c4.  Definition src0_E_lock : Z := 0x1f94c.
Definition src0_A_unlock : Z := 0x1f94c.  Definition src0_E_unlock : Z := 0x1f9c0.
Definition src0_A_syscall_cp_c : Z := 0x1f9c0.  Definition src0_E_syscall_cp_c : Z := 0x1f9e4.
Definition src0_A_syscall_cp : Z := 0x1f9e4.  Definition src0_E_syscall_cp : Z := 0x1f9e8.
Definition src0_A_set_thread_area : Z := 0x1f9e8.  Definition src0_E_set_thread_area : Z := 0x1f9f4.
Definition src0_A_unistd_exit : Z := 0x1f9f4.  Definition src0_E_unistd_exit : Z := 0x1fa00.
Definition src0_A_close : Z := 0x1fa00.  Definition src0_E_close : Z := 0x1fa54.
Definition src0_A_lseek : Z := 0x1fa54.  Definition src0_E_lseek : Z := 0x1fa60.
Definition src0_A_read : Z := 0x1fa60.  Definition src0_E_read : Z := 0x1fa94.
Definition src0_D_str_n0X0x : Z := 0x102f9.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x10363.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10376.
Definition src0_D_str_d_n : Z := 0x1038a.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x103b3.
Definition src0_D_str_cli_config_len_overruns : Z := 0x103c4.
Definition src0_D_str_inf : Z := 0x104dc.
Definition src0_D_str_INF : Z := 0x10585.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10589.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10852.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10867.
Definition src0_D_str_NAN : Z := 0x108c0.
Definition src0_D_str_nan : Z := 0x108c9.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x108d1.
Definition src0_D_str_dev_null : Z := 0x10999.
Definition src0_D_str_null : Z := 0x109a3.
Definition src0_D_const_double_0x1p28 : Z := 0x109b0.
Definition src0_D_const_double_1_0 : Z := 0x109c0.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x109c8.
Definition src0_D_const_double_0_5 : Z := 0x109d0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x109d8.
Definition src0_D_const_double_0x1p1023 : Z := 0x109e0.
Definition src0_D_const_double_1_5 : Z := 0x109e8.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x109f0.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x109f8.
Definition src0_D_const_double_0x1p120 : Z := 0x10a00.
Definition src0_D_debruijn32 : Z := 0x11330.
Definition src0_D_size_classes : Z := 0x11350.
Definition src0_D_small_cnt_tab : Z := 0x113b0.
Definition src0_D_med_cnt_tab : Z := 0x113cb.
Definition src0_D_jt_printf_core_1 : Z := 0x113e0.
Definition src0_D_jt_printf_core_2 : Z := 0x114c0.
Definition src0_D_jt_pop_arg : Z := 0x114e0.
Definition src0_D_states : Z := 0x11528.
Definition src0_D_xdigits : Z := 0x116f8.
Definition src0_D_errmsgstr : Z := 0x10a80.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11228.
Definition src0_D_fe_getround : Z := 0x11708.
Definition src0_D_EH_FRAME_LIST : Z := 0x119e0.
Definition src0_D_init_array_start : Z := 0x20a98.
Definition src0_D_fini_array_start : Z := 0x20aa0.
Definition src0_D_stderr : Z := 0x21788.
Definition src0_D_stdout : Z := 0x21790.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x21798.
Definition src0_D_got_DYNAMIC : Z := 0x217a0.
Definition src0_D_got_main : Z := 0x217a8.
Definition src0_D_got_init : Z := 0x217b0.
Definition src0_D_got_fini : Z := 0x217b8.
Definition src0_D_got_register_frame_info : Z := 0x217c0.
Definition src0_D_got_cxa_finalize : Z := 0x217c8.
Definition src0_D_got_deregister_frame_info : Z := 0x217d0.
Definition src0_D_got_stderr : Z := 0x217d8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x217e0.
Definition src0_D_got_stdout : Z := 0x217e8.
Definition src0_D_got_environ : Z := 0x217f0.
Definition src0_D_got_progname_full : Z := 0x217f8.
Definition src0_D_got_progname : Z := 0x21800.
Definition src0_D_got_init_array_end : Z := 0x21808.
Definition src0_D_got_init_array_start : Z := 0x21810.
Definition src0_D_got_stack_chk_guard : Z := 0x21818.
Definition src0_D_got_fini_array_end : Z := 0x21820.
Definition src0_D_got_fini_array_start : Z := 0x21828.
Definition src0_D_dso_handle : Z := 0x22830.
Definition src0_D_aef_arg0 : Z := 0x22838.
Definition src0_D_aef_argc : Z := 0x22840.
Definition src0_D_aef_argv : Z := 0x22848.
Definition src0_D_stderr_FILE : Z := 0x22858.
Definition src0_D_stderr_used : Z := 0x22940.
Definition src0_D_stdout_FILE : Z := 0x22948.
Definition src0_D_stdout_used : Z := 0x22a30.
Definition src0_D_default_stacksize : Z := 0x22a38.
Definition src0_D_do_init_initialized : Z := 0x22a40.
Definition src0_D_do_init_object : Z := 0x22a48.
Definition src0_D_do_fini_finalized : Z := 0x22a88.
Definition src0_D_read_stage : Z := 0x22a89.
Definition src0_D_target_run_initialized : Z := 0x32a90.
Definition src0_D_aef_in_callback : Z := 0x32a94.
Definition src0_D_aef_aligned_copy_empty : Z := 0x32aa0.
Definition src0_D_environ : Z := 0x32b40.
Definition src0_D_thread_list_lock : Z := 0x52c18.
Definition src0_D_main_tls : Z := 0x52c20.
Definition src0_D_builtin_tls : Z := 0x32b48.
Definition src0_D_finished_atexit : Z := 0x52c58.
Definition src0_D_atexit_lock : Z := 0x52c5c.
Definition src0_D_atexit_slot : Z := 0x52c60.
Definition src0_D_atexit_head : Z := 0x52c68.
Definition src0_D_atexit_builtin : Z := 0x52c70.
Definition src0_D_exit_exit_lock : Z := 0x52e78.
Definition src0_D_stack_chk_guard : Z := 0x52e80.
Definition src0_D_sysinfo : Z := 0x52e88.
Definition src0_D_progname : Z := 0x52e90.
Definition src0_D_progname_full : Z := 0x52e98.
Definition src0_D_libc : Z := 0x52ea0.
Definition src0_D_hwcap : Z := 0x52f08.
Definition src0_D_malloc_lock : Z := 0x52f10.
Definition src0_D_malloc_context : Z := 0x52f18.
Definition src0_D_malloc_replaced : Z := 0x532b8.
Definition src0_D_stdin_used : Z := 0x532c0.
Definition src0_D_ofl_lock : Z := 0x532c8.
Definition src0_D_ofl_head : Z := 0x532d0.
Definition src0_D_stderr_buf : Z := 0x532d8.
Definition src0_D_stdout_buf : Z := 0x532e0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
