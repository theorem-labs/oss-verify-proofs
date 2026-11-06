(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x124f0.  Definition src0_text_hi : Z := 0x1b1dc.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x110d4.
Definition src0_eh_frame_lo : Z := 0x111a0.  Definition src0_eh_frame_hi : Z := 0x114f0.
Definition src0_init_array_lo : Z := 0x1c1e0.  Definition src0_init_array_hi : Z := 0x1c1e8.
Definition src0_fini_array_lo : Z := 0x1c1e8.  Definition src0_fini_array_hi : Z := 0x1c1f0.
Definition src0_data_rel_ro_lo : Z := 0x1c1f0.  Definition src0_data_rel_ro_hi : Z := 0x1c200.
Definition src0_got_lo : Z := 0x1c200.  Definition src0_got_hi : Z := 0x1c298.
Definition src0_data_lo : Z := 0x1d298.  Definition src0_data_hi : Z := 0x1d4a4.
Definition src0_bss_lo : Z := 0x1d4b0.  Definition src0_bss_hi : Z := 0x4e0d8.
Definition src0_A_start : Z := 0x124f0.  Definition src0_E_start : Z := 0x12538.
Definition src0_A_do_init : Z := 0x12538.  Definition src0_E_do_init : Z := 0x125ac.
Definition src0_A_do_fini : Z := 0x125ac.  Definition src0_E_do_fini : Z := 0x1263c.
Definition src0_A_main : Z := 0x1263c.  Definition src0_E_main : Z := 0x12900.
Definition src0_A_target_alloc_init : Z := 0x12900.  Definition src0_E_target_alloc_init : Z := 0x12904.
Definition src0_A_target_alloc_count : Z := 0x12904.  Definition src0_E_target_alloc_count : Z := 0x1290c.
Definition src0_A_target_run : Z := 0x1290c.  Definition src0_E_target_run : Z := 0x12a64.
Definition src0_A_aef_exit_guard : Z := 0x12a64.  Definition src0_E_aef_exit_guard : Z := 0x12a94.
Definition src0_A_emit_printf : Z := 0x12a94.  Definition src0_E_emit_printf : Z := 0x12adc.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12adc.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x12d50.
Definition src0_A_init : Z := 0x12e18.  Definition src0_E_init : Z := 0x12e1c.
Definition src0_A_init_libc : Z := 0x12e1c.  Definition src0_E_init_libc : Z := 0x13048.
Definition src0_A_libc_start_init : Z := 0x13048.  Definition src0_E_libc_start_init : Z := 0x13094.
Definition src0_A_libc_start_main : Z := 0x13094.  Definition src0_E_libc_start_main : Z := 0x130f4.
Definition src0_A_libc_start_main_stage2 : Z := 0x130f4.  Definition src0_E_libc_start_main_stage2 : Z := 0x1313c.
Definition src0_A_init_tls : Z := 0x1313c.  Definition src0_E_init_tls : Z := 0x133ec.
Definition src0_A_funcs_on_exit : Z := 0x1349c.  Definition src0_E_funcs_on_exit : Z := 0x13564.
Definition src0_A_cxa_finalize : Z := 0x13564.  Definition src0_E_cxa_finalize : Z := 0x13568.
Definition src0_A_atexit : Z := 0x13568.  Definition src0_E_atexit : Z := 0x1362c.
Definition src0_A_atexit_call : Z := 0x1362c.  Definition src0_E_atexit_call : Z := 0x13630.
Definition src0_A_fini : Z := 0x13630.  Definition src0_E_fini : Z := 0x13634.
Definition src0_A_libc_exit_fini : Z := 0x13634.  Definition src0_E_libc_exit_fini : Z := 0x13680.
Definition src0_A_exit : Z := 0x13680.  Definition src0_E_exit : Z := 0x136f4.
Definition src0_A_Exit : Z := 0x13480.  Definition src0_E_Exit : Z := 0x1349c.
Definition src0_A_open : Z := 0x136f4.  Definition src0_E_open : Z := 0x137d8.
Definition src0_A_init_ssp : Z := 0x137d8.  Definition src0_E_init_ssp : Z := 0x13838.
Definition src0_A_stack_chk_fail : Z := 0x13838.  Definition src0_E_stack_chk_fail : Z := 0x13840.
Definition src0_A_syscall_ret : Z := 0x13840.  Definition src0_E_syscall_ret : Z := 0x13878.
Definition src0_A_errno_location : Z := 0x13878.  Definition src0_E_errno_location : Z := 0x13884.
Definition src0_A_free : Z := 0x13884.  Definition src0_E_free : Z := 0x13888.
Definition src0_A_libc_calloc : Z := 0x13888.  Definition src0_E_libc_calloc : Z := 0x139c0.
Definition src0_A_libc_malloc : Z := 0x139c0.  Definition src0_E_libc_malloc : Z := 0x139c4.
Definition src0_A_malloc : Z := 0x139c4.  Definition src0_E_malloc : Z := 0x139c8.
Definition src0_A_libc_free : Z := 0x139c8.  Definition src0_E_libc_free : Z := 0x13b94.
Definition src0_A_get_meta : Z := 0x13b94.  Definition src0_E_get_meta : Z := 0x13ca4.
Definition src0_A_nontrivial_free : Z := 0x13ca4.  Definition src0_E_nontrivial_free : Z := 0x1407c.
Definition src0_A_alloc_meta : Z := 0x1407c.  Definition src0_E_alloc_meta : Z := 0x14354.
Definition src0_A_libc_malloc_impl : Z := 0x14354.  Definition src0_E_libc_malloc_impl : Z := 0x146c4.
Definition src0_A_alloc_slot : Z := 0x146c4.  Definition src0_E_alloc_slot : Z := 0x14f68.
Definition src0_A_enframe : Z := 0x14f68.  Definition src0_E_enframe : Z := 0x150b8.
Definition src0_A_malloc_allzerop : Z := 0x150b8.  Definition src0_E_malloc_allzerop : Z := 0x15230.
Definition src0_A_vm_wait : Z := 0x15230.  Definition src0_E_vm_wait : Z := 0x15234.
Definition src0_A_mmap : Z := 0x15234.  Definition src0_E_mmap : Z := 0x15320.
Definition src0_A_mprotect : Z := 0x15320.  Definition src0_E_mprotect : Z := 0x15368.
Definition src0_A_munmap : Z := 0x15368.  Definition src0_E_munmap : Z := 0x153b0.
Definition src0_A_fflush : Z := 0x15484.  Definition src0_E_fflush : Z := 0x155f4.
Definition src0_A_lockfile : Z := 0x155f4.  Definition src0_E_lockfile : Z := 0x156f0.
Definition src0_A_unlockfile : Z := 0x156f0.  Definition src0_E_unlockfile : Z := 0x15750.
Definition src0_A_stdio_write : Z := 0x15c08.  Definition src0_E_stdio_write : Z := 0x15d98.
Definition src0_A_stdio_seek : Z := 0x15d98.  Definition src0_E_stdio_seek : Z := 0x15da0.
Definition src0_A_aio_close : Z := 0x15bd8.  Definition src0_E_aio_close : Z := 0x15bdc.
Definition src0_A_stdio_close : Z := 0x15bdc.  Definition src0_E_stdio_close : Z := 0x15c08.
Definition src0_A_fprintf : Z := 0x15750.  Definition src0_E_fprintf : Z := 0x157b4.
Definition src0_A_fwritex : Z := 0x157b4.  Definition src0_E_fwritex : Z := 0x158ec.
Definition src0_A_fwrite : Z := 0x158ec.  Definition src0_E_fwrite : Z := 0x159a4.
Definition src0_A_towrite : Z := 0x159a4.  Definition src0_E_towrite : Z := 0x159f8.
Definition src0_A_stdio_exit : Z := 0x159f8.  Definition src0_E_stdio_exit : Z := 0x15b9c.
Definition src0_A_ofl_lock : Z := 0x15b9c.  Definition src0_E_ofl_lock : Z := 0x15bcc.
Definition src0_A_ofl_unlock : Z := 0x15bcc.  Definition src0_E_ofl_unlock : Z := 0x15bd8.
Definition src0_A_stdout_write : Z := 0x15da0.  Definition src0_E_stdout_write : Z := 0x15e40.
Definition src0_A_vfprintf : Z := 0x15e40.  Definition src0_E_vfprintf : Z := 0x15ff0.
Definition src0_A_printf_core : Z := 0x15ff0.  Definition src0_E_printf_core : Z := 0x16e20.
Definition src0_A_pop_arg : Z := 0x16e20.  Definition src0_E_pop_arg : Z := 0x16f54.
Definition src0_A_pad : Z := 0x16f54.  Definition src0_E_pad : Z := 0x17028.
Definition src0_A_fmt_fp : Z := 0x17028.  Definition src0_E_fmt_fp : Z := 0x186f0.
Definition src0_A_strerror : Z := 0x186f0.  Definition src0_E_strerror : Z := 0x1872c.
Definition src0_A_lctrans_impl : Z := 0x1872c.  Definition src0_E_lctrans_impl : Z := 0x18730.
Definition src0_A_lctrans : Z := 0x18730.  Definition src0_E_lctrans : Z := 0x18734.
Definition src0_A_wctomb : Z := 0x18734.  Definition src0_E_wctomb : Z := 0x18758.
Definition src0_A_wcrtomb : Z := 0x18758.  Definition src0_E_wcrtomb : Z := 0x18884.
Definition src0_A_extenddftf2 : Z := 0x18884.  Definition src0_E_extenddftf2 : Z := 0x18a14.
Definition src0_A_signbitl : Z := 0x18a14.  Definition src0_E_signbitl : Z := 0x18a1c.
Definition src0_A_fpclassifyl : Z := 0x18a1c.  Definition src0_E_fpclassifyl : Z := 0x18a60.
Definition src0_A_frexpl : Z := 0x18a60.  Definition src0_E_frexpl : Z := 0x18b38.
Definition src0_A_letf2 : Z := 0x18b38.  Definition src0_E_letf2 : Z := 0x18c00.
Definition src0_A_multf3 : Z := 0x18c00.  Definition src0_E_multf3 : Z := 0x19300.
Definition src0_A_floatsitf : Z := 0x19300.  Definition src0_E_floatsitf : Z := 0x19408.
Definition src0_A_scalbn : Z := 0x19408.  Definition src0_E_scalbn : Z := 0x194a0.
Definition src0_A_subtf3 : Z := 0x194a0.  Definition src0_E_subtf3 : Z := 0x194b0.
Definition src0_A_addtf3 : Z := 0x194b0.  Definition src0_E_addtf3 : Z := 0x19c7c.
Definition src0_A_fe_getround : Z := 0x19c7c.  Definition src0_E_fe_getround : Z := 0x19cac.
Definition src0_A_fe_raise_inexact : Z := 0x19cac.  Definition src0_E_fe_raise_inexact : Z := 0x19cb8.
Definition src0_A_fixunstfsi : Z := 0x19cb8.  Definition src0_E_fixunstfsi : Z := 0x19d4c.
Definition src0_A_floatunsitf : Z := 0x19d4c.  Definition src0_E_floatunsitf : Z := 0x19e38.
Definition src0_A_fixtfsi : Z := 0x19e38.  Definition src0_E_fixtfsi : Z := 0x19ee0.
Definition src0_A_divtf3 : Z := 0x19ee0.  Definition src0_E_divtf3 : Z := 0x1a7e4.
Definition src0_A_vprintf : Z := 0x1a7e4.  Definition src0_E_vprintf : Z := 0x1a800.
Definition src0_A_memcpy : Z := 0x1a800.  Definition src0_E_memcpy : Z := 0x1ac04.
Definition src0_A_memset : Z := 0x1ac04.  Definition src0_E_memset : Z := 0x1acfc.
Definition src0_A_strnlen : Z := 0x1acfc.  Definition src0_E_strnlen : Z := 0x1ad40.
Definition src0_A_memchr : Z := 0x1ad40.  Definition src0_E_memchr : Z := 0x1ae0c.
Definition src0_A_lock : Z := 0x1ae0c.  Definition src0_E_lock : Z := 0x1b094.
Definition src0_A_unlock : Z := 0x1b094.  Definition src0_E_unlock : Z := 0x1b108.
Definition src0_A_syscall_cp_c : Z := 0x1b108.  Definition src0_E_syscall_cp_c : Z := 0x1b12c.
Definition src0_A_syscall_cp : Z := 0x1b12c.  Definition src0_E_syscall_cp : Z := 0x1b130.
Definition src0_A_set_thread_area : Z := 0x1b130.  Definition src0_E_set_thread_area : Z := 0x1b13c.
Definition src0_A_unistd_exit : Z := 0x1b13c.  Definition src0_E_unistd_exit : Z := 0x1b148.
Definition src0_A_close : Z := 0x1b148.  Definition src0_E_close : Z := 0x1b19c.
Definition src0_A_lseek : Z := 0x1b19c.  Definition src0_E_lseek : Z := 0x1b1a8.
Definition src0_A_read : Z := 0x1b1a8.  Definition src0_E_read : Z := 0x1b1dc.
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
Definition src0_D_str_NAN : Z := 0x10356.
Definition src0_D_str_nan : Z := 0x1035a.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1035e.
Definition src0_D_str_dev_null : Z := 0x1037e.
Definition src0_D_str_null : Z := 0x10388.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x105f8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10608.
Definition src0_D_debruijn32 : Z := 0x103eb.
Definition src0_D_size_classes : Z := 0x1040c.
Definition src0_D_small_cnt_tab : Z := 0x1046c.
Definition src0_D_med_cnt_tab : Z := 0x10487.
Definition src0_D_states : Z := 0x10638.
Definition src0_D_xdigits : Z := 0x10808.
Definition src0_D_errmsgstr : Z := 0x10818.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x10fc0.
Definition src0_D_fe_getround : Z := 0x110c8.
Definition src0_D_EH_FRAME_LIST : Z := 0x111a0.
Definition src0_D_init_array_start : Z := 0x1c1e0.
Definition src0_D_fini_array_start : Z := 0x1c1e8.
Definition src0_D_stderr : Z := 0x1c1f0.
Definition src0_D_stdout : Z := 0x1c1f8.
Definition src0_D_got_DYNAMIC : Z := 0x1c208.
Definition src0_D_got_main : Z := 0x1c210.
Definition src0_D_got_init : Z := 0x1c218.
Definition src0_D_got_fini : Z := 0x1c220.
Definition src0_D_got_register_frame_info : Z := 0x1c228.
Definition src0_D_got_cxa_finalize : Z := 0x1c230.
Definition src0_D_got_deregister_frame_info : Z := 0x1c238.
Definition src0_D_got_stderr : Z := 0x1c240.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1c248.
Definition src0_D_got_stdout : Z := 0x1c250.
Definition src0_D_got_environ : Z := 0x1c258.
Definition src0_D_got_progname_full : Z := 0x1c260.
Definition src0_D_got_progname : Z := 0x1c268.
Definition src0_D_got_init_array_end : Z := 0x1c270.
Definition src0_D_got_init_array_start : Z := 0x1c278.
Definition src0_D_got_stack_chk_guard : Z := 0x1c280.
Definition src0_D_got_fini_array_end : Z := 0x1c288.
Definition src0_D_got_fini_array_start : Z := 0x1c290.
Definition src0_D_dso_handle : Z := 0x1d298.
Definition src0_D_aef_argc : Z := 0x1d2a8.
Definition src0_D_stderr_FILE : Z := 0x1d2c0.
Definition src0_D_stderr_used : Z := 0x1d3a8.
Definition src0_D_stdout_FILE : Z := 0x1d3b0.
Definition src0_D_stdout_used : Z := 0x1d498.
Definition src0_D_default_stacksize : Z := 0x1d4a0.
Definition src0_D_do_init_initialized : Z := 0x1d4b0.
Definition src0_D_do_init_object : Z := 0x1d4b8.
Definition src0_D_do_fini_finalized : Z := 0x1d4f8.
Definition src0_D_read_stage : Z := 0x1d4f9.
Definition src0_D_target_run_initialized : Z := 0x2d500.
Definition src0_D_aef_in_callback : Z := 0x2d504.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2d510.
Definition src0_D_environ : Z := 0x2d530.
Definition src0_D_thread_list_lock : Z := 0x4d608.
Definition src0_D_main_tls : Z := 0x4d610.
Definition src0_D_builtin_tls : Z := 0x2d538.
Definition src0_D_finished_atexit : Z := 0x4d648.
Definition src0_D_atexit_lock : Z := 0x4d64c.
Definition src0_D_atexit_slot : Z := 0x4d650.
Definition src0_D_atexit_head : Z := 0x4d658.
Definition src0_D_atexit_builtin : Z := 0x4d660.
Definition src0_D_exit_exit_lock : Z := 0x4d868.
Definition src0_D_stack_chk_guard : Z := 0x4d870.
Definition src0_D_sysinfo : Z := 0x4d878.
Definition src0_D_progname : Z := 0x4d880.
Definition src0_D_progname_full : Z := 0x4d888.
Definition src0_D_libc : Z := 0x4d890.
Definition src0_D_hwcap : Z := 0x4d8f8.
Definition src0_D_malloc_lock : Z := 0x4d900.
Definition src0_D_malloc_context : Z := 0x4d908.
Definition src0_D_malloc_replaced : Z := 0x4dca8.
Definition src0_D_stdin_used : Z := 0x4dcb0.
Definition src0_D_ofl_lock : Z := 0x4dcb8.
Definition src0_D_ofl_head : Z := 0x4dcc0.
Definition src0_D_stderr_buf : Z := 0x4dcc8.
Definition src0_D_stdout_buf : Z := 0x4dcd0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 33.
