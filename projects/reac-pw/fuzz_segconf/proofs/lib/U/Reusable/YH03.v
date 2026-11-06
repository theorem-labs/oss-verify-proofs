(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x1329c.  Definition src0_text_hi : Z := 0x20430.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1181e.
Definition src0_eh_frame_lo : Z := 0x119f0.  Definition src0_eh_frame_hi : Z := 0x1229c.
Definition src0_init_array_lo : Z := 0x21430.  Definition src0_init_array_hi : Z := 0x21438.
Definition src0_fini_array_lo : Z := 0x21438.  Definition src0_fini_array_hi : Z := 0x21440.
Definition src0_data_rel_ro_lo : Z := 0x21440.  Definition src0_data_rel_ro_hi : Z := 0x22130.
Definition src0_got_lo : Z := 0x22130.  Definition src0_got_hi : Z := 0x221c8.
Definition src0_data_lo : Z := 0x231c8.  Definition src0_data_hi : Z := 0x233d4.
Definition src0_bss_lo : Z := 0x233e0.  Definition src0_bss_hi : Z := 0x54088.
Definition src0_A_start : Z := 0x1329c.  Definition src0_E_start : Z := 0x132e4.
Definition src0_A_do_init : Z := 0x132e4.  Definition src0_E_do_init : Z := 0x13358.
Definition src0_A_do_fini : Z := 0x13358.  Definition src0_E_do_fini : Z := 0x133e8.
Definition src0_A_main : Z := 0x133e8.  Definition src0_E_main : Z := 0x136ac.
Definition src0_A_target_alloc_init : Z := 0x136ac.  Definition src0_E_target_alloc_init : Z := 0x136b0.
Definition src0_A_target_alloc_count : Z := 0x136b0.  Definition src0_E_target_alloc_count : Z := 0x136b8.
Definition src0_A_target_run : Z := 0x136b8.  Definition src0_E_target_run : Z := 0x13810.
Definition src0_A_aef_exit_guard : Z := 0x13810.  Definition src0_E_aef_exit_guard : Z := 0x13840.
Definition src0_A_emit_printf : Z := 0x13840.  Definition src0_E_emit_printf : Z := 0x13888.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13888.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14268.
Definition src0_A_init : Z := 0x167f0.  Definition src0_E_init : Z := 0x167f4.
Definition src0_A_init_libc : Z := 0x167f4.  Definition src0_E_init_libc : Z := 0x16a20.
Definition src0_A_libc_start_init : Z := 0x16a20.  Definition src0_E_libc_start_init : Z := 0x16a6c.
Definition src0_A_libc_start_main : Z := 0x16a6c.  Definition src0_E_libc_start_main : Z := 0x16acc.
Definition src0_A_libc_start_main_stage2 : Z := 0x16acc.  Definition src0_E_libc_start_main_stage2 : Z := 0x16b14.
Definition src0_A_init_tls : Z := 0x16b14.  Definition src0_E_init_tls : Z := 0x16dc4.
Definition src0_A_funcs_on_exit : Z := 0x16ebc.  Definition src0_E_funcs_on_exit : Z := 0x16f84.
Definition src0_A_cxa_finalize : Z := 0x16f84.  Definition src0_E_cxa_finalize : Z := 0x16f88.
Definition src0_A_atexit : Z := 0x16f88.  Definition src0_E_atexit : Z := 0x1704c.
Definition src0_A_atexit_call : Z := 0x1704c.  Definition src0_E_atexit_call : Z := 0x17050.
Definition src0_A_fini : Z := 0x17050.  Definition src0_E_fini : Z := 0x17054.
Definition src0_A_libc_exit_fini : Z := 0x17054.  Definition src0_E_libc_exit_fini : Z := 0x170a0.
Definition src0_A_exit : Z := 0x170a0.  Definition src0_E_exit : Z := 0x17114.
Definition src0_A_Exit : Z := 0x16ea0.  Definition src0_E_Exit : Z := 0x16ebc.
Definition src0_A_open : Z := 0x17114.  Definition src0_E_open : Z := 0x171f8.
Definition src0_A_init_ssp : Z := 0x171f8.  Definition src0_E_init_ssp : Z := 0x17258.
Definition src0_A_stack_chk_fail : Z := 0x17258.  Definition src0_E_stack_chk_fail : Z := 0x17260.
Definition src0_A_syscall_ret : Z := 0x17260.  Definition src0_E_syscall_ret : Z := 0x17298.
Definition src0_A_errno_location : Z := 0x16dc4.  Definition src0_E_errno_location : Z := 0x16dd0.
Definition src0_A_free : Z := 0x173d8.  Definition src0_E_free : Z := 0x173dc.
Definition src0_A_libc_calloc : Z := 0x173dc.  Definition src0_E_libc_calloc : Z := 0x17514.
Definition src0_A_libc_malloc : Z := 0x17514.  Definition src0_E_libc_malloc : Z := 0x17518.
Definition src0_A_malloc : Z := 0x17518.  Definition src0_E_malloc : Z := 0x1751c.
Definition src0_A_libc_free : Z := 0x1751c.  Definition src0_E_libc_free : Z := 0x176e8.
Definition src0_A_get_meta : Z := 0x176e8.  Definition src0_E_get_meta : Z := 0x177f8.
Definition src0_A_nontrivial_free : Z := 0x177f8.  Definition src0_E_nontrivial_free : Z := 0x17bd0.
Definition src0_A_alloc_meta : Z := 0x17bd0.  Definition src0_E_alloc_meta : Z := 0x17ea8.
Definition src0_A_libc_malloc_impl : Z := 0x17ea8.  Definition src0_E_libc_malloc_impl : Z := 0x18218.
Definition src0_A_alloc_slot : Z := 0x18218.  Definition src0_E_alloc_slot : Z := 0x18abc.
Definition src0_A_enframe : Z := 0x18abc.  Definition src0_E_enframe : Z := 0x18c0c.
Definition src0_A_malloc_allzerop : Z := 0x18c0c.  Definition src0_E_malloc_allzerop : Z := 0x18d84.
Definition src0_A_vm_wait : Z := 0x18d84.  Definition src0_E_vm_wait : Z := 0x18d88.
Definition src0_A_mmap : Z := 0x18d88.  Definition src0_E_mmap : Z := 0x18e74.
Definition src0_A_mprotect : Z := 0x18e74.  Definition src0_E_mprotect : Z := 0x18ebc.
Definition src0_A_munmap : Z := 0x18ebc.  Definition src0_E_munmap : Z := 0x18f04.
Definition src0_A_fflush : Z := 0x18fd8.  Definition src0_E_fflush : Z := 0x19148.
Definition src0_A_lockfile : Z := 0x19148.  Definition src0_E_lockfile : Z := 0x19244.
Definition src0_A_unlockfile : Z := 0x19244.  Definition src0_E_unlockfile : Z := 0x192a4.
Definition src0_A_stdio_write : Z := 0x19568.  Definition src0_E_stdio_write : Z := 0x196f8.
Definition src0_A_aio_close : Z := 0x19700.  Definition src0_E_aio_close : Z := 0x19704.
Definition src0_A_stdio_close : Z := 0x19704.  Definition src0_E_stdio_close : Z := 0x19730.
Definition src0_A_fprintf : Z := 0x19730.  Definition src0_E_fprintf : Z := 0x19794.
Definition src0_A_fwritex : Z := 0x19794.  Definition src0_E_fwritex : Z := 0x198cc.
Definition src0_A_fwrite : Z := 0x198cc.  Definition src0_E_fwrite : Z := 0x19984.
Definition src0_A_towrite : Z := 0x19984.  Definition src0_E_towrite : Z := 0x199d8.
Definition src0_A_stdio_exit : Z := 0x193c4.  Definition src0_E_stdio_exit : Z := 0x19568.
Definition src0_A_ofl_lock : Z := 0x199d8.  Definition src0_E_ofl_lock : Z := 0x19a08.
Definition src0_A_ofl_unlock : Z := 0x19a08.  Definition src0_E_ofl_unlock : Z := 0x19a14.
Definition src0_A_stdout_write : Z := 0x19a74.  Definition src0_E_stdout_write : Z := 0x19b14.
Definition src0_A_vfprintf : Z := 0x19b14.  Definition src0_E_vfprintf : Z := 0x19cc4.
Definition src0_A_printf_core : Z := 0x19cc4.  Definition src0_E_printf_core : Z := 0x1aaf4.
Definition src0_A_pop_arg : Z := 0x1aaf4.  Definition src0_E_pop_arg : Z := 0x1ac28.
Definition src0_A_pad : Z := 0x1ac28.  Definition src0_E_pad : Z := 0x1acfc.
Definition src0_A_fmt_fp : Z := 0x1acfc.  Definition src0_E_fmt_fp : Z := 0x1c3c4.
Definition src0_A_strerror : Z := 0x16dd0.  Definition src0_E_strerror : Z := 0x16e0c.
Definition src0_A_lctrans_impl : Z := 0x17298.  Definition src0_E_lctrans_impl : Z := 0x1729c.
Definition src0_A_lctrans : Z := 0x1729c.  Definition src0_E_lctrans : Z := 0x172a0.
Definition src0_A_wctomb : Z := 0x1c3c4.  Definition src0_E_wctomb : Z := 0x1c3e8.
Definition src0_A_wcrtomb : Z := 0x1c3e8.  Definition src0_E_wcrtomb : Z := 0x1c514.
Definition src0_A_extenddftf2 : Z := 0x1c514.  Definition src0_E_extenddftf2 : Z := 0x1c6a4.
Definition src0_A_signbitl : Z := 0x1c6a4.  Definition src0_E_signbitl : Z := 0x1c6ac.
Definition src0_A_fpclassifyl : Z := 0x1c6ac.  Definition src0_E_fpclassifyl : Z := 0x1c6f0.
Definition src0_A_frexpl : Z := 0x1c6f0.  Definition src0_E_frexpl : Z := 0x1c7c8.
Definition src0_A_letf2 : Z := 0x1c7c8.  Definition src0_E_letf2 : Z := 0x1c890.
Definition src0_A_multf3 : Z := 0x1c890.  Definition src0_E_multf3 : Z := 0x1cf90.
Definition src0_A_floatsitf : Z := 0x1cf90.  Definition src0_E_floatsitf : Z := 0x1d098.
Definition src0_A_scalbn : Z := 0x1d098.  Definition src0_E_scalbn : Z := 0x1d130.
Definition src0_A_subtf3 : Z := 0x1d130.  Definition src0_E_subtf3 : Z := 0x1d140.
Definition src0_A_addtf3 : Z := 0x1d140.  Definition src0_E_addtf3 : Z := 0x1d90c.
Definition src0_A_fe_getround : Z := 0x1d90c.  Definition src0_E_fe_getround : Z := 0x1d93c.
Definition src0_A_fe_raise_inexact : Z := 0x1d93c.  Definition src0_E_fe_raise_inexact : Z := 0x1d948.
Definition src0_A_fixunstfsi : Z := 0x1d948.  Definition src0_E_fixunstfsi : Z := 0x1d9dc.
Definition src0_A_floatunsitf : Z := 0x1d9dc.  Definition src0_E_floatunsitf : Z := 0x1dac8.
Definition src0_A_fixtfsi : Z := 0x1dac8.  Definition src0_E_fixtfsi : Z := 0x1db70.
Definition src0_A_divtf3 : Z := 0x1db70.  Definition src0_E_divtf3 : Z := 0x1e474.
Definition src0_A_vprintf : Z := 0x1e474.  Definition src0_E_vprintf : Z := 0x1e490.
Definition src0_A_bcmp : Z := 0x1edc8.  Definition src0_E_bcmp : Z := 0x1edcc.
Definition src0_A_memcmp : Z := 0x1ee98.  Definition src0_E_memcmp : Z := 0x1eec8.
Definition src0_A_memcpy : Z := 0x1eec8.  Definition src0_E_memcpy : Z := 0x1f2cc.
Definition src0_A_memset : Z := 0x1f2cc.  Definition src0_E_memset : Z := 0x1f3c4.
Definition src0_A_strchr : Z := 0x1f478.  Definition src0_E_strchr : Z := 0x1f4b4.
Definition src0_A_strchrnul : Z := 0x1f4b4.  Definition src0_E_strchrnul : Z := 0x1f594.
Definition src0_A_strlen : Z := 0x1f5cc.  Definition src0_E_strlen : Z := 0x1f65c.
Definition src0_A_strnlen : Z := 0x1f8b8.  Definition src0_E_strnlen : Z := 0x1f8fc.
Definition src0_A_memchr : Z := 0x1edcc.  Definition src0_E_memchr : Z := 0x1ee98.
Definition src0_A_lock : Z := 0x20060.  Definition src0_E_lock : Z := 0x202e8.
Definition src0_A_unlock : Z := 0x202e8.  Definition src0_E_unlock : Z := 0x2035c.
Definition src0_A_syscall_cp_c : Z := 0x2035c.  Definition src0_E_syscall_cp_c : Z := 0x20380.
Definition src0_A_syscall_cp : Z := 0x20380.  Definition src0_E_syscall_cp : Z := 0x20384.
Definition src0_A_set_thread_area : Z := 0x20384.  Definition src0_E_set_thread_area : Z := 0x20390.
Definition src0_A_unistd_exit : Z := 0x20390.  Definition src0_E_unistd_exit : Z := 0x2039c.
Definition src0_A_close : Z := 0x2039c.  Definition src0_E_close : Z := 0x203f0.
Definition src0_A_lseek : Z := 0x203f0.  Definition src0_E_lseek : Z := 0x203fc.
Definition src0_A_read : Z := 0x203fc.  Definition src0_E_read : Z := 0x20430.
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
Definition src0_D_EH_FRAME_LIST : Z := 0x119f0.
Definition src0_D_init_array_start : Z := 0x21430.
Definition src0_D_fini_array_start : Z := 0x21438.
Definition src0_D_stderr : Z := 0x22120.
Definition src0_D_stdout : Z := 0x22128.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x22130.
Definition src0_D_got_DYNAMIC : Z := 0x22138.
Definition src0_D_got_main : Z := 0x22140.
Definition src0_D_got_init : Z := 0x22148.
Definition src0_D_got_fini : Z := 0x22150.
Definition src0_D_got_register_frame_info : Z := 0x22158.
Definition src0_D_got_cxa_finalize : Z := 0x22160.
Definition src0_D_got_deregister_frame_info : Z := 0x22168.
Definition src0_D_got_stderr : Z := 0x22170.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x22178.
Definition src0_D_got_stdout : Z := 0x22180.
Definition src0_D_got_environ : Z := 0x22188.
Definition src0_D_got_progname_full : Z := 0x22190.
Definition src0_D_got_progname : Z := 0x22198.
Definition src0_D_got_init_array_end : Z := 0x221a0.
Definition src0_D_got_init_array_start : Z := 0x221a8.
Definition src0_D_got_stack_chk_guard : Z := 0x221b0.
Definition src0_D_got_fini_array_end : Z := 0x221b8.
Definition src0_D_got_fini_array_start : Z := 0x221c0.
Definition src0_D_dso_handle : Z := 0x231c8.
Definition src0_D_aef_arg0 : Z := 0x231d0.
Definition src0_D_aef_argc : Z := 0x231d8.
Definition src0_D_aef_argv : Z := 0x231e0.
Definition src0_D_stderr_FILE : Z := 0x231f0.
Definition src0_D_stderr_used : Z := 0x232d8.
Definition src0_D_stdout_FILE : Z := 0x232e0.
Definition src0_D_stdout_used : Z := 0x233c8.
Definition src0_D_default_stacksize : Z := 0x233d0.
Definition src0_D_do_init_initialized : Z := 0x233e0.
Definition src0_D_do_init_object : Z := 0x233e8.
Definition src0_D_do_fini_finalized : Z := 0x23428.
Definition src0_D_read_stage : Z := 0x23429.
Definition src0_D_target_run_initialized : Z := 0x33430.
Definition src0_D_aef_in_callback : Z := 0x33434.
Definition src0_D_aef_aligned_copy_empty : Z := 0x33440.
Definition src0_D_environ : Z := 0x334e0.
Definition src0_D_thread_list_lock : Z := 0x535b8.
Definition src0_D_main_tls : Z := 0x535c0.
Definition src0_D_builtin_tls : Z := 0x334e8.
Definition src0_D_finished_atexit : Z := 0x535f8.
Definition src0_D_atexit_lock : Z := 0x535fc.
Definition src0_D_atexit_slot : Z := 0x53600.
Definition src0_D_atexit_head : Z := 0x53608.
Definition src0_D_atexit_builtin : Z := 0x53610.
Definition src0_D_exit_exit_lock : Z := 0x53818.
Definition src0_D_stack_chk_guard : Z := 0x53820.
Definition src0_D_sysinfo : Z := 0x53828.
Definition src0_D_progname : Z := 0x53830.
Definition src0_D_progname_full : Z := 0x53838.
Definition src0_D_libc : Z := 0x53840.
Definition src0_D_hwcap : Z := 0x538a8.
Definition src0_D_malloc_lock : Z := 0x538b0.
Definition src0_D_malloc_context : Z := 0x538b8.
Definition src0_D_malloc_replaced : Z := 0x53c58.
Definition src0_D_stdin_used : Z := 0x53c60.
Definition src0_D_ofl_lock : Z := 0x53c68.
Definition src0_D_ofl_head : Z := 0x53c70.
Definition src0_D_stderr_buf : Z := 0x53c78.
Definition src0_D_stdout_buf : Z := 0x53c80.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
