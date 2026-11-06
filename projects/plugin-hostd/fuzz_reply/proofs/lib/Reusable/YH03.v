(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12a20.  Definition src0_text_hi : Z := 0x1ec54.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11174.
Definition src0_eh_frame_lo : Z := 0x112e8.  Definition src0_eh_frame_hi : Z := 0x11a20.
Definition src0_init_array_lo : Z := 0x1fc58.  Definition src0_init_array_hi : Z := 0x1fc60.
Definition src0_fini_array_lo : Z := 0x1fc60.  Definition src0_fini_array_hi : Z := 0x1fc68.
Definition src0_data_rel_ro_lo : Z := 0x1fc68.  Definition src0_data_rel_ro_hi : Z := 0x1fc78.
Definition src0_got_lo : Z := 0x1fc78.  Definition src0_got_hi : Z := 0x1fd10.
Definition src0_data_lo : Z := 0x20d10.  Definition src0_data_hi : Z := 0x20f38.
Definition src0_bss_lo : Z := 0x20f40.  Definition src0_bss_hi : Z := 0x51d7c.
Definition src0_A_do_init : Z := 0x12a68.  Definition src0_E_do_init : Z := 0x12adc.
Definition src0_A_do_fini : Z := 0x12adc.  Definition src0_E_do_fini : Z := 0x12b6c.
Definition src0_A_main : Z := 0x12b6c.  Definition src0_E_main : Z := 0x12e30.
Definition src0_A_target_alloc_init : Z := 0x12e30.  Definition src0_E_target_alloc_init : Z := 0x12e34.
Definition src0_A_target_alloc_count : Z := 0x12e34.  Definition src0_E_target_alloc_count : Z := 0x12e3c.
Definition src0_A_target_run : Z := 0x12e3c.  Definition src0_E_target_run : Z := 0x12f94.
Definition src0_A_aef_exit_guard : Z := 0x12f94.  Definition src0_E_aef_exit_guard : Z := 0x12fc4.
Definition src0_A_emit_printf : Z := 0x12fc4.  Definition src0_E_emit_printf : Z := 0x1300c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13b54.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x141f0.
Definition src0_A_init : Z := 0x14bf8.  Definition src0_E_init : Z := 0x14bfc.
Definition src0_A_init_libc : Z := 0x14bfc.  Definition src0_E_init_libc : Z := 0x14e28.
Definition src0_A_libc_start_init : Z := 0x14e28.  Definition src0_E_libc_start_init : Z := 0x14e74.
Definition src0_A_libc_start_main : Z := 0x14e74.  Definition src0_E_libc_start_main : Z := 0x14ed4.
Definition src0_A_libc_start_main_stage2 : Z := 0x14ed4.  Definition src0_E_libc_start_main_stage2 : Z := 0x14f1c.
Definition src0_A_init_tls : Z := 0x14f1c.  Definition src0_E_init_tls : Z := 0x151cc.
Definition src0_A_funcs_on_exit : Z := 0x15288.  Definition src0_E_funcs_on_exit : Z := 0x15350.
Definition src0_A_cxa_finalize : Z := 0x15350.  Definition src0_E_cxa_finalize : Z := 0x15354.
Definition src0_A_atexit : Z := 0x15354.  Definition src0_E_atexit : Z := 0x15418.
Definition src0_A_atexit_call : Z := 0x15418.  Definition src0_E_atexit_call : Z := 0x1541c.
Definition src0_A_fini : Z := 0x1541c.  Definition src0_E_fini : Z := 0x15420.
Definition src0_A_libc_exit_fini : Z := 0x15420.  Definition src0_E_libc_exit_fini : Z := 0x1546c.
Definition src0_A_exit : Z := 0x1546c.  Definition src0_E_exit : Z := 0x154e0.
Definition src0_A_Exit : Z := 0x1526c.  Definition src0_E_Exit : Z := 0x15288.
Definition src0_A_open : Z := 0x154e0.  Definition src0_E_open : Z := 0x155c4.
Definition src0_A_init_ssp : Z := 0x155c4.  Definition src0_E_init_ssp : Z := 0x15624.
Definition src0_A_stack_chk_fail : Z := 0x15624.  Definition src0_E_stack_chk_fail : Z := 0x1562c.
Definition src0_A_syscall_ret : Z := 0x1562c.  Definition src0_E_syscall_ret : Z := 0x15664.
Definition src0_A_errno_location : Z := 0x151cc.  Definition src0_E_errno_location : Z := 0x151d8.
Definition src0_A_free : Z := 0x15664.  Definition src0_E_free : Z := 0x15668.
Definition src0_A_libc_calloc : Z := 0x15668.  Definition src0_E_libc_calloc : Z := 0x157a0.
Definition src0_A_libc_malloc : Z := 0x157a0.  Definition src0_E_libc_malloc : Z := 0x157a4.
Definition src0_A_malloc : Z := 0x157a4.  Definition src0_E_malloc : Z := 0x157a8.
Definition src0_A_libc_free : Z := 0x157a8.  Definition src0_E_libc_free : Z := 0x15974.
Definition src0_A_get_meta : Z := 0x15974.  Definition src0_E_get_meta : Z := 0x15a84.
Definition src0_A_nontrivial_free : Z := 0x15a84.  Definition src0_E_nontrivial_free : Z := 0x15e5c.
Definition src0_A_alloc_meta : Z := 0x15e5c.  Definition src0_E_alloc_meta : Z := 0x16134.
Definition src0_A_libc_malloc_impl : Z := 0x16134.  Definition src0_E_libc_malloc_impl : Z := 0x164a4.
Definition src0_A_alloc_slot : Z := 0x164a4.  Definition src0_E_alloc_slot : Z := 0x16d48.
Definition src0_A_enframe : Z := 0x16d48.  Definition src0_E_enframe : Z := 0x16e98.
Definition src0_A_malloc_allzerop : Z := 0x16e98.  Definition src0_E_malloc_allzerop : Z := 0x17010.
Definition src0_A_vm_wait : Z := 0x1e5d4.  Definition src0_E_vm_wait : Z := 0x1e624.
Definition src0_A_mmap : Z := 0x17454.  Definition src0_E_mmap : Z := 0x17540.
Definition src0_A_mprotect : Z := 0x17540.  Definition src0_E_mprotect : Z := 0x17588.
Definition src0_A_munmap : Z := 0x1765c.  Definition src0_E_munmap : Z := 0x176a4.
Definition src0_A_fflush : Z := 0x17778.  Definition src0_E_fflush : Z := 0x178e8.
Definition src0_A_lockfile : Z := 0x178e8.  Definition src0_E_lockfile : Z := 0x179e4.
Definition src0_A_unlockfile : Z := 0x179e4.  Definition src0_E_unlockfile : Z := 0x17a44.
Definition src0_A_stdio_write : Z := 0x17fa0.  Definition src0_E_stdio_write : Z := 0x18130.
Definition src0_A_aio_close : Z := 0x17f70.  Definition src0_E_aio_close : Z := 0x17f74.
Definition src0_A_stdio_close : Z := 0x17f74.  Definition src0_E_stdio_close : Z := 0x17fa0.
Definition src0_A_fprintf : Z := 0x17a44.  Definition src0_E_fprintf : Z := 0x17aa8.
Definition src0_A_fwritex : Z := 0x17aa8.  Definition src0_E_fwritex : Z := 0x17be0.
Definition src0_A_fwrite : Z := 0x17be0.  Definition src0_E_fwrite : Z := 0x17c98.
Definition src0_A_towrite : Z := 0x17c98.  Definition src0_E_towrite : Z := 0x17cec.
Definition src0_A_stdio_exit : Z := 0x17cec.  Definition src0_E_stdio_exit : Z := 0x17e90.
Definition src0_A_ofl_lock : Z := 0x17e90.  Definition src0_E_ofl_lock : Z := 0x17ec0.
Definition src0_A_ofl_unlock : Z := 0x17ec0.  Definition src0_E_ofl_unlock : Z := 0x17ecc.
Definition src0_A_stdout_write : Z := 0x18138.  Definition src0_E_stdout_write : Z := 0x181d8.
Definition src0_A_vfprintf : Z := 0x181d8.  Definition src0_E_vfprintf : Z := 0x18388.
Definition src0_A_printf_core : Z := 0x18388.  Definition src0_E_printf_core : Z := 0x191b8.
Definition src0_A_pop_arg : Z := 0x191b8.  Definition src0_E_pop_arg : Z := 0x192ec.
Definition src0_A_pad : Z := 0x192ec.  Definition src0_E_pad : Z := 0x193c0.
Definition src0_A_fmt_fp : Z := 0x193c0.  Definition src0_E_fmt_fp : Z := 0x1aa88.
Definition src0_A_strerror : Z := 0x17ecc.  Definition src0_E_strerror : Z := 0x17f08.
Definition src0_A_lctrans_impl : Z := 0x17f08.  Definition src0_E_lctrans_impl : Z := 0x17f0c.
Definition src0_A_lctrans : Z := 0x17f0c.  Definition src0_E_lctrans : Z := 0x17f10.
Definition src0_A_wctomb : Z := 0x1aa88.  Definition src0_E_wctomb : Z := 0x1aaac.
Definition src0_A_wcrtomb : Z := 0x1aaac.  Definition src0_E_wcrtomb : Z := 0x1abd8.
Definition src0_A_extenddftf2 : Z := 0x1abd8.  Definition src0_E_extenddftf2 : Z := 0x1ad68.
Definition src0_A_signbitl : Z := 0x1ad68.  Definition src0_E_signbitl : Z := 0x1ad70.
Definition src0_A_fpclassifyl : Z := 0x1ad70.  Definition src0_E_fpclassifyl : Z := 0x1adb4.
Definition src0_A_frexpl : Z := 0x1adb4.  Definition src0_E_frexpl : Z := 0x1ae8c.
Definition src0_A_letf2 : Z := 0x1ae8c.  Definition src0_E_letf2 : Z := 0x1af54.
Definition src0_A_multf3 : Z := 0x1af54.  Definition src0_E_multf3 : Z := 0x1b654.
Definition src0_A_floatsitf : Z := 0x1b654.  Definition src0_E_floatsitf : Z := 0x1b75c.
Definition src0_A_scalbn : Z := 0x1b75c.  Definition src0_E_scalbn : Z := 0x1b7f4.
Definition src0_A_subtf3 : Z := 0x1b7f4.  Definition src0_E_subtf3 : Z := 0x1b804.
Definition src0_A_addtf3 : Z := 0x1b804.  Definition src0_E_addtf3 : Z := 0x1bfd0.
Definition src0_A_fe_getround : Z := 0x1bfd0.  Definition src0_E_fe_getround : Z := 0x1c000.
Definition src0_A_fe_raise_inexact : Z := 0x1c000.  Definition src0_E_fe_raise_inexact : Z := 0x1c00c.
Definition src0_A_fixunstfsi : Z := 0x1c00c.  Definition src0_E_fixunstfsi : Z := 0x1c0a0.
Definition src0_A_floatunsitf : Z := 0x1c0a0.  Definition src0_E_floatunsitf : Z := 0x1c18c.
Definition src0_A_fixtfsi : Z := 0x1c18c.  Definition src0_E_fixtfsi : Z := 0x1c234.
Definition src0_A_divtf3 : Z := 0x1c234.  Definition src0_E_divtf3 : Z := 0x1cb38.
Definition src0_A_vprintf : Z := 0x1cb38.  Definition src0_E_vprintf : Z := 0x1cb54.
Definition src0_A_bcmp : Z := 0x1ccfc.  Definition src0_E_bcmp : Z := 0x1cd00.
Definition src0_A_memcmp : Z := 0x1cdcc.  Definition src0_E_memcmp : Z := 0x1cdfc.
Definition src0_A_memcpy : Z := 0x1cdfc.  Definition src0_E_memcpy : Z := 0x1d200.
Definition src0_A_memset : Z := 0x1d37c.  Definition src0_E_memset : Z := 0x1d474.
Definition src0_A_strlen : Z := 0x1d4ac.  Definition src0_E_strlen : Z := 0x1d53c.
Definition src0_A_strnlen : Z := 0x1d5fc.  Definition src0_E_strnlen : Z := 0x1d640.
Definition src0_A_memchr : Z := 0x1cd00.  Definition src0_E_memchr : Z := 0x1cdcc.
Definition src0_A_lock : Z := 0x1d6ac.  Definition src0_E_lock : Z := 0x1d934.
Definition src0_A_unlock : Z := 0x1d934.  Definition src0_E_unlock : Z := 0x1d9a8.
Definition src0_A_syscall_cp_c : Z := 0x1d9a8.  Definition src0_E_syscall_cp_c : Z := 0x1d9cc.
Definition src0_A_syscall_cp : Z := 0x1d9cc.  Definition src0_E_syscall_cp : Z := 0x1d9d0.
Definition src0_A_unistd_exit : Z := 0x1eb80.  Definition src0_E_unistd_exit : Z := 0x1eb8c.
Definition src0_A_close : Z := 0x1eb8c.  Definition src0_E_close : Z := 0x1ebe0.
Definition src0_A_lseek : Z := 0x1ebe0.  Definition src0_E_lseek : Z := 0x1ebec.
Definition src0_A_read : Z := 0x1ebec.  Definition src0_E_read : Z := 0x1ec20.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102be.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102d1.
Definition src0_D_str_d_n : Z := 0x102e5.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102ec.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102fd.
Definition src0_D_str_inf : Z := 0x1031d.
Definition src0_D_str_INF : Z := 0x1035e.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10362.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10383.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10398.
Definition src0_D_str_NAN : Z := 0x103b3.
Definition src0_D_str_nan : Z := 0x103b7.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x103c6.
Definition src0_D_str_dev_null : Z := 0x103f4.
Definition src0_D_str_null : Z := 0x103fe.
Definition src0_D_const_double_0x1p28 : Z := 0x103a8.
Definition src0_D_const_double_1_0 : Z := 0x103b0.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10420.
Definition src0_D_const_double_0_5 : Z := 0x103c0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10430.
Definition src0_D_const_double_0x1p1023 : Z := 0x103d0.
Definition src0_D_const_double_1_5 : Z := 0x103d8.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103e0.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e8.
Definition src0_D_const_u64_0x0101010101010102 : Z := 0x103f0.
Definition src0_D_const_double_0x1p120 : Z := 0x103f8.
Definition src0_D_debruijn32 : Z := 0x104e0.
Definition src0_D_size_classes : Z := 0x10500.
Definition src0_D_small_cnt_tab : Z := 0x10560.
Definition src0_D_med_cnt_tab : Z := 0x1057b.
Definition src0_D_jt_printf_core_1 : Z := 0x11b40.
Definition src0_D_jt_printf_core_2 : Z := 0x11c20.
Definition src0_D_jt_pop_arg : Z := 0x11c40.
Definition src0_D_states : Z := 0x10f88.
Definition src0_D_xdigits : Z := 0x11158.
Definition src0_D_errmsgstr : Z := 0x10590.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x10d38.
Definition src0_D_fe_getround : Z := 0x11168.
Definition src0_D_EH_FRAME_LIST : Z := 0x112e8.
Definition src0_D_init_array_start : Z := 0x1fc58.
Definition src0_D_fini_array_start : Z := 0x1fc60.
Definition src0_D_stderr : Z := 0x1fc68.
Definition src0_D_stdout : Z := 0x1fc70.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1fc78.
Definition src0_D_got_DYNAMIC : Z := 0x1fc80.
Definition src0_D_got_main : Z := 0x1fc88.
Definition src0_D_got_init : Z := 0x1fc90.
Definition src0_D_got_fini : Z := 0x1fc98.
Definition src0_D_got_register_frame_info : Z := 0x1fca0.
Definition src0_D_got_cxa_finalize : Z := 0x1fca8.
Definition src0_D_got_deregister_frame_info : Z := 0x1fcb0.
Definition src0_D_got_stderr : Z := 0x1fcb8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1fcc0.
Definition src0_D_got_stdout : Z := 0x1fcc8.
Definition src0_D_got_environ : Z := 0x1fcd0.
Definition src0_D_got_progname_full : Z := 0x1fcd8.
Definition src0_D_got_progname : Z := 0x1fce0.
Definition src0_D_got_init_array_end : Z := 0x1fce8.
Definition src0_D_got_init_array_start : Z := 0x1fcf0.
Definition src0_D_got_stack_chk_guard : Z := 0x1fcf8.
Definition src0_D_got_fini_array_end : Z := 0x1fd00.
Definition src0_D_got_fini_array_start : Z := 0x1fd08.
Definition src0_D_dso_handle : Z := 0x20d10.
Definition src0_D_aef_arg0 : Z := 0x21410.
Definition src0_D_aef_argc : Z := 0x20d20.
Definition src0_D_aef_argv : Z := 0x21420.
Definition src0_D_stderr_FILE : Z := 0x20d48.
Definition src0_D_stderr_used : Z := 0x20e30.
Definition src0_D_stdout_FILE : Z := 0x20e38.
Definition src0_D_stdout_used : Z := 0x20f20.
Definition src0_D_default_stacksize : Z := 0x20f28.
Definition src0_D_do_init_initialized : Z := 0x20f40.
Definition src0_D_do_init_object : Z := 0x20f48.
Definition src0_D_do_fini_finalized : Z := 0x20f88.
Definition src0_D_read_stage : Z := 0x20f89.
Definition src0_D_target_run_initialized : Z := 0x30f90.
Definition src0_D_aef_in_callback : Z := 0x30f94.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30fa0.
Definition src0_D_environ : Z := 0x311c0.
Definition src0_D_thread_list_lock : Z := 0x51298.
Definition src0_D_main_tls : Z := 0x512a0.
Definition src0_D_builtin_tls : Z := 0x311c8.
Definition src0_D_finished_atexit : Z := 0x512d8.
Definition src0_D_atexit_lock : Z := 0x512dc.
Definition src0_D_atexit_slot : Z := 0x512e0.
Definition src0_D_atexit_head : Z := 0x512e8.
Definition src0_D_atexit_builtin : Z := 0x512f0.
Definition src0_D_exit_exit_lock : Z := 0x514f8.
Definition src0_D_stack_chk_guard : Z := 0x51500.
Definition src0_D_sysinfo : Z := 0x51508.
Definition src0_D_progname : Z := 0x51510.
Definition src0_D_progname_full : Z := 0x51518.
Definition src0_D_libc : Z := 0x51520.
Definition src0_D_hwcap : Z := 0x51588.
Definition src0_D_malloc_lock : Z := 0x51590.
Definition src0_D_malloc_context : Z := 0x51598.
Definition src0_D_malloc_replaced : Z := 0x51938.
Definition src0_D_stdin_used : Z := 0x51940.
Definition src0_D_ofl_lock : Z := 0x51948.
Definition src0_D_ofl_head : Z := 0x51950.
Definition src0_D_stderr_buf : Z := 0x51958.
Definition src0_D_stdout_buf : Z := 0x51960.
Definition src0_A_realloc : Z := 0x17010.  Definition src0_E_realloc : Z := 0x17014.
Definition src0_A_mremap : Z := 0x17588.  Definition src0_E_mremap : Z := 0x1765c.
Definition src0_vmlock : option Z := Some 0x51d74.
Definition src0_debruijn_len : Z := 32.
