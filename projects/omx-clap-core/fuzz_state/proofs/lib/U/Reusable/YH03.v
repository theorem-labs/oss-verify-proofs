(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12d9c.  Definition src0_text_hi : Z := 0x217e4.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x111fc.
Definition src0_eh_frame_lo : Z := 0x113f0.  Definition src0_eh_frame_hi : Z := 0x11d9c.
Definition src0_init_array_lo : Z := 0x227e8.  Definition src0_init_array_hi : Z := 0x227f0.
Definition src0_fini_array_lo : Z := 0x227f0.  Definition src0_fini_array_hi : Z := 0x227f8.
Definition src0_data_rel_ro_lo : Z := 0x227f8.  Definition src0_data_rel_ro_hi : Z := 0x22808.
Definition src0_got_lo : Z := 0x22808.  Definition src0_got_hi : Z := 0x228a0.
Definition src0_data_lo : Z := 0x238a0.  Definition src0_data_hi : Z := 0x23ab4.
Definition src0_bss_lo : Z := 0x23ac0.  Definition src0_bss_hi : Z := 0x54700.
Definition src0_A_do_init : Z := 0x12de4.  Definition src0_E_do_init : Z := 0x12e58.
Definition src0_A_do_fini : Z := 0x12e58.  Definition src0_E_do_fini : Z := 0x12ee8.
Definition src0_A_main : Z := 0x12ee8.  Definition src0_E_main : Z := 0x131ac.
Definition src0_A_target_alloc_init : Z := 0x131ac.  Definition src0_E_target_alloc_init : Z := 0x131b0.
Definition src0_A_target_alloc_count : Z := 0x131b0.  Definition src0_E_target_alloc_count : Z := 0x131b8.
Definition src0_A_target_run : Z := 0x131b8.  Definition src0_E_target_run : Z := 0x13310.
Definition src0_A_aef_exit_guard : Z := 0x13310.  Definition src0_E_aef_exit_guard : Z := 0x13340.
Definition src0_A_emit_printf : Z := 0x13340.  Definition src0_E_emit_printf : Z := 0x13388.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13388.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x134c0.
Definition src0_A_init : Z := 0x160d0.  Definition src0_E_init : Z := 0x160d4.
Definition src0_A_init_libc : Z := 0x160d4.  Definition src0_E_init_libc : Z := 0x16300.
Definition src0_A_libc_start_init : Z := 0x16300.  Definition src0_E_libc_start_init : Z := 0x1634c.
Definition src0_A_libc_start_main : Z := 0x1634c.  Definition src0_E_libc_start_main : Z := 0x163ac.
Definition src0_A_libc_start_main_stage2 : Z := 0x163ac.  Definition src0_E_libc_start_main_stage2 : Z := 0x163f4.
Definition src0_A_init_tls : Z := 0x163f4.  Definition src0_E_init_tls : Z := 0x166a4.
Definition src0_A_funcs_on_exit : Z := 0x16754.  Definition src0_E_funcs_on_exit : Z := 0x1681c.
Definition src0_A_cxa_finalize : Z := 0x1681c.  Definition src0_E_cxa_finalize : Z := 0x16820.
Definition src0_A_atexit : Z := 0x16820.  Definition src0_E_atexit : Z := 0x168e4.
Definition src0_A_atexit_call : Z := 0x168e4.  Definition src0_E_atexit_call : Z := 0x168e8.
Definition src0_A_fini : Z := 0x168e8.  Definition src0_E_fini : Z := 0x168ec.
Definition src0_A_libc_exit_fini : Z := 0x168ec.  Definition src0_E_libc_exit_fini : Z := 0x16938.
Definition src0_A_exit : Z := 0x16938.  Definition src0_E_exit : Z := 0x169ac.
Definition src0_A_Exit : Z := 0x16738.  Definition src0_E_Exit : Z := 0x16754.
Definition src0_A_open : Z := 0x169ac.  Definition src0_E_open : Z := 0x16a90.
Definition src0_A_init_ssp : Z := 0x16a90.  Definition src0_E_init_ssp : Z := 0x16af0.
Definition src0_A_stack_chk_fail : Z := 0x16af0.  Definition src0_E_stack_chk_fail : Z := 0x16af8.
Definition src0_A_syscall_ret : Z := 0x16af8.  Definition src0_E_syscall_ret : Z := 0x16b30.
Definition src0_A_errno_location : Z := 0x16b30.  Definition src0_E_errno_location : Z := 0x16b3c.
Definition src0_A_free : Z := 0x16b3c.  Definition src0_E_free : Z := 0x16b40.
Definition src0_A_libc_calloc : Z := 0x16b40.  Definition src0_E_libc_calloc : Z := 0x16c78.
Definition src0_A_libc_malloc : Z := 0x16c78.  Definition src0_E_libc_malloc : Z := 0x16c7c.
Definition src0_A_malloc : Z := 0x16c7c.  Definition src0_E_malloc : Z := 0x16c80.
Definition src0_A_libc_free : Z := 0x16c80.  Definition src0_E_libc_free : Z := 0x16e4c.
Definition src0_A_get_meta : Z := 0x16e4c.  Definition src0_E_get_meta : Z := 0x16f5c.
Definition src0_A_nontrivial_free : Z := 0x16f5c.  Definition src0_E_nontrivial_free : Z := 0x17334.
Definition src0_A_alloc_meta : Z := 0x17334.  Definition src0_E_alloc_meta : Z := 0x1760c.
Definition src0_A_libc_malloc_impl : Z := 0x1760c.  Definition src0_E_libc_malloc_impl : Z := 0x1797c.
Definition src0_A_alloc_slot : Z := 0x1797c.  Definition src0_E_alloc_slot : Z := 0x18220.
Definition src0_A_enframe : Z := 0x18220.  Definition src0_E_enframe : Z := 0x18370.
Definition src0_A_malloc_allzerop : Z := 0x18370.  Definition src0_E_malloc_allzerop : Z := 0x184e8.
Definition src0_A_vm_wait : Z := 0x1892c.  Definition src0_E_vm_wait : Z := 0x18930.
Definition src0_A_mmap : Z := 0x18930.  Definition src0_E_mmap : Z := 0x18a1c.
Definition src0_A_mprotect : Z := 0x18a1c.  Definition src0_E_mprotect : Z := 0x18a64.
Definition src0_A_munmap : Z := 0x18b38.  Definition src0_E_munmap : Z := 0x18b80.
Definition src0_A_fflush : Z := 0x18db0.  Definition src0_E_fflush : Z := 0x18f20.
Definition src0_A_lockfile : Z := 0x18c54.  Definition src0_E_lockfile : Z := 0x18d50.
Definition src0_A_unlockfile : Z := 0x18d50.  Definition src0_E_unlockfile : Z := 0x18db0.
Definition src0_A_stdio_write : Z := 0x18f20.  Definition src0_E_stdio_write : Z := 0x190b0.
Definition src0_A_stdio_seek : Z := 0x190b0.  Definition src0_E_stdio_seek : Z := 0x190b8.
Definition src0_A_aio_close : Z := 0x190b8.  Definition src0_E_aio_close : Z := 0x190bc.
Definition src0_A_stdio_close : Z := 0x190bc.  Definition src0_E_stdio_close : Z := 0x190e8.
Definition src0_A_fprintf : Z := 0x190e8.  Definition src0_E_fprintf : Z := 0x1914c.
Definition src0_A_fwritex : Z := 0x19384.  Definition src0_E_fwritex : Z := 0x194bc.
Definition src0_A_fwrite : Z := 0x194bc.  Definition src0_E_fwrite : Z := 0x19574.
Definition src0_A_towrite : Z := 0x19574.  Definition src0_E_towrite : Z := 0x195c8.
Definition src0_A_stdio_exit : Z := 0x191e0.  Definition src0_E_stdio_exit : Z := 0x19384.
Definition src0_A_ofl_lock : Z := 0x195c8.  Definition src0_E_ofl_lock : Z := 0x195f8.
Definition src0_A_ofl_unlock : Z := 0x195f8.  Definition src0_E_ofl_unlock : Z := 0x19604.
Definition src0_A_stdout_write : Z := 0x19664.  Definition src0_E_stdout_write : Z := 0x19704.
Definition src0_A_vfprintf : Z := 0x19704.  Definition src0_E_vfprintf : Z := 0x198b4.
Definition src0_A_printf_core : Z := 0x198b4.  Definition src0_E_printf_core : Z := 0x1a6e4.
Definition src0_A_pop_arg : Z := 0x1a6e4.  Definition src0_E_pop_arg : Z := 0x1a818.
Definition src0_A_pad : Z := 0x1a818.  Definition src0_E_pad : Z := 0x1a8ec.
Definition src0_A_fmt_fp : Z := 0x1a8ec.  Definition src0_E_fmt_fp : Z := 0x1bfb4.
Definition src0_A_strerror : Z := 0x1bfb4.  Definition src0_E_strerror : Z := 0x1bff0.
Definition src0_A_lctrans_impl : Z := 0x1bff0.  Definition src0_E_lctrans_impl : Z := 0x1bff4.
Definition src0_A_lctrans : Z := 0x1bff4.  Definition src0_E_lctrans : Z := 0x1bff8.
Definition src0_A_wctomb : Z := 0x1bff8.  Definition src0_E_wctomb : Z := 0x1c01c.
Definition src0_A_wcrtomb : Z := 0x1c01c.  Definition src0_E_wcrtomb : Z := 0x1c148.
Definition src0_A_extenddftf2 : Z := 0x1c148.  Definition src0_E_extenddftf2 : Z := 0x1c2d8.
Definition src0_A_signbitl : Z := 0x1c2d8.  Definition src0_E_signbitl : Z := 0x1c2e0.
Definition src0_A_fpclassifyl : Z := 0x1c2e0.  Definition src0_E_fpclassifyl : Z := 0x1c324.
Definition src0_A_frexpl : Z := 0x1c324.  Definition src0_E_frexpl : Z := 0x1c3fc.
Definition src0_A_letf2 : Z := 0x1c3fc.  Definition src0_E_letf2 : Z := 0x1c4c4.
Definition src0_A_multf3 : Z := 0x1c580.  Definition src0_E_multf3 : Z := 0x1cc80.
Definition src0_A_floatsitf : Z := 0x1cc80.  Definition src0_E_floatsitf : Z := 0x1cd88.
Definition src0_A_scalbn : Z := 0x1cd88.  Definition src0_E_scalbn : Z := 0x1ce20.
Definition src0_A_subtf3 : Z := 0x1ce20.  Definition src0_E_subtf3 : Z := 0x1ce30.
Definition src0_A_addtf3 : Z := 0x1ce30.  Definition src0_E_addtf3 : Z := 0x1d5fc.
Definition src0_A_fe_getround : Z := 0x1d5fc.  Definition src0_E_fe_getround : Z := 0x1d62c.
Definition src0_A_fe_raise_inexact : Z := 0x1d62c.  Definition src0_E_fe_raise_inexact : Z := 0x1d638.
Definition src0_A_fixunstfsi : Z := 0x1d638.  Definition src0_E_fixunstfsi : Z := 0x1d6cc.
Definition src0_A_floatunsitf : Z := 0x1d6cc.  Definition src0_E_floatunsitf : Z := 0x1d7b8.
Definition src0_A_fixtfsi : Z := 0x1d7b8.  Definition src0_E_fixtfsi : Z := 0x1d860.
Definition src0_A_divtf3 : Z := 0x1d860.  Definition src0_E_divtf3 : Z := 0x1e164.
Definition src0_A_vprintf : Z := 0x1e164.  Definition src0_E_vprintf : Z := 0x1e180.
Definition src0_A_bcmp : Z := 0x20d0c.  Definition src0_E_bcmp : Z := 0x20d10.
Definition src0_A_memcmp : Z := 0x20ddc.  Definition src0_E_memcmp : Z := 0x20e0c.
Definition src0_A_memcpy : Z := 0x20e0c.  Definition src0_E_memcpy : Z := 0x21210.
Definition src0_A_memset : Z := 0x21210.  Definition src0_E_memset : Z := 0x21308.
Definition src0_A_strlen : Z := 0x21340.  Definition src0_E_strlen : Z := 0x213d0.
Definition src0_A_strnlen : Z := 0x213d0.  Definition src0_E_strnlen : Z := 0x21414.
Definition src0_A_memchr : Z := 0x20d10.  Definition src0_E_memchr : Z := 0x20ddc.
Definition src0_A_lock : Z := 0x21414.  Definition src0_E_lock : Z := 0x2169c.
Definition src0_A_unlock : Z := 0x2169c.  Definition src0_E_unlock : Z := 0x21710.
Definition src0_A_syscall_cp_c : Z := 0x21710.  Definition src0_E_syscall_cp_c : Z := 0x21734.
Definition src0_A_syscall_cp : Z := 0x21734.  Definition src0_E_syscall_cp : Z := 0x21738.
Definition src0_A_unistd_exit : Z := 0x21744.  Definition src0_E_unistd_exit : Z := 0x21750.
Definition src0_A_close : Z := 0x21750.  Definition src0_E_close : Z := 0x217a4.
Definition src0_A_lseek : Z := 0x217a4.  Definition src0_E_lseek : Z := 0x217b0.
Definition src0_A_read : Z := 0x217b0.  Definition src0_E_read : Z := 0x217e4.
Definition src0_D_str_n0X0x : Z := 0x1029e.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102ca.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102dd.
Definition src0_D_str_d_n : Z := 0x102f1.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10303.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10314.
Definition src0_D_str_inf : Z := 0x10338.
Definition src0_D_str_INF : Z := 0x10343.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10347.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10391.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103a6.
Definition src0_D_str_NAN : Z := 0x103bd.
Definition src0_D_str_nan : Z := 0x103c1.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x103cf.
Definition src0_D_str_dev_null : Z := 0x10402.
Definition src0_D_str_null : Z := 0x1040c.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10438.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10448.
Definition src0_D_debruijn32 : Z := 0x10564.
Definition src0_D_size_classes : Z := 0x10584.
Definition src0_D_small_cnt_tab : Z := 0x105e4.
Definition src0_D_med_cnt_tab : Z := 0x105ff.
Definition src0_D_states : Z := 0x10760.
Definition src0_D_xdigits : Z := 0x10930.
Definition src0_D_errmsgstr : Z := 0x10940.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x110e8.
Definition src0_D_fe_getround : Z := 0x111f0.
Definition src0_D_EH_FRAME_LIST : Z := 0x113f0.
Definition src0_D_init_array_start : Z := 0x227e8.
Definition src0_D_fini_array_start : Z := 0x227f0.
Definition src0_D_stderr : Z := 0x227f8.
Definition src0_D_stdout : Z := 0x22800.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x22808.
Definition src0_D_got_DYNAMIC : Z := 0x22810.
Definition src0_D_got_main : Z := 0x22818.
Definition src0_D_got_init : Z := 0x22820.
Definition src0_D_got_fini : Z := 0x22828.
Definition src0_D_got_register_frame_info : Z := 0x22830.
Definition src0_D_got_cxa_finalize : Z := 0x22838.
Definition src0_D_got_deregister_frame_info : Z := 0x22840.
Definition src0_D_got_stderr : Z := 0x22848.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x22850.
Definition src0_D_got_stdout : Z := 0x22858.
Definition src0_D_got_environ : Z := 0x22860.
Definition src0_D_got_progname_full : Z := 0x22868.
Definition src0_D_got_progname : Z := 0x22870.
Definition src0_D_got_init_array_end : Z := 0x22878.
Definition src0_D_got_init_array_start : Z := 0x22880.
Definition src0_D_got_stack_chk_guard : Z := 0x22888.
Definition src0_D_got_fini_array_end : Z := 0x22890.
Definition src0_D_got_fini_array_start : Z := 0x22898.
Definition src0_D_dso_handle : Z := 0x238a0.
Definition src0_D_aef_argc : Z := 0x238b0.
Definition src0_D_stderr_FILE : Z := 0x238d0.
Definition src0_D_stderr_used : Z := 0x239b8.
Definition src0_D_stdout_FILE : Z := 0x239c0.
Definition src0_D_stdout_used : Z := 0x23aa8.
Definition src0_D_default_stacksize : Z := 0x23ab0.
Definition src0_D_do_init_initialized : Z := 0x23ac0.
Definition src0_D_do_init_object : Z := 0x23ac8.
Definition src0_D_do_fini_finalized : Z := 0x23b08.
Definition src0_D_read_stage : Z := 0x23b09.
Definition src0_D_target_run_initialized : Z := 0x33b10.
Definition src0_D_aef_in_callback : Z := 0x33b14.
Definition src0_D_aef_aligned_copy_empty : Z := 0x33b20.
Definition src0_D_environ : Z := 0x33b58.
Definition src0_D_thread_list_lock : Z := 0x53c30.
Definition src0_D_main_tls : Z := 0x53c38.
Definition src0_D_builtin_tls : Z := 0x33b60.
Definition src0_D_finished_atexit : Z := 0x53c70.
Definition src0_D_atexit_lock : Z := 0x53c74.
Definition src0_D_atexit_slot : Z := 0x53c78.
Definition src0_D_atexit_head : Z := 0x53c80.
Definition src0_D_atexit_builtin : Z := 0x53c88.
Definition src0_D_exit_exit_lock : Z := 0x53e90.
Definition src0_D_stack_chk_guard : Z := 0x53e98.
Definition src0_D_sysinfo : Z := 0x53ea0.
Definition src0_D_progname : Z := 0x53ea8.
Definition src0_D_progname_full : Z := 0x53eb0.
Definition src0_D_libc : Z := 0x53eb8.
Definition src0_D_hwcap : Z := 0x53f20.
Definition src0_D_malloc_lock : Z := 0x53f28.
Definition src0_D_malloc_context : Z := 0x53f30.
Definition src0_D_malloc_replaced : Z := 0x542d0.
Definition src0_D_stdin_used : Z := 0x542d8.
Definition src0_D_ofl_lock : Z := 0x542e0.
Definition src0_D_ofl_head : Z := 0x542e8.
Definition src0_D_stderr_buf : Z := 0x542f0.
Definition src0_D_stdout_buf : Z := 0x542f8.
Definition src0_A_realloc : Z := 0x184e8.  Definition src0_E_realloc : Z := 0x184ec.
Definition src0_A_mremap : Z := 0x18a64.  Definition src0_E_mremap : Z := 0x18b38.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
