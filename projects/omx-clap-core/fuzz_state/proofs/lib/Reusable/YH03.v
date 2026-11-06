(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12d30.  Definition src0_text_hi : Z := 0x210fc.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x111fc.
Definition src0_eh_frame_lo : Z := 0x113e8.  Definition src0_eh_frame_hi : Z := 0x11d30.
Definition src0_init_array_lo : Z := 0x22100.  Definition src0_init_array_hi : Z := 0x22108.
Definition src0_fini_array_lo : Z := 0x22108.  Definition src0_fini_array_hi : Z := 0x22110.
Definition src0_data_rel_ro_lo : Z := 0x22110.  Definition src0_data_rel_ro_hi : Z := 0x22120.
Definition src0_got_lo : Z := 0x22120.  Definition src0_got_hi : Z := 0x221b8.
Definition src0_data_lo : Z := 0x231b8.  Definition src0_data_hi : Z := 0x233cc.
Definition src0_bss_lo : Z := 0x233d0.  Definition src0_bss_hi : Z := 0x54010.
Definition src0_A_do_init : Z := 0x12d78.  Definition src0_E_do_init : Z := 0x12dec.
Definition src0_A_do_fini : Z := 0x12dec.  Definition src0_E_do_fini : Z := 0x12e7c.
Definition src0_A_main : Z := 0x12e7c.  Definition src0_E_main : Z := 0x13140.
Definition src0_A_target_alloc_init : Z := 0x13140.  Definition src0_E_target_alloc_init : Z := 0x13144.
Definition src0_A_target_alloc_count : Z := 0x13144.  Definition src0_E_target_alloc_count : Z := 0x1314c.
Definition src0_A_target_run : Z := 0x1314c.  Definition src0_E_target_run : Z := 0x132a4.
Definition src0_A_aef_exit_guard : Z := 0x132a4.  Definition src0_E_aef_exit_guard : Z := 0x132d4.
Definition src0_A_emit_printf : Z := 0x132d4.  Definition src0_E_emit_printf : Z := 0x1331c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x1331c.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x13440.
Definition src0_A_init : Z := 0x159e8.  Definition src0_E_init : Z := 0x159ec.
Definition src0_A_init_libc : Z := 0x159ec.  Definition src0_E_init_libc : Z := 0x15c18.
Definition src0_A_libc_start_init : Z := 0x15c18.  Definition src0_E_libc_start_init : Z := 0x15c64.
Definition src0_A_libc_start_main : Z := 0x15c64.  Definition src0_E_libc_start_main : Z := 0x15cc4.
Definition src0_A_libc_start_main_stage2 : Z := 0x15cc4.  Definition src0_E_libc_start_main_stage2 : Z := 0x15d0c.
Definition src0_A_init_tls : Z := 0x15d0c.  Definition src0_E_init_tls : Z := 0x15fbc.
Definition src0_A_funcs_on_exit : Z := 0x1606c.  Definition src0_E_funcs_on_exit : Z := 0x16134.
Definition src0_A_cxa_finalize : Z := 0x16134.  Definition src0_E_cxa_finalize : Z := 0x16138.
Definition src0_A_atexit : Z := 0x16138.  Definition src0_E_atexit : Z := 0x161fc.
Definition src0_A_atexit_call : Z := 0x161fc.  Definition src0_E_atexit_call : Z := 0x16200.
Definition src0_A_fini : Z := 0x16200.  Definition src0_E_fini : Z := 0x16204.
Definition src0_A_libc_exit_fini : Z := 0x16204.  Definition src0_E_libc_exit_fini : Z := 0x16250.
Definition src0_A_exit : Z := 0x16250.  Definition src0_E_exit : Z := 0x162c4.
Definition src0_A_Exit : Z := 0x16050.  Definition src0_E_Exit : Z := 0x1606c.
Definition src0_A_open : Z := 0x162c4.  Definition src0_E_open : Z := 0x163a8.
Definition src0_A_init_ssp : Z := 0x163a8.  Definition src0_E_init_ssp : Z := 0x16408.
Definition src0_A_stack_chk_fail : Z := 0x16408.  Definition src0_E_stack_chk_fail : Z := 0x16410.
Definition src0_A_syscall_ret : Z := 0x16410.  Definition src0_E_syscall_ret : Z := 0x16448.
Definition src0_A_errno_location : Z := 0x16448.  Definition src0_E_errno_location : Z := 0x16454.
Definition src0_A_free : Z := 0x16454.  Definition src0_E_free : Z := 0x16458.
Definition src0_A_libc_calloc : Z := 0x16458.  Definition src0_E_libc_calloc : Z := 0x16590.
Definition src0_A_libc_malloc : Z := 0x16590.  Definition src0_E_libc_malloc : Z := 0x16594.
Definition src0_A_malloc : Z := 0x16594.  Definition src0_E_malloc : Z := 0x16598.
Definition src0_A_libc_free : Z := 0x16598.  Definition src0_E_libc_free : Z := 0x16764.
Definition src0_A_get_meta : Z := 0x16764.  Definition src0_E_get_meta : Z := 0x16874.
Definition src0_A_nontrivial_free : Z := 0x16874.  Definition src0_E_nontrivial_free : Z := 0x16c4c.
Definition src0_A_alloc_meta : Z := 0x16c4c.  Definition src0_E_alloc_meta : Z := 0x16f24.
Definition src0_A_libc_malloc_impl : Z := 0x16f24.  Definition src0_E_libc_malloc_impl : Z := 0x17294.
Definition src0_A_alloc_slot : Z := 0x17294.  Definition src0_E_alloc_slot : Z := 0x17b38.
Definition src0_A_enframe : Z := 0x17b38.  Definition src0_E_enframe : Z := 0x17c88.
Definition src0_A_malloc_allzerop : Z := 0x17c88.  Definition src0_E_malloc_allzerop : Z := 0x17e00.
Definition src0_A_vm_wait : Z := 0x18244.  Definition src0_E_vm_wait : Z := 0x18248.
Definition src0_A_mmap : Z := 0x18248.  Definition src0_E_mmap : Z := 0x18334.
Definition src0_A_mprotect : Z := 0x18334.  Definition src0_E_mprotect : Z := 0x1837c.
Definition src0_A_munmap : Z := 0x18450.  Definition src0_E_munmap : Z := 0x18498.
Definition src0_A_fflush : Z := 0x186c8.  Definition src0_E_fflush : Z := 0x18838.
Definition src0_A_lockfile : Z := 0x1856c.  Definition src0_E_lockfile : Z := 0x18668.
Definition src0_A_unlockfile : Z := 0x18668.  Definition src0_E_unlockfile : Z := 0x186c8.
Definition src0_A_stdio_write : Z := 0x18838.  Definition src0_E_stdio_write : Z := 0x189c8.
Definition src0_A_stdio_seek : Z := 0x189c8.  Definition src0_E_stdio_seek : Z := 0x189d0.
Definition src0_A_aio_close : Z := 0x189d0.  Definition src0_E_aio_close : Z := 0x189d4.
Definition src0_A_stdio_close : Z := 0x189d4.  Definition src0_E_stdio_close : Z := 0x18a00.
Definition src0_A_fprintf : Z := 0x18a00.  Definition src0_E_fprintf : Z := 0x18a64.
Definition src0_A_fwritex : Z := 0x18c9c.  Definition src0_E_fwritex : Z := 0x18dd4.
Definition src0_A_fwrite : Z := 0x18dd4.  Definition src0_E_fwrite : Z := 0x18e8c.
Definition src0_A_towrite : Z := 0x18e8c.  Definition src0_E_towrite : Z := 0x18ee0.
Definition src0_A_stdio_exit : Z := 0x18af8.  Definition src0_E_stdio_exit : Z := 0x18c9c.
Definition src0_A_ofl_lock : Z := 0x18ee0.  Definition src0_E_ofl_lock : Z := 0x18f10.
Definition src0_A_ofl_unlock : Z := 0x18f10.  Definition src0_E_ofl_unlock : Z := 0x18f1c.
Definition src0_A_stdout_write : Z := 0x18f7c.  Definition src0_E_stdout_write : Z := 0x1901c.
Definition src0_A_vfprintf : Z := 0x1901c.  Definition src0_E_vfprintf : Z := 0x191cc.
Definition src0_A_printf_core : Z := 0x191cc.  Definition src0_E_printf_core : Z := 0x19ffc.
Definition src0_A_pop_arg : Z := 0x19ffc.  Definition src0_E_pop_arg : Z := 0x1a130.
Definition src0_A_pad : Z := 0x1a130.  Definition src0_E_pad : Z := 0x1a204.
Definition src0_A_fmt_fp : Z := 0x1a204.  Definition src0_E_fmt_fp : Z := 0x1b8cc.
Definition src0_A_strerror : Z := 0x1b8cc.  Definition src0_E_strerror : Z := 0x1b908.
Definition src0_A_lctrans_impl : Z := 0x1b908.  Definition src0_E_lctrans_impl : Z := 0x1b90c.
Definition src0_A_lctrans : Z := 0x1b90c.  Definition src0_E_lctrans : Z := 0x1b910.
Definition src0_A_wctomb : Z := 0x1b910.  Definition src0_E_wctomb : Z := 0x1b934.
Definition src0_A_wcrtomb : Z := 0x1b934.  Definition src0_E_wcrtomb : Z := 0x1ba60.
Definition src0_A_extenddftf2 : Z := 0x1ba60.  Definition src0_E_extenddftf2 : Z := 0x1bbf0.
Definition src0_A_signbitl : Z := 0x1bbf0.  Definition src0_E_signbitl : Z := 0x1bbf8.
Definition src0_A_fpclassifyl : Z := 0x1bbf8.  Definition src0_E_fpclassifyl : Z := 0x1bc3c.
Definition src0_A_frexpl : Z := 0x1bc3c.  Definition src0_E_frexpl : Z := 0x1bd14.
Definition src0_A_letf2 : Z := 0x1bd14.  Definition src0_E_letf2 : Z := 0x1bddc.
Definition src0_A_multf3 : Z := 0x1be98.  Definition src0_E_multf3 : Z := 0x1c598.
Definition src0_A_floatsitf : Z := 0x1c598.  Definition src0_E_floatsitf : Z := 0x1c6a0.
Definition src0_A_scalbn : Z := 0x1c6a0.  Definition src0_E_scalbn : Z := 0x1c738.
Definition src0_A_subtf3 : Z := 0x1c738.  Definition src0_E_subtf3 : Z := 0x1c748.
Definition src0_A_addtf3 : Z := 0x1c748.  Definition src0_E_addtf3 : Z := 0x1cf14.
Definition src0_A_fe_getround : Z := 0x1cf14.  Definition src0_E_fe_getround : Z := 0x1cf44.
Definition src0_A_fe_raise_inexact : Z := 0x1cf44.  Definition src0_E_fe_raise_inexact : Z := 0x1cf50.
Definition src0_A_fixunstfsi : Z := 0x1cf50.  Definition src0_E_fixunstfsi : Z := 0x1cfe4.
Definition src0_A_floatunsitf : Z := 0x1cfe4.  Definition src0_E_floatunsitf : Z := 0x1d0d0.
Definition src0_A_fixtfsi : Z := 0x1d0d0.  Definition src0_E_fixtfsi : Z := 0x1d178.
Definition src0_A_divtf3 : Z := 0x1d178.  Definition src0_E_divtf3 : Z := 0x1da7c.
Definition src0_A_vprintf : Z := 0x1da7c.  Definition src0_E_vprintf : Z := 0x1da98.
Definition src0_A_bcmp : Z := 0x20624.  Definition src0_E_bcmp : Z := 0x20628.
Definition src0_A_memcmp : Z := 0x206f4.  Definition src0_E_memcmp : Z := 0x20724.
Definition src0_A_memcpy : Z := 0x20724.  Definition src0_E_memcpy : Z := 0x20b28.
Definition src0_A_memset : Z := 0x20b28.  Definition src0_E_memset : Z := 0x20c20.
Definition src0_A_strlen : Z := 0x20c58.  Definition src0_E_strlen : Z := 0x20ce8.
Definition src0_A_strnlen : Z := 0x20ce8.  Definition src0_E_strnlen : Z := 0x20d2c.
Definition src0_A_memchr : Z := 0x20628.  Definition src0_E_memchr : Z := 0x206f4.
Definition src0_A_lock : Z := 0x20d2c.  Definition src0_E_lock : Z := 0x20fb4.
Definition src0_A_unlock : Z := 0x20fb4.  Definition src0_E_unlock : Z := 0x21028.
Definition src0_A_syscall_cp_c : Z := 0x21028.  Definition src0_E_syscall_cp_c : Z := 0x2104c.
Definition src0_A_syscall_cp : Z := 0x2104c.  Definition src0_E_syscall_cp : Z := 0x21050.
Definition src0_A_unistd_exit : Z := 0x2105c.  Definition src0_E_unistd_exit : Z := 0x21068.
Definition src0_A_close : Z := 0x21068.  Definition src0_E_close : Z := 0x210bc.
Definition src0_A_lseek : Z := 0x210bc.  Definition src0_E_lseek : Z := 0x210c8.
Definition src0_A_read : Z := 0x210c8.  Definition src0_E_read : Z := 0x210fc.
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
Definition src0_D_EH_FRAME_LIST : Z := 0x113e8.
Definition src0_D_init_array_start : Z := 0x22100.
Definition src0_D_fini_array_start : Z := 0x22108.
Definition src0_D_stderr : Z := 0x22110.
Definition src0_D_stdout : Z := 0x22118.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x22120.
Definition src0_D_got_DYNAMIC : Z := 0x22128.
Definition src0_D_got_main : Z := 0x22130.
Definition src0_D_got_init : Z := 0x22138.
Definition src0_D_got_fini : Z := 0x22140.
Definition src0_D_got_register_frame_info : Z := 0x22148.
Definition src0_D_got_cxa_finalize : Z := 0x22150.
Definition src0_D_got_deregister_frame_info : Z := 0x22158.
Definition src0_D_got_stderr : Z := 0x22160.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x22168.
Definition src0_D_got_stdout : Z := 0x22170.
Definition src0_D_got_environ : Z := 0x22178.
Definition src0_D_got_progname_full : Z := 0x22180.
Definition src0_D_got_progname : Z := 0x22188.
Definition src0_D_got_init_array_end : Z := 0x22190.
Definition src0_D_got_init_array_start : Z := 0x22198.
Definition src0_D_got_stack_chk_guard : Z := 0x221a0.
Definition src0_D_got_fini_array_end : Z := 0x221a8.
Definition src0_D_got_fini_array_start : Z := 0x221b0.
Definition src0_D_dso_handle : Z := 0x231b8.
Definition src0_D_aef_argc : Z := 0x231c8.
Definition src0_D_stderr_FILE : Z := 0x231e8.
Definition src0_D_stderr_used : Z := 0x232d0.
Definition src0_D_stdout_FILE : Z := 0x232d8.
Definition src0_D_stdout_used : Z := 0x233c0.
Definition src0_D_default_stacksize : Z := 0x233c8.
Definition src0_D_do_init_initialized : Z := 0x233d0.
Definition src0_D_do_init_object : Z := 0x233d8.
Definition src0_D_do_fini_finalized : Z := 0x23418.
Definition src0_D_read_stage : Z := 0x23419.
Definition src0_D_target_run_initialized : Z := 0x33420.
Definition src0_D_aef_in_callback : Z := 0x33424.
Definition src0_D_aef_aligned_copy_empty : Z := 0x33430.
Definition src0_D_environ : Z := 0x33468.
Definition src0_D_thread_list_lock : Z := 0x53540.
Definition src0_D_main_tls : Z := 0x53548.
Definition src0_D_builtin_tls : Z := 0x33470.
Definition src0_D_finished_atexit : Z := 0x53580.
Definition src0_D_atexit_lock : Z := 0x53584.
Definition src0_D_atexit_slot : Z := 0x53588.
Definition src0_D_atexit_head : Z := 0x53590.
Definition src0_D_atexit_builtin : Z := 0x53598.
Definition src0_D_exit_exit_lock : Z := 0x537a0.
Definition src0_D_stack_chk_guard : Z := 0x537a8.
Definition src0_D_sysinfo : Z := 0x537b0.
Definition src0_D_progname : Z := 0x537b8.
Definition src0_D_progname_full : Z := 0x537c0.
Definition src0_D_libc : Z := 0x537c8.
Definition src0_D_hwcap : Z := 0x53830.
Definition src0_D_malloc_lock : Z := 0x53838.
Definition src0_D_malloc_context : Z := 0x53840.
Definition src0_D_malloc_replaced : Z := 0x53be0.
Definition src0_D_stdin_used : Z := 0x53be8.
Definition src0_D_ofl_lock : Z := 0x53bf0.
Definition src0_D_ofl_head : Z := 0x53bf8.
Definition src0_D_stderr_buf : Z := 0x53c00.
Definition src0_D_stdout_buf : Z := 0x53c08.
Definition src0_A_realloc : Z := 0x17e00.  Definition src0_E_realloc : Z := 0x17e04.
Definition src0_A_mremap : Z := 0x1837c.  Definition src0_E_mremap : Z := 0x18450.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
