(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12680.  Definition src0_text_hi : Z := 0x1c23c.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x110dc.
Definition src0_eh_frame_lo : Z := 0x111e0.  Definition src0_eh_frame_hi : Z := 0x11680.
Definition src0_init_array_lo : Z := 0x1d240.  Definition src0_init_array_hi : Z := 0x1d248.
Definition src0_fini_array_lo : Z := 0x1d248.  Definition src0_fini_array_hi : Z := 0x1d250.
Definition src0_data_rel_ro_lo : Z := 0x1d250.  Definition src0_data_rel_ro_hi : Z := 0x1d260.
Definition src0_got_lo : Z := 0x1d260.  Definition src0_got_hi : Z := 0x1d2f8.
Definition src0_data_lo : Z := 0x1e2f8.  Definition src0_data_hi : Z := 0x1e504.
Definition src0_bss_lo : Z := 0x1e510.  Definition src0_bss_hi : Z := 0x4f138.
Definition src0_A_do_init : Z := 0x126c8.  Definition src0_E_do_init : Z := 0x1273c.
Definition src0_A_do_fini : Z := 0x1273c.  Definition src0_E_do_fini : Z := 0x127cc.
Definition src0_A_main : Z := 0x127cc.  Definition src0_E_main : Z := 0x12a90.
Definition src0_A_target_alloc_init : Z := 0x12a90.  Definition src0_E_target_alloc_init : Z := 0x12a94.
Definition src0_A_target_alloc_count : Z := 0x12a94.  Definition src0_E_target_alloc_count : Z := 0x12a9c.
Definition src0_A_target_run : Z := 0x12a9c.  Definition src0_E_target_run : Z := 0x12bf4.
Definition src0_A_aef_exit_guard : Z := 0x12bf4.  Definition src0_E_aef_exit_guard : Z := 0x12c24.
Definition src0_A_emit_printf : Z := 0x12c24.  Definition src0_E_emit_printf : Z := 0x12c6c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12c6c.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x13454.
Definition src0_A_init : Z := 0x13bdc.  Definition src0_E_init : Z := 0x13be0.
Definition src0_A_init_libc : Z := 0x13be0.  Definition src0_E_init_libc : Z := 0x13e0c.
Definition src0_A_libc_start_init : Z := 0x13e0c.  Definition src0_E_libc_start_init : Z := 0x13e58.
Definition src0_A_libc_start_main : Z := 0x13e58.  Definition src0_E_libc_start_main : Z := 0x13eb8.
Definition src0_A_libc_start_main_stage2 : Z := 0x13eb8.  Definition src0_E_libc_start_main_stage2 : Z := 0x13f00.
Definition src0_A_init_tls : Z := 0x13f00.  Definition src0_E_init_tls : Z := 0x141b0.
Definition src0_A_funcs_on_exit : Z := 0x14260.  Definition src0_E_funcs_on_exit : Z := 0x14328.
Definition src0_A_cxa_finalize : Z := 0x14328.  Definition src0_E_cxa_finalize : Z := 0x1432c.
Definition src0_A_atexit : Z := 0x1432c.  Definition src0_E_atexit : Z := 0x143f0.
Definition src0_A_atexit_call : Z := 0x143f0.  Definition src0_E_atexit_call : Z := 0x143f4.
Definition src0_A_fini : Z := 0x143f4.  Definition src0_E_fini : Z := 0x143f8.
Definition src0_A_libc_exit_fini : Z := 0x143f8.  Definition src0_E_libc_exit_fini : Z := 0x14444.
Definition src0_A_exit : Z := 0x14444.  Definition src0_E_exit : Z := 0x144b8.
Definition src0_A_Exit : Z := 0x14244.  Definition src0_E_Exit : Z := 0x14260.
Definition src0_A_open : Z := 0x144b8.  Definition src0_E_open : Z := 0x1459c.
Definition src0_A_init_ssp : Z := 0x1459c.  Definition src0_E_init_ssp : Z := 0x145fc.
Definition src0_A_stack_chk_fail : Z := 0x145fc.  Definition src0_E_stack_chk_fail : Z := 0x14604.
Definition src0_A_syscall_ret : Z := 0x14604.  Definition src0_E_syscall_ret : Z := 0x1463c.
Definition src0_A_errno_location : Z := 0x1463c.  Definition src0_E_errno_location : Z := 0x14648.
Definition src0_A_free : Z := 0x14648.  Definition src0_E_free : Z := 0x1464c.
Definition src0_A_libc_calloc : Z := 0x1464c.  Definition src0_E_libc_calloc : Z := 0x14784.
Definition src0_A_libc_malloc : Z := 0x14784.  Definition src0_E_libc_malloc : Z := 0x14788.
Definition src0_A_malloc : Z := 0x14788.  Definition src0_E_malloc : Z := 0x1478c.
Definition src0_A_libc_free : Z := 0x1478c.  Definition src0_E_libc_free : Z := 0x14958.
Definition src0_A_get_meta : Z := 0x14958.  Definition src0_E_get_meta : Z := 0x14a68.
Definition src0_A_nontrivial_free : Z := 0x14a68.  Definition src0_E_nontrivial_free : Z := 0x14e40.
Definition src0_A_alloc_meta : Z := 0x14e40.  Definition src0_E_alloc_meta : Z := 0x15118.
Definition src0_A_libc_malloc_impl : Z := 0x15118.  Definition src0_E_libc_malloc_impl : Z := 0x15488.
Definition src0_A_alloc_slot : Z := 0x15488.  Definition src0_E_alloc_slot : Z := 0x15d2c.
Definition src0_A_enframe : Z := 0x15d2c.  Definition src0_E_enframe : Z := 0x15e7c.
Definition src0_A_malloc_allzerop : Z := 0x15e7c.  Definition src0_E_malloc_allzerop : Z := 0x15ff4.
Definition src0_A_vm_wait : Z := 0x15ff4.  Definition src0_E_vm_wait : Z := 0x15ff8.
Definition src0_A_mmap : Z := 0x15ff8.  Definition src0_E_mmap : Z := 0x160e4.
Definition src0_A_mprotect : Z := 0x160e4.  Definition src0_E_mprotect : Z := 0x1612c.
Definition src0_A_munmap : Z := 0x1612c.  Definition src0_E_munmap : Z := 0x16174.
Definition src0_A_fflush : Z := 0x16248.  Definition src0_E_fflush : Z := 0x163b8.
Definition src0_A_lockfile : Z := 0x163b8.  Definition src0_E_lockfile : Z := 0x164b4.
Definition src0_A_unlockfile : Z := 0x164b4.  Definition src0_E_unlockfile : Z := 0x16514.
Definition src0_A_stdio_write : Z := 0x16a2c.  Definition src0_E_stdio_write : Z := 0x16bbc.
Definition src0_A_aio_close : Z := 0x169fc.  Definition src0_E_aio_close : Z := 0x16a00.
Definition src0_A_stdio_close : Z := 0x16a00.  Definition src0_E_stdio_close : Z := 0x16a2c.
Definition src0_A_fprintf : Z := 0x16514.  Definition src0_E_fprintf : Z := 0x16578.
Definition src0_A_fwritex : Z := 0x16578.  Definition src0_E_fwritex : Z := 0x166b0.
Definition src0_A_fwrite : Z := 0x166b0.  Definition src0_E_fwrite : Z := 0x16768.
Definition src0_A_towrite : Z := 0x16768.  Definition src0_E_towrite : Z := 0x167bc.
Definition src0_A_stdio_exit : Z := 0x167bc.  Definition src0_E_stdio_exit : Z := 0x16960.
Definition src0_A_ofl_lock : Z := 0x16960.  Definition src0_E_ofl_lock : Z := 0x16990.
Definition src0_A_ofl_unlock : Z := 0x16990.  Definition src0_E_ofl_unlock : Z := 0x1699c.
Definition src0_A_stdout_write : Z := 0x16bc4.  Definition src0_E_stdout_write : Z := 0x16c64.
Definition src0_A_vfprintf : Z := 0x16c64.  Definition src0_E_vfprintf : Z := 0x16e14.
Definition src0_A_printf_core : Z := 0x16e14.  Definition src0_E_printf_core : Z := 0x17c44.
Definition src0_A_pop_arg : Z := 0x17c44.  Definition src0_E_pop_arg : Z := 0x17d78.
Definition src0_A_pad : Z := 0x17d78.  Definition src0_E_pad : Z := 0x17e4c.
Definition src0_A_fmt_fp : Z := 0x17e4c.  Definition src0_E_fmt_fp : Z := 0x19514.
Definition src0_A_strerror : Z := 0x19514.  Definition src0_E_strerror : Z := 0x19550.
Definition src0_A_lctrans_impl : Z := 0x19550.  Definition src0_E_lctrans_impl : Z := 0x19554.
Definition src0_A_lctrans : Z := 0x19554.  Definition src0_E_lctrans : Z := 0x19558.
Definition src0_A_wctomb : Z := 0x19558.  Definition src0_E_wctomb : Z := 0x1957c.
Definition src0_A_wcrtomb : Z := 0x1957c.  Definition src0_E_wcrtomb : Z := 0x196a8.
Definition src0_A_extenddftf2 : Z := 0x196a8.  Definition src0_E_extenddftf2 : Z := 0x19838.
Definition src0_A_signbitl : Z := 0x19838.  Definition src0_E_signbitl : Z := 0x19840.
Definition src0_A_fpclassifyl : Z := 0x19840.  Definition src0_E_fpclassifyl : Z := 0x19884.
Definition src0_A_frexpl : Z := 0x19884.  Definition src0_E_frexpl : Z := 0x1995c.
Definition src0_A_letf2 : Z := 0x1995c.  Definition src0_E_letf2 : Z := 0x19a24.
Definition src0_A_multf3 : Z := 0x19a24.  Definition src0_E_multf3 : Z := 0x1a124.
Definition src0_A_floatsitf : Z := 0x1a124.  Definition src0_E_floatsitf : Z := 0x1a22c.
Definition src0_A_scalbn : Z := 0x1a22c.  Definition src0_E_scalbn : Z := 0x1a2c4.
Definition src0_A_subtf3 : Z := 0x1a2c4.  Definition src0_E_subtf3 : Z := 0x1a2d4.
Definition src0_A_addtf3 : Z := 0x1a2d4.  Definition src0_E_addtf3 : Z := 0x1aaa0.
Definition src0_A_fe_getround : Z := 0x1aaa0.  Definition src0_E_fe_getround : Z := 0x1aad0.
Definition src0_A_fe_raise_inexact : Z := 0x1aad0.  Definition src0_E_fe_raise_inexact : Z := 0x1aadc.
Definition src0_A_fixunstfsi : Z := 0x1aadc.  Definition src0_E_fixunstfsi : Z := 0x1ab70.
Definition src0_A_floatunsitf : Z := 0x1ab70.  Definition src0_E_floatunsitf : Z := 0x1ac5c.
Definition src0_A_fixtfsi : Z := 0x1ac5c.  Definition src0_E_fixtfsi : Z := 0x1ad04.
Definition src0_A_divtf3 : Z := 0x1ad04.  Definition src0_E_divtf3 : Z := 0x1b608.
Definition src0_A_vprintf : Z := 0x1b608.  Definition src0_E_vprintf : Z := 0x1b624.
Definition src0_A_bcmp : Z := 0x1b7cc.  Definition src0_E_bcmp : Z := 0x1b7d0.
Definition src0_A_memcmp : Z := 0x1b89c.  Definition src0_E_memcmp : Z := 0x1b8cc.
Definition src0_A_memcpy : Z := 0x1b8cc.  Definition src0_E_memcpy : Z := 0x1bcd0.
Definition src0_A_memset : Z := 0x1bcd0.  Definition src0_E_memset : Z := 0x1bdc8.
Definition src0_A_strnlen : Z := 0x1be28.  Definition src0_E_strnlen : Z := 0x1be6c.
Definition src0_A_memchr : Z := 0x1b7d0.  Definition src0_E_memchr : Z := 0x1b89c.
Definition src0_A_lock : Z := 0x1be6c.  Definition src0_E_lock : Z := 0x1c0f4.
Definition src0_A_unlock : Z := 0x1c0f4.  Definition src0_E_unlock : Z := 0x1c168.
Definition src0_A_syscall_cp_c : Z := 0x1c168.  Definition src0_E_syscall_cp_c : Z := 0x1c18c.
Definition src0_A_syscall_cp : Z := 0x1c18c.  Definition src0_E_syscall_cp : Z := 0x1c190.
Definition src0_A_unistd_exit : Z := 0x1c19c.  Definition src0_E_unistd_exit : Z := 0x1c1a8.
Definition src0_A_close : Z := 0x1c1a8.  Definition src0_E_close : Z := 0x1c1fc.
Definition src0_A_lseek : Z := 0x1c1fc.  Definition src0_E_lseek : Z := 0x1c208.
Definition src0_A_read : Z := 0x1c208.  Definition src0_E_read : Z := 0x1c23c.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b5.
Definition src0_D_str_d_n : Z := 0x102c9.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d0.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e1.
Definition src0_D_str_inf : Z := 0x10301.
Definition src0_D_str_INF : Z := 0x10308.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1030c.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1032d.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10342.
Definition src0_D_str_NAN : Z := 0x10359.
Definition src0_D_str_nan : Z := 0x1035d.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10361.
Definition src0_D_str_dev_null : Z := 0x10381.
Definition src0_D_str_null : Z := 0x1038b.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10600.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10610.
Definition src0_D_debruijn32 : Z := 0x103f4.
Definition src0_D_size_classes : Z := 0x10414.
Definition src0_D_small_cnt_tab : Z := 0x10474.
Definition src0_D_med_cnt_tab : Z := 0x1048f.
Definition src0_D_states : Z := 0x10640.
Definition src0_D_xdigits : Z := 0x10810.
Definition src0_D_errmsgstr : Z := 0x10820.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x10fc8.
Definition src0_D_fe_getround : Z := 0x110d0.
Definition src0_D_EH_FRAME_LIST : Z := 0x111e0.
Definition src0_D_init_array_start : Z := 0x1d240.
Definition src0_D_fini_array_start : Z := 0x1d248.
Definition src0_D_stderr : Z := 0x1d250.
Definition src0_D_stdout : Z := 0x1d258.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1d260.
Definition src0_D_got_DYNAMIC : Z := 0x1d268.
Definition src0_D_got_main : Z := 0x1d270.
Definition src0_D_got_init : Z := 0x1d278.
Definition src0_D_got_fini : Z := 0x1d280.
Definition src0_D_got_register_frame_info : Z := 0x1d288.
Definition src0_D_got_cxa_finalize : Z := 0x1d290.
Definition src0_D_got_deregister_frame_info : Z := 0x1d298.
Definition src0_D_got_stderr : Z := 0x1d2a0.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1d2a8.
Definition src0_D_got_stdout : Z := 0x1d2b0.
Definition src0_D_got_environ : Z := 0x1d2b8.
Definition src0_D_got_progname_full : Z := 0x1d2c0.
Definition src0_D_got_progname : Z := 0x1d2c8.
Definition src0_D_got_init_array_end : Z := 0x1d2d0.
Definition src0_D_got_init_array_start : Z := 0x1d2d8.
Definition src0_D_got_stack_chk_guard : Z := 0x1d2e0.
Definition src0_D_got_fini_array_end : Z := 0x1d2e8.
Definition src0_D_got_fini_array_start : Z := 0x1d2f0.
Definition src0_D_dso_handle : Z := 0x1e2f8.
Definition src0_D_aef_argc : Z := 0x1e308.
Definition src0_D_stderr_FILE : Z := 0x1e320.
Definition src0_D_stderr_used : Z := 0x1e408.
Definition src0_D_stdout_FILE : Z := 0x1e410.
Definition src0_D_stdout_used : Z := 0x1e4f8.
Definition src0_D_default_stacksize : Z := 0x1e500.
Definition src0_D_do_init_initialized : Z := 0x1e510.
Definition src0_D_do_init_object : Z := 0x1e518.
Definition src0_D_do_fini_finalized : Z := 0x1e558.
Definition src0_D_read_stage : Z := 0x1e559.
Definition src0_D_target_run_initialized : Z := 0x2e560.
Definition src0_D_aef_in_callback : Z := 0x2e564.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2e570.
Definition src0_D_environ : Z := 0x2e590.
Definition src0_D_thread_list_lock : Z := 0x4e668.
Definition src0_D_main_tls : Z := 0x4e670.
Definition src0_D_builtin_tls : Z := 0x2e598.
Definition src0_D_finished_atexit : Z := 0x4e6a8.
Definition src0_D_atexit_lock : Z := 0x4e6ac.
Definition src0_D_atexit_slot : Z := 0x4e6b0.
Definition src0_D_atexit_head : Z := 0x4e6b8.
Definition src0_D_atexit_builtin : Z := 0x4e6c0.
Definition src0_D_exit_exit_lock : Z := 0x4e8c8.
Definition src0_D_stack_chk_guard : Z := 0x4e8d0.
Definition src0_D_sysinfo : Z := 0x4e8d8.
Definition src0_D_progname : Z := 0x4e8e0.
Definition src0_D_progname_full : Z := 0x4e8e8.
Definition src0_D_libc : Z := 0x4e8f0.
Definition src0_D_hwcap : Z := 0x4e958.
Definition src0_D_malloc_lock : Z := 0x4e960.
Definition src0_D_malloc_context : Z := 0x4e968.
Definition src0_D_malloc_replaced : Z := 0x4ed08.
Definition src0_D_stdin_used : Z := 0x4ed10.
Definition src0_D_ofl_lock : Z := 0x4ed18.
Definition src0_D_ofl_head : Z := 0x4ed20.
Definition src0_D_stderr_buf : Z := 0x4ed28.
Definition src0_D_stdout_buf : Z := 0x4ed30.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
