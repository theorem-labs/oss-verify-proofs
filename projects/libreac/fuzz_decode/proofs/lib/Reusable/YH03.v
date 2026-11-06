(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12674.  Definition src0_text_hi : Z := 0x1c010.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11114.
Definition src0_eh_frame_lo : Z := 0x11220.  Definition src0_eh_frame_hi : Z := 0x11674.
Definition src0_init_array_lo : Z := 0x1d010.  Definition src0_init_array_hi : Z := 0x1d018.
Definition src0_fini_array_lo : Z := 0x1d018.  Definition src0_fini_array_hi : Z := 0x1d020.
Definition src0_data_rel_ro_lo : Z := 0x1d020.  Definition src0_data_rel_ro_hi : Z := 0x1d030.
Definition src0_got_lo : Z := 0x1d030.  Definition src0_got_hi : Z := 0x1d0e0.
Definition src0_data_lo : Z := 0x1e0e0.  Definition src0_data_hi : Z := 0x1e2ec.
Definition src0_bss_lo : Z := 0x1e2f0.  Definition src0_bss_hi : Z := 0x4ef18.
Definition src0_A_do_init : Z := 0x126bc.  Definition src0_E_do_init : Z := 0x12730.
Definition src0_A_do_fini : Z := 0x12730.  Definition src0_E_do_fini : Z := 0x127c0.
Definition src0_A_main : Z := 0x127c0.  Definition src0_E_main : Z := 0x12a84.
Definition src0_A_target_alloc_init : Z := 0x12a84.  Definition src0_E_target_alloc_init : Z := 0x12a88.
Definition src0_A_target_alloc_count : Z := 0x12a88.  Definition src0_E_target_alloc_count : Z := 0x12a90.
Definition src0_A_target_run : Z := 0x12a90.  Definition src0_E_target_run : Z := 0x12be8.
Definition src0_A_aef_exit_guard : Z := 0x12be8.  Definition src0_E_aef_exit_guard : Z := 0x12c18.
Definition src0_A_emit_printf : Z := 0x12c18.  Definition src0_E_emit_printf : Z := 0x12c60.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12c60.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x132f8.
Definition src0_A_init : Z := 0x13ae0.  Definition src0_E_init : Z := 0x13ae4.
Definition src0_A_init_libc : Z := 0x13ae4.  Definition src0_E_init_libc : Z := 0x13d10.
Definition src0_A_libc_start_init : Z := 0x13d10.  Definition src0_E_libc_start_init : Z := 0x13d5c.
Definition src0_A_libc_start_main : Z := 0x13d5c.  Definition src0_E_libc_start_main : Z := 0x13dbc.
Definition src0_A_libc_start_main_stage2 : Z := 0x13dbc.  Definition src0_E_libc_start_main_stage2 : Z := 0x13e04.
Definition src0_A_init_tls : Z := 0x13e04.  Definition src0_E_init_tls : Z := 0x140b4.
Definition src0_A_funcs_on_exit : Z := 0x14164.  Definition src0_E_funcs_on_exit : Z := 0x1422c.
Definition src0_A_cxa_finalize : Z := 0x1422c.  Definition src0_E_cxa_finalize : Z := 0x14230.
Definition src0_A_atexit : Z := 0x14230.  Definition src0_E_atexit : Z := 0x142f4.
Definition src0_A_atexit_call : Z := 0x142f4.  Definition src0_E_atexit_call : Z := 0x142f8.
Definition src0_A_fini : Z := 0x142f8.  Definition src0_E_fini : Z := 0x142fc.
Definition src0_A_libc_exit_fini : Z := 0x142fc.  Definition src0_E_libc_exit_fini : Z := 0x14348.
Definition src0_A_exit : Z := 0x14348.  Definition src0_E_exit : Z := 0x143bc.
Definition src0_A_Exit : Z := 0x14148.  Definition src0_E_Exit : Z := 0x14164.
Definition src0_A_open : Z := 0x14424.  Definition src0_E_open : Z := 0x14508.
Definition src0_A_init_ssp : Z := 0x143bc.  Definition src0_E_init_ssp : Z := 0x1441c.
Definition src0_A_stack_chk_fail : Z := 0x1441c.  Definition src0_E_stack_chk_fail : Z := 0x14424.
Definition src0_A_syscall_ret : Z := 0x14508.  Definition src0_E_syscall_ret : Z := 0x14540.
Definition src0_A_errno_location : Z := 0x14540.  Definition src0_E_errno_location : Z := 0x1454c.
Definition src0_A_free : Z := 0x14684.  Definition src0_E_free : Z := 0x14688.
Definition src0_A_libc_calloc : Z := 0x14688.  Definition src0_E_libc_calloc : Z := 0x147c0.
Definition src0_A_libc_malloc : Z := 0x147c0.  Definition src0_E_libc_malloc : Z := 0x147c4.
Definition src0_A_malloc : Z := 0x147c4.  Definition src0_E_malloc : Z := 0x147c8.
Definition src0_A_libc_free : Z := 0x147c8.  Definition src0_E_libc_free : Z := 0x14994.
Definition src0_A_get_meta : Z := 0x14994.  Definition src0_E_get_meta : Z := 0x14aa4.
Definition src0_A_nontrivial_free : Z := 0x14aa4.  Definition src0_E_nontrivial_free : Z := 0x14e7c.
Definition src0_A_alloc_meta : Z := 0x14e7c.  Definition src0_E_alloc_meta : Z := 0x15154.
Definition src0_A_libc_malloc_impl : Z := 0x15154.  Definition src0_E_libc_malloc_impl : Z := 0x154c4.
Definition src0_A_alloc_slot : Z := 0x154c4.  Definition src0_E_alloc_slot : Z := 0x15d68.
Definition src0_A_enframe : Z := 0x15d68.  Definition src0_E_enframe : Z := 0x15eb8.
Definition src0_A_malloc_allzerop : Z := 0x15eb8.  Definition src0_E_malloc_allzerop : Z := 0x16030.
Definition src0_A_vm_wait : Z := 0x16030.  Definition src0_E_vm_wait : Z := 0x16034.
Definition src0_A_mmap : Z := 0x16034.  Definition src0_E_mmap : Z := 0x16120.
Definition src0_A_mprotect : Z := 0x16120.  Definition src0_E_mprotect : Z := 0x16168.
Definition src0_A_munmap : Z := 0x16168.  Definition src0_E_munmap : Z := 0x161b0.
Definition src0_A_fflush : Z := 0x16284.  Definition src0_E_fflush : Z := 0x163f4.
Definition src0_A_lockfile : Z := 0x163f4.  Definition src0_E_lockfile : Z := 0x164f0.
Definition src0_A_unlockfile : Z := 0x164f0.  Definition src0_E_unlockfile : Z := 0x16550.
Definition src0_A_stdio_write : Z := 0x16a08.  Definition src0_E_stdio_write : Z := 0x16b98.
Definition src0_A_stdio_seek : Z := 0x16b98.  Definition src0_E_stdio_seek : Z := 0x16ba0.
Definition src0_A_aio_close : Z := 0x169d8.  Definition src0_E_aio_close : Z := 0x169dc.
Definition src0_A_stdio_close : Z := 0x169dc.  Definition src0_E_stdio_close : Z := 0x16a08.
Definition src0_A_fprintf : Z := 0x16550.  Definition src0_E_fprintf : Z := 0x165b4.
Definition src0_A_fwritex : Z := 0x165b4.  Definition src0_E_fwritex : Z := 0x166ec.
Definition src0_A_fwrite : Z := 0x166ec.  Definition src0_E_fwrite : Z := 0x167a4.
Definition src0_A_towrite : Z := 0x167a4.  Definition src0_E_towrite : Z := 0x167f8.
Definition src0_A_stdio_exit : Z := 0x167f8.  Definition src0_E_stdio_exit : Z := 0x1699c.
Definition src0_A_ofl_lock : Z := 0x1699c.  Definition src0_E_ofl_lock : Z := 0x169cc.
Definition src0_A_ofl_unlock : Z := 0x169cc.  Definition src0_E_ofl_unlock : Z := 0x169d8.
Definition src0_A_stdout_write : Z := 0x16ba0.  Definition src0_E_stdout_write : Z := 0x16c40.
Definition src0_A_vfprintf : Z := 0x16c40.  Definition src0_E_vfprintf : Z := 0x16df0.
Definition src0_A_printf_core : Z := 0x16df0.  Definition src0_E_printf_core : Z := 0x17c20.
Definition src0_A_pop_arg : Z := 0x17c20.  Definition src0_E_pop_arg : Z := 0x17d54.
Definition src0_A_pad : Z := 0x17d54.  Definition src0_E_pad : Z := 0x17e28.
Definition src0_A_fmt_fp : Z := 0x17e28.  Definition src0_E_fmt_fp : Z := 0x194f0.
Definition src0_A_strerror : Z := 0x194f0.  Definition src0_E_strerror : Z := 0x1952c.
Definition src0_A_lctrans_impl : Z := 0x1952c.  Definition src0_E_lctrans_impl : Z := 0x19530.
Definition src0_A_lctrans : Z := 0x19530.  Definition src0_E_lctrans : Z := 0x19534.
Definition src0_A_wctomb : Z := 0x19534.  Definition src0_E_wctomb : Z := 0x19558.
Definition src0_A_wcrtomb : Z := 0x19558.  Definition src0_E_wcrtomb : Z := 0x19684.
Definition src0_A_extenddftf2 : Z := 0x19684.  Definition src0_E_extenddftf2 : Z := 0x19814.
Definition src0_A_signbitl : Z := 0x19814.  Definition src0_E_signbitl : Z := 0x1981c.
Definition src0_A_fpclassifyl : Z := 0x1981c.  Definition src0_E_fpclassifyl : Z := 0x19860.
Definition src0_A_frexpl : Z := 0x19860.  Definition src0_E_frexpl : Z := 0x19938.
Definition src0_A_letf2 : Z := 0x19938.  Definition src0_E_letf2 : Z := 0x19a00.
Definition src0_A_multf3 : Z := 0x19a00.  Definition src0_E_multf3 : Z := 0x1a100.
Definition src0_A_floatsitf : Z := 0x1a100.  Definition src0_E_floatsitf : Z := 0x1a208.
Definition src0_A_scalbn : Z := 0x1a208.  Definition src0_E_scalbn : Z := 0x1a2a0.
Definition src0_A_subtf3 : Z := 0x1a2a0.  Definition src0_E_subtf3 : Z := 0x1a2b0.
Definition src0_A_addtf3 : Z := 0x1a2b0.  Definition src0_E_addtf3 : Z := 0x1aa7c.
Definition src0_A_fe_getround : Z := 0x1aa7c.  Definition src0_E_fe_getround : Z := 0x1aaac.
Definition src0_A_fe_raise_inexact : Z := 0x1aaac.  Definition src0_E_fe_raise_inexact : Z := 0x1aab8.
Definition src0_A_fixunstfsi : Z := 0x1aab8.  Definition src0_E_fixunstfsi : Z := 0x1ab4c.
Definition src0_A_floatunsitf : Z := 0x1ab4c.  Definition src0_E_floatunsitf : Z := 0x1ac38.
Definition src0_A_fixtfsi : Z := 0x1ac38.  Definition src0_E_fixtfsi : Z := 0x1ace0.
Definition src0_A_divtf3 : Z := 0x1ace0.  Definition src0_E_divtf3 : Z := 0x1b5e4.
Definition src0_A_vprintf : Z := 0x1b5e4.  Definition src0_E_vprintf : Z := 0x1b600.
Definition src0_A_bcmp : Z := 0x1b600.  Definition src0_E_bcmp : Z := 0x1b604.
Definition src0_A_memcmp : Z := 0x1b604.  Definition src0_E_memcmp : Z := 0x1b634.
Definition src0_A_memcpy : Z := 0x1b634.  Definition src0_E_memcpy : Z := 0x1ba38.
Definition src0_A_memset : Z := 0x1ba38.  Definition src0_E_memset : Z := 0x1bb30.
Definition src0_A_strnlen : Z := 0x1bb30.  Definition src0_E_strnlen : Z := 0x1bb74.
Definition src0_A_memchr : Z := 0x1bb74.  Definition src0_E_memchr : Z := 0x1bc40.
Definition src0_A_lock : Z := 0x1bc40.  Definition src0_E_lock : Z := 0x1bec8.
Definition src0_A_unlock : Z := 0x1bec8.  Definition src0_E_unlock : Z := 0x1bf3c.
Definition src0_A_syscall_cp_c : Z := 0x1bf3c.  Definition src0_E_syscall_cp_c : Z := 0x1bf60.
Definition src0_A_syscall_cp : Z := 0x1bf60.  Definition src0_E_syscall_cp : Z := 0x1bf64.
Definition src0_A_unistd_exit : Z := 0x1bf70.  Definition src0_E_unistd_exit : Z := 0x1bf7c.
Definition src0_A_close : Z := 0x1bf7c.  Definition src0_E_close : Z := 0x1bfd0.
Definition src0_A_lseek : Z := 0x1bfd0.  Definition src0_E_lseek : Z := 0x1bfdc.
Definition src0_A_read : Z := 0x1bfdc.  Definition src0_E_read : Z := 0x1c010.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a2.
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
Definition src0_D_const_double_0x1p28 : Z := 0x10390.
Definition src0_D_const_double_1_0 : Z := 0x103a8.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b0.
Definition src0_D_const_double_0_5 : Z := 0x103b8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103c0.
Definition src0_D_const_double_0x1p1023 : Z := 0x103c8.
Definition src0_D_const_double_1_5 : Z := 0x103d0.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x103d8.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x103e0.
Definition src0_D_const_double_0x1p120 : Z := 0x103f0.
Definition src0_D_debruijn32 : Z := 0x10480.
Definition src0_D_size_classes : Z := 0x104a0.
Definition src0_D_small_cnt_tab : Z := 0x10500.
Definition src0_D_med_cnt_tab : Z := 0x10420.
Definition src0_D_jt_printf_core_1 : Z := 0x10530.
Definition src0_D_jt_printf_core_2 : Z := 0x10610.
Definition src0_D_jt_pop_arg : Z := 0x10630.
Definition src0_D_states : Z := 0x10678.
Definition src0_D_xdigits : Z := 0x10848.
Definition src0_D_errmsgstr : Z := 0x10858.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11000.
Definition src0_D_fe_getround : Z := 0x11108.
Definition src0_D_EH_FRAME_LIST : Z := 0x11220.
Definition src0_D_init_array_start : Z := 0x1d010.
Definition src0_D_fini_array_start : Z := 0x1d018.
Definition src0_D_stderr : Z := 0x1d020.
Definition src0_D_stdout : Z := 0x1d028.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1d030.
Definition src0_D_got_DYNAMIC : Z := 0x1d038.
Definition src0_D_got_main : Z := 0x1d040.
Definition src0_D_got_init : Z := 0x1d048.
Definition src0_D_got_fini : Z := 0x1d050.
Definition src0_D_got_register_frame_info : Z := 0x1d058.
Definition src0_D_got_cxa_finalize : Z := 0x1d060.
Definition src0_D_got_deregister_frame_info : Z := 0x1d068.
Definition src0_D_got_stderr : Z := 0x1d070.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1d078.
Definition src0_D_got_stdout : Z := 0x1d080.
Definition src0_D_got_environ : Z := 0x1d0a0.
Definition src0_D_got_progname_full : Z := 0x1d0a8.
Definition src0_D_got_progname : Z := 0x1d0b0.
Definition src0_D_got_init_array_end : Z := 0x1d0b8.
Definition src0_D_got_init_array_start : Z := 0x1d0c0.
Definition src0_D_got_stack_chk_guard : Z := 0x1d0c8.
Definition src0_D_got_fini_array_end : Z := 0x1d0d0.
Definition src0_D_got_fini_array_start : Z := 0x1d0d8.
Definition src0_D_dso_handle : Z := 0x1e0e0.
Definition src0_D_aef_arg0 : Z := 0x1e0e8.
Definition src0_D_aef_argc : Z := 0x1e0f0.
Definition src0_D_aef_argv : Z := 0x1e0f8.
Definition src0_D_stderr_FILE : Z := 0x1e108.
Definition src0_D_stderr_used : Z := 0x1e1f0.
Definition src0_D_stdout_FILE : Z := 0x1e1f8.
Definition src0_D_stdout_used : Z := 0x1e2e0.
Definition src0_D_default_stacksize : Z := 0x1e2e8.
Definition src0_D_do_init_initialized : Z := 0x1e2f0.
Definition src0_D_do_init_object : Z := 0x1e2f8.
Definition src0_D_do_fini_finalized : Z := 0x1e338.
Definition src0_D_read_stage : Z := 0x1e339.
Definition src0_D_target_run_initialized : Z := 0x2e340.
Definition src0_D_aef_in_callback : Z := 0x2e344.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2e350.
Definition src0_D_environ : Z := 0x2e370.
Definition src0_D_thread_list_lock : Z := 0x4e448.
Definition src0_D_main_tls : Z := 0x4e450.
Definition src0_D_builtin_tls : Z := 0x2e378.
Definition src0_D_finished_atexit : Z := 0x4e488.
Definition src0_D_atexit_lock : Z := 0x4e48c.
Definition src0_D_atexit_slot : Z := 0x4e490.
Definition src0_D_atexit_head : Z := 0x4e498.
Definition src0_D_atexit_builtin : Z := 0x4e4a0.
Definition src0_D_exit_exit_lock : Z := 0x4e6a8.
Definition src0_D_stack_chk_guard : Z := 0x4e6b0.
Definition src0_D_sysinfo : Z := 0x4e6b8.
Definition src0_D_progname : Z := 0x4e6c0.
Definition src0_D_progname_full : Z := 0x4e6c8.
Definition src0_D_libc : Z := 0x4e6d0.
Definition src0_D_hwcap : Z := 0x4e738.
Definition src0_D_malloc_lock : Z := 0x4e740.
Definition src0_D_malloc_context : Z := 0x4e748.
Definition src0_D_malloc_replaced : Z := 0x4eae8.
Definition src0_D_stdin_used : Z := 0x4eaf0.
Definition src0_D_ofl_lock : Z := 0x4eaf8.
Definition src0_D_ofl_head : Z := 0x4eb00.
Definition src0_D_stderr_buf : Z := 0x4eb08.
Definition src0_D_stdout_buf : Z := 0x4eb10.
Definition src0_A_calloc : Z := 0x1454c.  Definition src0_E_calloc : Z := 0x14684.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
