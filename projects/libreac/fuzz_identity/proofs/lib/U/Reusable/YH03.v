(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YH03.v, with its addresses changed; 6 of its 205 lines of code are new or changed and 51 lines of the source are left out. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12910.  Definition src0_text_hi : Z := 0x1d3c8.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x112ec.
Definition src0_eh_frame_lo : Z := 0x11418.  Definition src0_eh_frame_hi : Z := 0x11910.
Definition src0_init_array_lo : Z := 0x1e3c8.  Definition src0_init_array_hi : Z := 0x1e3d0.
Definition src0_fini_array_lo : Z := 0x1e3d0.  Definition src0_fini_array_hi : Z := 0x1e3d8.
Definition src0_data_rel_ro_lo : Z := 0x1e3d8.  Definition src0_data_rel_ro_hi : Z := 0x1f0b8.
Definition src0_got_lo : Z := 0x1f0b8.  Definition src0_got_hi : Z := 0x1f150.
Definition src0_data_lo : Z := 0x20150.  Definition src0_data_hi : Z := 0x2035c.
Definition src0_bss_lo : Z := 0x20360.  Definition src0_bss_hi : Z := 0x50f88.
Definition src0_A_start : Z := 0x12910.  Definition src0_E_start : Z := 0x12958.
Definition src0_A_do_init : Z := 0x12958.  Definition src0_E_do_init : Z := 0x129cc.
Definition src0_A_do_fini : Z := 0x129cc.  Definition src0_E_do_fini : Z := 0x12a5c.
Definition src0_A_main : Z := 0x12a5c.  Definition src0_E_main : Z := 0x12d20.
Definition src0_A_target_alloc_init : Z := 0x12d20.  Definition src0_E_target_alloc_init : Z := 0x12d24.
Definition src0_A_target_alloc_count : Z := 0x12d24.  Definition src0_E_target_alloc_count : Z := 0x12d2c.
Definition src0_A_target_run : Z := 0x12d2c.  Definition src0_E_target_run : Z := 0x12e84.
Definition src0_A_oft_exit_guard : Z := 0x12e84.  Definition src0_E_oft_exit_guard : Z := 0x12eb4.
Definition src0_A_emit_printf : Z := 0x12eb4.  Definition src0_E_emit_printf : Z := 0x12efc.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12efc.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x140f0.
Definition src0_A_init : Z := 0x14f08.  Definition src0_E_init : Z := 0x14f0c.
Definition src0_A_init_libc : Z := 0x14f0c.  Definition src0_E_init_libc : Z := 0x15138.
Definition src0_A_libc_start_init : Z := 0x15138.  Definition src0_E_libc_start_init : Z := 0x15184.
Definition src0_A_libc_start_main : Z := 0x15184.  Definition src0_E_libc_start_main : Z := 0x151e4.
Definition src0_A_libc_start_main_stage2 : Z := 0x151e4.  Definition src0_E_libc_start_main_stage2 : Z := 0x1522c.
Definition src0_A_init_tls : Z := 0x1522c.  Definition src0_E_init_tls : Z := 0x154dc.
Definition src0_A_funcs_on_exit : Z := 0x1558c.  Definition src0_E_funcs_on_exit : Z := 0x15654.
Definition src0_A_cxa_finalize : Z := 0x15654.  Definition src0_E_cxa_finalize : Z := 0x15658.
Definition src0_A_atexit : Z := 0x15658.  Definition src0_E_atexit : Z := 0x1571c.
Definition src0_A_atexit_call : Z := 0x1571c.  Definition src0_E_atexit_call : Z := 0x15720.
Definition src0_A_fini : Z := 0x15720.  Definition src0_E_fini : Z := 0x15724.
Definition src0_A_libc_exit_fini : Z := 0x15724.  Definition src0_E_libc_exit_fini : Z := 0x15770.
Definition src0_A_exit : Z := 0x15770.  Definition src0_E_exit : Z := 0x157e4.
Definition src0_A_Exit : Z := 0x15570.  Definition src0_E_Exit : Z := 0x1558c.
Definition src0_A_open : Z := 0x157e4.  Definition src0_E_open : Z := 0x158c8.
Definition src0_A_init_ssp : Z := 0x158c8.  Definition src0_E_init_ssp : Z := 0x15928.
Definition src0_A_stack_chk_fail : Z := 0x15928.  Definition src0_E_stack_chk_fail : Z := 0x15930.
Definition src0_A_syscall_ret : Z := 0x15930.  Definition src0_E_syscall_ret : Z := 0x15968.
Definition src0_A_errno_location : Z := 0x15968.  Definition src0_E_errno_location : Z := 0x15974.
Definition src0_A_free : Z := 0x15974.  Definition src0_E_free : Z := 0x15978.
Definition src0_A_libc_calloc : Z := 0x15978.  Definition src0_E_libc_calloc : Z := 0x15ab0.
Definition src0_A_libc_malloc : Z := 0x15ab0.  Definition src0_E_libc_malloc : Z := 0x15ab4.
Definition src0_A_malloc : Z := 0x15ab4.  Definition src0_E_malloc : Z := 0x15ab8.
Definition src0_A_libc_free : Z := 0x15ab8.  Definition src0_E_libc_free : Z := 0x15c84.
Definition src0_A_get_meta : Z := 0x15c84.  Definition src0_E_get_meta : Z := 0x15d94.
Definition src0_A_nontrivial_free : Z := 0x15d94.  Definition src0_E_nontrivial_free : Z := 0x1616c.
Definition src0_A_alloc_meta : Z := 0x1616c.  Definition src0_E_alloc_meta : Z := 0x16444.
Definition src0_A_libc_malloc_impl : Z := 0x16444.  Definition src0_E_libc_malloc_impl : Z := 0x167b4.
Definition src0_A_alloc_slot : Z := 0x167b4.  Definition src0_E_alloc_slot : Z := 0x17058.
Definition src0_A_enframe : Z := 0x17058.  Definition src0_E_enframe : Z := 0x171a8.
Definition src0_A_malloc_allzerop : Z := 0x171a8.  Definition src0_E_malloc_allzerop : Z := 0x17320.
Definition src0_A_vm_wait : Z := 0x17320.  Definition src0_E_vm_wait : Z := 0x17324.
Definition src0_A_mmap : Z := 0x17324.  Definition src0_E_mmap : Z := 0x17410.
Definition src0_A_mprotect : Z := 0x17410.  Definition src0_E_mprotect : Z := 0x17458.
Definition src0_A_munmap : Z := 0x17458.  Definition src0_E_munmap : Z := 0x174a0.
Definition src0_A_fflush : Z := 0x17574.  Definition src0_E_fflush : Z := 0x176e4.
Definition src0_A_lockfile : Z := 0x176e4.  Definition src0_E_lockfile : Z := 0x177e0.
Definition src0_A_unlockfile : Z := 0x177e0.  Definition src0_E_unlockfile : Z := 0x17840.
Definition src0_A_stdio_write : Z := 0x17cf8.  Definition src0_E_stdio_write : Z := 0x17e88.
Definition src0_A_stdio_seek : Z := 0x17e88.  Definition src0_E_stdio_seek : Z := 0x17e90.
Definition src0_A_aio_close : Z := 0x17cc8.  Definition src0_E_aio_close : Z := 0x17ccc.
Definition src0_A_stdio_close : Z := 0x17ccc.  Definition src0_E_stdio_close : Z := 0x17cf8.
Definition src0_A_fprintf : Z := 0x17840.  Definition src0_E_fprintf : Z := 0x178a4.
Definition src0_A_fwritex : Z := 0x178a4.  Definition src0_E_fwritex : Z := 0x179dc.
Definition src0_A_fwrite : Z := 0x179dc.  Definition src0_E_fwrite : Z := 0x17a94.
Definition src0_A_towrite : Z := 0x17a94.  Definition src0_E_towrite : Z := 0x17ae8.
Definition src0_A_stdio_exit : Z := 0x17ae8.  Definition src0_E_stdio_exit : Z := 0x17c8c.
Definition src0_A_ofl_lock : Z := 0x17c8c.  Definition src0_E_ofl_lock : Z := 0x17cbc.
Definition src0_A_ofl_unlock : Z := 0x17cbc.  Definition src0_E_ofl_unlock : Z := 0x17cc8.
Definition src0_A_stdout_write : Z := 0x17e90.  Definition src0_E_stdout_write : Z := 0x17f30.
Definition src0_A_vfprintf : Z := 0x17f30.  Definition src0_E_vfprintf : Z := 0x180e0.
Definition src0_A_printf_core : Z := 0x180e0.  Definition src0_E_printf_core : Z := 0x18f10.
Definition src0_A_pop_arg : Z := 0x18f10.  Definition src0_E_pop_arg : Z := 0x19044.
Definition src0_A_pad : Z := 0x19044.  Definition src0_E_pad : Z := 0x19118.
Definition src0_A_fmt_fp : Z := 0x19118.  Definition src0_E_fmt_fp : Z := 0x1a7e0.
Definition src0_A_strerror : Z := 0x1a7e0.  Definition src0_E_strerror : Z := 0x1a81c.
Definition src0_A_lctrans_impl : Z := 0x1a81c.  Definition src0_E_lctrans_impl : Z := 0x1a820.
Definition src0_A_lctrans : Z := 0x1a820.  Definition src0_E_lctrans : Z := 0x1a824.
Definition src0_A_wctomb : Z := 0x1a824.  Definition src0_E_wctomb : Z := 0x1a848.
Definition src0_A_wcrtomb : Z := 0x1a848.  Definition src0_E_wcrtomb : Z := 0x1a974.
Definition src0_A_extenddftf2 : Z := 0x1a974.  Definition src0_E_extenddftf2 : Z := 0x1ab04.
Definition src0_A_signbitl : Z := 0x1ab04.  Definition src0_E_signbitl : Z := 0x1ab0c.
Definition src0_A_fpclassifyl : Z := 0x1ab0c.  Definition src0_E_fpclassifyl : Z := 0x1ab50.
Definition src0_A_frexpl : Z := 0x1ab50.  Definition src0_E_frexpl : Z := 0x1ac28.
Definition src0_A_letf2 : Z := 0x1ac28.  Definition src0_E_letf2 : Z := 0x1acf0.
Definition src0_A_multf3 : Z := 0x1acf0.  Definition src0_E_multf3 : Z := 0x1b3f0.
Definition src0_A_floatsitf : Z := 0x1b3f0.  Definition src0_E_floatsitf : Z := 0x1b4f8.
Definition src0_A_scalbn : Z := 0x1b4f8.  Definition src0_E_scalbn : Z := 0x1b590.
Definition src0_A_subtf3 : Z := 0x1b590.  Definition src0_E_subtf3 : Z := 0x1b5a0.
Definition src0_A_addtf3 : Z := 0x1b5a0.  Definition src0_E_addtf3 : Z := 0x1bd6c.
Definition src0_A_fe_getround : Z := 0x1bd6c.  Definition src0_E_fe_getround : Z := 0x1bd9c.
Definition src0_A_fe_raise_inexact : Z := 0x1bd9c.  Definition src0_E_fe_raise_inexact : Z := 0x1bda8.
Definition src0_A_fixunstfsi : Z := 0x1bda8.  Definition src0_E_fixunstfsi : Z := 0x1be3c.
Definition src0_A_floatunsitf : Z := 0x1be3c.  Definition src0_E_floatunsitf : Z := 0x1bf28.
Definition src0_A_fixtfsi : Z := 0x1bf28.  Definition src0_E_fixtfsi : Z := 0x1bfd0.
Definition src0_A_divtf3 : Z := 0x1bfd0.  Definition src0_E_divtf3 : Z := 0x1c8d4.
Definition src0_A_vprintf : Z := 0x1c8d4.  Definition src0_E_vprintf : Z := 0x1c8f0.
Definition src0_A_bcmp : Z := 0x1c8f0.  Definition src0_E_bcmp : Z := 0x1c8f4.
Definition src0_A_memcmp : Z := 0x1c9c0.  Definition src0_E_memcmp : Z := 0x1c9f0.
Definition src0_A_memcpy : Z := 0x1c9f0.  Definition src0_E_memcpy : Z := 0x1cdf4.
Definition src0_A_memset : Z := 0x1cdf4.  Definition src0_E_memset : Z := 0x1ceec.
Definition src0_A_strlen : Z := 0x1cf24.  Definition src0_E_strlen : Z := 0x1cfb4.
Definition src0_A_strnlen : Z := 0x1cfb4.  Definition src0_E_strnlen : Z := 0x1cff8.
Definition src0_A_memchr : Z := 0x1c8f4.  Definition src0_E_memchr : Z := 0x1c9c0.
Definition src0_A_lock : Z := 0x1cff8.  Definition src0_E_lock : Z := 0x1d280.
Definition src0_A_unlock : Z := 0x1d280.  Definition src0_E_unlock : Z := 0x1d2f4.
Definition src0_A_syscall_cp_c : Z := 0x1d2f4.  Definition src0_E_syscall_cp_c : Z := 0x1d318.
Definition src0_A_syscall_cp : Z := 0x1d318.  Definition src0_E_syscall_cp : Z := 0x1d31c.
Definition src0_A_set_thread_area : Z := 0x1d31c.  Definition src0_E_set_thread_area : Z := 0x1d328.
Definition src0_A_unistd_exit : Z := 0x1d328.  Definition src0_E_unistd_exit : Z := 0x1d334.
Definition src0_A_close : Z := 0x1d334.  Definition src0_E_close : Z := 0x1d388.
Definition src0_A_lseek : Z := 0x1d388.  Definition src0_E_lseek : Z := 0x1d394.
Definition src0_A_read : Z := 0x1d394.  Definition src0_E_read : Z := 0x1d3c8.
Definition src0_D_str_n0X0x : Z := 0x102b7.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x10312.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10325.
Definition src0_D_str_d_n : Z := 0x10339.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10355.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10366.
Definition src0_D_str_inf : Z := 0x103b2.
Definition src0_D_str_INF : Z := 0x10407.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1040b.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x104bd.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x104d2.
Definition src0_D_str_NAN : Z := 0x104ff.
Definition src0_D_str_nan : Z := 0x10503.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1050d.
Definition src0_D_str_dev_null : Z := 0x1053f.
Definition src0_D_str_null : Z := 0x10549.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10560.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10570.
Definition src0_D_debruijn32 : Z := 0x10658.
Definition src0_D_size_classes : Z := 0x10678.
Definition src0_D_small_cnt_tab : Z := 0x106d8.
Definition src0_D_med_cnt_tab : Z := 0x106f3.
Definition src0_D_states : Z := 0x10850.
Definition src0_D_xdigits : Z := 0x10a20.
Definition src0_D_errmsgstr : Z := 0x10a30.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x111d8.
Definition src0_D_fe_getround : Z := 0x112e0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11418.
Definition src0_D_init_array_start : Z := 0x1e3c8.
Definition src0_D_fini_array_start : Z := 0x1e3d0.
Definition src0_D_stdout : Z := 0x1f0b0.
Definition src0_D_got_DYNAMIC : Z := 0x1f0c0.
Definition src0_D_got_main : Z := 0x1f0c8.
Definition src0_D_got_init : Z := 0x1f0d0.
Definition src0_D_got_fini : Z := 0x1f0d8.
Definition src0_D_got_register_frame_info : Z := 0x1f0e0.
Definition src0_D_got_cxa_finalize : Z := 0x1f0e8.
Definition src0_D_got_deregister_frame_info : Z := 0x1f0f0.
Definition src0_D_got_stderr : Z := 0x1f0f8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1f100.
Definition src0_D_got_stdout : Z := 0x1f108.
Definition src0_D_got_environ : Z := 0x1f110.
Definition src0_D_got_progname_full : Z := 0x1f118.
Definition src0_D_got_progname : Z := 0x1f120.
Definition src0_D_got_init_array_end : Z := 0x1f128.
Definition src0_D_got_init_array_start : Z := 0x1f130.
Definition src0_D_got_stack_chk_guard : Z := 0x1f138.
Definition src0_D_got_fini_array_end : Z := 0x1f140.
Definition src0_D_got_fini_array_start : Z := 0x1f148.
Definition src0_D_dso_handle : Z := 0x20150.
Definition src0_D_oft_argc : Z := 0x20160.
Definition src0_D_stderr_FILE : Z := 0x20178.
Definition src0_D_stderr_used : Z := 0x20260.
Definition src0_D_stdout_FILE : Z := 0x20268.
Definition src0_D_stdout_used : Z := 0x20350.
Definition src0_D_default_stacksize : Z := 0x20358.
Definition src0_D_do_init_initialized : Z := 0x20360.
Definition src0_D_do_init_object : Z := 0x20368.
Definition src0_D_do_fini_finalized : Z := 0x203a8.
Definition src0_D_read_stage : Z := 0x203a9.
Definition src0_D_target_run_initialized : Z := 0x303b0.
Definition src0_D_oft_in_callback : Z := 0x303b4.
Definition src0_D_oft_aligned_copy_empty : Z := 0x303c0.
Definition src0_D_environ : Z := 0x303e0.
Definition src0_D_thread_list_lock : Z := 0x504b8.
Definition src0_D_main_tls : Z := 0x504c0.
Definition src0_D_builtin_tls : Z := 0x303e8.
Definition src0_D_finished_atexit : Z := 0x504f8.
Definition src0_D_atexit_lock : Z := 0x504fc.
Definition src0_D_atexit_slot : Z := 0x50500.
Definition src0_D_atexit_head : Z := 0x50508.
Definition src0_D_atexit_builtin : Z := 0x50510.
Definition src0_D_exit_exit_lock : Z := 0x50718.
Definition src0_D_stack_chk_guard : Z := 0x50720.
Definition src0_D_sysinfo : Z := 0x50728.
Definition src0_D_progname : Z := 0x50730.
Definition src0_D_progname_full : Z := 0x50738.
Definition src0_D_libc : Z := 0x50740.
Definition src0_D_hwcap : Z := 0x507a8.
Definition src0_D_malloc_lock : Z := 0x507b0.
Definition src0_D_malloc_context : Z := 0x507b8.
Definition src0_D_malloc_replaced : Z := 0x50b58.
Definition src0_D_stdin_used : Z := 0x50b60.
Definition src0_D_ofl_lock : Z := 0x50b68.
Definition src0_D_ofl_head : Z := 0x50b70.
Definition src0_D_stderr_buf : Z := 0x50b78.
Definition src0_D_stdout_buf : Z := 0x50b80.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
