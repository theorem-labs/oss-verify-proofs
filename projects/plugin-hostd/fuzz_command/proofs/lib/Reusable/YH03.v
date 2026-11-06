(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x13a5c.  Definition src0_text_hi : Z := 0x214a8.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x119e6.
Definition src0_eh_frame_lo : Z := 0x11c90.  Definition src0_eh_frame_hi : Z := 0x12a5c.
Definition src0_init_array_lo : Z := 0x224a8.  Definition src0_init_array_hi : Z := 0x224b0.
Definition src0_fini_array_lo : Z := 0x224b0.  Definition src0_fini_array_hi : Z := 0x224b8.
Definition src0_data_rel_ro_lo : Z := 0x224b8.  Definition src0_data_rel_ro_hi : Z := 0x229c8.
Definition src0_got_lo : Z := 0x229c8.  Definition src0_got_hi : Z := 0x22a80.
Definition src0_data_lo : Z := 0x23a80.  Definition src0_data_hi : Z := 0x23c8c.
Definition src0_bss_lo : Z := 0x23c90.  Definition src0_bss_hi : Z := 0x54cb8.

Definition src0_A_do_init : Z := 0x13aa4.  Definition src0_E_do_init : Z := 0x13b18.
Definition src0_A_do_fini : Z := 0x13b18.  Definition src0_E_do_fini : Z := 0x13ba8.
Definition src0_A_main : Z := 0x13ba8.  Definition src0_E_main : Z := 0x13e6c.
Definition src0_A_target_alloc_init : Z := 0x13e6c.  Definition src0_E_target_alloc_init : Z := 0x13e70.
Definition src0_A_target_alloc_count : Z := 0x13e70.  Definition src0_E_target_alloc_count : Z := 0x13e78.
Definition src0_A_target_run : Z := 0x13e78.  Definition src0_E_target_run : Z := 0x13fd0.
Definition src0_A_aef_exit_guard : Z := 0x13fd0.  Definition src0_E_aef_exit_guard : Z := 0x14000.
Definition src0_A_emit_printf : Z := 0x14000.  Definition src0_E_emit_printf : Z := 0x14048.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x14048.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14374.
Definition src0_A_init : Z := 0x17e60.  Definition src0_E_init : Z := 0x17e64.
Definition src0_A_init_libc : Z := 0x17e64.  Definition src0_E_init_libc : Z := 0x18090.
Definition src0_A_libc_start_init : Z := 0x18090.  Definition src0_E_libc_start_init : Z := 0x180dc.
Definition src0_A_libc_start_main : Z := 0x180dc.  Definition src0_E_libc_start_main : Z := 0x1813c.
Definition src0_A_libc_start_main_stage2 : Z := 0x1813c.  Definition src0_E_libc_start_main_stage2 : Z := 0x18184.
Definition src0_A_init_tls : Z := 0x18184.  Definition src0_E_init_tls : Z := 0x18434.
Definition src0_A_funcs_on_exit : Z := 0x184e4.  Definition src0_E_funcs_on_exit : Z := 0x185ac.
Definition src0_A_cxa_finalize : Z := 0x185ac.  Definition src0_E_cxa_finalize : Z := 0x185b0.
Definition src0_A_atexit : Z := 0x185b0.  Definition src0_E_atexit : Z := 0x18674.
Definition src0_A_atexit_call : Z := 0x18674.  Definition src0_E_atexit_call : Z := 0x18678.
Definition src0_A_fini : Z := 0x18678.  Definition src0_E_fini : Z := 0x1867c.
Definition src0_A_libc_exit_fini : Z := 0x1867c.  Definition src0_E_libc_exit_fini : Z := 0x186c8.
Definition src0_A_exit : Z := 0x186c8.  Definition src0_E_exit : Z := 0x1873c.
Definition src0_A_Exit : Z := 0x184c8.  Definition src0_E_Exit : Z := 0x184e4.
Definition src0_A_open : Z := 0x1873c.  Definition src0_E_open : Z := 0x18820.
Definition src0_A_init_ssp : Z := 0x18820.  Definition src0_E_init_ssp : Z := 0x18880.
Definition src0_A_stack_chk_fail : Z := 0x18880.  Definition src0_E_stack_chk_fail : Z := 0x18888.
Definition src0_A_syscall_ret : Z := 0x18888.  Definition src0_E_syscall_ret : Z := 0x188c0.
Definition src0_A_errno_location : Z := 0x188c0.  Definition src0_E_errno_location : Z := 0x188cc.
Definition src0_A_free : Z := 0x188cc.  Definition src0_E_free : Z := 0x188d0.
Definition src0_A_libc_calloc : Z := 0x188d0.  Definition src0_E_libc_calloc : Z := 0x18a08.
Definition src0_A_libc_malloc : Z := 0x18a08.  Definition src0_E_libc_malloc : Z := 0x18a0c.
Definition src0_A_malloc : Z := 0x18a0c.  Definition src0_E_malloc : Z := 0x18a10.
Definition src0_A_libc_free : Z := 0x18a10.  Definition src0_E_libc_free : Z := 0x18bdc.
Definition src0_A_get_meta : Z := 0x18bdc.  Definition src0_E_get_meta : Z := 0x18cec.
Definition src0_A_nontrivial_free : Z := 0x18cec.  Definition src0_E_nontrivial_free : Z := 0x190c4.
Definition src0_A_alloc_meta : Z := 0x190c4.  Definition src0_E_alloc_meta : Z := 0x1939c.
Definition src0_A_libc_malloc_impl : Z := 0x1939c.  Definition src0_E_libc_malloc_impl : Z := 0x1970c.
Definition src0_A_alloc_slot : Z := 0x1970c.  Definition src0_E_alloc_slot : Z := 0x19fb0.
Definition src0_A_enframe : Z := 0x19fb0.  Definition src0_E_enframe : Z := 0x1a100.
Definition src0_A_malloc_allzerop : Z := 0x1a100.  Definition src0_E_malloc_allzerop : Z := 0x1a278.
Definition src0_A_vm_wait : Z := 0x1a278.  Definition src0_E_vm_wait : Z := 0x1a27c.
Definition src0_A_mmap : Z := 0x1a27c.  Definition src0_E_mmap : Z := 0x1a368.
Definition src0_A_mprotect : Z := 0x1a368.  Definition src0_E_mprotect : Z := 0x1a3b0.
Definition src0_A_munmap : Z := 0x1a3b0.  Definition src0_E_munmap : Z := 0x1a3f8.
Definition src0_A_fflush : Z := 0x1a4cc.  Definition src0_E_fflush : Z := 0x1a63c.
Definition src0_A_lockfile : Z := 0x1a63c.  Definition src0_E_lockfile : Z := 0x1a738.
Definition src0_A_unlockfile : Z := 0x1a738.  Definition src0_E_unlockfile : Z := 0x1a798.
Definition src0_A_stdio_write : Z := 0x1ad14.  Definition src0_E_stdio_write : Z := 0x1aea4.
Definition src0_A_stdio_seek : Z := 0x1aea4.  Definition src0_E_stdio_seek : Z := 0x1aeac.
Definition src0_A_aio_close : Z := 0x1ace4.  Definition src0_E_aio_close : Z := 0x1ace8.
Definition src0_A_stdio_close : Z := 0x1ace8.  Definition src0_E_stdio_close : Z := 0x1ad14.
Definition src0_A_fprintf : Z := 0x1a798.  Definition src0_E_fprintf : Z := 0x1a7fc.
Definition src0_A_fwritex : Z := 0x1a7fc.  Definition src0_E_fwritex : Z := 0x1a934.
Definition src0_A_fwrite : Z := 0x1a934.  Definition src0_E_fwrite : Z := 0x1a9ec.
Definition src0_A_towrite : Z := 0x1a9ec.  Definition src0_E_towrite : Z := 0x1aa40.
Definition src0_A_stdio_exit : Z := 0x1aa40.  Definition src0_E_stdio_exit : Z := 0x1abe4.
Definition src0_A_ofl_lock : Z := 0x1abe4.  Definition src0_E_ofl_lock : Z := 0x1ac14.
Definition src0_A_ofl_unlock : Z := 0x1ac14.  Definition src0_E_ofl_unlock : Z := 0x1ac20.
Definition src0_A_stdout_write : Z := 0x1aeac.  Definition src0_E_stdout_write : Z := 0x1af4c.
Definition src0_A_vfprintf : Z := 0x1af4c.  Definition src0_E_vfprintf : Z := 0x1b0fc.
Definition src0_A_printf_core : Z := 0x1b0fc.  Definition src0_E_printf_core : Z := 0x1bf2c.
Definition src0_A_pop_arg : Z := 0x1bf2c.  Definition src0_E_pop_arg : Z := 0x1c060.
Definition src0_A_pad : Z := 0x1c060.  Definition src0_E_pad : Z := 0x1c134.
Definition src0_A_fmt_fp : Z := 0x1c134.  Definition src0_E_fmt_fp : Z := 0x1d7fc.
Definition src0_A_strerror : Z := 0x1d7fc.  Definition src0_E_strerror : Z := 0x1d838.
Definition src0_A_lctrans_impl : Z := 0x1d838.  Definition src0_E_lctrans_impl : Z := 0x1d83c.
Definition src0_A_lctrans : Z := 0x1d83c.  Definition src0_E_lctrans : Z := 0x1d840.
Definition src0_A_wctomb : Z := 0x1d840.  Definition src0_E_wctomb : Z := 0x1d864.
Definition src0_A_wcrtomb : Z := 0x1d864.  Definition src0_E_wcrtomb : Z := 0x1d990.
Definition src0_A_extenddftf2 : Z := 0x1d990.  Definition src0_E_extenddftf2 : Z := 0x1db20.
Definition src0_A_signbitl : Z := 0x1db20.  Definition src0_E_signbitl : Z := 0x1db28.
Definition src0_A_fpclassifyl : Z := 0x1db28.  Definition src0_E_fpclassifyl : Z := 0x1db6c.
Definition src0_A_frexpl : Z := 0x1db6c.  Definition src0_E_frexpl : Z := 0x1dc44.
Definition src0_A_letf2 : Z := 0x1dc44.  Definition src0_E_letf2 : Z := 0x1dd0c.
Definition src0_A_multf3 : Z := 0x1dd0c.  Definition src0_E_multf3 : Z := 0x1e40c.
Definition src0_A_floatsitf : Z := 0x1e40c.  Definition src0_E_floatsitf : Z := 0x1e514.
Definition src0_A_scalbn : Z := 0x1e514.  Definition src0_E_scalbn : Z := 0x1e5ac.
Definition src0_A_subtf3 : Z := 0x1e5ac.  Definition src0_E_subtf3 : Z := 0x1e5bc.
Definition src0_A_addtf3 : Z := 0x1e5bc.  Definition src0_E_addtf3 : Z := 0x1ed88.
Definition src0_A_fe_getround : Z := 0x1ed88.  Definition src0_E_fe_getround : Z := 0x1edb8.
Definition src0_A_fe_raise_inexact : Z := 0x1edb8.  Definition src0_E_fe_raise_inexact : Z := 0x1edc4.
Definition src0_A_fixunstfsi : Z := 0x1edc4.  Definition src0_E_fixunstfsi : Z := 0x1ee58.
Definition src0_A_floatunsitf : Z := 0x1ee58.  Definition src0_E_floatunsitf : Z := 0x1ef44.
Definition src0_A_fixtfsi : Z := 0x1ef44.  Definition src0_E_fixtfsi : Z := 0x1efec.
Definition src0_A_divtf3 : Z := 0x1efec.  Definition src0_E_divtf3 : Z := 0x1f8f0.
Definition src0_A_vprintf : Z := 0x1f8f0.  Definition src0_E_vprintf : Z := 0x1f90c.
Definition src0_A_bcmp : Z := 0x20410.  Definition src0_E_bcmp : Z := 0x20414.
Definition src0_A_memcmp : Z := 0x204e0.  Definition src0_E_memcmp : Z := 0x20510.
Definition src0_A_memcpy : Z := 0x20510.  Definition src0_E_memcpy : Z := 0x20914.
Definition src0_A_memset : Z := 0x20914.  Definition src0_E_memset : Z := 0x20a0c.
Definition src0_A_strchrnul : Z := 0x20c84.  Definition src0_E_strchrnul : Z := 0x20d64.
Definition src0_A_strlen : Z := 0x20dbc.  Definition src0_E_strlen : Z := 0x20e4c.
Definition src0_A_strnlen : Z := 0x20f0c.  Definition src0_E_strnlen : Z := 0x20f50.
Definition src0_A_memchr : Z := 0x20414.  Definition src0_E_memchr : Z := 0x204e0.
Definition src0_A_lock : Z := 0x210d8.  Definition src0_E_lock : Z := 0x21360.
Definition src0_A_unlock : Z := 0x21360.  Definition src0_E_unlock : Z := 0x213d4.
Definition src0_A_syscall_cp_c : Z := 0x213d4.  Definition src0_E_syscall_cp_c : Z := 0x213f8.
Definition src0_A_syscall_cp : Z := 0x213f8.  Definition src0_E_syscall_cp : Z := 0x213fc.

Definition src0_A_unistd_exit : Z := 0x21408.  Definition src0_E_unistd_exit : Z := 0x21414.
Definition src0_A_close : Z := 0x21414.  Definition src0_E_close : Z := 0x21468.
Definition src0_A_lseek : Z := 0x21468.  Definition src0_E_lseek : Z := 0x21474.
Definition src0_A_read : Z := 0x21474.  Definition src0_E_read : Z := 0x214a8.
Definition src0_D_str_n0X0x : Z := 0x102f6.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x10404.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10443.
Definition src0_D_str_d_n : Z := 0x10457.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10558.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10569.
Definition src0_D_str_inf : Z := 0x10668.
Definition src0_D_str_INF : Z := 0x1075c.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10760.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10912.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10927.
Definition src0_D_str_NAN : Z := 0x1097e.
Definition src0_D_str_nan : Z := 0x109b8.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x109cf.
Definition src0_D_str_dev_null : Z := 0x10a2d.
Definition src0_D_str_null : Z := 0x10a19.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10ac0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10ad0.
Definition src0_D_debruijn32 : Z := 0x10c48.
Definition src0_D_size_classes : Z := 0x10c68.
Definition src0_D_small_cnt_tab : Z := 0x10cc8.
Definition src0_D_med_cnt_tab : Z := 0x10ce3.
Definition src0_D_states : Z := 0x10e40.
Definition src0_D_xdigits : Z := 0x11010.
Definition src0_D_errmsgstr : Z := 0x11020.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x117c8.
Definition src0_D_fe_getround : Z := 0x118d0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11c90.
Definition src0_D_init_array_start : Z := 0x224a8.
Definition src0_D_fini_array_start : Z := 0x224b0.
Definition src0_D_stdout : Z := 0x229c0.
Definition src0_D_got_DYNAMIC : Z := 0x229d0.
Definition src0_D_got_main : Z := 0x229d8.
Definition src0_D_got_init : Z := 0x229e0.
Definition src0_D_got_fini : Z := 0x229e8.
Definition src0_D_got_register_frame_info : Z := 0x229f0.
Definition src0_D_got_cxa_finalize : Z := 0x229f8.
Definition src0_D_got_deregister_frame_info : Z := 0x22a00.
Definition src0_D_got_stderr : Z := 0x22a08.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x22a10.
Definition src0_D_got_stdout : Z := 0x22a18.
Definition src0_D_got_environ : Z := 0x22a40.
Definition src0_D_got_progname_full : Z := 0x22a48.
Definition src0_D_got_progname : Z := 0x22a50.
Definition src0_D_got_init_array_end : Z := 0x22a58.
Definition src0_D_got_init_array_start : Z := 0x22a60.
Definition src0_D_got_stack_chk_guard : Z := 0x22a68.
Definition src0_D_got_fini_array_end : Z := 0x22a70.
Definition src0_D_got_fini_array_start : Z := 0x22a78.
Definition src0_D_dso_handle : Z := 0x23a80.
Definition src0_D_aef_argc : Z := 0x23a90.
Definition src0_D_stderr_FILE : Z := 0x23aa8.
Definition src0_D_stderr_used : Z := 0x23b90.
Definition src0_D_stdout_FILE : Z := 0x23b98.
Definition src0_D_stdout_used : Z := 0x23c80.
Definition src0_D_default_stacksize : Z := 0x23c88.
Definition src0_D_do_init_initialized : Z := 0x23c90.
Definition src0_D_do_init_object : Z := 0x23c98.
Definition src0_D_do_fini_finalized : Z := 0x23cd8.
Definition src0_D_read_stage : Z := 0x23cd9.
Definition src0_D_target_run_initialized : Z := 0x33ce0.
Definition src0_D_aef_in_callback : Z := 0x33ce4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x33cf0.
Definition src0_D_environ : Z := 0x34110.
Definition src0_D_thread_list_lock : Z := 0x541e8.
Definition src0_D_main_tls : Z := 0x541f0.
Definition src0_D_builtin_tls : Z := 0x34118.
Definition src0_D_finished_atexit : Z := 0x54228.
Definition src0_D_atexit_lock : Z := 0x5422c.
Definition src0_D_atexit_slot : Z := 0x54230.
Definition src0_D_atexit_head : Z := 0x54238.
Definition src0_D_atexit_builtin : Z := 0x54240.
Definition src0_D_exit_exit_lock : Z := 0x54448.
Definition src0_D_stack_chk_guard : Z := 0x54450.
Definition src0_D_sysinfo : Z := 0x54458.
Definition src0_D_progname : Z := 0x54460.
Definition src0_D_progname_full : Z := 0x54468.
Definition src0_D_libc : Z := 0x54470.
Definition src0_D_hwcap : Z := 0x544d8.
Definition src0_D_malloc_lock : Z := 0x544e0.
Definition src0_D_malloc_context : Z := 0x544e8.
Definition src0_D_malloc_replaced : Z := 0x54888.
Definition src0_D_stdin_used : Z := 0x54890.
Definition src0_D_ofl_lock : Z := 0x54898.
Definition src0_D_ofl_head : Z := 0x548a0.
Definition src0_D_stderr_buf : Z := 0x548a8.
Definition src0_D_stdout_buf : Z := 0x548b0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
