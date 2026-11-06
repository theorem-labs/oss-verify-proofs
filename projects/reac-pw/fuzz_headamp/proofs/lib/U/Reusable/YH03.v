(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x129bc.  Definition src0_text_hi : Z := 0x1e24c.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x113ea.
Definition src0_eh_frame_lo : Z := 0x11510.  Definition src0_eh_frame_hi : Z := 0x119bc.
Definition src0_init_array_lo : Z := 0x1f250.  Definition src0_init_array_hi : Z := 0x1f258.
Definition src0_fini_array_lo : Z := 0x1f258.  Definition src0_fini_array_hi : Z := 0x1f260.
Definition src0_data_rel_ro_lo : Z := 0x1f260.  Definition src0_data_rel_ro_hi : Z := 0x1f368.
Definition src0_got_lo : Z := 0x1f368.  Definition src0_got_hi : Z := 0x1f400.
Definition src0_data_lo : Z := 0x20400.  Definition src0_data_hi : Z := 0x2060c.
Definition src0_bss_lo : Z := 0x20610.  Definition src0_bss_hi : Z := 0x51238.
Definition src0_A_do_init : Z := 0x12a04.  Definition src0_E_do_init : Z := 0x12a78.
Definition src0_A_do_fini : Z := 0x12a78.  Definition src0_E_do_fini : Z := 0x12b08.
Definition src0_A_main : Z := 0x12b08.  Definition src0_E_main : Z := 0x12dcc.
Definition src0_A_target_alloc_init : Z := 0x12dcc.  Definition src0_E_target_alloc_init : Z := 0x12dd0.
Definition src0_A_target_alloc_count : Z := 0x12dd0.  Definition src0_E_target_alloc_count : Z := 0x12dd8.
Definition src0_A_target_run : Z := 0x12dd8.  Definition src0_E_target_run : Z := 0x12f30.
Definition src0_A_emit_printf : Z := 0x12f60.  Definition src0_E_emit_printf : Z := 0x12fa8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12fa8.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x148ac.
Definition src0_A_init : Z := 0x15d90.  Definition src0_E_init : Z := 0x15d94.
Definition src0_A_init_libc : Z := 0x15d94.  Definition src0_E_init_libc : Z := 0x15fc0.
Definition src0_A_libc_start_init : Z := 0x15fc0.  Definition src0_E_libc_start_init : Z := 0x1600c.
Definition src0_A_libc_start_main : Z := 0x1600c.  Definition src0_E_libc_start_main : Z := 0x1606c.
Definition src0_A_libc_start_main_stage2 : Z := 0x1606c.  Definition src0_E_libc_start_main_stage2 : Z := 0x160b4.
Definition src0_A_init_tls : Z := 0x160b4.  Definition src0_E_init_tls : Z := 0x16364.
Definition src0_A_funcs_on_exit : Z := 0x16414.  Definition src0_E_funcs_on_exit : Z := 0x164dc.
Definition src0_A_cxa_finalize : Z := 0x164dc.  Definition src0_E_cxa_finalize : Z := 0x164e0.
Definition src0_A_atexit : Z := 0x164e0.  Definition src0_E_atexit : Z := 0x165a4.
Definition src0_A_atexit_call : Z := 0x165a4.  Definition src0_E_atexit_call : Z := 0x165a8.
Definition src0_A_fini : Z := 0x165a8.  Definition src0_E_fini : Z := 0x165ac.
Definition src0_A_libc_exit_fini : Z := 0x165ac.  Definition src0_E_libc_exit_fini : Z := 0x165f8.
Definition src0_A_exit : Z := 0x165f8.  Definition src0_E_exit : Z := 0x1666c.
Definition src0_A_Exit : Z := 0x163f8.  Definition src0_E_Exit : Z := 0x16414.
Definition src0_A_open : Z := 0x1666c.  Definition src0_E_open : Z := 0x16750.
Definition src0_A_init_ssp : Z := 0x16750.  Definition src0_E_init_ssp : Z := 0x167b0.
Definition src0_A_stack_chk_fail : Z := 0x167b0.  Definition src0_E_stack_chk_fail : Z := 0x167b8.
Definition src0_A_syscall_ret : Z := 0x167b8.  Definition src0_E_syscall_ret : Z := 0x167f0.
Definition src0_A_errno_location : Z := 0x167f0.  Definition src0_E_errno_location : Z := 0x167fc.
Definition src0_A_free : Z := 0x167fc.  Definition src0_E_free : Z := 0x16800.
Definition src0_A_libc_calloc : Z := 0x16800.  Definition src0_E_libc_calloc : Z := 0x16938.
Definition src0_A_libc_malloc : Z := 0x16938.  Definition src0_E_libc_malloc : Z := 0x1693c.
Definition src0_A_malloc : Z := 0x1693c.  Definition src0_E_malloc : Z := 0x16940.
Definition src0_A_libc_free : Z := 0x16940.  Definition src0_E_libc_free : Z := 0x16b0c.
Definition src0_A_get_meta : Z := 0x16b0c.  Definition src0_E_get_meta : Z := 0x16c1c.
Definition src0_A_nontrivial_free : Z := 0x16c1c.  Definition src0_E_nontrivial_free : Z := 0x16ff4.
Definition src0_A_alloc_meta : Z := 0x16ff4.  Definition src0_E_alloc_meta : Z := 0x172cc.
Definition src0_A_libc_malloc_impl : Z := 0x172cc.  Definition src0_E_libc_malloc_impl : Z := 0x1763c.
Definition src0_A_alloc_slot : Z := 0x1763c.  Definition src0_E_alloc_slot : Z := 0x17ee0.
Definition src0_A_enframe : Z := 0x17ee0.  Definition src0_E_enframe : Z := 0x18030.
Definition src0_A_malloc_allzerop : Z := 0x18030.  Definition src0_E_malloc_allzerop : Z := 0x181a8.
Definition src0_A_vm_wait : Z := 0x181a8.  Definition src0_E_vm_wait : Z := 0x181ac.
Definition src0_A_mmap : Z := 0x181ac.  Definition src0_E_mmap : Z := 0x18298.
Definition src0_A_mprotect : Z := 0x18298.  Definition src0_E_mprotect : Z := 0x182e0.
Definition src0_A_munmap : Z := 0x182e0.  Definition src0_E_munmap : Z := 0x18328.
Definition src0_A_fflush : Z := 0x183fc.  Definition src0_E_fflush : Z := 0x1856c.
Definition src0_A_lockfile : Z := 0x1856c.  Definition src0_E_lockfile : Z := 0x18668.
Definition src0_A_unlockfile : Z := 0x18668.  Definition src0_E_unlockfile : Z := 0x186c8.
Definition src0_A_stdio_write : Z := 0x18b80.  Definition src0_E_stdio_write : Z := 0x18d10.
Definition src0_A_aio_close : Z := 0x18b50.  Definition src0_E_aio_close : Z := 0x18b54.
Definition src0_A_stdio_close : Z := 0x18b54.  Definition src0_E_stdio_close : Z := 0x18b80.
Definition src0_A_fprintf : Z := 0x186c8.  Definition src0_E_fprintf : Z := 0x1872c.
Definition src0_A_fwritex : Z := 0x1872c.  Definition src0_E_fwritex : Z := 0x18864.
Definition src0_A_fwrite : Z := 0x18864.  Definition src0_E_fwrite : Z := 0x1891c.
Definition src0_A_towrite : Z := 0x1891c.  Definition src0_E_towrite : Z := 0x18970.
Definition src0_A_stdio_exit : Z := 0x18970.  Definition src0_E_stdio_exit : Z := 0x18b14.
Definition src0_A_ofl_lock : Z := 0x18b14.  Definition src0_E_ofl_lock : Z := 0x18b44.
Definition src0_A_ofl_unlock : Z := 0x18b44.  Definition src0_E_ofl_unlock : Z := 0x18b50.
Definition src0_A_stdout_write : Z := 0x18d18.  Definition src0_E_stdout_write : Z := 0x18db8.
Definition src0_A_vfprintf : Z := 0x18db8.  Definition src0_E_vfprintf : Z := 0x18f68.
Definition src0_A_printf_core : Z := 0x18f68.  Definition src0_E_printf_core : Z := 0x19d98.
Definition src0_A_pop_arg : Z := 0x19d98.  Definition src0_E_pop_arg : Z := 0x19ecc.
Definition src0_A_pad : Z := 0x19ecc.  Definition src0_E_pad : Z := 0x19fa0.
Definition src0_A_fmt_fp : Z := 0x19fa0.  Definition src0_E_fmt_fp : Z := 0x1b668.
Definition src0_A_strerror : Z := 0x1b668.  Definition src0_E_strerror : Z := 0x1b6a4.
Definition src0_A_lctrans_impl : Z := 0x1b6a4.  Definition src0_E_lctrans_impl : Z := 0x1b6a8.
Definition src0_A_lctrans : Z := 0x1b6a8.  Definition src0_E_lctrans : Z := 0x1b6ac.
Definition src0_A_wctomb : Z := 0x1b6ac.  Definition src0_E_wctomb : Z := 0x1b6d0.
Definition src0_A_wcrtomb : Z := 0x1b6d0.  Definition src0_E_wcrtomb : Z := 0x1b7fc.
Definition src0_A_extenddftf2 : Z := 0x1b7fc.  Definition src0_E_extenddftf2 : Z := 0x1b98c.
Definition src0_A_signbitl : Z := 0x1b98c.  Definition src0_E_signbitl : Z := 0x1b994.
Definition src0_A_fpclassifyl : Z := 0x1b994.  Definition src0_E_fpclassifyl : Z := 0x1b9d8.
Definition src0_A_frexpl : Z := 0x1b9d8.  Definition src0_E_frexpl : Z := 0x1bab0.
Definition src0_A_letf2 : Z := 0x15174.  Definition src0_E_letf2 : Z := 0x1523c.
Definition src0_A_multf3 : Z := 0x1bab0.  Definition src0_E_multf3 : Z := 0x1c1b0.
Definition src0_A_floatsitf : Z := 0x1c1b0.  Definition src0_E_floatsitf : Z := 0x1c2b8.
Definition src0_A_scalbn : Z := 0x1c2b8.  Definition src0_E_scalbn : Z := 0x1c350.
Definition src0_A_subtf3 : Z := 0x15578.  Definition src0_E_subtf3 : Z := 0x15588.
Definition src0_A_addtf3 : Z := 0x15588.  Definition src0_E_addtf3 : Z := 0x15d54.
Definition src0_A_fe_getround : Z := 0x15d54.  Definition src0_E_fe_getround : Z := 0x15d84.
Definition src0_A_fe_raise_inexact : Z := 0x15d84.  Definition src0_E_fe_raise_inexact : Z := 0x15d90.
Definition src0_A_fixunstfsi : Z := 0x1c350.  Definition src0_E_fixunstfsi : Z := 0x1c3e4.
Definition src0_A_floatunsitf : Z := 0x1c3e4.  Definition src0_E_floatunsitf : Z := 0x1c4d0.
Definition src0_A_fixtfsi : Z := 0x1c4d0.  Definition src0_E_fixtfsi : Z := 0x1c578.
Definition src0_A_divtf3 : Z := 0x1c578.  Definition src0_E_divtf3 : Z := 0x1ce7c.
Definition src0_A_vprintf : Z := 0x1ce7c.  Definition src0_E_vprintf : Z := 0x1ce98.
Definition src0_A_memcpy : Z := 0x1d748.  Definition src0_E_memcpy : Z := 0x1db4c.
Definition src0_A_memset : Z := 0x1db4c.  Definition src0_E_memset : Z := 0x1dc44.
Definition src0_A_strlen : Z := 0x1dc7c.  Definition src0_E_strlen : Z := 0x1dd0c.
Definition src0_A_strnlen : Z := 0x1dd6c.  Definition src0_E_strnlen : Z := 0x1ddb0.
Definition src0_A_memchr : Z := 0x1ddb0.  Definition src0_E_memchr : Z := 0x1de7c.
Definition src0_A_lock : Z := 0x1de7c.  Definition src0_E_lock : Z := 0x1e104.
Definition src0_A_unlock : Z := 0x1e104.  Definition src0_E_unlock : Z := 0x1e178.
Definition src0_A_syscall_cp_c : Z := 0x1e178.  Definition src0_E_syscall_cp_c : Z := 0x1e19c.
Definition src0_A_syscall_cp : Z := 0x1e19c.  Definition src0_E_syscall_cp : Z := 0x1e1a0.
Definition src0_A_set_thread_area : Z := 0x1e1a0.  Definition src0_E_set_thread_area : Z := 0x1e1ac.
Definition src0_A_unistd_exit : Z := 0x1e1ac.  Definition src0_E_unistd_exit : Z := 0x1e1b8.
Definition src0_A_close : Z := 0x1e1b8.  Definition src0_E_close : Z := 0x1e20c.
Definition src0_A_lseek : Z := 0x1e20c.  Definition src0_E_lseek : Z := 0x1e218.
Definition src0_A_read : Z := 0x1e218.  Definition src0_E_read : Z := 0x1e24c.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102fd.
Definition src0_D_str_d_n : Z := 0x10311.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10337.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10348.
Definition src0_D_str_inf : Z := 0x10368.
Definition src0_D_str_INF : Z := 0x1037c.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10380.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103e4.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103f9.
Definition src0_D_str_NAN : Z := 0x1041f.
Definition src0_D_str_nan : Z := 0x10426.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1043c.
Definition src0_D_str_dev_null : Z := 0x10479.
Definition src0_D_str_null : Z := 0x10483.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x104c8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x104d8.
Definition src0_D_debruijn32 : Z := 0x10658.
Definition src0_D_size_classes : Z := 0x10678.
Definition src0_D_small_cnt_tab : Z := 0x106d8.
Definition src0_D_med_cnt_tab : Z := 0x106f3.
Definition src0_D_states : Z := 0x10850.
Definition src0_D_xdigits : Z := 0x10a20.
Definition src0_D_errmsgstr : Z := 0x10a30.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x111d8.
Definition src0_D_fe_getround : Z := 0x105f0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11510.
Definition src0_D_init_array_start : Z := 0x1f250.
Definition src0_D_fini_array_start : Z := 0x1f258.
Definition src0_D_stderr : Z := 0x1f358.
Definition src0_D_stdout : Z := 0x1f360.
Definition src0_D_got_DYNAMIC : Z := 0x1f370.
Definition src0_D_got_main : Z := 0x1f378.
Definition src0_D_got_init : Z := 0x1f380.
Definition src0_D_got_fini : Z := 0x1f388.
Definition src0_D_got_register_frame_info : Z := 0x1f390.
Definition src0_D_got_cxa_finalize : Z := 0x1f398.
Definition src0_D_got_deregister_frame_info : Z := 0x1f3a0.
Definition src0_D_got_stderr : Z := 0x1f3a8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1f3b0.
Definition src0_D_got_stdout : Z := 0x1f3b8.
Definition src0_D_got_environ : Z := 0x1f3c0.
Definition src0_D_got_progname_full : Z := 0x1f3c8.
Definition src0_D_got_progname : Z := 0x1f3d0.
Definition src0_D_got_init_array_end : Z := 0x1f3d8.
Definition src0_D_got_init_array_start : Z := 0x1f3e0.
Definition src0_D_got_stack_chk_guard : Z := 0x1f3e8.
Definition src0_D_got_fini_array_end : Z := 0x1f3f0.
Definition src0_D_got_fini_array_start : Z := 0x1f3f8.
Definition src0_D_dso_handle : Z := 0x20400.
Definition src0_D_stderr_FILE : Z := 0x20428.
Definition src0_D_stderr_used : Z := 0x20510.
Definition src0_D_stdout_FILE : Z := 0x20518.
Definition src0_D_stdout_used : Z := 0x20600.
Definition src0_D_default_stacksize : Z := 0x20608.
Definition src0_D_do_init_initialized : Z := 0x20610.
Definition src0_D_do_init_object : Z := 0x20618.
Definition src0_D_do_fini_finalized : Z := 0x20658.
Definition src0_D_read_stage : Z := 0x20659.
Definition src0_D_target_run_initialized : Z := 0x30660.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30670.
Definition src0_D_environ : Z := 0x30690.
Definition src0_D_thread_list_lock : Z := 0x50768.
Definition src0_D_main_tls : Z := 0x50770.
Definition src0_D_builtin_tls : Z := 0x30698.
Definition src0_D_finished_atexit : Z := 0x507a8.
Definition src0_D_atexit_lock : Z := 0x507ac.
Definition src0_D_atexit_slot : Z := 0x507b0.
Definition src0_D_atexit_head : Z := 0x507b8.
Definition src0_D_atexit_builtin : Z := 0x507c0.
Definition src0_D_exit_exit_lock : Z := 0x509c8.
Definition src0_D_stack_chk_guard : Z := 0x509d0.
Definition src0_D_sysinfo : Z := 0x509d8.
Definition src0_D_progname : Z := 0x509e0.
Definition src0_D_progname_full : Z := 0x509e8.
Definition src0_D_libc : Z := 0x509f0.
Definition src0_D_hwcap : Z := 0x50a58.
Definition src0_D_malloc_lock : Z := 0x50a60.
Definition src0_D_malloc_context : Z := 0x50a68.
Definition src0_D_malloc_replaced : Z := 0x50e08.
Definition src0_D_stdin_used : Z := 0x50e10.
Definition src0_D_ofl_lock : Z := 0x50e18.
Definition src0_D_ofl_head : Z := 0x50e20.
Definition src0_D_stderr_buf : Z := 0x50e28.
Definition src0_D_stdout_buf : Z := 0x50e30.
Definition src0_vmlock : option Z := None.
(* musl's debruijn32 table runs to the next .rodata object, size_classes: 32 bytes here. An abbreviation, so
   src0_msyms's field is these two image addresses, which the proofs that unfold the record already unfold. *)
Abbreviation src0_debruijn_len := (src0_D_size_classes - src0_D_debruijn32).
