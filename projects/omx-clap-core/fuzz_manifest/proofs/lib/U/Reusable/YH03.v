(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x128f8.  Definition src0_text_hi : Z := 0x1d2c4.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x111cc.
Definition src0_eh_frame_lo : Z := 0x11310.  Definition src0_eh_frame_hi : Z := 0x118f8.
Definition src0_init_array_lo : Z := 0x1e2c8.  Definition src0_init_array_hi : Z := 0x1e2d0.
Definition src0_fini_array_lo : Z := 0x1e2d0.  Definition src0_fini_array_hi : Z := 0x1e2d8.
Definition src0_data_rel_ro_lo : Z := 0x1e2d8.  Definition src0_data_rel_ro_hi : Z := 0x1e2e8.
Definition src0_got_lo : Z := 0x1e2e8.  Definition src0_got_hi : Z := 0x1e380.
Definition src0_data_lo : Z := 0x1f380.  Definition src0_data_hi : Z := 0x1f594.
Definition src0_bss_lo : Z := 0x1f5a0.  Definition src0_bss_hi : Z := 0x501e0.
Definition src0_A_start : Z := 0x128f8.  Definition src0_E_start : Z := 0x12940.
Definition src0_A_do_init : Z := 0x12940.  Definition src0_E_do_init : Z := 0x129b4.
Definition src0_A_do_fini : Z := 0x129b4.  Definition src0_E_do_fini : Z := 0x12a44.
Definition src0_A_main : Z := 0x12a44.  Definition src0_E_main : Z := 0x12d08.
Definition src0_A_target_alloc_init : Z := 0x12d08.  Definition src0_E_target_alloc_init : Z := 0x12d0c.
Definition src0_A_target_alloc_count : Z := 0x12d0c.  Definition src0_E_target_alloc_count : Z := 0x12d14.
Definition src0_A_target_run : Z := 0x12d14.  Definition src0_E_target_run : Z := 0x12e6c.
Definition src0_A_aef_exit_guard : Z := 0x12e6c.  Definition src0_E_aef_exit_guard : Z := 0x12e9c.
Definition src0_A_emit_printf : Z := 0x12e9c.  Definition src0_E_emit_printf : Z := 0x12ee4.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ee4.
Definition src0_A_init : Z := 0x143e0.  Definition src0_E_init : Z := 0x143e4.
Definition src0_A_init_libc : Z := 0x143e4.  Definition src0_E_init_libc : Z := 0x14610.
Definition src0_A_libc_start_init : Z := 0x14610.  Definition src0_E_libc_start_init : Z := 0x1465c.
Definition src0_A_libc_start_main : Z := 0x1465c.  Definition src0_E_libc_start_main : Z := 0x146bc.
Definition src0_A_libc_start_main_stage2 : Z := 0x146bc.  Definition src0_E_libc_start_main_stage2 : Z := 0x14704.
Definition src0_A_init_tls : Z := 0x14704.  Definition src0_E_init_tls : Z := 0x149b4.
Definition src0_A_funcs_on_exit : Z := 0x14a70.  Definition src0_E_funcs_on_exit : Z := 0x14b38.
Definition src0_A_cxa_finalize : Z := 0x14b38.  Definition src0_E_cxa_finalize : Z := 0x14b3c.
Definition src0_A_atexit : Z := 0x14b3c.  Definition src0_E_atexit : Z := 0x14c00.
Definition src0_A_atexit_call : Z := 0x14c00.  Definition src0_E_atexit_call : Z := 0x14c04.
Definition src0_A_fini : Z := 0x14c04.  Definition src0_E_fini : Z := 0x14c08.
Definition src0_A_libc_exit_fini : Z := 0x14c08.  Definition src0_E_libc_exit_fini : Z := 0x14c54.
Definition src0_A_exit : Z := 0x14c54.  Definition src0_E_exit : Z := 0x14cc8.
Definition src0_A_Exit : Z := 0x14a54.  Definition src0_E_Exit : Z := 0x14a70.
Definition src0_A_open : Z := 0x14cc8.  Definition src0_E_open : Z := 0x14dac.
Definition src0_A_init_ssp : Z := 0x14dac.  Definition src0_E_init_ssp : Z := 0x14e0c.
Definition src0_A_stack_chk_fail : Z := 0x14e0c.  Definition src0_E_stack_chk_fail : Z := 0x14e14.
Definition src0_A_syscall_ret : Z := 0x14e14.  Definition src0_E_syscall_ret : Z := 0x14e4c.
Definition src0_A_errno_location : Z := 0x149b4.  Definition src0_E_errno_location : Z := 0x149c0.
Definition src0_A_free : Z := 0x14e4c.  Definition src0_E_free : Z := 0x14e50.
Definition src0_A_libc_calloc : Z := 0x14e50.  Definition src0_E_libc_calloc : Z := 0x14f88.
Definition src0_A_libc_malloc : Z := 0x14f88.  Definition src0_E_libc_malloc : Z := 0x14f8c.
Definition src0_A_malloc : Z := 0x14f8c.  Definition src0_E_malloc : Z := 0x14f90.
Definition src0_A_libc_free : Z := 0x14f90.  Definition src0_E_libc_free : Z := 0x1515c.
Definition src0_A_get_meta : Z := 0x1515c.  Definition src0_E_get_meta : Z := 0x1526c.
Definition src0_A_nontrivial_free : Z := 0x1526c.  Definition src0_E_nontrivial_free : Z := 0x15644.
Definition src0_A_alloc_meta : Z := 0x15644.  Definition src0_E_alloc_meta : Z := 0x1591c.
Definition src0_A_libc_malloc_impl : Z := 0x1591c.  Definition src0_E_libc_malloc_impl : Z := 0x15c8c.
Definition src0_A_alloc_slot : Z := 0x15c8c.  Definition src0_E_alloc_slot : Z := 0x16530.
Definition src0_A_enframe : Z := 0x16530.  Definition src0_E_enframe : Z := 0x16680.
Definition src0_A_malloc_allzerop : Z := 0x16680.  Definition src0_E_malloc_allzerop : Z := 0x167f8.
Definition src0_A_vm_wait : Z := 0x167f8.  Definition src0_E_vm_wait : Z := 0x167fc.
Definition src0_A_mmap : Z := 0x167fc.  Definition src0_E_mmap : Z := 0x168e8.
Definition src0_A_mprotect : Z := 0x168e8.  Definition src0_E_mprotect : Z := 0x16930.
Definition src0_A_munmap : Z := 0x16930.  Definition src0_E_munmap : Z := 0x16978.
Definition src0_A_fflush : Z := 0x16a4c.  Definition src0_E_fflush : Z := 0x16bbc.
Definition src0_A_lockfile : Z := 0x16bbc.  Definition src0_E_lockfile : Z := 0x16cb8.
Definition src0_A_unlockfile : Z := 0x16cb8.  Definition src0_E_unlockfile : Z := 0x16d18.
Definition src0_A_aio_close : Z := 0x16eb0.  Definition src0_E_aio_close : Z := 0x16eb4.
Definition src0_A_fprintf : Z := 0x16ee0.  Definition src0_E_fprintf : Z := 0x16f44.
Definition src0_A_fwritex : Z := 0x170e8.  Definition src0_E_fwritex : Z := 0x17220.
Definition src0_A_fwrite : Z := 0x17220.  Definition src0_E_fwrite : Z := 0x172d8.
Definition src0_A_towrite : Z := 0x172d8.  Definition src0_E_towrite : Z := 0x1732c.
Definition src0_A_stdio_exit : Z := 0x16f44.  Definition src0_E_stdio_exit : Z := 0x170e8.
Definition src0_A_ofl_lock : Z := 0x1732c.  Definition src0_E_ofl_lock : Z := 0x1735c.
Definition src0_A_ofl_unlock : Z := 0x1735c.  Definition src0_E_ofl_unlock : Z := 0x17368.
Definition src0_A_stdout_write : Z := 0x173c8.  Definition src0_E_stdout_write : Z := 0x17468.
Definition src0_A_vfprintf : Z := 0x17468.  Definition src0_E_vfprintf : Z := 0x17618.
Definition src0_A_printf_core : Z := 0x17618.  Definition src0_E_printf_core : Z := 0x18448.
Definition src0_A_pop_arg : Z := 0x18448.  Definition src0_E_pop_arg : Z := 0x1857c.
Definition src0_A_pad : Z := 0x1857c.  Definition src0_E_pad : Z := 0x18650.
Definition src0_A_fmt_fp : Z := 0x18650.  Definition src0_E_fmt_fp : Z := 0x19d18.
Definition src0_A_strerror : Z := 0x19d18.  Definition src0_E_strerror : Z := 0x19d54.
Definition src0_A_lctrans_impl : Z := 0x19d54.  Definition src0_E_lctrans_impl : Z := 0x19d58.
Definition src0_A_lctrans : Z := 0x19d58.  Definition src0_E_lctrans : Z := 0x19d5c.
Definition src0_A_wctomb : Z := 0x19d5c.  Definition src0_E_wctomb : Z := 0x19d80.
Definition src0_A_wcrtomb : Z := 0x19d80.  Definition src0_E_wcrtomb : Z := 0x19eac.
Definition src0_A_extenddftf2 : Z := 0x19eac.  Definition src0_E_extenddftf2 : Z := 0x1a03c.
Definition src0_A_signbitl : Z := 0x1a03c.  Definition src0_E_signbitl : Z := 0x1a044.
Definition src0_A_fpclassifyl : Z := 0x1a044.  Definition src0_E_fpclassifyl : Z := 0x1a088.
Definition src0_A_frexpl : Z := 0x1a088.  Definition src0_E_frexpl : Z := 0x1a160.
Definition src0_A_letf2 : Z := 0x1a160.  Definition src0_E_letf2 : Z := 0x1a228.
Definition src0_A_multf3 : Z := 0x1a228.  Definition src0_E_multf3 : Z := 0x1a928.
Definition src0_A_floatsitf : Z := 0x1a928.  Definition src0_E_floatsitf : Z := 0x1aa30.
Definition src0_A_scalbn : Z := 0x1aa30.  Definition src0_E_scalbn : Z := 0x1aac8.
Definition src0_A_subtf3 : Z := 0x1aac8.  Definition src0_E_subtf3 : Z := 0x1aad8.
Definition src0_A_addtf3 : Z := 0x1aad8.  Definition src0_E_addtf3 : Z := 0x1b2a4.
Definition src0_A_fe_getround : Z := 0x1b2a4.  Definition src0_E_fe_getround : Z := 0x1b2d4.
Definition src0_A_fe_raise_inexact : Z := 0x1b2d4.  Definition src0_E_fe_raise_inexact : Z := 0x1b2e0.
Definition src0_A_fixunstfsi : Z := 0x1b2e0.  Definition src0_E_fixunstfsi : Z := 0x1b374.
Definition src0_A_floatunsitf : Z := 0x1b374.  Definition src0_E_floatunsitf : Z := 0x1b460.
Definition src0_A_fixtfsi : Z := 0x1b460.  Definition src0_E_fixtfsi : Z := 0x1b508.
Definition src0_A_divtf3 : Z := 0x1b508.  Definition src0_E_divtf3 : Z := 0x1be0c.
Definition src0_A_vprintf : Z := 0x1be0c.  Definition src0_E_vprintf : Z := 0x1be28.
Definition src0_A_bcmp : Z := 0x1bfd0.  Definition src0_E_bcmp : Z := 0x1bfd4.
Definition src0_A_memcmp : Z := 0x1c0a0.  Definition src0_E_memcmp : Z := 0x1c0d0.
Definition src0_A_memcpy : Z := 0x1c0d0.  Definition src0_E_memcpy : Z := 0x1c4d4.
Definition src0_A_memset : Z := 0x1c4d4.
Definition src0_E_strlen : Z := 0x1c778.
Definition src0_A_strnlen : Z := 0x1c8b0.  Definition src0_E_strnlen : Z := 0x1c8f4.
Definition src0_A_memchr : Z := 0x1bfd4.  Definition src0_E_memchr : Z := 0x1c0a0.
Definition src0_A_lock : Z := 0x1cef4.  Definition src0_E_lock : Z := 0x1d17c.
Definition src0_A_unlock : Z := 0x1d17c.  Definition src0_E_unlock : Z := 0x1d1f0.
Definition src0_A_syscall_cp_c : Z := 0x1d1f0.  Definition src0_E_syscall_cp_c : Z := 0x1d214.
Definition src0_A_syscall_cp : Z := 0x1d214.  Definition src0_E_syscall_cp : Z := 0x1d218.
Definition src0_A_set_thread_area : Z := 0x1d218.  Definition src0_E_set_thread_area : Z := 0x1d224.
Definition src0_A_unistd_exit : Z := 0x1d224.  Definition src0_E_unistd_exit : Z := 0x1d230.
Definition src0_A_close : Z := 0x1d230.  Definition src0_E_close : Z := 0x1d284.
Definition src0_A_lseek : Z := 0x1d284.  Definition src0_E_lseek : Z := 0x1d290.
Definition src0_A_read : Z := 0x1d290.
Definition src0_D_str_n0X0x : Z := 0x102b2.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102bc.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102cf.
Definition src0_D_str_d_n : Z := 0x102e3.
Definition src0_D_str : Z := 0x102e7.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102ea.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102fb.
Definition src0_D_str_inf : Z := 0x1031b.
Definition src0_D_str_INF : Z := 0x1031f.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10323.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103ea.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103ff.
Definition src0_D_str_NAN : Z := 0x10447.
Definition src0_D_str_nan : Z := 0x10450.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10454.
Definition src0_D_str_dev_null : Z := 0x10474.
Definition src0_D_str_null : Z := 0x1047e.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x106f0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10700.
Definition src0_D_debruijn32 : Z := 0x104e8.
Definition src0_D_size_classes : Z := 0x10508.
Definition src0_D_small_cnt_tab : Z := 0x10568.
Definition src0_D_med_cnt_tab : Z := 0x10583.
Definition src0_D_states : Z := 0x10730.
Definition src0_D_xdigits : Z := 0x10900.
Definition src0_D_errmsgstr : Z := 0x10910.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x110b8.
Definition src0_D_fe_getround : Z := 0x111c0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11310.
Definition src0_D_init_array_start : Z := 0x1e2c8.
Definition src0_D_fini_array_start : Z := 0x1e2d0.
Definition src0_D_stderr : Z := 0x1e2d8.
Definition src0_D_stdout : Z := 0x1e2e0.
Definition src0_D_got_DYNAMIC : Z := 0x1e2f0.
Definition src0_D_got_main : Z := 0x1e2f8.
Definition src0_D_got_init : Z := 0x1e300.
Definition src0_D_got_fini : Z := 0x1e308.
Definition src0_D_got_register_frame_info : Z := 0x1e310.
Definition src0_D_got_cxa_finalize : Z := 0x1e318.
Definition src0_D_got_deregister_frame_info : Z := 0x1e320.
Definition src0_D_got_stderr : Z := 0x1e328.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e330.
Definition src0_D_got_stdout : Z := 0x1e338.
Definition src0_D_got_environ : Z := 0x1e340.
Definition src0_D_got_progname_full : Z := 0x1e348.
Definition src0_D_got_progname : Z := 0x1e350.
Definition src0_D_got_init_array_end : Z := 0x1e358.
Definition src0_D_got_init_array_start : Z := 0x1e360.
Definition src0_D_got_stack_chk_guard : Z := 0x1e368.
Definition src0_D_got_fini_array_end : Z := 0x1e370.
Definition src0_D_got_fini_array_start : Z := 0x1e378.
Definition src0_D_dso_handle : Z := 0x1f380.
Definition src0_D_aef_argc : Z := 0x1f390.
Definition src0_D_stderr_FILE : Z := 0x1f3b0.
Definition src0_D_stderr_used : Z := 0x1f498.
Definition src0_D_stdout_FILE : Z := 0x1f4a0.
Definition src0_D_stdout_used : Z := 0x1f588.
Definition src0_D_default_stacksize : Z := 0x1f590.
Definition src0_D_do_init_initialized : Z := 0x1f5a0.
Definition src0_D_do_init_object : Z := 0x1f5a8.
Definition src0_D_do_fini_finalized : Z := 0x1f5e8.
Definition src0_D_read_stage : Z := 0x1f5e9.
Definition src0_D_target_run_initialized : Z := 0x2f5f0.
Definition src0_D_aef_in_callback : Z := 0x2f5f4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f600.
Definition src0_D_environ : Z := 0x2f638.
Definition src0_D_thread_list_lock : Z := 0x4f710.
Definition src0_D_main_tls : Z := 0x4f718.
Definition src0_D_builtin_tls : Z := 0x2f640.
Definition src0_D_finished_atexit : Z := 0x4f750.
Definition src0_D_atexit_lock : Z := 0x4f754.
Definition src0_D_atexit_slot : Z := 0x4f758.
Definition src0_D_atexit_head : Z := 0x4f760.
Definition src0_D_atexit_builtin : Z := 0x4f768.
Definition src0_D_exit_exit_lock : Z := 0x4f970.
Definition src0_D_stack_chk_guard : Z := 0x4f978.
Definition src0_D_sysinfo : Z := 0x4f980.
Definition src0_D_progname : Z := 0x4f988.
Definition src0_D_progname_full : Z := 0x4f990.
Definition src0_D_libc : Z := 0x4f998.
Definition src0_D_hwcap : Z := 0x4fa00.
Definition src0_D_malloc_lock : Z := 0x4fa08.
Definition src0_D_malloc_context : Z := 0x4fa10.
Definition src0_D_malloc_replaced : Z := 0x4fdb0.
Definition src0_D_stdin_used : Z := 0x4fdb8.
Definition src0_D_ofl_lock : Z := 0x4fdc0.
Definition src0_D_ofl_head : Z := 0x4fdc8.
Definition src0_D_stderr_buf : Z := 0x4fdd0.
Definition src0_D_stdout_buf : Z := 0x4fdd8.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
