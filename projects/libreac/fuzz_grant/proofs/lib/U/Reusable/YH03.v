(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: 38 names that no proof reads are deleted: 31 whose value is not the address of the symbol they name in this image, and 7 that only the cgif FILE sink used (src0_A_stdio_read, src0_A_stdio_write, src0_A_stdio_seek, src0_A_stdio_close and the tmp_out.gif, wb and ';' strings). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12b50.  Definition src0_text_hi : Z := 0x1dd20.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11344.
Definition src0_eh_frame_lo : Z := 0x114d0.  Definition src0_eh_frame_hi : Z := 0x11b50.
Definition src0_init_array_lo : Z := 0x1ed20.  Definition src0_init_array_hi : Z := 0x1ed28.
Definition src0_fini_array_lo : Z := 0x1ed28.  Definition src0_fini_array_hi : Z := 0x1ed30.
Definition src0_data_rel_ro_lo : Z := 0x1ed30.  Definition src0_data_rel_ro_hi : Z := 0x1ee48.
Definition src0_got_lo : Z := 0x1ee48.  Definition src0_got_hi : Z := 0x1eee0.
Definition src0_data_lo : Z := 0x1fee0.  Definition src0_data_hi : Z := 0x200ec.
Definition src0_bss_lo : Z := 0x200f0.  Definition src0_bss_hi : Z := 0x50d18.
Definition src0_A_do_init : Z := 0x12b98.  Definition src0_E_do_init : Z := 0x12c0c.
Definition src0_A_do_fini : Z := 0x12c0c.  Definition src0_E_do_fini : Z := 0x12c9c.
Definition src0_A_main : Z := 0x12c9c.  Definition src0_E_main : Z := 0x12f60.
Definition src0_A_target_alloc_init : Z := 0x12f60.  Definition src0_E_target_alloc_init : Z := 0x12f64.
Definition src0_A_target_alloc_count : Z := 0x12f64.  Definition src0_E_target_alloc_count : Z := 0x12f6c.
Definition src0_A_target_run : Z := 0x12f6c.  Definition src0_E_target_run : Z := 0x130c4.
Definition src0_A_aef_exit_guard : Z := 0x130c4.  Definition src0_E_aef_exit_guard : Z := 0x130f4.
Definition src0_A_emit_printf : Z := 0x130f4.  Definition src0_E_emit_printf : Z := 0x1313c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x1313c.
Definition src0_A_init : Z := 0x15928.  Definition src0_E_init : Z := 0x1592c.
Definition src0_A_init_libc : Z := 0x1592c.  Definition src0_E_init_libc : Z := 0x15b58.
Definition src0_A_libc_start_init : Z := 0x15b58.  Definition src0_E_libc_start_init : Z := 0x15ba4.
Definition src0_A_libc_start_main : Z := 0x15ba4.  Definition src0_E_libc_start_main : Z := 0x15c04.
Definition src0_A_libc_start_main_stage2 : Z := 0x15c04.  Definition src0_E_libc_start_main_stage2 : Z := 0x15c4c.
Definition src0_A_init_tls : Z := 0x15c4c.
Definition src0_A_funcs_on_exit : Z := 0x15fac.  Definition src0_E_funcs_on_exit : Z := 0x16074.
Definition src0_A_cxa_finalize : Z := 0x16074.  Definition src0_E_cxa_finalize : Z := 0x16078.
Definition src0_A_atexit : Z := 0x16078.  Definition src0_E_atexit : Z := 0x1613c.
Definition src0_A_atexit_call : Z := 0x1613c.  Definition src0_E_atexit_call : Z := 0x16140.
Definition src0_A_fini : Z := 0x16140.  Definition src0_E_fini : Z := 0x16144.
Definition src0_A_libc_exit_fini : Z := 0x16144.  Definition src0_E_libc_exit_fini : Z := 0x16190.
Definition src0_A_exit : Z := 0x16190.
Definition src0_A_Exit : Z := 0x15f90.
Definition src0_A_open : Z := 0x16204.  Definition src0_E_open : Z := 0x162e8.
Definition src0_A_init_ssp : Z := 0x162e8.  Definition src0_E_init_ssp : Z := 0x16348.
Definition src0_A_stack_chk_fail : Z := 0x16348.  Definition src0_E_stack_chk_fail : Z := 0x16350.
Definition src0_A_syscall_ret : Z := 0x16350.  Definition src0_E_syscall_ret : Z := 0x16388.
Definition src0_A_errno_location : Z := 0x16388.  Definition src0_E_errno_location : Z := 0x16394.
Definition src0_A_free : Z := 0x16394.  Definition src0_E_free : Z := 0x16398.
Definition src0_A_libc_calloc : Z := 0x16398.  Definition src0_E_libc_calloc : Z := 0x164d0.
Definition src0_A_libc_malloc : Z := 0x164d0.  Definition src0_E_libc_malloc : Z := 0x164d4.
Definition src0_A_malloc : Z := 0x164d4.  Definition src0_E_malloc : Z := 0x164d8.
Definition src0_A_libc_free : Z := 0x164d8.  Definition src0_E_libc_free : Z := 0x166a4.
Definition src0_A_get_meta : Z := 0x166a4.  Definition src0_E_get_meta : Z := 0x167b4.
Definition src0_A_nontrivial_free : Z := 0x167b4.  Definition src0_E_nontrivial_free : Z := 0x16b8c.
Definition src0_A_alloc_meta : Z := 0x16b8c.  Definition src0_E_alloc_meta : Z := 0x16e64.
Definition src0_A_libc_malloc_impl : Z := 0x16e64.  Definition src0_E_libc_malloc_impl : Z := 0x171d4.
Definition src0_A_alloc_slot : Z := 0x171d4.  Definition src0_E_alloc_slot : Z := 0x17a78.
Definition src0_A_enframe : Z := 0x17a78.  Definition src0_E_enframe : Z := 0x17bc8.
Definition src0_A_malloc_allzerop : Z := 0x17bc8.  Definition src0_E_malloc_allzerop : Z := 0x17d40.
Definition src0_A_vm_wait : Z := 0x17d40.  Definition src0_E_vm_wait : Z := 0x17d44.
Definition src0_A_mmap : Z := 0x17d44.  Definition src0_E_mmap : Z := 0x17e30.
Definition src0_A_mprotect : Z := 0x17e30.  Definition src0_E_mprotect : Z := 0x17e78.
Definition src0_A_munmap : Z := 0x17e78.
Definition src0_A_fflush : Z := 0x17f94.  Definition src0_E_fflush : Z := 0x18104.
Definition src0_A_lockfile : Z := 0x18104.  Definition src0_E_lockfile : Z := 0x18200.
Definition src0_A_unlockfile : Z := 0x18200.
Definition src0_A_aio_close : Z := 0x186e8.  Definition src0_E_aio_close : Z := 0x186ec.
Definition src0_A_fprintf : Z := 0x18260.  Definition src0_E_fprintf : Z := 0x182c4.
Definition src0_A_fwritex : Z := 0x182c4.  Definition src0_E_fwritex : Z := 0x183fc.
Definition src0_A_fwrite : Z := 0x183fc.  Definition src0_E_fwrite : Z := 0x184b4.
Definition src0_A_towrite : Z := 0x184b4.  Definition src0_E_towrite : Z := 0x18508.
Definition src0_A_stdio_exit : Z := 0x18508.  Definition src0_E_stdio_exit : Z := 0x186ac.
Definition src0_A_ofl_lock : Z := 0x186ac.  Definition src0_E_ofl_lock : Z := 0x186dc.
Definition src0_A_ofl_unlock : Z := 0x186dc.
Definition src0_A_stdout_write : Z := 0x188b0.  Definition src0_E_stdout_write : Z := 0x18950.
Definition src0_A_vfprintf : Z := 0x18950.  Definition src0_E_vfprintf : Z := 0x18b00.
Definition src0_A_printf_core : Z := 0x18b00.  Definition src0_E_printf_core : Z := 0x19930.
Definition src0_A_pop_arg : Z := 0x19930.  Definition src0_E_pop_arg : Z := 0x19a64.
Definition src0_A_pad : Z := 0x19a64.  Definition src0_E_pad : Z := 0x19b38.
Definition src0_A_fmt_fp : Z := 0x19b38.  Definition src0_E_fmt_fp : Z := 0x1b200.
Definition src0_A_strerror : Z := 0x1b200.
Definition src0_E_lctrans_impl : Z := 0x1b240.
Definition src0_A_lctrans : Z := 0x1b240.  Definition src0_E_lctrans : Z := 0x1b244.
Definition src0_A_wctomb : Z := 0x1b244.  Definition src0_E_wctomb : Z := 0x1b268.
Definition src0_A_wcrtomb : Z := 0x1b268.  Definition src0_E_wcrtomb : Z := 0x1b394.
Definition src0_A_extenddftf2 : Z := 0x1b394.
Definition src0_E_signbitl : Z := 0x1b52c.
Definition src0_A_fpclassifyl : Z := 0x1b52c.
Definition src0_E_frexpl : Z := 0x1b648.
Definition src0_A_letf2 : Z := 0x1b648.  Definition src0_E_letf2 : Z := 0x1b710.
Definition src0_A_multf3 : Z := 0x1b710.  Definition src0_E_multf3 : Z := 0x1be10.
Definition src0_A_floatsitf : Z := 0x1be10.
Definition src0_E_scalbn : Z := 0x1bfb0.
Definition src0_A_subtf3 : Z := 0x1bfb0.  Definition src0_E_subtf3 : Z := 0x1bfc0.
Definition src0_A_addtf3 : Z := 0x1bfc0.  Definition src0_E_addtf3 : Z := 0x1c78c.
Definition src0_A_fe_getround : Z := 0x1c78c.  Definition src0_E_fe_getround : Z := 0x1c7bc.
Definition src0_A_fe_raise_inexact : Z := 0x1c7bc.  Definition src0_E_fe_raise_inexact : Z := 0x1c7c8.
Definition src0_A_fixunstfsi : Z := 0x1c7c8.  Definition src0_E_fixunstfsi : Z := 0x1c85c.
Definition src0_A_floatunsitf : Z := 0x1c85c.  Definition src0_E_floatunsitf : Z := 0x1c948.
Definition src0_A_fixtfsi : Z := 0x1c948.  Definition src0_E_fixtfsi : Z := 0x1c9f0.
Definition src0_A_divtf3 : Z := 0x1c9f0.  Definition src0_E_divtf3 : Z := 0x1d2f4.
Definition src0_A_vprintf : Z := 0x1d2f4.
Definition src0_E_memcmp : Z := 0x1d344.
Definition src0_A_memcpy : Z := 0x1d344.  Definition src0_E_memcpy : Z := 0x1d748.
Definition src0_A_memset : Z := 0x1d748.
Definition src0_A_strnlen : Z := 0x1d840.  Definition src0_E_strnlen : Z := 0x1d884.
Definition src0_A_memchr : Z := 0x1d884.  Definition src0_E_memchr : Z := 0x1d950.
Definition src0_A_lock : Z := 0x1d950.  Definition src0_E_lock : Z := 0x1dbd8.
Definition src0_A_unlock : Z := 0x1dbd8.  Definition src0_E_unlock : Z := 0x1dc4c.
Definition src0_A_syscall_cp_c : Z := 0x1dc4c.  Definition src0_E_syscall_cp_c : Z := 0x1dc70.
Definition src0_A_syscall_cp : Z := 0x1dc70.  Definition src0_E_syscall_cp : Z := 0x1dc74.
Definition src0_A_unistd_exit : Z := 0x1dc80.  Definition src0_E_unistd_exit : Z := 0x1dc8c.
Definition src0_A_close : Z := 0x1dc8c.  Definition src0_E_close : Z := 0x1dce0.
Definition src0_A_lseek : Z := 0x1dce0.  Definition src0_E_lseek : Z := 0x1dcec.
Definition src0_A_read : Z := 0x1dcec.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b5.
Definition src0_D_str_d_n : Z := 0x102c9.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d0.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e1.
Definition src0_D_str_inf : Z := 0x10301.
Definition src0_D_str_INF : Z := 0x10305.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10309.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1032a.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x1033f.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10365.
Definition src0_D_str_dev_null : Z := 0x10385.
Definition src0_D_str_null : Z := 0x1038f.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103b0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103c0.
Definition src0_D_debruijn32 : Z := 0x10654.
Definition src0_D_size_classes : Z := 0x106d0.
Definition src0_D_small_cnt_tab : Z := 0x10730.
Definition src0_D_med_cnt_tab : Z := 0x1074b.
Definition src0_D_states : Z := 0x108a8.
Definition src0_D_xdigits : Z := 0x10a78.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11230.
Definition src0_D_fe_getround : Z := 0x11338.
Definition src0_D_EH_FRAME_LIST : Z := 0x114d0.
Definition src0_D_init_array_start : Z := 0x1ed20.
Definition src0_D_fini_array_start : Z := 0x1ed28.
Definition src0_D_stdout : Z := 0x1ee40.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1ee48.
Definition src0_D_got_DYNAMIC : Z := 0x1ee50.
Definition src0_D_got_main : Z := 0x1ee58.
Definition src0_D_got_init : Z := 0x1ee60.
Definition src0_D_got_fini : Z := 0x1ee68.
Definition src0_D_got_register_frame_info : Z := 0x1ee70.
Definition src0_D_got_cxa_finalize : Z := 0x1ee78.
Definition src0_D_got_deregister_frame_info : Z := 0x1ee80.
Definition src0_D_got_stderr : Z := 0x1ee88.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1ee90.
Definition src0_D_got_stdout : Z := 0x1ee98.
Definition src0_D_got_environ : Z := 0x1eea0.
Definition src0_D_got_progname_full : Z := 0x1eea8.
Definition src0_D_got_progname : Z := 0x1eeb0.
Definition src0_D_got_init_array_end : Z := 0x1eeb8.
Definition src0_D_got_init_array_start : Z := 0x1eec0.
Definition src0_D_got_stack_chk_guard : Z := 0x1eec8.
Definition src0_D_got_fini_array_end : Z := 0x1eed0.
Definition src0_D_got_fini_array_start : Z := 0x1eed8.
Definition src0_D_dso_handle : Z := 0x1fee0.
Definition src0_D_aef_argc : Z := 0x1fef0.
Definition src0_D_stderr_FILE : Z := 0x1ff08.
Definition src0_D_stderr_used : Z := 0x1fff0.
Definition src0_D_stdout_FILE : Z := 0x1fff8.
Definition src0_D_stdout_used : Z := 0x200e0.
Definition src0_D_default_stacksize : Z := 0x200e8.
Definition src0_D_do_init_initialized : Z := 0x200f0.
Definition src0_D_do_init_object : Z := 0x200f8.
Definition src0_D_do_fini_finalized : Z := 0x20138.
Definition src0_D_read_stage : Z := 0x20139.
Definition src0_D_target_run_initialized : Z := 0x30140.
Definition src0_D_aef_in_callback : Z := 0x30144.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30150.
Definition src0_D_environ : Z := 0x30170.
Definition src0_D_thread_list_lock : Z := 0x50248.
Definition src0_D_main_tls : Z := 0x50250.
Definition src0_D_builtin_tls : Z := 0x30178.
Definition src0_D_finished_atexit : Z := 0x50288.
Definition src0_D_atexit_lock : Z := 0x5028c.
Definition src0_D_atexit_slot : Z := 0x50290.
Definition src0_D_atexit_head : Z := 0x50298.
Definition src0_D_atexit_builtin : Z := 0x502a0.
Definition src0_D_exit_exit_lock : Z := 0x504a8.
Definition src0_D_stack_chk_guard : Z := 0x504b0.
Definition src0_D_sysinfo : Z := 0x504b8.
Definition src0_D_progname : Z := 0x504c0.
Definition src0_D_progname_full : Z := 0x504c8.
Definition src0_D_libc : Z := 0x504d0.
Definition src0_D_hwcap : Z := 0x50538.
Definition src0_D_malloc_lock : Z := 0x50540.
Definition src0_D_malloc_context : Z := 0x50548.
Definition src0_D_malloc_replaced : Z := 0x508e8.
Definition src0_D_stdin_used : Z := 0x508f0.
Definition src0_D_ofl_lock : Z := 0x508f8.
Definition src0_D_ofl_head : Z := 0x50900.
Definition src0_D_stderr_buf : Z := 0x50908.
Definition src0_D_stdout_buf : Z := 0x50910.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 124.
