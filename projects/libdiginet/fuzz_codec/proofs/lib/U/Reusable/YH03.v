(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: removes 78 cells that no proof of this unit reads, and renames 5 cells to oft_*, the names this image gives those symbols (values unchanged). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12ccc.  Definition src0_text_hi : Z := 0x1e664.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1138c.
Definition src0_eh_frame_lo : Z := 0x11550.  Definition src0_eh_frame_hi : Z := 0x11ccc.
Definition src0_init_array_lo : Z := 0x1f668.  Definition src0_init_array_hi : Z := 0x1f670.
Definition src0_fini_array_lo : Z := 0x1f670.  Definition src0_fini_array_hi : Z := 0x1f678.
Definition src0_data_rel_ro_lo : Z := 0x1f678.  Definition src0_data_rel_ro_hi : Z := 0x1f8c0.
Definition src0_got_lo : Z := 0x1f8c0.  Definition src0_got_hi : Z := 0x1f958.
Definition src0_data_lo : Z := 0x20958.  Definition src0_data_hi : Z := 0x20b64.
Definition src0_bss_lo : Z := 0x20b70.  Definition src0_bss_hi : Z := 0x51798.
Definition src0_A_do_init : Z := 0x12d14.  Definition src0_E_do_init : Z := 0x12d88.
Definition src0_A_do_fini : Z := 0x12d88.  Definition src0_E_do_fini : Z := 0x12e18.
Definition src0_A_main : Z := 0x12e18.  Definition src0_E_main : Z := 0x130dc.
Definition src0_A_target_alloc_init : Z := 0x130dc.  Definition src0_E_target_alloc_init : Z := 0x130e0.
Definition src0_A_target_alloc_count : Z := 0x130e0.  Definition src0_E_target_alloc_count : Z := 0x130e8.
Definition src0_A_target_run : Z := 0x130e8.  Definition src0_E_target_run : Z := 0x13240.
Definition src0_A_oft_exit_guard : Z := 0x13240.  Definition src0_E_oft_exit_guard : Z := 0x13270.
Definition src0_A_emit_printf : Z := 0x13270.  Definition src0_E_emit_printf : Z := 0x132b8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x132b8.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14bbc.
Definition src0_A_init : Z := 0x16234.  Definition src0_E_init : Z := 0x16238.
Definition src0_A_init_libc : Z := 0x16238.  Definition src0_E_init_libc : Z := 0x16464.
Definition src0_A_libc_start_init : Z := 0x16464.  Definition src0_E_libc_start_init : Z := 0x164b0.
Definition src0_A_libc_start_main : Z := 0x164b0.  Definition src0_E_libc_start_main : Z := 0x16510.
Definition src0_A_libc_start_main_stage2 : Z := 0x16510.  Definition src0_E_libc_start_main_stage2 : Z := 0x16558.
Definition src0_A_init_tls : Z := 0x16558.  Definition src0_E_init_tls : Z := 0x16808.
Definition src0_A_funcs_on_exit : Z := 0x168b8.  Definition src0_E_funcs_on_exit : Z := 0x16980.
Definition src0_A_cxa_finalize : Z := 0x16980.  Definition src0_E_cxa_finalize : Z := 0x16984.
Definition src0_A_atexit : Z := 0x16984.  Definition src0_E_atexit : Z := 0x16a48.
Definition src0_A_atexit_call : Z := 0x16a48.  Definition src0_E_atexit_call : Z := 0x16a4c.
Definition src0_A_fini : Z := 0x16a4c.  Definition src0_E_fini : Z := 0x16a50.
Definition src0_A_libc_exit_fini : Z := 0x16a50.  Definition src0_E_libc_exit_fini : Z := 0x16a9c.
Definition src0_A_exit : Z := 0x16a9c.  Definition src0_E_exit : Z := 0x16b10.
Definition src0_A_Exit : Z := 0x1689c.  Definition src0_E_Exit : Z := 0x168b8.
Definition src0_A_open : Z := 0x16b10.  Definition src0_E_open : Z := 0x16bf4.
Definition src0_A_init_ssp : Z := 0x16bf4.  Definition src0_E_init_ssp : Z := 0x16c54.
Definition src0_A_stack_chk_fail : Z := 0x16c54.  Definition src0_E_stack_chk_fail : Z := 0x16c5c.
Definition src0_A_syscall_ret : Z := 0x16c5c.  Definition src0_E_syscall_ret : Z := 0x16c94.
Definition src0_A_errno_location : Z := 0x16c94.  Definition src0_E_errno_location : Z := 0x16ca0.
Definition src0_A_free : Z := 0x16ca0.  Definition src0_E_free : Z := 0x16ca4.
Definition src0_A_libc_calloc : Z := 0x16ca4.  Definition src0_E_libc_calloc : Z := 0x16ddc.
Definition src0_A_libc_malloc : Z := 0x16ddc.  Definition src0_E_libc_malloc : Z := 0x16de0.
Definition src0_A_malloc : Z := 0x16de0.  Definition src0_E_malloc : Z := 0x16de4.
Definition src0_A_libc_free : Z := 0x16de4.  Definition src0_E_libc_free : Z := 0x16fb0.
Definition src0_A_get_meta : Z := 0x16fb0.  Definition src0_E_get_meta : Z := 0x170c0.
Definition src0_A_nontrivial_free : Z := 0x170c0.  Definition src0_E_nontrivial_free : Z := 0x17498.
Definition src0_A_alloc_meta : Z := 0x17498.  Definition src0_E_alloc_meta : Z := 0x17770.
Definition src0_A_libc_malloc_impl : Z := 0x17770.  Definition src0_E_libc_malloc_impl : Z := 0x17ae0.
Definition src0_A_alloc_slot : Z := 0x17ae0.  Definition src0_E_alloc_slot : Z := 0x18384.
Definition src0_A_enframe : Z := 0x18384.  Definition src0_E_enframe : Z := 0x184d4.
Definition src0_A_malloc_allzerop : Z := 0x184d4.  Definition src0_E_malloc_allzerop : Z := 0x1864c.
Definition src0_A_vm_wait : Z := 0x1864c.  Definition src0_E_vm_wait : Z := 0x18650.
Definition src0_A_mmap : Z := 0x18650.  Definition src0_E_mmap : Z := 0x1873c.
Definition src0_A_mprotect : Z := 0x1873c.  Definition src0_E_mprotect : Z := 0x18784.
Definition src0_A_munmap : Z := 0x18784.  Definition src0_E_munmap : Z := 0x187cc.
Definition src0_A_fflush : Z := 0x188a0.  Definition src0_E_fflush : Z := 0x18a10.
Definition src0_A_lockfile : Z := 0x18a10.  Definition src0_E_lockfile : Z := 0x18b0c.
Definition src0_A_unlockfile : Z := 0x18b0c.  Definition src0_E_unlockfile : Z := 0x18b6c.
Definition src0_A_stdio_write : Z := 0x19024.  Definition src0_E_stdio_write : Z := 0x191b4.
Definition src0_A_stdio_seek : Z := 0x191b4.  Definition src0_E_stdio_seek : Z := 0x191bc.
Definition src0_A_aio_close : Z := 0x18ff4.  Definition src0_E_aio_close : Z := 0x18ff8.
Definition src0_A_stdio_close : Z := 0x18ff8.  Definition src0_E_stdio_close : Z := 0x19024.
Definition src0_A_fprintf : Z := 0x18b6c.  Definition src0_E_fprintf : Z := 0x18bd0.
Definition src0_A_fwritex : Z := 0x18bd0.  Definition src0_E_fwritex : Z := 0x18d08.
Definition src0_A_fwrite : Z := 0x18d08.  Definition src0_E_fwrite : Z := 0x18dc0.
Definition src0_A_towrite : Z := 0x18dc0.  Definition src0_E_towrite : Z := 0x18e14.
Definition src0_A_stdio_exit : Z := 0x18e14.  Definition src0_E_stdio_exit : Z := 0x18fb8.
Definition src0_A_ofl_lock : Z := 0x18fb8.  Definition src0_E_ofl_lock : Z := 0x18fe8.
Definition src0_A_ofl_unlock : Z := 0x18fe8.  Definition src0_E_ofl_unlock : Z := 0x18ff4.
Definition src0_A_stdout_write : Z := 0x191bc.  Definition src0_E_stdout_write : Z := 0x1925c.
Definition src0_A_vfprintf : Z := 0x1925c.  Definition src0_E_vfprintf : Z := 0x1940c.
Definition src0_A_printf_core : Z := 0x1940c.  Definition src0_E_printf_core : Z := 0x1a23c.
Definition src0_A_pop_arg : Z := 0x1a23c.  Definition src0_E_pop_arg : Z := 0x1a370.
Definition src0_A_pad : Z := 0x1a370.  Definition src0_E_pad : Z := 0x1a444.
Definition src0_A_fmt_fp : Z := 0x1a444.  Definition src0_E_fmt_fp : Z := 0x1bb0c.
Definition src0_A_strerror : Z := 0x1bb0c.  Definition src0_E_strerror : Z := 0x1bb48.
Definition src0_A_lctrans_impl : Z := 0x1bb48.  Definition src0_E_lctrans_impl : Z := 0x1bb4c.
Definition src0_A_lctrans : Z := 0x1bb4c.  Definition src0_E_lctrans : Z := 0x1bb50.
Definition src0_A_wctomb : Z := 0x1bb50.  Definition src0_E_wctomb : Z := 0x1bb74.
Definition src0_A_wcrtomb : Z := 0x1bb74.  Definition src0_E_wcrtomb : Z := 0x1bca0.
Definition src0_A_extenddftf2 : Z := 0x1bca0.  Definition src0_E_extenddftf2 : Z := 0x1be30.
Definition src0_A_signbitl : Z := 0x1be30.  Definition src0_E_signbitl : Z := 0x1be38.
Definition src0_A_fpclassifyl : Z := 0x1be38.  Definition src0_E_fpclassifyl : Z := 0x1be7c.
Definition src0_A_frexpl : Z := 0x1be7c.  Definition src0_E_frexpl : Z := 0x1bf54.
Definition src0_A_letf2 : Z := 0x1bf54.  Definition src0_E_letf2 : Z := 0x1c01c.
Definition src0_A_multf3 : Z := 0x1c01c.  Definition src0_E_multf3 : Z := 0x1c71c.
Definition src0_A_floatsitf : Z := 0x1c71c.  Definition src0_E_floatsitf : Z := 0x1c824.
Definition src0_A_scalbn : Z := 0x1c824.  Definition src0_E_scalbn : Z := 0x1c8bc.
Definition src0_A_subtf3 : Z := 0x1c8bc.  Definition src0_E_subtf3 : Z := 0x1c8cc.
Definition src0_A_addtf3 : Z := 0x1c8cc.  Definition src0_E_addtf3 : Z := 0x1d098.
Definition src0_A_fe_getround : Z := 0x1d098.  Definition src0_E_fe_getround : Z := 0x1d0c8.
Definition src0_A_fe_raise_inexact : Z := 0x1d0c8.  Definition src0_E_fe_raise_inexact : Z := 0x1d0d4.
Definition src0_A_fixunstfsi : Z := 0x1d0d4.  Definition src0_E_fixunstfsi : Z := 0x1d168.
Definition src0_A_floatunsitf : Z := 0x1d168.  Definition src0_E_floatunsitf : Z := 0x1d254.
Definition src0_A_fixtfsi : Z := 0x1d254.  Definition src0_E_fixtfsi : Z := 0x1d2fc.
Definition src0_A_divtf3 : Z := 0x1d2fc.  Definition src0_E_divtf3 : Z := 0x1dc00.
Definition src0_A_vprintf : Z := 0x1dc00.  Definition src0_E_vprintf : Z := 0x1dc1c.
Definition src0_A_bcmp : Z := 0x1dc1c.  Definition src0_E_bcmp : Z := 0x1dc20.
Definition src0_A_memcmp : Z := 0x1dc20.  Definition src0_E_memcmp : Z := 0x1dc50.
Definition src0_A_memcpy : Z := 0x1dc50.  Definition src0_E_memcpy : Z := 0x1e054.
Definition src0_A_memset : Z := 0x1e054.  Definition src0_E_memset : Z := 0x1e14c.
Definition src0_A_strnlen : Z := 0x1e184.  Definition src0_E_strnlen : Z := 0x1e1c8.
Definition src0_A_memchr : Z := 0x1e1c8.  Definition src0_E_memchr : Z := 0x1e294.
Definition src0_A_lock : Z := 0x1e294.  Definition src0_E_lock : Z := 0x1e51c.
Definition src0_A_unlock : Z := 0x1e51c.  Definition src0_E_unlock : Z := 0x1e590.
Definition src0_A_syscall_cp_c : Z := 0x1e590.  Definition src0_E_syscall_cp_c : Z := 0x1e5b4.
Definition src0_A_syscall_cp : Z := 0x1e5b4.  Definition src0_E_syscall_cp : Z := 0x1e5b8.
Definition src0_A_unistd_exit : Z := 0x1e5c4.  Definition src0_E_unistd_exit : Z := 0x1e5d0.
Definition src0_A_close : Z := 0x1e5d0.  Definition src0_E_close : Z := 0x1e624.
Definition src0_A_lseek : Z := 0x1e624.  Definition src0_E_lseek : Z := 0x1e630.
Definition src0_A_read : Z := 0x1e630.  Definition src0_E_read : Z := 0x1e664.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102c6.
Definition src0_D_str_d_n : Z := 0x102da.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102ec.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102fd.
Definition src0_D_str_inf : Z := 0x1032b.
Definition src0_D_str_INF : Z := 0x10346.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x1034a.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103aa.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103bf.
Definition src0_D_str_NAN : Z := 0x103f7.
Definition src0_D_str_nan : Z := 0x10404.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10408.
Definition src0_D_str_dev_null : Z := 0x10430.
Definition src0_D_str_null : Z := 0x1043a.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x108b0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x108c0.
Definition src0_D_debruijn32 : Z := 0x106a8.
Definition src0_D_size_classes : Z := 0x106c8.
Definition src0_D_small_cnt_tab : Z := 0x10728.
Definition src0_D_med_cnt_tab : Z := 0x10743.
Definition src0_D_states : Z := 0x108f0.
Definition src0_D_xdigits : Z := 0x10ac0.
Definition src0_D_errmsgstr : Z := 0x10ad0.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11278.
Definition src0_D_fe_getround : Z := 0x11380.
Definition src0_D_EH_FRAME_LIST : Z := 0x11550.
Definition src0_D_init_array_start : Z := 0x1f668.
Definition src0_D_fini_array_start : Z := 0x1f670.
Definition src0_D_stderr : Z := 0x1f8b0.
Definition src0_D_stdout : Z := 0x1f8b8.
Definition src0_D_got_DYNAMIC : Z := 0x1f8c8.
Definition src0_D_got_main : Z := 0x1f8d0.
Definition src0_D_got_init : Z := 0x1f8d8.
Definition src0_D_got_fini : Z := 0x1f8e0.
Definition src0_D_got_register_frame_info : Z := 0x1f8e8.
Definition src0_D_got_cxa_finalize : Z := 0x1f8f0.
Definition src0_D_got_deregister_frame_info : Z := 0x1f8f8.
Definition src0_D_got_stderr : Z := 0x1f900.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1f908.
Definition src0_D_got_stdout : Z := 0x1f910.
Definition src0_D_got_environ : Z := 0x1f918.
Definition src0_D_got_progname_full : Z := 0x1f920.
Definition src0_D_got_progname : Z := 0x1f928.
Definition src0_D_got_init_array_end : Z := 0x1f930.
Definition src0_D_got_init_array_start : Z := 0x1f938.
Definition src0_D_got_stack_chk_guard : Z := 0x1f940.
Definition src0_D_got_fini_array_end : Z := 0x1f948.
Definition src0_D_got_fini_array_start : Z := 0x1f950.
Definition src0_D_dso_handle : Z := 0x20958.
Definition src0_D_oft_argc : Z := 0x20968.
Definition src0_D_stderr_FILE : Z := 0x20980.
Definition src0_D_stderr_used : Z := 0x20a68.
Definition src0_D_stdout_FILE : Z := 0x20a70.
Definition src0_D_stdout_used : Z := 0x20b58.
Definition src0_D_default_stacksize : Z := 0x20b60.
Definition src0_D_do_init_initialized : Z := 0x20b70.
Definition src0_D_do_init_object : Z := 0x20b78.
Definition src0_D_do_fini_finalized : Z := 0x20bb8.
Definition src0_D_read_stage : Z := 0x20bb9.
Definition src0_D_target_run_initialized : Z := 0x30bc0.
Definition src0_D_oft_in_callback : Z := 0x30bc4.
Definition src0_D_oft_aligned_copy_empty : Z := 0x30bd0.
Definition src0_D_environ : Z := 0x30bf0.
Definition src0_D_thread_list_lock : Z := 0x50cc8.
Definition src0_D_main_tls : Z := 0x50cd0.
Definition src0_D_builtin_tls : Z := 0x30bf8.
Definition src0_D_finished_atexit : Z := 0x50d08.
Definition src0_D_atexit_lock : Z := 0x50d0c.
Definition src0_D_atexit_slot : Z := 0x50d10.
Definition src0_D_atexit_head : Z := 0x50d18.
Definition src0_D_atexit_builtin : Z := 0x50d20.
Definition src0_D_exit_exit_lock : Z := 0x50f28.
Definition src0_D_stack_chk_guard : Z := 0x50f30.
Definition src0_D_sysinfo : Z := 0x50f38.
Definition src0_D_progname : Z := 0x50f40.
Definition src0_D_progname_full : Z := 0x50f48.
Definition src0_D_libc : Z := 0x50f50.
Definition src0_D_hwcap : Z := 0x50fb8.
Definition src0_D_malloc_lock : Z := 0x50fc0.
Definition src0_D_malloc_context : Z := 0x50fc8.
Definition src0_D_malloc_replaced : Z := 0x51368.
Definition src0_D_stdin_used : Z := 0x51370.
Definition src0_D_ofl_lock : Z := 0x51378.
Definition src0_D_ofl_head : Z := 0x51380.
Definition src0_D_stderr_buf : Z := 0x51388.
Definition src0_D_stdout_buf : Z := 0x51390.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 33.
