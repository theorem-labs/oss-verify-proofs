(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x128dc.  Definition src0_text_hi : Z := 0x1d018.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x111cc.
Definition src0_eh_frame_lo : Z := 0x11310.  Definition src0_eh_frame_hi : Z := 0x118dc.
Definition src0_init_array_lo : Z := 0x1e018.  Definition src0_init_array_hi : Z := 0x1e020.
Definition src0_fini_array_lo : Z := 0x1e020.  Definition src0_fini_array_hi : Z := 0x1e028.
Definition src0_data_rel_ro_lo : Z := 0x1e028.  Definition src0_data_rel_ro_hi : Z := 0x1e038.
Definition src0_got_lo : Z := 0x1e038.  Definition src0_got_hi : Z := 0x1e0d0.
Definition src0_data_lo : Z := 0x1f0d0.  Definition src0_data_hi : Z := 0x1f2e4.
Definition src0_bss_lo : Z := 0x1f2f0.  Definition src0_bss_hi : Z := 0x4ff30.
Definition src0_A_start : Z := 0x128dc.  Definition src0_E_start : Z := 0x12924.
Definition src0_A_do_init : Z := 0x12924.  Definition src0_E_do_init : Z := 0x12998.
Definition src0_A_do_fini : Z := 0x12998.  Definition src0_E_do_fini : Z := 0x12a28.
Definition src0_A_main : Z := 0x12a28.  Definition src0_E_main : Z := 0x12cec.
Definition src0_A_target_alloc_init : Z := 0x12cec.  Definition src0_E_target_alloc_init : Z := 0x12cf0.
Definition src0_A_target_alloc_count : Z := 0x12cf0.  Definition src0_E_target_alloc_count : Z := 0x12cf8.
Definition src0_A_target_run : Z := 0x12cf8.  Definition src0_E_target_run : Z := 0x12e50.
Definition src0_A_aef_exit_guard : Z := 0x12e50.  Definition src0_E_aef_exit_guard : Z := 0x12e80.
Definition src0_A_emit_printf : Z := 0x12e80.  Definition src0_E_emit_printf : Z := 0x12ec8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ec8.
Definition src0_A_init : Z := 0x14134.  Definition src0_E_init : Z := 0x14138.
Definition src0_A_init_libc : Z := 0x14138.  Definition src0_E_init_libc : Z := 0x14364.
Definition src0_A_libc_start_init : Z := 0x14364.  Definition src0_E_libc_start_init : Z := 0x143b0.
Definition src0_A_libc_start_main : Z := 0x143b0.  Definition src0_E_libc_start_main : Z := 0x14410.
Definition src0_A_libc_start_main_stage2 : Z := 0x14410.  Definition src0_E_libc_start_main_stage2 : Z := 0x14458.
Definition src0_A_init_tls : Z := 0x14458.  Definition src0_E_init_tls : Z := 0x14708.
Definition src0_A_funcs_on_exit : Z := 0x147c4.  Definition src0_E_funcs_on_exit : Z := 0x1488c.
Definition src0_A_cxa_finalize : Z := 0x1488c.  Definition src0_E_cxa_finalize : Z := 0x14890.
Definition src0_A_atexit : Z := 0x14890.  Definition src0_E_atexit : Z := 0x14954.
Definition src0_A_atexit_call : Z := 0x14954.  Definition src0_E_atexit_call : Z := 0x14958.
Definition src0_A_fini : Z := 0x14958.  Definition src0_E_fini : Z := 0x1495c.
Definition src0_A_libc_exit_fini : Z := 0x1495c.  Definition src0_E_libc_exit_fini : Z := 0x149a8.
Definition src0_A_exit : Z := 0x149a8.  Definition src0_E_exit : Z := 0x14a1c.
Definition src0_A_Exit : Z := 0x147a8.  Definition src0_E_Exit : Z := 0x147c4.
Definition src0_A_open : Z := 0x14a1c.  Definition src0_E_open : Z := 0x14b00.
Definition src0_A_init_ssp : Z := 0x14b00.  Definition src0_E_init_ssp : Z := 0x14b60.
Definition src0_A_stack_chk_fail : Z := 0x14b60.  Definition src0_E_stack_chk_fail : Z := 0x14b68.
Definition src0_A_syscall_ret : Z := 0x14b68.  Definition src0_E_syscall_ret : Z := 0x14ba0.
Definition src0_A_errno_location : Z := 0x14708.  Definition src0_E_errno_location : Z := 0x14714.
Definition src0_A_free : Z := 0x14ba0.  Definition src0_E_free : Z := 0x14ba4.
Definition src0_A_libc_calloc : Z := 0x14ba4.  Definition src0_E_libc_calloc : Z := 0x14cdc.
Definition src0_A_libc_malloc : Z := 0x14cdc.  Definition src0_E_libc_malloc : Z := 0x14ce0.
Definition src0_A_malloc : Z := 0x14ce0.  Definition src0_E_malloc : Z := 0x14ce4.
Definition src0_A_libc_free : Z := 0x14ce4.  Definition src0_E_libc_free : Z := 0x14eb0.
Definition src0_A_get_meta : Z := 0x14eb0.  Definition src0_E_get_meta : Z := 0x14fc0.
Definition src0_A_nontrivial_free : Z := 0x14fc0.  Definition src0_E_nontrivial_free : Z := 0x15398.
Definition src0_A_alloc_meta : Z := 0x15398.  Definition src0_E_alloc_meta : Z := 0x15670.
Definition src0_A_libc_malloc_impl : Z := 0x15670.  Definition src0_E_libc_malloc_impl : Z := 0x159e0.
Definition src0_A_alloc_slot : Z := 0x159e0.  Definition src0_E_alloc_slot : Z := 0x16284.
Definition src0_A_enframe : Z := 0x16284.  Definition src0_E_enframe : Z := 0x163d4.
Definition src0_A_malloc_allzerop : Z := 0x163d4.  Definition src0_E_malloc_allzerop : Z := 0x1654c.
Definition src0_A_vm_wait : Z := 0x1654c.  Definition src0_E_vm_wait : Z := 0x16550.
Definition src0_A_mmap : Z := 0x16550.  Definition src0_E_mmap : Z := 0x1663c.
Definition src0_A_mprotect : Z := 0x1663c.  Definition src0_E_mprotect : Z := 0x16684.
Definition src0_A_munmap : Z := 0x16684.
Definition src0_A_fflush : Z := 0x167a0.  Definition src0_E_fflush : Z := 0x16910.
Definition src0_A_lockfile : Z := 0x16910.  Definition src0_E_lockfile : Z := 0x16a0c.
Definition src0_A_unlockfile : Z := 0x16a0c.
Definition src0_A_aio_close : Z := 0x16c04.  Definition src0_E_aio_close : Z := 0x16c08.
Definition src0_A_fprintf : Z := 0x16c34.  Definition src0_E_fprintf : Z := 0x16c98.
Definition src0_A_fwritex : Z := 0x16e3c.  Definition src0_E_fwritex : Z := 0x16f74.
Definition src0_A_fwrite : Z := 0x16f74.  Definition src0_E_fwrite : Z := 0x1702c.
Definition src0_A_towrite : Z := 0x1702c.  Definition src0_E_towrite : Z := 0x17080.
Definition src0_A_stdio_exit : Z := 0x16c98.  Definition src0_E_stdio_exit : Z := 0x16e3c.
Definition src0_A_ofl_lock : Z := 0x17080.  Definition src0_E_ofl_lock : Z := 0x170b0.
Definition src0_A_ofl_unlock : Z := 0x170b0.
Definition src0_A_stdout_write : Z := 0x1711c.  Definition src0_E_stdout_write : Z := 0x171bc.
Definition src0_A_vfprintf : Z := 0x171bc.  Definition src0_E_vfprintf : Z := 0x1736c.
Definition src0_A_printf_core : Z := 0x1736c.  Definition src0_E_printf_core : Z := 0x1819c.
Definition src0_A_pop_arg : Z := 0x1819c.  Definition src0_E_pop_arg : Z := 0x182d0.
Definition src0_A_pad : Z := 0x182d0.  Definition src0_E_pad : Z := 0x183a4.
Definition src0_A_fmt_fp : Z := 0x183a4.  Definition src0_E_fmt_fp : Z := 0x19a6c.
Definition src0_A_strerror : Z := 0x19a6c.
Definition src0_E_lctrans_impl : Z := 0x19aac.
Definition src0_A_lctrans : Z := 0x19aac.  Definition src0_E_lctrans : Z := 0x19ab0.
Definition src0_A_wctomb : Z := 0x19ab0.  Definition src0_E_wctomb : Z := 0x19ad4.
Definition src0_A_wcrtomb : Z := 0x19ad4.  Definition src0_E_wcrtomb : Z := 0x19c00.
Definition src0_A_extenddftf2 : Z := 0x19c00.
Definition src0_E_signbitl : Z := 0x19d98.
Definition src0_A_fpclassifyl : Z := 0x19d98.
Definition src0_E_frexpl : Z := 0x19eb4.
Definition src0_A_letf2 : Z := 0x19eb4.  Definition src0_E_letf2 : Z := 0x19f7c.
Definition src0_A_multf3 : Z := 0x19f7c.  Definition src0_E_multf3 : Z := 0x1a67c.
Definition src0_A_floatsitf : Z := 0x1a67c.
Definition src0_E_scalbn : Z := 0x1a81c.
Definition src0_A_subtf3 : Z := 0x1a81c.  Definition src0_E_subtf3 : Z := 0x1a82c.
Definition src0_A_addtf3 : Z := 0x1a82c.  Definition src0_E_addtf3 : Z := 0x1aff8.
Definition src0_A_fe_getround : Z := 0x1aff8.  Definition src0_E_fe_getround : Z := 0x1b028.
Definition src0_A_fe_raise_inexact : Z := 0x1b028.  Definition src0_E_fe_raise_inexact : Z := 0x1b034.
Definition src0_A_fixunstfsi : Z := 0x1b034.  Definition src0_E_fixunstfsi : Z := 0x1b0c8.
Definition src0_A_floatunsitf : Z := 0x1b0c8.  Definition src0_E_floatunsitf : Z := 0x1b1b4.
Definition src0_A_fixtfsi : Z := 0x1b1b4.  Definition src0_E_fixtfsi : Z := 0x1b25c.
Definition src0_A_divtf3 : Z := 0x1b25c.  Definition src0_E_divtf3 : Z := 0x1bb60.
Definition src0_A_vprintf : Z := 0x1bb60.
Definition src0_E_memcmp : Z := 0x1be24.
Definition src0_A_memcpy : Z := 0x1be24.  Definition src0_E_memcpy : Z := 0x1c228.
Definition src0_A_memset : Z := 0x1c228.
Definition src0_E_strlen : Z := 0x1c4cc.
Definition src0_A_strnlen : Z := 0x1c604.  Definition src0_E_strnlen : Z := 0x1c648.
Definition src0_A_memchr : Z := 0x1bd28.  Definition src0_E_memchr : Z := 0x1bdf4.
Definition src0_A_lock : Z := 0x1cc48.  Definition src0_E_lock : Z := 0x1ced0.
Definition src0_A_unlock : Z := 0x1ced0.  Definition src0_E_unlock : Z := 0x1cf44.
Definition src0_A_syscall_cp_c : Z := 0x1cf44.  Definition src0_E_syscall_cp_c : Z := 0x1cf68.
Definition src0_A_syscall_cp : Z := 0x1cf68.  Definition src0_E_syscall_cp : Z := 0x1cf6c.
Definition src0_A_set_thread_area : Z := 0x1cf6c.  Definition src0_E_set_thread_area : Z := 0x1cf78.
Definition src0_A_unistd_exit : Z := 0x1cf78.  Definition src0_E_unistd_exit : Z := 0x1cf84.
Definition src0_A_close : Z := 0x1cf84.  Definition src0_E_close : Z := 0x1cfd8.
Definition src0_A_lseek : Z := 0x1cfd8.  Definition src0_E_lseek : Z := 0x1cfe4.
Definition src0_A_read : Z := 0x1cfe4.
Definition src0_D_str_n0X0x : Z := 0x102b2.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102cf.
Definition src0_D_str_d_n : Z := 0x102e3.
Definition src0_D_str : Z := 0x102e7.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102ea.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102fb.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10323.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103ea.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103ff.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10454.
Definition src0_D_str_dev_null : Z := 0x10474.
Definition src0_D_str_null : Z := 0x1047e.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x106f0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10700.
Definition src0_D_debruijn32 : Z := 0x104e1.
Definition src0_D_size_classes : Z := 0x10502.
Definition src0_D_small_cnt_tab : Z := 0x10562.
Definition src0_D_med_cnt_tab : Z := 0x1057d.
Definition src0_D_states : Z := 0x10730.
Definition src0_D_xdigits : Z := 0x10900.
Definition src0_D_errmsgstr : Z := 0x10910.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x110b8.
Definition src0_D_fe_getround : Z := 0x111c0.
Definition src0_D_EH_FRAME_LIST : Z := 0x11310.
Definition src0_D_init_array_start : Z := 0x1e018.
Definition src0_D_fini_array_start : Z := 0x1e020.
Definition src0_D_stderr : Z := 0x1e028.
Definition src0_D_stdout : Z := 0x1e030.
Definition src0_D_got_DYNAMIC : Z := 0x1e040.
Definition src0_D_got_main : Z := 0x1e048.
Definition src0_D_got_init : Z := 0x1e050.
Definition src0_D_got_fini : Z := 0x1e058.
Definition src0_D_got_register_frame_info : Z := 0x1e060.
Definition src0_D_got_cxa_finalize : Z := 0x1e068.
Definition src0_D_got_deregister_frame_info : Z := 0x1e070.
Definition src0_D_got_stderr : Z := 0x1e078.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1e080.
Definition src0_D_got_stdout : Z := 0x1e088.
Definition src0_D_got_environ : Z := 0x1e090.
Definition src0_D_got_progname_full : Z := 0x1e098.
Definition src0_D_got_progname : Z := 0x1e0a0.
Definition src0_D_got_init_array_end : Z := 0x1e0a8.
Definition src0_D_got_init_array_start : Z := 0x1e0b0.
Definition src0_D_got_stack_chk_guard : Z := 0x1e0b8.
Definition src0_D_got_fini_array_end : Z := 0x1e0c0.
Definition src0_D_got_fini_array_start : Z := 0x1e0c8.
Definition src0_D_dso_handle : Z := 0x1f0d0.
Definition src0_D_aef_argc : Z := 0x1f0e0.
Definition src0_D_stderr_FILE : Z := 0x1f100.
Definition src0_D_stderr_used : Z := 0x1f1e8.
Definition src0_D_stdout_FILE : Z := 0x1f1f0.
Definition src0_D_stdout_used : Z := 0x1f2d8.
Definition src0_D_default_stacksize : Z := 0x1f2e0.
Definition src0_D_do_init_initialized : Z := 0x1f2f0.
Definition src0_D_do_init_object : Z := 0x1f2f8.
Definition src0_D_do_fini_finalized : Z := 0x1f338.
Definition src0_D_read_stage : Z := 0x1f339.
Definition src0_D_target_run_initialized : Z := 0x2f340.
Definition src0_D_aef_in_callback : Z := 0x2f344.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f350.
Definition src0_D_environ : Z := 0x2f388.
Definition src0_D_thread_list_lock : Z := 0x4f460.
Definition src0_D_main_tls : Z := 0x4f468.
Definition src0_D_builtin_tls : Z := 0x2f390.
Definition src0_D_finished_atexit : Z := 0x4f4a0.
Definition src0_D_atexit_lock : Z := 0x4f4a4.
Definition src0_D_atexit_slot : Z := 0x4f4a8.
Definition src0_D_atexit_head : Z := 0x4f4b0.
Definition src0_D_atexit_builtin : Z := 0x4f4b8.
Definition src0_D_exit_exit_lock : Z := 0x4f6c0.
Definition src0_D_stack_chk_guard : Z := 0x4f6c8.
Definition src0_D_sysinfo : Z := 0x4f6d0.
Definition src0_D_progname : Z := 0x4f6d8.
Definition src0_D_progname_full : Z := 0x4f6e0.
Definition src0_D_libc : Z := 0x4f6e8.
Definition src0_D_hwcap : Z := 0x4f750.
Definition src0_D_malloc_lock : Z := 0x4f758.
Definition src0_D_malloc_context : Z := 0x4f760.
Definition src0_D_malloc_replaced : Z := 0x4fb00.
Definition src0_D_stdin_used : Z := 0x4fb08.
Definition src0_D_ofl_lock : Z := 0x4fb10.
Definition src0_D_ofl_head : Z := 0x4fb18.
Definition src0_D_stderr_buf : Z := 0x4fb20.
Definition src0_D_stdout_buf : Z := 0x4fb28.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 33.
