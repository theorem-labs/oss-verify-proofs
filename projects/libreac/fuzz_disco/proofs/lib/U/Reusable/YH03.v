(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: cells re-derived from fuzz_disco's own ubsan image (pin 56121de6ba4c and its unstripped twin): A/E rows by the address-table re-derivation tool from the twin's symbols, src0_D_stderr by hand to the stderr object, D_str / const / jt / got / NOSYM cells by their bytes and the code that reads them; a cell with no reader outside this file is deleted when this image has no counterpart for it or its value is wrong (table: the unit's yh03-fix table, ubsan). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12d40.  Definition src0_text_hi : Z := 0x1f5d0.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11294.
Definition src0_eh_frame_lo : Z := 0x11470.  Definition src0_eh_frame_hi : Z := 0x11d40.
Definition src0_init_array_lo : Z := 0x205d0.  Definition src0_init_array_hi : Z := 0x205d8.
Definition src0_fini_array_lo : Z := 0x205d8.  Definition src0_fini_array_hi : Z := 0x205e0.
Definition src0_data_rel_ro_lo : Z := 0x205e0.  Definition src0_data_rel_ro_hi : Z := 0x20620.
Definition src0_got_lo : Z := 0x20620.  Definition src0_got_hi : Z := 0x206b8.
Definition src0_data_lo : Z := 0x216b8.  Definition src0_data_hi : Z := 0x218c4.
Definition src0_bss_lo : Z := 0x218d0.  Definition src0_bss_hi : Z := 0x524f8.
Definition src0_A_start : Z := 0x12d40.  Definition src0_E_start : Z := 0x12d88.
Definition src0_A_do_init : Z := 0x12d88.  Definition src0_E_do_init : Z := 0x12dfc.
Definition src0_A_do_fini : Z := 0x12dfc.  Definition src0_E_do_fini : Z := 0x12e8c.
Definition src0_A_main : Z := 0x12e8c.  Definition src0_E_main : Z := 0x13150.
Definition src0_A_target_alloc_init : Z := 0x13150.  Definition src0_E_target_alloc_init : Z := 0x13154.
Definition src0_A_target_alloc_count : Z := 0x13154.  Definition src0_E_target_alloc_count : Z := 0x1315c.
Definition src0_A_target_run : Z := 0x1315c.  Definition src0_E_target_run : Z := 0x132b4.
Definition src0_A_aef_exit_guard : Z := 0x132b4.  Definition src0_E_aef_exit_guard : Z := 0x132e4.
Definition src0_A_emit_printf : Z := 0x132e4.  Definition src0_E_emit_printf : Z := 0x1332c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x1332c.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x145bc.
Definition src0_A_init : Z := 0x16f40.  Definition src0_E_init : Z := 0x16f44.
Definition src0_A_init_libc : Z := 0x16f44.  Definition src0_E_init_libc : Z := 0x17170.
Definition src0_A_libc_start_init : Z := 0x17170.  Definition src0_E_libc_start_init : Z := 0x171bc.
Definition src0_A_libc_start_main : Z := 0x171bc.  Definition src0_E_libc_start_main : Z := 0x1721c.
Definition src0_A_libc_start_main_stage2 : Z := 0x1721c.  Definition src0_E_libc_start_main_stage2 : Z := 0x17264.
Definition src0_A_init_tls : Z := 0x17264.  Definition src0_E_init_tls : Z := 0x17514.
Definition src0_A_funcs_on_exit : Z := 0x175c4.  Definition src0_E_funcs_on_exit : Z := 0x1768c.
Definition src0_A_cxa_finalize : Z := 0x1768c.  Definition src0_E_cxa_finalize : Z := 0x17690.
Definition src0_A_atexit : Z := 0x17690.  Definition src0_E_atexit : Z := 0x17754.
Definition src0_A_atexit_call : Z := 0x17754.  Definition src0_E_atexit_call : Z := 0x17758.
Definition src0_A_fini : Z := 0x17758.  Definition src0_E_fini : Z := 0x1775c.
Definition src0_A_libc_exit_fini : Z := 0x1775c.  Definition src0_E_libc_exit_fini : Z := 0x177a8.
Definition src0_A_exit : Z := 0x177a8.  Definition src0_E_exit : Z := 0x1781c.
Definition src0_A_Exit : Z := 0x175a8.  Definition src0_E_Exit : Z := 0x175c4.
Definition src0_A_open : Z := 0x17884.  Definition src0_E_open : Z := 0x17968.
Definition src0_A_init_ssp : Z := 0x1781c.  Definition src0_E_init_ssp : Z := 0x1787c.
Definition src0_A_stack_chk_fail : Z := 0x1787c.  Definition src0_E_stack_chk_fail : Z := 0x17884.
Definition src0_A_syscall_ret : Z := 0x17968.  Definition src0_E_syscall_ret : Z := 0x179a0.
Definition src0_A_errno_location : Z := 0x179a0.  Definition src0_E_errno_location : Z := 0x179ac.
Definition src0_A_free : Z := 0x179ac.  Definition src0_E_free : Z := 0x179b0.
Definition src0_A_libc_calloc : Z := 0x179b0.  Definition src0_E_libc_calloc : Z := 0x17ae8.
Definition src0_A_libc_malloc : Z := 0x17ae8.  Definition src0_E_libc_malloc : Z := 0x17aec.
Definition src0_A_malloc : Z := 0x17aec.  Definition src0_E_malloc : Z := 0x17af0.
Definition src0_A_libc_free : Z := 0x17af0.  Definition src0_E_libc_free : Z := 0x17cbc.
Definition src0_A_get_meta : Z := 0x17cbc.  Definition src0_E_get_meta : Z := 0x17dcc.
Definition src0_A_nontrivial_free : Z := 0x17dcc.  Definition src0_E_nontrivial_free : Z := 0x181a4.
Definition src0_A_alloc_meta : Z := 0x181a4.  Definition src0_E_alloc_meta : Z := 0x1847c.
Definition src0_A_libc_malloc_impl : Z := 0x1847c.  Definition src0_E_libc_malloc_impl : Z := 0x187ec.
Definition src0_A_alloc_slot : Z := 0x187ec.  Definition src0_E_alloc_slot : Z := 0x19090.
Definition src0_A_enframe : Z := 0x19090.  Definition src0_E_enframe : Z := 0x191e0.
Definition src0_A_malloc_allzerop : Z := 0x191e0.  Definition src0_E_malloc_allzerop : Z := 0x19358.
Definition src0_A_vm_wait : Z := 0x19358.  Definition src0_E_vm_wait : Z := 0x1935c.
Definition src0_A_mmap : Z := 0x1935c.  Definition src0_E_mmap : Z := 0x19448.
Definition src0_A_mprotect : Z := 0x19448.  Definition src0_E_mprotect : Z := 0x19490.
Definition src0_A_munmap : Z := 0x19490.  Definition src0_E_munmap : Z := 0x194d8.
Definition src0_A_fflush : Z := 0x195ac.  Definition src0_E_fflush : Z := 0x1971c.
Definition src0_A_lockfile : Z := 0x1971c.  Definition src0_E_lockfile : Z := 0x19818.
Definition src0_A_unlockfile : Z := 0x19818.  Definition src0_E_unlockfile : Z := 0x19878.
Definition src0_A_stdio_write : Z := 0x19d90.  Definition src0_E_stdio_write : Z := 0x19f20.
Definition src0_A_stdio_seek : Z := 0x19f20.  Definition src0_E_stdio_seek : Z := 0x19f28.
Definition src0_A_aio_close : Z := 0x19d60.  Definition src0_E_aio_close : Z := 0x19d64.
Definition src0_A_stdio_close : Z := 0x19d64.  Definition src0_E_stdio_close : Z := 0x19d90.
Definition src0_A_fprintf : Z := 0x19878.  Definition src0_E_fprintf : Z := 0x198dc.
Definition src0_A_fwritex : Z := 0x198dc.  Definition src0_E_fwritex : Z := 0x19a14.
Definition src0_A_fwrite : Z := 0x19a14.  Definition src0_E_fwrite : Z := 0x19acc.
Definition src0_A_towrite : Z := 0x19acc.  Definition src0_E_towrite : Z := 0x19b20.
Definition src0_A_stdio_exit : Z := 0x19b20.  Definition src0_E_stdio_exit : Z := 0x19cc4.
Definition src0_A_ofl_lock : Z := 0x19cc4.  Definition src0_E_ofl_lock : Z := 0x19cf4.
Definition src0_A_ofl_unlock : Z := 0x19cf4.  Definition src0_E_ofl_unlock : Z := 0x19d00.
Definition src0_A_stdout_write : Z := 0x19f28.  Definition src0_E_stdout_write : Z := 0x19fc8.
Definition src0_A_vfprintf : Z := 0x19fc8.  Definition src0_E_vfprintf : Z := 0x1a178.
Definition src0_A_printf_core : Z := 0x1a178.  Definition src0_E_printf_core : Z := 0x1afa8.
Definition src0_A_pop_arg : Z := 0x1afa8.  Definition src0_E_pop_arg : Z := 0x1b0dc.
Definition src0_A_pad : Z := 0x1b0dc.  Definition src0_E_pad : Z := 0x1b1b0.
Definition src0_A_fmt_fp : Z := 0x1b1b0.  Definition src0_E_fmt_fp : Z := 0x1c878.
Definition src0_A_strerror : Z := 0x1c878.  Definition src0_E_strerror : Z := 0x1c8b4.
Definition src0_A_lctrans_impl : Z := 0x1c8b4.  Definition src0_E_lctrans_impl : Z := 0x1c8b8.
Definition src0_A_lctrans : Z := 0x1c8b8.  Definition src0_E_lctrans : Z := 0x1c8bc.
Definition src0_A_wctomb : Z := 0x1c8bc.  Definition src0_E_wctomb : Z := 0x1c8e0.
Definition src0_A_wcrtomb : Z := 0x1c8e0.  Definition src0_E_wcrtomb : Z := 0x1ca0c.
Definition src0_A_extenddftf2 : Z := 0x1ca0c.  Definition src0_E_extenddftf2 : Z := 0x1cb9c.
Definition src0_A_signbitl : Z := 0x1cb9c.  Definition src0_E_signbitl : Z := 0x1cba4.
Definition src0_A_fpclassifyl : Z := 0x1cba4.  Definition src0_E_fpclassifyl : Z := 0x1cbe8.
Definition src0_A_frexpl : Z := 0x1cbe8.  Definition src0_E_frexpl : Z := 0x1ccc0.
Definition src0_A_letf2 : Z := 0x1ccc0.  Definition src0_E_letf2 : Z := 0x1cd88.
Definition src0_A_multf3 : Z := 0x1cd88.  Definition src0_E_multf3 : Z := 0x1d488.
Definition src0_A_floatsitf : Z := 0x1d488.  Definition src0_E_floatsitf : Z := 0x1d590.
Definition src0_A_scalbn : Z := 0x1d590.  Definition src0_E_scalbn : Z := 0x1d628.
Definition src0_A_subtf3 : Z := 0x1d628.  Definition src0_E_subtf3 : Z := 0x1d638.
Definition src0_A_addtf3 : Z := 0x1d638.  Definition src0_E_addtf3 : Z := 0x1de04.
Definition src0_A_fe_getround : Z := 0x1de04.  Definition src0_E_fe_getround : Z := 0x1de34.
Definition src0_A_fe_raise_inexact : Z := 0x1de34.  Definition src0_E_fe_raise_inexact : Z := 0x1de40.
Definition src0_A_fixunstfsi : Z := 0x1de40.  Definition src0_E_fixunstfsi : Z := 0x1ded4.
Definition src0_A_floatunsitf : Z := 0x1ded4.  Definition src0_E_floatunsitf : Z := 0x1dfc0.
Definition src0_A_fixtfsi : Z := 0x1dfc0.  Definition src0_E_fixtfsi : Z := 0x1e068.
Definition src0_A_divtf3 : Z := 0x1e068.  Definition src0_E_divtf3 : Z := 0x1e96c.
Definition src0_A_vprintf : Z := 0x1e96c.  Definition src0_E_vprintf : Z := 0x1e988.
Definition src0_A_bcmp : Z := 0x1eb30.  Definition src0_E_bcmp : Z := 0x1eb34.
Definition src0_A_memcmp : Z := 0x1ec00.  Definition src0_E_memcmp : Z := 0x1ec30.
Definition src0_A_memcpy : Z := 0x1ec30.  Definition src0_E_memcpy : Z := 0x1f034.
Definition src0_A_memset : Z := 0x1f034.  Definition src0_E_memset : Z := 0x1f12c.
Definition src0_A_strlen : Z := 0x1f12c.  Definition src0_E_strlen : Z := 0x1f1bc.
Definition src0_A_strnlen : Z := 0x1f1bc.  Definition src0_E_strnlen : Z := 0x1f200.
Definition src0_A_memchr : Z := 0x1eb34.  Definition src0_E_memchr : Z := 0x1ec00.
Definition src0_A_lock : Z := 0x1f200.  Definition src0_E_lock : Z := 0x1f488.
Definition src0_A_unlock : Z := 0x1f488.  Definition src0_E_unlock : Z := 0x1f4fc.
Definition src0_A_syscall_cp_c : Z := 0x1f4fc.  Definition src0_E_syscall_cp_c : Z := 0x1f520.
Definition src0_A_syscall_cp : Z := 0x1f520.  Definition src0_E_syscall_cp : Z := 0x1f524.
Definition src0_A_set_thread_area : Z := 0x1f524.  Definition src0_E_set_thread_area : Z := 0x1f530.
Definition src0_A_unistd_exit : Z := 0x1f530.  Definition src0_E_unistd_exit : Z := 0x1f53c.
Definition src0_A_close : Z := 0x1f53c.  Definition src0_E_close : Z := 0x1f590.
Definition src0_A_lseek : Z := 0x1f590.  Definition src0_E_lseek : Z := 0x1f59c.
Definition src0_A_read : Z := 0x1f59c.  Definition src0_E_read : Z := 0x1f5d0.
Definition src0_D_str_n0X0x : Z := 0x102a3.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10303.
Definition src0_D_str_d_n : Z := 0x10317.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10332.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10343.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10401.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1045f.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10474.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x104ac.
Definition src0_D_str_dev_null : Z := 0x104d7.
Definition src0_D_str_null : Z := 0x104e1.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10510.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10528.
Definition src0_D_debruijn32 : Z := 0x10600.
Definition src0_D_size_classes : Z := 0x10620.
Definition src0_D_small_cnt_tab : Z := 0x10680.
Definition src0_D_med_cnt_tab : Z := 0x1069b.
Definition src0_D_states : Z := 0x107f8.
Definition src0_D_xdigits : Z := 0x109c8.
Definition src0_D_errmsgstr : Z := 0x109d8.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11180.
Definition src0_D_fe_getround : Z := 0x11288.
Definition src0_D_EH_FRAME_LIST : Z := 0x11470.
Definition src0_D_init_array_start : Z := 0x205d0.
Definition src0_D_fini_array_start : Z := 0x205d8.
Definition src0_D_stderr : Z := 0x20610.
Definition src0_D_stdout : Z := 0x20618.
Definition src0_D_got_DYNAMIC : Z := 0x20628.
Definition src0_D_got_main : Z := 0x20630.
Definition src0_D_got_init : Z := 0x20638.
Definition src0_D_got_fini : Z := 0x20640.
Definition src0_D_got_register_frame_info : Z := 0x20648.
Definition src0_D_got_cxa_finalize : Z := 0x20650.
Definition src0_D_got_deregister_frame_info : Z := 0x20658.
Definition src0_D_got_stderr : Z := 0x20660.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x20668.
Definition src0_D_got_stdout : Z := 0x20670.
Definition src0_D_got_environ : Z := 0x20678.
Definition src0_D_got_progname_full : Z := 0x20680.
Definition src0_D_got_progname : Z := 0x20688.
Definition src0_D_got_init_array_end : Z := 0x20690.
Definition src0_D_got_init_array_start : Z := 0x20698.
Definition src0_D_got_stack_chk_guard : Z := 0x206a0.
Definition src0_D_got_fini_array_end : Z := 0x206a8.
Definition src0_D_got_fini_array_start : Z := 0x206b0.
Definition src0_D_dso_handle : Z := 0x216b8.
Definition src0_D_aef_arg0 : Z := 0x216c0.
Definition src0_D_aef_argc : Z := 0x216c8.
Definition src0_D_aef_argv : Z := 0x216d0.
Definition src0_D_stderr_FILE : Z := 0x216e0.
Definition src0_D_stderr_used : Z := 0x217c8.
Definition src0_D_stdout_FILE : Z := 0x217d0.
Definition src0_D_stdout_used : Z := 0x218b8.
Definition src0_D_default_stacksize : Z := 0x218c0.
Definition src0_D_do_init_initialized : Z := 0x218d0.
Definition src0_D_do_init_object : Z := 0x218d8.
Definition src0_D_do_fini_finalized : Z := 0x21918.
Definition src0_D_read_stage : Z := 0x21919.
Definition src0_D_target_run_initialized : Z := 0x31920.
Definition src0_D_aef_in_callback : Z := 0x31924.
Definition src0_D_aef_aligned_copy_empty : Z := 0x31930.
Definition src0_D_environ : Z := 0x31950.
Definition src0_D_thread_list_lock : Z := 0x51a28.
Definition src0_D_main_tls : Z := 0x51a30.
Definition src0_D_builtin_tls : Z := 0x31958.
Definition src0_D_finished_atexit : Z := 0x51a68.
Definition src0_D_atexit_lock : Z := 0x51a6c.
Definition src0_D_atexit_slot : Z := 0x51a70.
Definition src0_D_atexit_head : Z := 0x51a78.
Definition src0_D_atexit_builtin : Z := 0x51a80.
Definition src0_D_exit_exit_lock : Z := 0x51c88.
Definition src0_D_stack_chk_guard : Z := 0x51c90.
Definition src0_D_sysinfo : Z := 0x51c98.
Definition src0_D_progname : Z := 0x51ca0.
Definition src0_D_progname_full : Z := 0x51ca8.
Definition src0_D_libc : Z := 0x51cb0.
Definition src0_D_hwcap : Z := 0x51d18.
Definition src0_D_malloc_lock : Z := 0x51d20.
Definition src0_D_malloc_context : Z := 0x51d28.
Definition src0_D_malloc_replaced : Z := 0x520c8.
Definition src0_D_stdin_used : Z := 0x520d0.
Definition src0_D_ofl_lock : Z := 0x520d8.
Definition src0_D_ofl_head : Z := 0x520e0.
Definition src0_D_stderr_buf : Z := 0x520e8.
Definition src0_D_stdout_buf : Z := 0x520f0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
