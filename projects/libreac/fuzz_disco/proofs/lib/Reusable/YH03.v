(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10: cells re-derived from fuzz_disco's own plain image (pin 04988e3ab313 and its unstripped twin): A/E rows by the address-table re-derivation tool from the twin's symbols, src0_D_stderr by hand to the stderr object, D_str / const / jt / got / NOSYM cells by their bytes and the code that reads them; a cell with no reader outside this file is deleted when this image has no counterpart for it or its value is wrong (table: the unit's yh03-fix table, plain). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12c90.  Definition src0_text_hi : Z := 0x1ee14.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11294.
Definition src0_eh_frame_lo : Z := 0x11460.  Definition src0_eh_frame_hi : Z := 0x11c90.
Definition src0_init_array_lo : Z := 0x1fe18.  Definition src0_init_array_hi : Z := 0x1fe20.
Definition src0_fini_array_lo : Z := 0x1fe20.  Definition src0_fini_array_hi : Z := 0x1fe28.
Definition src0_data_rel_ro_lo : Z := 0x1fe28.  Definition src0_data_rel_ro_hi : Z := 0x1fe68.
Definition src0_got_lo : Z := 0x1fe68.  Definition src0_got_hi : Z := 0x1ff00.
Definition src0_data_lo : Z := 0x20f00.  Definition src0_data_hi : Z := 0x2110c.
Definition src0_bss_lo : Z := 0x21110.  Definition src0_bss_hi : Z := 0x51d38.
Definition src0_A_start : Z := 0x12c90.  Definition src0_E_start : Z := 0x12cd8.
Definition src0_A_do_init : Z := 0x12cd8.  Definition src0_E_do_init : Z := 0x12d4c.
Definition src0_A_do_fini : Z := 0x12d4c.  Definition src0_E_do_fini : Z := 0x12ddc.
Definition src0_A_main : Z := 0x12ddc.  Definition src0_E_main : Z := 0x130a0.
Definition src0_A_target_alloc_init : Z := 0x130a0.  Definition src0_E_target_alloc_init : Z := 0x130a4.
Definition src0_A_target_alloc_count : Z := 0x130a4.  Definition src0_E_target_alloc_count : Z := 0x130ac.
Definition src0_A_target_run : Z := 0x130ac.  Definition src0_E_target_run : Z := 0x13204.
Definition src0_A_aef_exit_guard : Z := 0x13204.  Definition src0_E_aef_exit_guard : Z := 0x13234.
Definition src0_A_emit_printf : Z := 0x13234.  Definition src0_E_emit_printf : Z := 0x1327c.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x1327c.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x144e0.
Definition src0_A_init : Z := 0x16784.  Definition src0_E_init : Z := 0x16788.
Definition src0_A_init_libc : Z := 0x16788.  Definition src0_E_init_libc : Z := 0x169b4.
Definition src0_A_libc_start_init : Z := 0x169b4.  Definition src0_E_libc_start_init : Z := 0x16a00.
Definition src0_A_libc_start_main : Z := 0x16a00.  Definition src0_E_libc_start_main : Z := 0x16a60.
Definition src0_A_libc_start_main_stage2 : Z := 0x16a60.  Definition src0_E_libc_start_main_stage2 : Z := 0x16aa8.
Definition src0_A_init_tls : Z := 0x16aa8.  Definition src0_E_init_tls : Z := 0x16d58.
Definition src0_A_funcs_on_exit : Z := 0x16e08.  Definition src0_E_funcs_on_exit : Z := 0x16ed0.
Definition src0_A_cxa_finalize : Z := 0x16ed0.  Definition src0_E_cxa_finalize : Z := 0x16ed4.
Definition src0_A_atexit : Z := 0x16ed4.  Definition src0_E_atexit : Z := 0x16f98.
Definition src0_A_atexit_call : Z := 0x16f98.  Definition src0_E_atexit_call : Z := 0x16f9c.
Definition src0_A_fini : Z := 0x16f9c.  Definition src0_E_fini : Z := 0x16fa0.
Definition src0_A_libc_exit_fini : Z := 0x16fa0.  Definition src0_E_libc_exit_fini : Z := 0x16fec.
Definition src0_A_exit : Z := 0x16fec.  Definition src0_E_exit : Z := 0x17060.
Definition src0_A_Exit : Z := 0x16dec.  Definition src0_E_Exit : Z := 0x16e08.
Definition src0_A_open : Z := 0x170c8.  Definition src0_E_open : Z := 0x171ac.
Definition src0_A_init_ssp : Z := 0x17060.  Definition src0_E_init_ssp : Z := 0x170c0.
Definition src0_A_stack_chk_fail : Z := 0x170c0.  Definition src0_E_stack_chk_fail : Z := 0x170c8.
Definition src0_A_syscall_ret : Z := 0x171ac.  Definition src0_E_syscall_ret : Z := 0x171e4.
Definition src0_A_errno_location : Z := 0x171e4.  Definition src0_E_errno_location : Z := 0x171f0.
Definition src0_A_free : Z := 0x171f0.  Definition src0_E_free : Z := 0x171f4.
Definition src0_A_libc_calloc : Z := 0x171f4.  Definition src0_E_libc_calloc : Z := 0x1732c.
Definition src0_A_libc_malloc : Z := 0x1732c.  Definition src0_E_libc_malloc : Z := 0x17330.
Definition src0_A_malloc : Z := 0x17330.  Definition src0_E_malloc : Z := 0x17334.
Definition src0_A_libc_free : Z := 0x17334.  Definition src0_E_libc_free : Z := 0x17500.
Definition src0_A_get_meta : Z := 0x17500.  Definition src0_E_get_meta : Z := 0x17610.
Definition src0_A_nontrivial_free : Z := 0x17610.  Definition src0_E_nontrivial_free : Z := 0x179e8.
Definition src0_A_alloc_meta : Z := 0x179e8.  Definition src0_E_alloc_meta : Z := 0x17cc0.
Definition src0_A_libc_malloc_impl : Z := 0x17cc0.  Definition src0_E_libc_malloc_impl : Z := 0x18030.
Definition src0_A_alloc_slot : Z := 0x18030.  Definition src0_E_alloc_slot : Z := 0x188d4.
Definition src0_A_enframe : Z := 0x188d4.  Definition src0_E_enframe : Z := 0x18a24.
Definition src0_A_malloc_allzerop : Z := 0x18a24.  Definition src0_E_malloc_allzerop : Z := 0x18b9c.
Definition src0_A_vm_wait : Z := 0x18b9c.  Definition src0_E_vm_wait : Z := 0x18ba0.
Definition src0_A_mmap : Z := 0x18ba0.  Definition src0_E_mmap : Z := 0x18c8c.
Definition src0_A_mprotect : Z := 0x18c8c.  Definition src0_E_mprotect : Z := 0x18cd4.
Definition src0_A_munmap : Z := 0x18cd4.  Definition src0_E_munmap : Z := 0x18d1c.
Definition src0_A_fflush : Z := 0x18df0.  Definition src0_E_fflush : Z := 0x18f60.
Definition src0_A_lockfile : Z := 0x18f60.  Definition src0_E_lockfile : Z := 0x1905c.
Definition src0_A_unlockfile : Z := 0x1905c.  Definition src0_E_unlockfile : Z := 0x190bc.
Definition src0_A_stdio_write : Z := 0x195d4.  Definition src0_E_stdio_write : Z := 0x19764.
Definition src0_A_stdio_seek : Z := 0x19764.  Definition src0_E_stdio_seek : Z := 0x1976c.
Definition src0_A_aio_close : Z := 0x195a4.  Definition src0_E_aio_close : Z := 0x195a8.
Definition src0_A_stdio_close : Z := 0x195a8.  Definition src0_E_stdio_close : Z := 0x195d4.
Definition src0_A_fprintf : Z := 0x190bc.  Definition src0_E_fprintf : Z := 0x19120.
Definition src0_A_fwritex : Z := 0x19120.  Definition src0_E_fwritex : Z := 0x19258.
Definition src0_A_fwrite : Z := 0x19258.  Definition src0_E_fwrite : Z := 0x19310.
Definition src0_A_towrite : Z := 0x19310.  Definition src0_E_towrite : Z := 0x19364.
Definition src0_A_stdio_exit : Z := 0x19364.  Definition src0_E_stdio_exit : Z := 0x19508.
Definition src0_A_ofl_lock : Z := 0x19508.  Definition src0_E_ofl_lock : Z := 0x19538.
Definition src0_A_ofl_unlock : Z := 0x19538.  Definition src0_E_ofl_unlock : Z := 0x19544.
Definition src0_A_stdout_write : Z := 0x1976c.  Definition src0_E_stdout_write : Z := 0x1980c.
Definition src0_A_vfprintf : Z := 0x1980c.  Definition src0_E_vfprintf : Z := 0x199bc.
Definition src0_A_printf_core : Z := 0x199bc.  Definition src0_E_printf_core : Z := 0x1a7ec.
Definition src0_A_pop_arg : Z := 0x1a7ec.  Definition src0_E_pop_arg : Z := 0x1a920.
Definition src0_A_pad : Z := 0x1a920.  Definition src0_E_pad : Z := 0x1a9f4.
Definition src0_A_fmt_fp : Z := 0x1a9f4.  Definition src0_E_fmt_fp : Z := 0x1c0bc.
Definition src0_A_strerror : Z := 0x1c0bc.  Definition src0_E_strerror : Z := 0x1c0f8.
Definition src0_A_lctrans_impl : Z := 0x1c0f8.  Definition src0_E_lctrans_impl : Z := 0x1c0fc.
Definition src0_A_lctrans : Z := 0x1c0fc.  Definition src0_E_lctrans : Z := 0x1c100.
Definition src0_A_wctomb : Z := 0x1c100.  Definition src0_E_wctomb : Z := 0x1c124.
Definition src0_A_wcrtomb : Z := 0x1c124.  Definition src0_E_wcrtomb : Z := 0x1c250.
Definition src0_A_extenddftf2 : Z := 0x1c250.  Definition src0_E_extenddftf2 : Z := 0x1c3e0.
Definition src0_A_signbitl : Z := 0x1c3e0.  Definition src0_E_signbitl : Z := 0x1c3e8.
Definition src0_A_fpclassifyl : Z := 0x1c3e8.  Definition src0_E_fpclassifyl : Z := 0x1c42c.
Definition src0_A_frexpl : Z := 0x1c42c.  Definition src0_E_frexpl : Z := 0x1c504.
Definition src0_A_letf2 : Z := 0x1c504.  Definition src0_E_letf2 : Z := 0x1c5cc.
Definition src0_A_multf3 : Z := 0x1c5cc.  Definition src0_E_multf3 : Z := 0x1cccc.
Definition src0_A_floatsitf : Z := 0x1cccc.  Definition src0_E_floatsitf : Z := 0x1cdd4.
Definition src0_A_scalbn : Z := 0x1cdd4.  Definition src0_E_scalbn : Z := 0x1ce6c.
Definition src0_A_subtf3 : Z := 0x1ce6c.  Definition src0_E_subtf3 : Z := 0x1ce7c.
Definition src0_A_addtf3 : Z := 0x1ce7c.  Definition src0_E_addtf3 : Z := 0x1d648.
Definition src0_A_fe_getround : Z := 0x1d648.  Definition src0_E_fe_getround : Z := 0x1d678.
Definition src0_A_fe_raise_inexact : Z := 0x1d678.  Definition src0_E_fe_raise_inexact : Z := 0x1d684.
Definition src0_A_fixunstfsi : Z := 0x1d684.  Definition src0_E_fixunstfsi : Z := 0x1d718.
Definition src0_A_floatunsitf : Z := 0x1d718.  Definition src0_E_floatunsitf : Z := 0x1d804.
Definition src0_A_fixtfsi : Z := 0x1d804.  Definition src0_E_fixtfsi : Z := 0x1d8ac.
Definition src0_A_divtf3 : Z := 0x1d8ac.  Definition src0_E_divtf3 : Z := 0x1e1b0.
Definition src0_A_vprintf : Z := 0x1e1b0.  Definition src0_E_vprintf : Z := 0x1e1cc.
Definition src0_A_bcmp : Z := 0x1e374.  Definition src0_E_bcmp : Z := 0x1e378.
Definition src0_A_memcmp : Z := 0x1e444.  Definition src0_E_memcmp : Z := 0x1e474.
Definition src0_A_memcpy : Z := 0x1e474.  Definition src0_E_memcpy : Z := 0x1e878.
Definition src0_A_memset : Z := 0x1e878.  Definition src0_E_memset : Z := 0x1e970.
Definition src0_A_strlen : Z := 0x1e970.  Definition src0_E_strlen : Z := 0x1ea00.
Definition src0_A_strnlen : Z := 0x1ea00.  Definition src0_E_strnlen : Z := 0x1ea44.
Definition src0_A_memchr : Z := 0x1e378.  Definition src0_E_memchr : Z := 0x1e444.
Definition src0_A_lock : Z := 0x1ea44.  Definition src0_E_lock : Z := 0x1eccc.
Definition src0_A_unlock : Z := 0x1eccc.  Definition src0_E_unlock : Z := 0x1ed40.
Definition src0_A_syscall_cp_c : Z := 0x1ed40.  Definition src0_E_syscall_cp_c : Z := 0x1ed64.
Definition src0_A_syscall_cp : Z := 0x1ed64.  Definition src0_E_syscall_cp : Z := 0x1ed68.
Definition src0_A_set_thread_area : Z := 0x1ed68.  Definition src0_E_set_thread_area : Z := 0x1ed74.
Definition src0_A_unistd_exit : Z := 0x1ed74.  Definition src0_E_unistd_exit : Z := 0x1ed80.
Definition src0_A_close : Z := 0x1ed80.  Definition src0_E_close : Z := 0x1edd4.
Definition src0_A_lseek : Z := 0x1edd4.  Definition src0_E_lseek : Z := 0x1ede0.
Definition src0_A_read : Z := 0x1ede0.  Definition src0_E_read : Z := 0x1ee14.
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
Definition src0_D_EH_FRAME_LIST : Z := 0x11460.
Definition src0_D_init_array_start : Z := 0x1fe18.
Definition src0_D_fini_array_start : Z := 0x1fe20.
Definition src0_D_stderr : Z := 0x1fe58.
Definition src0_D_stdout : Z := 0x1fe60.
Definition src0_D_got_DYNAMIC : Z := 0x1fe70.
Definition src0_D_got_main : Z := 0x1fe78.
Definition src0_D_got_init : Z := 0x1fe80.
Definition src0_D_got_fini : Z := 0x1fe88.
Definition src0_D_got_register_frame_info : Z := 0x1fe90.
Definition src0_D_got_cxa_finalize : Z := 0x1fe98.
Definition src0_D_got_deregister_frame_info : Z := 0x1fea0.
Definition src0_D_got_stderr : Z := 0x1fea8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1feb0.
Definition src0_D_got_stdout : Z := 0x1feb8.
Definition src0_D_got_environ : Z := 0x1fec0.
Definition src0_D_got_progname_full : Z := 0x1fec8.
Definition src0_D_got_progname : Z := 0x1fed0.
Definition src0_D_got_init_array_end : Z := 0x1fed8.
Definition src0_D_got_init_array_start : Z := 0x1fee0.
Definition src0_D_got_stack_chk_guard : Z := 0x1fee8.
Definition src0_D_got_fini_array_end : Z := 0x1fef0.
Definition src0_D_got_fini_array_start : Z := 0x1fef8.
Definition src0_D_dso_handle : Z := 0x20f00.
Definition src0_D_aef_arg0 : Z := 0x20f08.
Definition src0_D_aef_argc : Z := 0x20f10.
Definition src0_D_aef_argv : Z := 0x20f18.
Definition src0_D_stderr_FILE : Z := 0x20f28.
Definition src0_D_stderr_used : Z := 0x21010.
Definition src0_D_stdout_FILE : Z := 0x21018.
Definition src0_D_stdout_used : Z := 0x21100.
Definition src0_D_default_stacksize : Z := 0x21108.
Definition src0_D_do_init_initialized : Z := 0x21110.
Definition src0_D_do_init_object : Z := 0x21118.
Definition src0_D_do_fini_finalized : Z := 0x21158.
Definition src0_D_read_stage : Z := 0x21159.
Definition src0_D_target_run_initialized : Z := 0x31160.
Definition src0_D_aef_in_callback : Z := 0x31164.
Definition src0_D_aef_aligned_copy_empty : Z := 0x31170.
Definition src0_D_environ : Z := 0x31190.
Definition src0_D_thread_list_lock : Z := 0x51268.
Definition src0_D_main_tls : Z := 0x51270.
Definition src0_D_builtin_tls : Z := 0x31198.
Definition src0_D_finished_atexit : Z := 0x512a8.
Definition src0_D_atexit_lock : Z := 0x512ac.
Definition src0_D_atexit_slot : Z := 0x512b0.
Definition src0_D_atexit_head : Z := 0x512b8.
Definition src0_D_atexit_builtin : Z := 0x512c0.
Definition src0_D_exit_exit_lock : Z := 0x514c8.
Definition src0_D_stack_chk_guard : Z := 0x514d0.
Definition src0_D_sysinfo : Z := 0x514d8.
Definition src0_D_progname : Z := 0x514e0.
Definition src0_D_progname_full : Z := 0x514e8.
Definition src0_D_libc : Z := 0x514f0.
Definition src0_D_hwcap : Z := 0x51558.
Definition src0_D_malloc_lock : Z := 0x51560.
Definition src0_D_malloc_context : Z := 0x51568.
Definition src0_D_malloc_replaced : Z := 0x51908.
Definition src0_D_stdin_used : Z := 0x51910.
Definition src0_D_ofl_lock : Z := 0x51918.
Definition src0_D_ofl_head : Z := 0x51920.
Definition src0_D_stderr_buf : Z := 0x51928.
Definition src0_D_stdout_buf : Z := 0x51930.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
