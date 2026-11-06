(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x1303c.  Definition src0_text_hi : Z := 0x22440.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1124c.
Definition src0_eh_frame_lo : Z := 0x11498.  Definition src0_eh_frame_hi : Z := 0x1203c.
Definition src0_init_array_lo : Z := 0x23440.  Definition src0_init_array_hi : Z := 0x23448.
Definition src0_fini_array_lo : Z := 0x23448.  Definition src0_fini_array_hi : Z := 0x23450.
Definition src0_data_rel_ro_lo : Z := 0x23450.  Definition src0_data_rel_ro_hi : Z := 0x23460.
Definition src0_got_lo : Z := 0x23460.  Definition src0_got_hi : Z := 0x234f8.
Definition src0_data_lo : Z := 0x244f8.  Definition src0_data_hi : Z := 0x24714.
Definition src0_bss_lo : Z := 0x24720.  Definition src0_bss_hi : Z := 0x55370.
Definition src0_A_do_init : Z := 0x13084.  Definition src0_E_do_init : Z := 0x130f8.
Definition src0_A_do_fini : Z := 0x130f8.  Definition src0_E_do_fini : Z := 0x13188.
Definition src0_A_main : Z := 0x13188.  Definition src0_E_main : Z := 0x1344c.
Definition src0_A_target_alloc_init : Z := 0x1344c.  Definition src0_E_target_alloc_init : Z := 0x13450.
Definition src0_A_target_alloc_count : Z := 0x13450.  Definition src0_E_target_alloc_count : Z := 0x13458.
Definition src0_A_target_run : Z := 0x13458.  Definition src0_E_target_run : Z := 0x135b0.
Definition src0_A_emit_printf : Z := 0x135e0.  Definition src0_E_emit_printf : Z := 0x13628.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x13628.
Definition src0_A_init : Z := 0x16d2c.  Definition src0_E_init : Z := 0x16d30.
Definition src0_A_init_libc : Z := 0x16d30.  Definition src0_E_init_libc : Z := 0x16f5c.
Definition src0_A_libc_start_init : Z := 0x16f5c.  Definition src0_E_libc_start_init : Z := 0x16fa8.
Definition src0_A_libc_start_main : Z := 0x16fa8.  Definition src0_E_libc_start_main : Z := 0x17008.
Definition src0_A_libc_start_main_stage2 : Z := 0x17008.  Definition src0_E_libc_start_main_stage2 : Z := 0x17050.
Definition src0_A_init_tls : Z := 0x17050.  Definition src0_E_init_tls : Z := 0x17300.
Definition src0_A_funcs_on_exit : Z := 0x173b0.  Definition src0_E_funcs_on_exit : Z := 0x17478.
Definition src0_A_cxa_finalize : Z := 0x17478.  Definition src0_E_cxa_finalize : Z := 0x1747c.
Definition src0_A_atexit : Z := 0x1747c.  Definition src0_E_atexit : Z := 0x17540.
Definition src0_A_fini : Z := 0x17544.  Definition src0_E_fini : Z := 0x17548.
Definition src0_A_libc_exit_fini : Z := 0x17548.  Definition src0_E_libc_exit_fini : Z := 0x17594.
Definition src0_A_exit : Z := 0x17594.  Definition src0_E_exit : Z := 0x17608.
Definition src0_A_Exit : Z := 0x17394.  Definition src0_E_Exit : Z := 0x173b0.
Definition src0_A_open : Z := 0x17608.  Definition src0_E_open : Z := 0x176ec.
Definition src0_A_init_ssp : Z := 0x176ec.  Definition src0_E_init_ssp : Z := 0x1774c.
Definition src0_A_stack_chk_fail : Z := 0x1774c.  Definition src0_E_stack_chk_fail : Z := 0x17754.
Definition src0_A_syscall_ret : Z := 0x17754.  Definition src0_E_syscall_ret : Z := 0x1778c.
Definition src0_A_errno_location : Z := 0x1778c.  Definition src0_E_errno_location : Z := 0x17798.
Definition src0_A_free : Z := 0x17798.  Definition src0_E_free : Z := 0x1779c.
Definition src0_A_libc_calloc : Z := 0x1779c.  Definition src0_E_libc_calloc : Z := 0x178d4.
Definition src0_A_libc_malloc : Z := 0x178d4.  Definition src0_E_libc_malloc : Z := 0x178d8.
Definition src0_A_malloc : Z := 0x178d8.  Definition src0_E_malloc : Z := 0x178dc.
Definition src0_A_libc_free : Z := 0x178dc.  Definition src0_E_libc_free : Z := 0x17aa8.
Definition src0_A_get_meta : Z := 0x17aa8.  Definition src0_E_get_meta : Z := 0x17bb8.
Definition src0_A_nontrivial_free : Z := 0x17bb8.  Definition src0_E_nontrivial_free : Z := 0x17f90.
Definition src0_A_alloc_meta : Z := 0x17f90.  Definition src0_E_alloc_meta : Z := 0x18268.
Definition src0_A_libc_malloc_impl : Z := 0x18268.  Definition src0_E_libc_malloc_impl : Z := 0x185d8.
Definition src0_A_alloc_slot : Z := 0x185d8.  Definition src0_E_alloc_slot : Z := 0x18e7c.
Definition src0_A_enframe : Z := 0x18e7c.  Definition src0_E_enframe : Z := 0x18fcc.
Definition src0_A_malloc_allzerop : Z := 0x18fcc.  Definition src0_E_malloc_allzerop : Z := 0x19144.
Definition src0_A_vm_wait : Z := 0x19588.  Definition src0_E_vm_wait : Z := 0x1958c.
Definition src0_A_mmap : Z := 0x1958c.  Definition src0_E_mmap : Z := 0x19678.
Definition src0_A_mprotect : Z := 0x19678.  Definition src0_E_mprotect : Z := 0x196c0.
Definition src0_A_munmap : Z := 0x19794.  Definition src0_E_munmap : Z := 0x197dc.
Definition src0_A_fflush : Z := 0x19a0c.  Definition src0_E_fflush : Z := 0x19b7c.
Definition src0_A_lockfile : Z := 0x198b0.  Definition src0_E_lockfile : Z := 0x199ac.
Definition src0_A_unlockfile : Z := 0x199ac.  Definition src0_E_unlockfile : Z := 0x19a0c.
Definition src0_A_aio_close : Z := 0x19d14.  Definition src0_E_aio_close : Z := 0x19d18.
Definition src0_A_fprintf : Z := 0x19d44.  Definition src0_E_fprintf : Z := 0x19da8.
Definition src0_A_fwritex : Z := 0x19fe0.  Definition src0_E_fwritex : Z := 0x1a118.
Definition src0_A_fwrite : Z := 0x1a118.  Definition src0_E_fwrite : Z := 0x1a1d0.
Definition src0_A_towrite : Z := 0x1a1d0.  Definition src0_E_towrite : Z := 0x1a224.
Definition src0_A_stdio_exit : Z := 0x19e3c.  Definition src0_E_stdio_exit : Z := 0x19fe0.
Definition src0_A_ofl_lock : Z := 0x1a224.  Definition src0_E_ofl_lock : Z := 0x1a254.
Definition src0_A_ofl_unlock : Z := 0x1a254.  Definition src0_E_ofl_unlock : Z := 0x1a260.
Definition src0_A_stdout_write : Z := 0x1a2c0.  Definition src0_E_stdout_write : Z := 0x1a360.
Definition src0_A_vfprintf : Z := 0x1a360.  Definition src0_E_vfprintf : Z := 0x1a510.
Definition src0_A_printf_core : Z := 0x1a510.  Definition src0_E_printf_core : Z := 0x1b340.
Definition src0_A_pop_arg : Z := 0x1b340.  Definition src0_E_pop_arg : Z := 0x1b474.
Definition src0_A_pad : Z := 0x1b474.  Definition src0_E_pad : Z := 0x1b548.
Definition src0_A_fmt_fp : Z := 0x1b548.  Definition src0_E_fmt_fp : Z := 0x1cc10.
Definition src0_A_strerror : Z := 0x1cc10.  Definition src0_E_strerror : Z := 0x1cc4c.
Definition src0_A_lctrans_impl : Z := 0x1cc4c.  Definition src0_E_lctrans_impl : Z := 0x1cc50.
Definition src0_A_lctrans : Z := 0x1cc50.  Definition src0_E_lctrans : Z := 0x1cc54.
Definition src0_A_wctomb : Z := 0x1cc54.  Definition src0_E_wctomb : Z := 0x1cc78.
Definition src0_A_wcrtomb : Z := 0x1cc78.  Definition src0_E_wcrtomb : Z := 0x1cda4.
Definition src0_A_extenddftf2 : Z := 0x1cda4.  Definition src0_E_extenddftf2 : Z := 0x1cf34.
Definition src0_A_signbitl : Z := 0x1cf34.  Definition src0_E_signbitl : Z := 0x1cf3c.
Definition src0_A_fpclassifyl : Z := 0x1cf3c.  Definition src0_E_fpclassifyl : Z := 0x1cf80.
Definition src0_A_frexpl : Z := 0x1cf80.  Definition src0_E_frexpl : Z := 0x1d058.
Definition src0_A_letf2 : Z := 0x1d058.  Definition src0_E_letf2 : Z := 0x1d120.
Definition src0_A_multf3 : Z := 0x1d1dc.  Definition src0_E_multf3 : Z := 0x1d8dc.
Definition src0_A_floatsitf : Z := 0x1d8dc.  Definition src0_E_floatsitf : Z := 0x1d9e4.
Definition src0_A_scalbn : Z := 0x1d9e4.  Definition src0_E_scalbn : Z := 0x1da7c.
Definition src0_A_subtf3 : Z := 0x1da7c.  Definition src0_E_subtf3 : Z := 0x1da8c.
Definition src0_A_addtf3 : Z := 0x1da8c.  Definition src0_E_addtf3 : Z := 0x1e258.
Definition src0_A_fe_getround : Z := 0x1e258.  Definition src0_E_fe_getround : Z := 0x1e288.
Definition src0_A_fe_raise_inexact : Z := 0x1e288.  Definition src0_E_fe_raise_inexact : Z := 0x1e294.
Definition src0_A_fixunstfsi : Z := 0x1e294.  Definition src0_E_fixunstfsi : Z := 0x1e328.
Definition src0_A_floatunsitf : Z := 0x1e328.  Definition src0_E_floatunsitf : Z := 0x1e414.
Definition src0_A_fixtfsi : Z := 0x1e414.  Definition src0_E_fixtfsi : Z := 0x1e4bc.
Definition src0_A_divtf3 : Z := 0x1e4bc.  Definition src0_E_divtf3 : Z := 0x1edc0.
Definition src0_A_vprintf : Z := 0x1edc0.  Definition src0_E_vprintf : Z := 0x1eddc.
Definition src0_A_bcmp : Z := 0x21968.  Definition src0_E_bcmp : Z := 0x2196c.
Definition src0_A_memcmp : Z := 0x21a38.  Definition src0_E_memcmp : Z := 0x21a68.
Definition src0_A_memcpy : Z := 0x21a68.  Definition src0_E_memcpy : Z := 0x21e6c.
Definition src0_A_memset : Z := 0x21e6c.  Definition src0_E_memset : Z := 0x21f64.
Definition src0_A_strlen : Z := 0x21f9c.  Definition src0_E_strlen : Z := 0x2202c.
Definition src0_A_strnlen : Z := 0x2202c.  Definition src0_E_strnlen : Z := 0x22070.
Definition src0_A_memchr : Z := 0x2196c.  Definition src0_E_memchr : Z := 0x21a38.
Definition src0_A_lock : Z := 0x22070.  Definition src0_E_lock : Z := 0x222f8.
Definition src0_A_unlock : Z := 0x222f8.  Definition src0_E_unlock : Z := 0x2236c.
Definition src0_A_syscall_cp_c : Z := 0x2236c.  Definition src0_E_syscall_cp_c : Z := 0x22390.
Definition src0_A_syscall_cp : Z := 0x22390.  Definition src0_E_syscall_cp : Z := 0x22394.
Definition src0_A_close : Z := 0x223ac.  Definition src0_E_close : Z := 0x22400.
Definition src0_A_lseek : Z := 0x22400.  Definition src0_E_lseek : Z := 0x2240c.
Definition src0_A_read : Z := 0x2240c.  Definition src0_E_read : Z := 0x22440.
Definition src0_D_str_n0X0x : Z := 0x1029e.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102bd.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102d0.
Definition src0_D_str_d_n : Z := 0x102e4.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10302.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10313.
Definition src0_D_str_inf : Z := 0x10337.
Definition src0_D_str_INF : Z := 0x1035e.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10362.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x103a7.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x103bc.
Definition src0_D_str_NAN : Z := 0x103e8.
Definition src0_D_str_nan : Z := 0x103fd.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10404.
Definition src0_D_str_dev_null : Z := 0x10437.
Definition src0_D_str_null : Z := 0x10441.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10760.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10770.
Definition src0_D_debruijn32 : Z := 0x10550.
Definition src0_D_size_classes : Z := 0x10570.
Definition src0_D_small_cnt_tab : Z := 0x105d0.
Definition src0_D_med_cnt_tab : Z := 0x105eb.
Definition src0_D_jt_printf_core_1 : Z := 0x10600.
Definition src0_D_jt_printf_core_2 : Z := 0x106e0.
Definition src0_D_jt_pop_arg : Z := 0x10700.
Definition src0_D_states : Z := 0x107b0.
Definition src0_D_xdigits : Z := 0x10980.
Definition src0_D_errmsgstr : Z := 0x10990.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11138.
Definition src0_D_fe_getround : Z := 0x11240.
Definition src0_D_EH_FRAME_LIST : Z := 0x11498.
Definition src0_D_init_array_start : Z := 0x23440.
Definition src0_D_fini_array_start : Z := 0x23448.
Definition src0_D_stderr : Z := 0x23450.
Definition src0_D_stdout : Z := 0x23458.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x23460.
Definition src0_D_got_DYNAMIC : Z := 0x23468.
Definition src0_D_got_main : Z := 0x23470.
Definition src0_D_got_init : Z := 0x23478.
Definition src0_D_got_fini : Z := 0x23480.
Definition src0_D_got_register_frame_info : Z := 0x23488.
Definition src0_D_got_cxa_finalize : Z := 0x23490.
Definition src0_D_got_deregister_frame_info : Z := 0x23498.
Definition src0_D_got_stderr : Z := 0x234a0.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x234a8.
Definition src0_D_got_stdout : Z := 0x234b0.
Definition src0_D_got_environ : Z := 0x234b8.
Definition src0_D_got_progname_full : Z := 0x234c0.
Definition src0_D_got_progname : Z := 0x234c8.
Definition src0_D_got_init_array_end : Z := 0x234d0.
Definition src0_D_got_init_array_start : Z := 0x234d8.
Definition src0_D_got_stack_chk_guard : Z := 0x234e0.
Definition src0_D_got_fini_array_end : Z := 0x234e8.
Definition src0_D_got_fini_array_start : Z := 0x234f0.
Definition src0_D_dso_handle : Z := 0x244f8.
Definition src0_D_aef_argc : Z := 0x24508.
Definition src0_D_stderr_FILE : Z := 0x24530.
Definition src0_D_stderr_used : Z := 0x24618.
Definition src0_D_stdout_FILE : Z := 0x24620.
Definition src0_D_stdout_used : Z := 0x24708.
Definition src0_D_default_stacksize : Z := 0x24710.
Definition src0_D_do_init_initialized : Z := 0x24720.
Definition src0_D_do_init_object : Z := 0x24728.
Definition src0_D_do_fini_finalized : Z := 0x24768.
Definition src0_D_read_stage : Z := 0x24769.
Definition src0_D_target_run_initialized : Z := 0x34770.
Definition src0_D_aef_in_callback : Z := 0x34774.
Definition src0_D_aef_aligned_copy_empty : Z := 0x34780.
Definition src0_D_environ : Z := 0x347c8.
Definition src0_D_thread_list_lock : Z := 0x548a0.
Definition src0_D_main_tls : Z := 0x548a8.
Definition src0_D_builtin_tls : Z := 0x347d0.
Definition src0_D_finished_atexit : Z := 0x548e0.
Definition src0_D_atexit_lock : Z := 0x548e4.
Definition src0_D_atexit_slot : Z := 0x548e8.
Definition src0_D_atexit_head : Z := 0x548f0.
Definition src0_D_atexit_builtin : Z := 0x548f8.
Definition src0_D_exit_exit_lock : Z := 0x54b00.
Definition src0_D_stack_chk_guard : Z := 0x54b08.
Definition src0_D_sysinfo : Z := 0x54b10.
Definition src0_D_progname : Z := 0x54b18.
Definition src0_D_progname_full : Z := 0x54b20.
Definition src0_D_libc : Z := 0x54b28.
Definition src0_D_hwcap : Z := 0x54b90.
Definition src0_D_malloc_lock : Z := 0x54b98.
Definition src0_D_malloc_context : Z := 0x54ba0.
Definition src0_D_malloc_replaced : Z := 0x54f40.
Definition src0_D_stdin_used : Z := 0x54f48.
Definition src0_D_ofl_lock : Z := 0x54f50.
Definition src0_D_ofl_head : Z := 0x54f58.
Definition src0_D_stderr_buf : Z := 0x54f60.
Definition src0_D_stdout_buf : Z := 0x54f68.
Definition src0_A_realloc : Z := 0x19144.  Definition src0_E_realloc : Z := 0x19148.
Definition src0_A_mremap : Z := 0x196c0.  Definition src0_E_mremap : Z := 0x19794.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
