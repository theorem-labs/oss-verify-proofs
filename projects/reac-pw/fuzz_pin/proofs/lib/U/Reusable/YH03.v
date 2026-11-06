(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x126d0.  Definition src0_text_hi : Z := 0x1b838.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1122c.
Definition src0_eh_frame_lo : Z := 0x11310.  Definition src0_eh_frame_hi : Z := 0x116d0.
Definition src0_init_array_lo : Z := 0x1c838.  Definition src0_init_array_hi : Z := 0x1c840.
Definition src0_fini_array_lo : Z := 0x1c840.  Definition src0_fini_array_hi : Z := 0x1c848.
Definition src0_data_rel_ro_lo : Z := 0x1c848.  Definition src0_data_rel_ro_hi : Z := 0x1d510.
Definition src0_got_lo : Z := 0x1d510.  Definition src0_got_hi : Z := 0x1d5a8.
Definition src0_data_lo : Z := 0x1e5a8.  Definition src0_data_hi : Z := 0x1e7b4.
Definition src0_bss_lo : Z := 0x1e7c0.  Definition src0_bss_hi : Z := 0x4f3e8.
Definition src0_A_start : Z := 0x126d0.  Definition src0_E_start : Z := 0x12718.
Definition src0_A_do_init : Z := 0x12718.  Definition src0_E_do_init : Z := 0x1278c.
Definition src0_A_do_fini : Z := 0x1278c.  Definition src0_E_do_fini : Z := 0x1281c.
Definition src0_A_main : Z := 0x1281c.  Definition src0_E_main : Z := 0x12ae0.
Definition src0_A_target_alloc_init : Z := 0x12ae0.  Definition src0_E_target_alloc_init : Z := 0x12ae4.
Definition src0_A_target_alloc_count : Z := 0x12ae4.  Definition src0_E_target_alloc_count : Z := 0x12aec.
Definition src0_A_target_run : Z := 0x12aec.  Definition src0_E_target_run : Z := 0x12c44.
Definition src0_A_aef_exit_guard : Z := 0x12c44.  Definition src0_E_aef_exit_guard : Z := 0x12c74.
Definition src0_A_emit_printf : Z := 0x12c74.  Definition src0_E_emit_printf : Z := 0x12cbc.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12cbc.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x12eb8.
Definition src0_A_read_frameconfig : Z := 0x13380.  Definition src0_E_read_frameconfig : Z := 0x135e8.
Definition src0_A_cgif_newgif : Z := 0x135e8.  Definition src0_E_cgif_newgif : Z := 0x137a0.
Definition src0_A_cgif_writecb : Z := 0x137a0.  Definition src0_E_cgif_writecb : Z := 0x13814.
Definition src0_A_freeCGIF : Z := 0x13814.  Definition src0_E_freeCGIF : Z := 0x1384c.
Definition src0_A_cgif_addframe : Z := 0x1384c.  Definition src0_E_cgif_addframe : Z := 0x13bb8.
Definition src0_A_cmpPixel : Z := 0x13bb8.  Definition src0_E_cmpPixel : Z := 0x13c6c.
Definition src0_A_flushFrame : Z := 0x13c6c.  Definition src0_E_flushFrame : Z := 0x14568.
Definition src0_A_freeFrame : Z := 0x14568.  Definition src0_E_freeFrame : Z := 0x145b0.
Definition src0_A_cgif_close : Z := 0x145b0.  Definition src0_E_cgif_close : Z := 0x14678.
Definition src0_A_cgif_raw_newgif : Z := 0x14678.  Definition src0_E_cgif_raw_newgif : Z := 0x1492c.
Definition src0_A_cgif_raw_addframe : Z := 0x1492c.  Definition src0_E_cgif_raw_addframe : Z := 0x14da8.
Definition src0_A_LZW_GenerateStream : Z := 0x14da8.  Definition src0_E_LZW_GenerateStream : Z := 0x15348.
Definition src0_A_cgif_raw_close : Z := 0x15348.  Definition src0_E_cgif_raw_close : Z := 0x153a8.
Definition src0_A_create_byte_list : Z := 0x153a8.  Definition src0_E_create_byte_list : Z := 0x15524.
Definition src0_A_create_byte_list_block : Z := 0x15524.  Definition src0_E_create_byte_list_block : Z := 0x13158.
Definition src0_A_init : Z := 0x13158.  Definition src0_E_init : Z := 0x1315c.
Definition src0_A_init_libc : Z := 0x1315c.  Definition src0_E_init_libc : Z := 0x13388.
Definition src0_A_libc_start_init : Z := 0x13388.  Definition src0_E_libc_start_init : Z := 0x133d4.
Definition src0_A_libc_start_main : Z := 0x133d4.  Definition src0_E_libc_start_main : Z := 0x13434.
Definition src0_A_libc_start_main_stage2 : Z := 0x13434.  Definition src0_E_libc_start_main_stage2 : Z := 0x1347c.
Definition src0_A_init_tls : Z := 0x1347c.  Definition src0_E_init_tls : Z := 0x1372c.
Definition src0_A_funcs_on_exit : Z := 0x137dc.  Definition src0_E_funcs_on_exit : Z := 0x138a4.
Definition src0_A_cxa_finalize : Z := 0x138a4.  Definition src0_E_cxa_finalize : Z := 0x138a8.
Definition src0_A_atexit : Z := 0x138a8.  Definition src0_E_atexit : Z := 0x1396c.
Definition src0_A_atexit_call : Z := 0x1396c.  Definition src0_E_atexit_call : Z := 0x13970.
Definition src0_A_fini : Z := 0x13970.  Definition src0_E_fini : Z := 0x13974.
Definition src0_A_libc_exit_fini : Z := 0x13974.  Definition src0_E_libc_exit_fini : Z := 0x139c0.
Definition src0_A_exit : Z := 0x139c0.  Definition src0_E_exit : Z := 0x13a34.
Definition src0_A_Exit : Z := 0x137c0.  Definition src0_E_Exit : Z := 0x137dc.
Definition src0_A_open : Z := 0x13a34.  Definition src0_E_open : Z := 0x13b18.
Definition src0_A_init_ssp : Z := 0x13b18.  Definition src0_E_init_ssp : Z := 0x13b78.
Definition src0_A_stack_chk_fail : Z := 0x13b78.  Definition src0_E_stack_chk_fail : Z := 0x13b80.
Definition src0_A_syscall_ret : Z := 0x13b80.  Definition src0_E_syscall_ret : Z := 0x13bb8.
Definition src0_A_errno_location : Z := 0x13bb8.  Definition src0_E_errno_location : Z := 0x13bc4.
Definition src0_A_free : Z := 0x13bc4.  Definition src0_E_free : Z := 0x13bc8.
Definition src0_A_libc_calloc : Z := 0x13bc8.  Definition src0_E_libc_calloc : Z := 0x13d00.
Definition src0_A_libc_malloc : Z := 0x13d00.  Definition src0_E_libc_malloc : Z := 0x13d04.
Definition src0_A_malloc : Z := 0x13d04.  Definition src0_E_malloc : Z := 0x13d08.
Definition src0_A_libc_free : Z := 0x13d08.  Definition src0_E_libc_free : Z := 0x13ed4.
Definition src0_A_get_meta : Z := 0x13ed4.  Definition src0_E_get_meta : Z := 0x13fe4.
Definition src0_A_nontrivial_free : Z := 0x13fe4.  Definition src0_E_nontrivial_free : Z := 0x143bc.
Definition src0_A_alloc_meta : Z := 0x143bc.  Definition src0_E_alloc_meta : Z := 0x14694.
Definition src0_A_libc_malloc_impl : Z := 0x14694.  Definition src0_E_libc_malloc_impl : Z := 0x14a04.
Definition src0_A_alloc_slot : Z := 0x14a04.  Definition src0_E_alloc_slot : Z := 0x152a8.
Definition src0_A_enframe : Z := 0x152a8.  Definition src0_E_enframe : Z := 0x153f8.
Definition src0_A_malloc_allzerop : Z := 0x153f8.  Definition src0_E_malloc_allzerop : Z := 0x15570.
Definition src0_A_vm_wait : Z := 0x15570.  Definition src0_E_vm_wait : Z := 0x15574.
Definition src0_A_mmap : Z := 0x15574.  Definition src0_E_mmap : Z := 0x15660.
Definition src0_A_mprotect : Z := 0x15660.  Definition src0_E_mprotect : Z := 0x156a8.
Definition src0_A_munmap : Z := 0x156a8.  Definition src0_E_munmap : Z := 0x156f0.
Definition src0_A_unlist_locked_file : Z := 0x15700.  Definition src0_E_unlist_locked_file : Z := 0x15704.
Definition src0_A_fclose : Z := 0x15704.  Definition src0_E_fclose : Z := 0x157c4.
Definition src0_A_fflush : Z := 0x157c4.  Definition src0_E_fflush : Z := 0x15934.
Definition src0_A_lockfile : Z := 0x15934.  Definition src0_E_lockfile : Z := 0x15a30.
Definition src0_A_unlockfile : Z := 0x15a30.  Definition src0_E_unlockfile : Z := 0x15a90.
Definition src0_A_fopen : Z := 0x15a9c.  Definition src0_E_fopen : Z := 0x15b78.
Definition src0_A_fmodeflags : Z := 0x15b78.  Definition src0_E_fmodeflags : Z := 0x15c2c.
Definition src0_A_fdopen : Z := 0x15c2c.  Definition src0_E_fdopen : Z := 0x15e04.
Definition src0_A_stdio_write : Z := 0x15f48.  Definition src0_E_stdio_write : Z := 0x160d8.
Definition src0_A_aio_close : Z := 0x15f18.  Definition src0_E_aio_close : Z := 0x15f1c.
Definition src0_A_stdio_close : Z := 0x15f1c.  Definition src0_E_stdio_close : Z := 0x15f48.
Definition src0_A_fprintf : Z := 0x15a90.  Definition src0_E_fprintf : Z := 0x15af4.
Definition src0_A_fwritex : Z := 0x15af4.  Definition src0_E_fwritex : Z := 0x15c2c.
Definition src0_A_fwrite : Z := 0x15c2c.  Definition src0_E_fwrite : Z := 0x15ce4.
Definition src0_A_towrite : Z := 0x15ce4.  Definition src0_E_towrite : Z := 0x15d38.
Definition src0_A_stdio_exit : Z := 0x15d38.  Definition src0_E_stdio_exit : Z := 0x15edc.
Definition src0_A_ofl_lock : Z := 0x15edc.  Definition src0_E_ofl_lock : Z := 0x15f0c.
Definition src0_A_ofl_unlock : Z := 0x15f0c.  Definition src0_E_ofl_unlock : Z := 0x15f18.
Definition src0_A_ofl_add : Z := 0x1656c.  Definition src0_E_ofl_add : Z := 0x160e0.
Definition src0_A_stdout_write : Z := 0x160e0.  Definition src0_E_stdout_write : Z := 0x16180.
Definition src0_A_vfprintf : Z := 0x16180.  Definition src0_E_vfprintf : Z := 0x16330.
Definition src0_A_printf_core : Z := 0x16330.  Definition src0_E_printf_core : Z := 0x17160.
Definition src0_A_pop_arg : Z := 0x17160.  Definition src0_E_pop_arg : Z := 0x17294.
Definition src0_A_pad : Z := 0x17294.  Definition src0_E_pad : Z := 0x17368.
Definition src0_A_fmt_fp : Z := 0x17368.  Definition src0_E_fmt_fp : Z := 0x18a30.
Definition src0_A_strerror : Z := 0x18a30.  Definition src0_E_strerror : Z := 0x18a6c.
Definition src0_A_lctrans_impl : Z := 0x18a6c.  Definition src0_E_lctrans_impl : Z := 0x18a70.
Definition src0_A_lctrans : Z := 0x18a70.  Definition src0_E_lctrans : Z := 0x18a74.
Definition src0_A_wctomb : Z := 0x18a74.  Definition src0_E_wctomb : Z := 0x18a98.
Definition src0_A_wcrtomb : Z := 0x18a98.  Definition src0_E_wcrtomb : Z := 0x18bc4.
Definition src0_A_extenddftf2 : Z := 0x18bc4.  Definition src0_E_extenddftf2 : Z := 0x18d54.
Definition src0_A_signbitl : Z := 0x18d54.  Definition src0_E_signbitl : Z := 0x18d5c.
Definition src0_A_fpclassifyl : Z := 0x18d5c.  Definition src0_E_fpclassifyl : Z := 0x18da0.
Definition src0_A_frexpl : Z := 0x18da0.  Definition src0_E_frexpl : Z := 0x18e78.
Definition src0_A_letf2 : Z := 0x18e78.  Definition src0_E_letf2 : Z := 0x18f40.
Definition src0_A_multf3 : Z := 0x18f40.  Definition src0_E_multf3 : Z := 0x19640.
Definition src0_A_floatsitf : Z := 0x19640.  Definition src0_E_floatsitf : Z := 0x19748.
Definition src0_A_scalbn : Z := 0x19748.  Definition src0_E_scalbn : Z := 0x197e0.
Definition src0_A_subtf3 : Z := 0x197e0.  Definition src0_E_subtf3 : Z := 0x197f0.
Definition src0_A_addtf3 : Z := 0x197f0.  Definition src0_E_addtf3 : Z := 0x19fbc.
Definition src0_A_fe_getround : Z := 0x19fbc.  Definition src0_E_fe_getround : Z := 0x19fec.
Definition src0_A_fe_raise_inexact : Z := 0x19fec.  Definition src0_E_fe_raise_inexact : Z := 0x19ff8.
Definition src0_A_fixunstfsi : Z := 0x19ff8.  Definition src0_E_fixunstfsi : Z := 0x1a08c.
Definition src0_A_floatunsitf : Z := 0x1a08c.  Definition src0_E_floatunsitf : Z := 0x1a178.
Definition src0_A_fixtfsi : Z := 0x1a178.  Definition src0_E_fixtfsi : Z := 0x1a220.
Definition src0_A_divtf3 : Z := 0x1a220.  Definition src0_E_divtf3 : Z := 0x1ab24.
Definition src0_A_vprintf : Z := 0x1ab24.  Definition src0_E_vprintf : Z := 0x1ab40.
Definition src0_A_bcmp : Z := 0x1ab40.  Definition src0_E_bcmp : Z := 0x1ab44.
Definition src0_A_memcmp : Z := 0x1ac10.  Definition src0_E_memcmp : Z := 0x1ac40.
Definition src0_A_memcpy : Z := 0x1ac40.  Definition src0_E_memcpy : Z := 0x1b044.
Definition src0_A_memset : Z := 0x1b044.  Definition src0_E_memset : Z := 0x1b13c.
Definition src0_A_strchr : Z := 0x1e954.  Definition src0_E_strchr : Z := 0x1e990.
Definition src0_A_strchrnul : Z := 0x1b254.  Definition src0_E_strchrnul : Z := 0x1b334.
Definition src0_A_strlen : Z := 0x1b334.  Definition src0_E_strlen : Z := 0x1b3c4.
Definition src0_A_strnlen : Z := 0x1b424.  Definition src0_E_strnlen : Z := 0x1b468.
Definition src0_A_memchr : Z := 0x1ab44.  Definition src0_E_memchr : Z := 0x1ac10.
Definition src0_A_lock : Z := 0x1b468.  Definition src0_E_lock : Z := 0x1b6f0.
Definition src0_A_unlock : Z := 0x1b6f0.  Definition src0_E_unlock : Z := 0x1b764.
Definition src0_A_syscall_cp_c : Z := 0x1b764.  Definition src0_E_syscall_cp_c : Z := 0x1b788.
Definition src0_A_syscall_cp : Z := 0x1b788.  Definition src0_E_syscall_cp : Z := 0x1b78c.
Definition src0_A_set_thread_area : Z := 0x1b78c.  Definition src0_E_set_thread_area : Z := 0x1b798.
Definition src0_A_unistd_exit : Z := 0x1b798.  Definition src0_E_unistd_exit : Z := 0x1b7a4.
Definition src0_A_close : Z := 0x1b7a4.  Definition src0_E_close : Z := 0x1b7f8.
Definition src0_A_lseek : Z := 0x1b7f8.  Definition src0_E_lseek : Z := 0x1b804.
Definition src0_A_read : Z := 0x1b804.  Definition src0_E_read : Z := 0x1b838.
Definition src0_A_unlink : Z := 0x1efe0.  Definition src0_E_unlink : Z := 0x1f010.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x1030d.
Definition src0_D_str_d_n : Z := 0x10321.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x1032e.
Definition src0_D_str_cli_config_len_overruns : Z := 0x1033f.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x103da.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10473.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10488.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x104ad.
Definition src0_D_str_dev_null : Z := 0x104da.
Definition src0_D_str_null : Z := 0x104e4.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10750.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10760.
Definition src0_D_debruijn32 : Z := 0x10547.
Definition src0_D_size_classes : Z := 0x10568.
Definition src0_D_small_cnt_tab : Z := 0x105c8.
Definition src0_D_med_cnt_tab : Z := 0x105e3.
Definition src0_D_states : Z := 0x10790.
Definition src0_D_xdigits : Z := 0x10960.
Definition src0_D_errmsgstr : Z := 0x10970.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11118.
Definition src0_D_fe_getround : Z := 0x11220.
Definition src0_D_EH_FRAME_LIST : Z := 0x11310.
Definition src0_D_init_array_start : Z := 0x1c838.
Definition src0_D_fini_array_start : Z := 0x1c840.
Definition src0_D_stderr : Z := 0x1d500.
Definition src0_D_stdout : Z := 0x1d508.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1d510.
Definition src0_D_got_DYNAMIC : Z := 0x1d518.
Definition src0_D_got_main : Z := 0x1d520.
Definition src0_D_got_init : Z := 0x1d528.
Definition src0_D_got_fini : Z := 0x1d530.
Definition src0_D_got_register_frame_info : Z := 0x1d538.
Definition src0_D_got_cxa_finalize : Z := 0x1d540.
Definition src0_D_got_deregister_frame_info : Z := 0x1d548.
Definition src0_D_got_stderr : Z := 0x1d550.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1d558.
Definition src0_D_got_stdout : Z := 0x1d560.
Definition src0_D_got_environ : Z := 0x1d568.
Definition src0_D_got_progname_full : Z := 0x1d570.
Definition src0_D_got_progname : Z := 0x1d578.
Definition src0_D_got_init_array_end : Z := 0x1d580.
Definition src0_D_got_init_array_start : Z := 0x1d588.
Definition src0_D_got_stack_chk_guard : Z := 0x1d590.
Definition src0_D_got_fini_array_end : Z := 0x1d598.
Definition src0_D_got_fini_array_start : Z := 0x1d5a0.
Definition src0_D_dso_handle : Z := 0x1e5a8.
Definition src0_D_aef_argc : Z := 0x1e5b8.
Definition src0_D_stderr_FILE : Z := 0x1e5d0.
Definition src0_D_stderr_used : Z := 0x1e6b8.
Definition src0_D_stdout_FILE : Z := 0x1e6c0.
Definition src0_D_stdout_used : Z := 0x1e7a8.
Definition src0_D_default_stacksize : Z := 0x1e7b0.
Definition src0_D_do_init_initialized : Z := 0x1e7c0.
Definition src0_D_do_init_object : Z := 0x1e7c8.
Definition src0_D_do_fini_finalized : Z := 0x1e808.
Definition src0_D_read_stage : Z := 0x1e809.
Definition src0_D_target_run_initialized : Z := 0x2e810.
Definition src0_D_aef_in_callback : Z := 0x2e814.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2e820.
Definition src0_D_environ : Z := 0x2e840.
Definition src0_D_thread_list_lock : Z := 0x4e918.
Definition src0_D_main_tls : Z := 0x4e920.
Definition src0_D_builtin_tls : Z := 0x2e848.
Definition src0_D_finished_atexit : Z := 0x4e958.
Definition src0_D_atexit_lock : Z := 0x4e95c.
Definition src0_D_atexit_slot : Z := 0x4e960.
Definition src0_D_atexit_head : Z := 0x4e968.
Definition src0_D_atexit_builtin : Z := 0x4e970.
Definition src0_D_exit_exit_lock : Z := 0x4eb78.
Definition src0_D_stack_chk_guard : Z := 0x4eb80.
Definition src0_D_sysinfo : Z := 0x4eb88.
Definition src0_D_progname : Z := 0x4eb90.
Definition src0_D_progname_full : Z := 0x4eb98.
Definition src0_D_libc : Z := 0x4eba0.
Definition src0_D_hwcap : Z := 0x4ec08.
Definition src0_D_malloc_lock : Z := 0x4ec10.
Definition src0_D_malloc_context : Z := 0x4ec18.
Definition src0_D_malloc_replaced : Z := 0x4efb8.
Definition src0_D_stdin_used : Z := 0x4efc0.
Definition src0_D_ofl_lock : Z := 0x4efc8.
Definition src0_D_ofl_head : Z := 0x4efd0.
Definition src0_D_stderr_buf : Z := 0x4efd8.
Definition src0_D_stdout_buf : Z := 0x4efe0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 33.
