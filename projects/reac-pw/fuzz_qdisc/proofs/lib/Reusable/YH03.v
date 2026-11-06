(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x124dc.  Definition src0_text_hi : Z := 0x1b094.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x110f4.
Definition src0_eh_frame_lo : Z := 0x111b8.  Definition src0_eh_frame_hi : Z := 0x114dc.
Definition src0_init_array_lo : Z := 0x1c098.  Definition src0_init_array_hi : Z := 0x1c0a0.
Definition src0_fini_array_lo : Z := 0x1c0a0.  Definition src0_fini_array_hi : Z := 0x1c0a8.
Definition src0_data_rel_ro_lo : Z := 0x1c0a8.  Definition src0_data_rel_ro_hi : Z := 0x1c0b8.
Definition src0_got_lo : Z := 0x1c0b8.  Definition src0_got_hi : Z := 0x1c150.
Definition src0_data_lo : Z := 0x1d150.  Definition src0_data_hi : Z := 0x1d35c.
Definition src0_bss_lo : Z := 0x1d360.  Definition src0_bss_hi : Z := 0x4df88.
Definition src0_A_start : Z := 0x124dc.  Definition src0_E_start : Z := 0x12524.
Definition src0_A_do_init : Z := 0x12524.  Definition src0_E_do_init : Z := 0x12598.
Definition src0_A_do_fini : Z := 0x12598.  Definition src0_E_do_fini : Z := 0x12628.
Definition src0_A_main : Z := 0x12628.  Definition src0_E_main : Z := 0x128ec.
Definition src0_A_target_alloc_init : Z := 0x128ec.  Definition src0_E_target_alloc_init : Z := 0x128f0.
Definition src0_A_target_alloc_count : Z := 0x128f0.  Definition src0_E_target_alloc_count : Z := 0x128f8.
Definition src0_A_target_run : Z := 0x128f8.  Definition src0_E_target_run : Z := 0x12a50.
Definition src0_A_aef_exit_guard : Z := 0x12a50.  Definition src0_E_aef_exit_guard : Z := 0x12a80.
Definition src0_A_emit_printf : Z := 0x12a80.  Definition src0_E_emit_printf : Z := 0x12ac8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ac8.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x12c00.
Definition src0_A_read_frameconfig : Z := 0x12f68.  Definition src0_E_read_frameconfig : Z := 0x131d0.
Definition src0_A_cgif_newgif : Z := 0x131d0.  Definition src0_E_cgif_newgif : Z := 0x13388.
Definition src0_A_cgif_writecb : Z := 0x13388.  Definition src0_E_cgif_writecb : Z := 0x133fc.
Definition src0_A_freeCGIF : Z := 0x133fc.  Definition src0_E_freeCGIF : Z := 0x13434.
Definition src0_A_cgif_addframe : Z := 0x13434.  Definition src0_E_cgif_addframe : Z := 0x137a0.
Definition src0_A_cmpPixel : Z := 0x137a0.  Definition src0_E_cmpPixel : Z := 0x13854.
Definition src0_A_flushFrame : Z := 0x13854.  Definition src0_E_flushFrame : Z := 0x14150.
Definition src0_A_freeFrame : Z := 0x14150.  Definition src0_E_freeFrame : Z := 0x14198.
Definition src0_A_cgif_close : Z := 0x14198.  Definition src0_E_cgif_close : Z := 0x14260.
Definition src0_A_cgif_raw_newgif : Z := 0x14260.  Definition src0_E_cgif_raw_newgif : Z := 0x14514.
Definition src0_A_cgif_raw_addframe : Z := 0x14514.  Definition src0_E_cgif_raw_addframe : Z := 0x14990.
Definition src0_A_LZW_GenerateStream : Z := 0x14990.  Definition src0_E_LZW_GenerateStream : Z := 0x14f30.
Definition src0_A_cgif_raw_close : Z := 0x14f30.  Definition src0_E_cgif_raw_close : Z := 0x14f90.
Definition src0_A_create_byte_list : Z := 0x14f90.  Definition src0_E_create_byte_list : Z := 0x1510c.
Definition src0_A_create_byte_list_block : Z := 0x1510c.  Definition src0_E_create_byte_list_block : Z := 0x12cd0.
Definition src0_A_init : Z := 0x12cd0.  Definition src0_E_init : Z := 0x12cd4.
Definition src0_A_init_libc : Z := 0x12cd4.  Definition src0_E_init_libc : Z := 0x12f00.
Definition src0_A_libc_start_init : Z := 0x12f00.  Definition src0_E_libc_start_init : Z := 0x12f4c.
Definition src0_A_libc_start_main : Z := 0x12f4c.  Definition src0_E_libc_start_main : Z := 0x12fac.
Definition src0_A_libc_start_main_stage2 : Z := 0x12fac.  Definition src0_E_libc_start_main_stage2 : Z := 0x12ff4.
Definition src0_A_init_tls : Z := 0x12ff4.  Definition src0_E_init_tls : Z := 0x132a4.
Definition src0_A_funcs_on_exit : Z := 0x13354.  Definition src0_E_funcs_on_exit : Z := 0x1341c.
Definition src0_A_cxa_finalize : Z := 0x1341c.  Definition src0_E_cxa_finalize : Z := 0x13420.
Definition src0_A_atexit : Z := 0x13420.  Definition src0_E_atexit : Z := 0x134e4.
Definition src0_A_atexit_call : Z := 0x134e4.  Definition src0_E_atexit_call : Z := 0x134e8.
Definition src0_A_fini : Z := 0x134e8.  Definition src0_E_fini : Z := 0x134ec.
Definition src0_A_libc_exit_fini : Z := 0x134ec.  Definition src0_E_libc_exit_fini : Z := 0x13538.
Definition src0_A_exit : Z := 0x13538.  Definition src0_E_exit : Z := 0x135ac.
Definition src0_A_Exit : Z := 0x13338.  Definition src0_E_Exit : Z := 0x13354.
Definition src0_A_open : Z := 0x135ac.  Definition src0_E_open : Z := 0x13690.
Definition src0_A_init_ssp : Z := 0x13690.  Definition src0_E_init_ssp : Z := 0x136f0.
Definition src0_A_stack_chk_fail : Z := 0x136f0.  Definition src0_E_stack_chk_fail : Z := 0x136f8.
Definition src0_A_syscall_ret : Z := 0x136f8.  Definition src0_E_syscall_ret : Z := 0x13730.
Definition src0_A_errno_location : Z := 0x13730.  Definition src0_E_errno_location : Z := 0x1373c.
Definition src0_A_free : Z := 0x1373c.  Definition src0_E_free : Z := 0x13740.
Definition src0_A_libc_calloc : Z := 0x13740.  Definition src0_E_libc_calloc : Z := 0x13878.
Definition src0_A_libc_malloc : Z := 0x13878.  Definition src0_E_libc_malloc : Z := 0x1387c.
Definition src0_A_malloc : Z := 0x1387c.  Definition src0_E_malloc : Z := 0x13880.
Definition src0_A_libc_free : Z := 0x13880.  Definition src0_E_libc_free : Z := 0x13a4c.
Definition src0_A_get_meta : Z := 0x13a4c.  Definition src0_E_get_meta : Z := 0x13b5c.
Definition src0_A_nontrivial_free : Z := 0x13b5c.  Definition src0_E_nontrivial_free : Z := 0x13f34.
Definition src0_A_alloc_meta : Z := 0x13f34.  Definition src0_E_alloc_meta : Z := 0x1420c.
Definition src0_A_libc_malloc_impl : Z := 0x1420c.  Definition src0_E_libc_malloc_impl : Z := 0x1457c.
Definition src0_A_alloc_slot : Z := 0x1457c.  Definition src0_E_alloc_slot : Z := 0x14e20.
Definition src0_A_enframe : Z := 0x14e20.  Definition src0_E_enframe : Z := 0x14f70.
Definition src0_A_malloc_allzerop : Z := 0x14f70.  Definition src0_E_malloc_allzerop : Z := 0x150e8.
Definition src0_A_vm_wait : Z := 0x150e8.  Definition src0_E_vm_wait : Z := 0x150ec.
Definition src0_A_mmap : Z := 0x150ec.  Definition src0_E_mmap : Z := 0x151d8.
Definition src0_A_mprotect : Z := 0x151d8.  Definition src0_E_mprotect : Z := 0x15220.
Definition src0_A_munmap : Z := 0x15220.  Definition src0_E_munmap : Z := 0x15268.
Definition src0_A_unlist_locked_file : Z := 0x15278.  Definition src0_E_unlist_locked_file : Z := 0x1527c.
Definition src0_A_fclose : Z := 0x1527c.  Definition src0_E_fclose : Z := 0x1533c.
Definition src0_A_fflush : Z := 0x1533c.  Definition src0_E_fflush : Z := 0x154ac.
Definition src0_A_lockfile : Z := 0x154ac.  Definition src0_E_lockfile : Z := 0x155a8.
Definition src0_A_unlockfile : Z := 0x155a8.  Definition src0_E_unlockfile : Z := 0x15608.
Definition src0_A_fopen : Z := 0x15614.  Definition src0_E_fopen : Z := 0x156f0.
Definition src0_A_fmodeflags : Z := 0x156f0.  Definition src0_E_fmodeflags : Z := 0x157a4.
Definition src0_A_fdopen : Z := 0x157a4.  Definition src0_E_fdopen : Z := 0x1597c.
Definition src0_A_stdio_write : Z := 0x15ac0.  Definition src0_E_stdio_write : Z := 0x15c50.
Definition src0_A_aio_close : Z := 0x15a90.  Definition src0_E_aio_close : Z := 0x15a94.
Definition src0_A_stdio_close : Z := 0x15a94.  Definition src0_E_stdio_close : Z := 0x15ac0.
Definition src0_A_fprintf : Z := 0x15608.  Definition src0_E_fprintf : Z := 0x1566c.
Definition src0_A_fwritex : Z := 0x1566c.  Definition src0_E_fwritex : Z := 0x157a4.
Definition src0_A_fwrite : Z := 0x157a4.  Definition src0_E_fwrite : Z := 0x1585c.
Definition src0_A_towrite : Z := 0x1585c.  Definition src0_E_towrite : Z := 0x158b0.
Definition src0_A_stdio_exit : Z := 0x158b0.  Definition src0_E_stdio_exit : Z := 0x15a54.
Definition src0_A_ofl_lock : Z := 0x15a54.  Definition src0_E_ofl_lock : Z := 0x15a84.
Definition src0_A_ofl_unlock : Z := 0x15a84.  Definition src0_E_ofl_unlock : Z := 0x15a90.
Definition src0_A_ofl_add : Z := 0x160e4.  Definition src0_E_ofl_add : Z := 0x15c58.
Definition src0_A_stdout_write : Z := 0x15c58.  Definition src0_E_stdout_write : Z := 0x15cf8.
Definition src0_A_vfprintf : Z := 0x15cf8.  Definition src0_E_vfprintf : Z := 0x15ea8.
Definition src0_A_printf_core : Z := 0x15ea8.  Definition src0_E_printf_core : Z := 0x16cd8.
Definition src0_A_pop_arg : Z := 0x16cd8.  Definition src0_E_pop_arg : Z := 0x16e0c.
Definition src0_A_pad : Z := 0x16e0c.  Definition src0_E_pad : Z := 0x16ee0.
Definition src0_A_fmt_fp : Z := 0x16ee0.  Definition src0_E_fmt_fp : Z := 0x185a8.
Definition src0_A_strerror : Z := 0x185a8.  Definition src0_E_strerror : Z := 0x185e4.
Definition src0_A_lctrans_impl : Z := 0x185e4.  Definition src0_E_lctrans_impl : Z := 0x185e8.
Definition src0_A_lctrans : Z := 0x185e8.  Definition src0_E_lctrans : Z := 0x185ec.
Definition src0_A_wctomb : Z := 0x185ec.  Definition src0_E_wctomb : Z := 0x18610.
Definition src0_A_wcrtomb : Z := 0x18610.  Definition src0_E_wcrtomb : Z := 0x1873c.
Definition src0_A_extenddftf2 : Z := 0x1873c.  Definition src0_E_extenddftf2 : Z := 0x188cc.
Definition src0_A_signbitl : Z := 0x188cc.  Definition src0_E_signbitl : Z := 0x188d4.
Definition src0_A_fpclassifyl : Z := 0x188d4.  Definition src0_E_fpclassifyl : Z := 0x18918.
Definition src0_A_frexpl : Z := 0x18918.  Definition src0_E_frexpl : Z := 0x189f0.
Definition src0_A_letf2 : Z := 0x189f0.  Definition src0_E_letf2 : Z := 0x18ab8.
Definition src0_A_multf3 : Z := 0x18ab8.  Definition src0_E_multf3 : Z := 0x191b8.
Definition src0_A_floatsitf : Z := 0x191b8.  Definition src0_E_floatsitf : Z := 0x192c0.
Definition src0_A_scalbn : Z := 0x192c0.  Definition src0_E_scalbn : Z := 0x19358.
Definition src0_A_subtf3 : Z := 0x19358.  Definition src0_E_subtf3 : Z := 0x19368.
Definition src0_A_addtf3 : Z := 0x19368.  Definition src0_E_addtf3 : Z := 0x19b34.
Definition src0_A_fe_getround : Z := 0x19b34.  Definition src0_E_fe_getround : Z := 0x19b64.
Definition src0_A_fe_raise_inexact : Z := 0x19b64.  Definition src0_E_fe_raise_inexact : Z := 0x19b70.
Definition src0_A_fixunstfsi : Z := 0x19b70.  Definition src0_E_fixunstfsi : Z := 0x19c04.
Definition src0_A_floatunsitf : Z := 0x19c04.  Definition src0_E_floatunsitf : Z := 0x19cf0.
Definition src0_A_fixtfsi : Z := 0x19cf0.  Definition src0_E_fixtfsi : Z := 0x19d98.
Definition src0_A_divtf3 : Z := 0x19d98.  Definition src0_E_divtf3 : Z := 0x1a69c.
Definition src0_A_vprintf : Z := 0x1a69c.  Definition src0_E_vprintf : Z := 0x1a6b8.
Definition src0_A_bcmp : Z := 0x1ab84.  Definition src0_E_bcmp : Z := 0x1ab88.
Definition src0_A_memcmp : Z := 0x1ab88.  Definition src0_E_memcmp : Z := 0x1a6b8.
Definition src0_A_memcpy : Z := 0x1a6b8.  Definition src0_E_memcpy : Z := 0x1aabc.
Definition src0_A_memset : Z := 0x1aabc.  Definition src0_E_memset : Z := 0x1abb4.
Definition src0_A_strchr : Z := 0x1d564.  Definition src0_E_strchr : Z := 0x1d5a0.
Definition src0_A_strchrnul : Z := 0x1d5a0.  Definition src0_E_strchrnul : Z := 0x1d680.
Definition src0_A_strlen : Z := 0x1d680.  Definition src0_E_strlen : Z := 0x1abb4.
Definition src0_A_strnlen : Z := 0x1abb4.  Definition src0_E_strnlen : Z := 0x1abf8.
Definition src0_A_memchr : Z := 0x1abf8.  Definition src0_E_memchr : Z := 0x1acc4.
Definition src0_A_lock : Z := 0x1acc4.  Definition src0_E_lock : Z := 0x1af4c.
Definition src0_A_unlock : Z := 0x1af4c.  Definition src0_E_unlock : Z := 0x1afc0.
Definition src0_A_syscall_cp_c : Z := 0x1afc0.  Definition src0_E_syscall_cp_c : Z := 0x1afe4.
Definition src0_A_syscall_cp : Z := 0x1afe4.  Definition src0_E_syscall_cp : Z := 0x1afe8.
Definition src0_A_set_thread_area : Z := 0x1afe8.  Definition src0_E_set_thread_area : Z := 0x1aff4.
Definition src0_A_unistd_exit : Z := 0x1aff4.  Definition src0_E_unistd_exit : Z := 0x1b000.
Definition src0_A_close : Z := 0x1b000.  Definition src0_E_close : Z := 0x1b054.
Definition src0_A_lseek : Z := 0x1b054.  Definition src0_E_lseek : Z := 0x1b060.
Definition src0_A_read : Z := 0x1b060.  Definition src0_E_read : Z := 0x1b094.
Definition src0_A_unlink : Z := 0x1dbf0.  Definition src0_E_unlink : Z := 0x1dc20.
Definition src0_D_str_n0X0x : Z := 0x10298.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x102a5.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x102b5.
Definition src0_D_str_d_n : Z := 0x102c9.
Definition src0_D_str : Z := 0x102cd.
Definition src0_D_str_2 : Z := 0x102d1.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x102d0.
Definition src0_D_str_cli_config_len_overruns : Z := 0x102e1.
Definition src0_D_str_inf : Z := 0x10313.
Definition src0_D_str_INF : Z := 0x10317.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10309.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1032a.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x1033f.
Definition src0_D_str_NAN : Z := 0x102c5.
Definition src0_D_str_nan : Z := 0x102c9.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1035e.
Definition src0_D_str_dev_null : Z := 0x1037e.
Definition src0_D_str_null : Z := 0x10388.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x103a0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x103b8.
Definition src0_D_debruijn32 : Z := 0x1045c.
Definition src0_D_size_classes : Z := 0x1047c.
Definition src0_D_small_cnt_tab : Z := 0x104dc.
Definition src0_D_med_cnt_tab : Z := 0x104f7.
Definition src0_D_states : Z := 0x10658.
Definition src0_D_xdigits : Z := 0x10828.
Definition src0_D_errmsgstr : Z := 0x10838.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x10fe0.
Definition src0_D_fe_getround : Z := 0x110e8.
Definition src0_D_EH_FRAME_LIST : Z := 0x111b8.
Definition src0_D_init_array_start : Z := 0x1c098.
Definition src0_D_fini_array_start : Z := 0x1c0a0.
Definition src0_D_stderr : Z := 0x1c0a8.
Definition src0_D_stdout : Z := 0x1c0b0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1c0b8.
Definition src0_D_got_DYNAMIC : Z := 0x1c0c0.
Definition src0_D_got_main : Z := 0x1c0c8.
Definition src0_D_got_init : Z := 0x1c0d0.
Definition src0_D_got_fini : Z := 0x1c0d8.
Definition src0_D_got_register_frame_info : Z := 0x1c0e0.
Definition src0_D_got_cxa_finalize : Z := 0x1c0e8.
Definition src0_D_got_deregister_frame_info : Z := 0x1c0f0.
Definition src0_D_got_stderr : Z := 0x1c0f8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1c100.
Definition src0_D_got_stdout : Z := 0x1c108.
Definition src0_D_got_environ : Z := 0x1c110.
Definition src0_D_got_progname_full : Z := 0x1c118.
Definition src0_D_got_progname : Z := 0x1c120.
Definition src0_D_got_init_array_end : Z := 0x1c128.
Definition src0_D_got_init_array_start : Z := 0x1c130.
Definition src0_D_got_stack_chk_guard : Z := 0x1c138.
Definition src0_D_got_fini_array_end : Z := 0x1c140.
Definition src0_D_got_fini_array_start : Z := 0x1c148.
Definition src0_D_dso_handle : Z := 0x1d150.
Definition src0_D_aef_argc : Z := 0x1d160.
Definition src0_D_stderr_FILE : Z := 0x1d178.
Definition src0_D_stderr_used : Z := 0x1d260.
Definition src0_D_stdout_FILE : Z := 0x1d268.
Definition src0_D_stdout_used : Z := 0x1d350.
Definition src0_D_default_stacksize : Z := 0x1d358.
Definition src0_D_do_init_initialized : Z := 0x1d360.
Definition src0_D_do_init_object : Z := 0x1d368.
Definition src0_D_do_fini_finalized : Z := 0x1d3a8.
Definition src0_D_read_stage : Z := 0x1d3a9.
Definition src0_D_target_run_initialized : Z := 0x2d3b0.
Definition src0_D_aef_in_callback : Z := 0x2d3b4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2d3c0.
Definition src0_D_environ : Z := 0x2d3e0.
Definition src0_D_thread_list_lock : Z := 0x4d4b8.
Definition src0_D_main_tls : Z := 0x4d4c0.
Definition src0_D_builtin_tls : Z := 0x2d3e8.
Definition src0_D_finished_atexit : Z := 0x4d4f8.
Definition src0_D_atexit_lock : Z := 0x4d4fc.
Definition src0_D_atexit_slot : Z := 0x4d500.
Definition src0_D_atexit_head : Z := 0x4d508.
Definition src0_D_atexit_builtin : Z := 0x4d510.
Definition src0_D_exit_exit_lock : Z := 0x4d718.
Definition src0_D_stack_chk_guard : Z := 0x4d720.
Definition src0_D_sysinfo : Z := 0x4d728.
Definition src0_D_progname : Z := 0x4d730.
Definition src0_D_progname_full : Z := 0x4d738.
Definition src0_D_libc : Z := 0x4d740.
Definition src0_D_hwcap : Z := 0x4d7a8.
Definition src0_D_malloc_lock : Z := 0x4d7b0.
Definition src0_D_malloc_context : Z := 0x4d7b8.
Definition src0_D_malloc_replaced : Z := 0x4db58.
Definition src0_D_stdin_used : Z := 0x4db60.
Definition src0_D_ofl_lock : Z := 0x4db68.
Definition src0_D_ofl_head : Z := 0x4db70.
Definition src0_D_stderr_buf : Z := 0x4db78.
Definition src0_D_stdout_buf : Z := 0x4db80.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
