(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x124e4.  Definition src0_text_hi : Z := 0x1b0c4.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x110f4.
Definition src0_eh_frame_lo : Z := 0x111b8.  Definition src0_eh_frame_hi : Z := 0x114e4.
Definition src0_init_array_lo : Z := 0x1c0c8.  Definition src0_init_array_hi : Z := 0x1c0d0.
Definition src0_fini_array_lo : Z := 0x1c0d0.  Definition src0_fini_array_hi : Z := 0x1c0d8.
Definition src0_data_rel_ro_lo : Z := 0x1c0d8.  Definition src0_data_rel_ro_hi : Z := 0x1c0e8.
Definition src0_got_lo : Z := 0x1c0e8.  Definition src0_got_hi : Z := 0x1c180.
Definition src0_data_lo : Z := 0x1d180.  Definition src0_data_hi : Z := 0x1d38c.
Definition src0_bss_lo : Z := 0x1d390.  Definition src0_bss_hi : Z := 0x4dfb8.
Definition src0_A_start : Z := 0x124e4.  Definition src0_E_start : Z := 0x1252c.
Definition src0_A_do_init : Z := 0x1252c.  Definition src0_E_do_init : Z := 0x125a0.
Definition src0_A_do_fini : Z := 0x125a0.  Definition src0_E_do_fini : Z := 0x12630.
Definition src0_A_main : Z := 0x12630.  Definition src0_E_main : Z := 0x128f4.
Definition src0_A_target_alloc_init : Z := 0x128f4.  Definition src0_E_target_alloc_init : Z := 0x128f8.
Definition src0_A_target_alloc_count : Z := 0x128f8.  Definition src0_E_target_alloc_count : Z := 0x12900.
Definition src0_A_target_run : Z := 0x12900.  Definition src0_E_target_run : Z := 0x12a58.
Definition src0_A_aef_exit_guard : Z := 0x12a58.  Definition src0_E_aef_exit_guard : Z := 0x12a88.
Definition src0_A_emit_printf : Z := 0x12a88.  Definition src0_E_emit_printf : Z := 0x12ad0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ad0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x12c2c.
Definition src0_A_read_frameconfig : Z := 0x12f28.  Definition src0_E_read_frameconfig : Z := 0x13190.
Definition src0_A_cgif_newgif : Z := 0x13190.  Definition src0_E_cgif_newgif : Z := 0x13348.
Definition src0_A_cgif_writecb : Z := 0x13348.  Definition src0_E_cgif_writecb : Z := 0x133bc.
Definition src0_A_freeCGIF : Z := 0x133bc.  Definition src0_E_freeCGIF : Z := 0x133f4.
Definition src0_A_cgif_addframe : Z := 0x133f4.  Definition src0_E_cgif_addframe : Z := 0x13760.
Definition src0_A_cmpPixel : Z := 0x13760.  Definition src0_E_cmpPixel : Z := 0x13814.
Definition src0_A_flushFrame : Z := 0x13814.  Definition src0_E_flushFrame : Z := 0x14110.
Definition src0_A_freeFrame : Z := 0x14110.  Definition src0_E_freeFrame : Z := 0x14158.
Definition src0_A_cgif_close : Z := 0x14158.  Definition src0_E_cgif_close : Z := 0x14220.
Definition src0_A_cgif_raw_newgif : Z := 0x14220.  Definition src0_E_cgif_raw_newgif : Z := 0x144d4.
Definition src0_A_cgif_raw_addframe : Z := 0x144d4.  Definition src0_E_cgif_raw_addframe : Z := 0x14950.
Definition src0_A_LZW_GenerateStream : Z := 0x14950.  Definition src0_E_LZW_GenerateStream : Z := 0x14ef0.
Definition src0_A_cgif_raw_close : Z := 0x14ef0.  Definition src0_E_cgif_raw_close : Z := 0x14f50.
Definition src0_A_create_byte_list : Z := 0x14f50.  Definition src0_E_create_byte_list : Z := 0x150cc.
Definition src0_A_create_byte_list_block : Z := 0x150cc.  Definition src0_E_create_byte_list_block : Z := 0x12d00.
Definition src0_A_init : Z := 0x12d00.  Definition src0_E_init : Z := 0x12d04.
Definition src0_A_init_libc : Z := 0x12d04.  Definition src0_E_init_libc : Z := 0x12f30.
Definition src0_A_libc_start_init : Z := 0x12f30.  Definition src0_E_libc_start_init : Z := 0x12f7c.
Definition src0_A_libc_start_main : Z := 0x12f7c.  Definition src0_E_libc_start_main : Z := 0x12fdc.
Definition src0_A_libc_start_main_stage2 : Z := 0x12fdc.  Definition src0_E_libc_start_main_stage2 : Z := 0x13024.
Definition src0_A_init_tls : Z := 0x13024.  Definition src0_E_init_tls : Z := 0x132d4.
Definition src0_A_funcs_on_exit : Z := 0x13384.  Definition src0_E_funcs_on_exit : Z := 0x1344c.
Definition src0_A_cxa_finalize : Z := 0x1344c.  Definition src0_E_cxa_finalize : Z := 0x13450.
Definition src0_A_atexit : Z := 0x13450.  Definition src0_E_atexit : Z := 0x13514.
Definition src0_A_atexit_call : Z := 0x13514.  Definition src0_E_atexit_call : Z := 0x13518.
Definition src0_A_fini : Z := 0x13518.  Definition src0_E_fini : Z := 0x1351c.
Definition src0_A_libc_exit_fini : Z := 0x1351c.  Definition src0_E_libc_exit_fini : Z := 0x13568.
Definition src0_A_exit : Z := 0x13568.  Definition src0_E_exit : Z := 0x135dc.
Definition src0_A_Exit : Z := 0x13368.  Definition src0_E_Exit : Z := 0x13384.
Definition src0_A_open : Z := 0x135dc.  Definition src0_E_open : Z := 0x136c0.
Definition src0_A_init_ssp : Z := 0x136c0.  Definition src0_E_init_ssp : Z := 0x13720.
Definition src0_A_stack_chk_fail : Z := 0x13720.  Definition src0_E_stack_chk_fail : Z := 0x13728.
Definition src0_A_syscall_ret : Z := 0x13728.  Definition src0_E_syscall_ret : Z := 0x13760.
Definition src0_A_errno_location : Z := 0x13760.  Definition src0_E_errno_location : Z := 0x1376c.
Definition src0_A_free : Z := 0x1376c.  Definition src0_E_free : Z := 0x13770.
Definition src0_A_libc_calloc : Z := 0x13770.  Definition src0_E_libc_calloc : Z := 0x138a8.
Definition src0_A_libc_malloc : Z := 0x138a8.  Definition src0_E_libc_malloc : Z := 0x138ac.
Definition src0_A_malloc : Z := 0x138ac.  Definition src0_E_malloc : Z := 0x138b0.
Definition src0_A_libc_free : Z := 0x138b0.  Definition src0_E_libc_free : Z := 0x13a7c.
Definition src0_A_get_meta : Z := 0x13a7c.  Definition src0_E_get_meta : Z := 0x13b8c.
Definition src0_A_nontrivial_free : Z := 0x13b8c.  Definition src0_E_nontrivial_free : Z := 0x13f64.
Definition src0_A_alloc_meta : Z := 0x13f64.  Definition src0_E_alloc_meta : Z := 0x1423c.
Definition src0_A_libc_malloc_impl : Z := 0x1423c.  Definition src0_E_libc_malloc_impl : Z := 0x145ac.
Definition src0_A_alloc_slot : Z := 0x145ac.  Definition src0_E_alloc_slot : Z := 0x14e50.
Definition src0_A_enframe : Z := 0x14e50.  Definition src0_E_enframe : Z := 0x14fa0.
Definition src0_A_malloc_allzerop : Z := 0x14fa0.  Definition src0_E_malloc_allzerop : Z := 0x15118.
Definition src0_A_vm_wait : Z := 0x15118.  Definition src0_E_vm_wait : Z := 0x1511c.
Definition src0_A_mmap : Z := 0x1511c.  Definition src0_E_mmap : Z := 0x15208.
Definition src0_A_mprotect : Z := 0x15208.  Definition src0_E_mprotect : Z := 0x15250.
Definition src0_A_munmap : Z := 0x15250.  Definition src0_E_munmap : Z := 0x15298.
Definition src0_A_unlist_locked_file : Z := 0x152a8.  Definition src0_E_unlist_locked_file : Z := 0x152ac.
Definition src0_A_fclose : Z := 0x152ac.  Definition src0_E_fclose : Z := 0x1536c.
Definition src0_A_fflush : Z := 0x1536c.  Definition src0_E_fflush : Z := 0x154dc.
Definition src0_A_lockfile : Z := 0x154dc.  Definition src0_E_lockfile : Z := 0x155d8.
Definition src0_A_unlockfile : Z := 0x155d8.  Definition src0_E_unlockfile : Z := 0x15638.
Definition src0_A_fopen : Z := 0x15644.  Definition src0_E_fopen : Z := 0x15720.
Definition src0_A_fmodeflags : Z := 0x15720.  Definition src0_E_fmodeflags : Z := 0x157d4.
Definition src0_A_fdopen : Z := 0x157d4.  Definition src0_E_fdopen : Z := 0x159ac.
Definition src0_A_stdio_write : Z := 0x15af0.  Definition src0_E_stdio_write : Z := 0x15c80.
Definition src0_A_aio_close : Z := 0x15ac0.  Definition src0_E_aio_close : Z := 0x15ac4.
Definition src0_A_stdio_close : Z := 0x15ac4.  Definition src0_E_stdio_close : Z := 0x15af0.
Definition src0_A_fprintf : Z := 0x15638.  Definition src0_E_fprintf : Z := 0x1569c.
Definition src0_A_fwritex : Z := 0x1569c.  Definition src0_E_fwritex : Z := 0x157d4.
Definition src0_A_fwrite : Z := 0x157d4.  Definition src0_E_fwrite : Z := 0x1588c.
Definition src0_A_towrite : Z := 0x1588c.  Definition src0_E_towrite : Z := 0x158e0.
Definition src0_A_stdio_exit : Z := 0x158e0.  Definition src0_E_stdio_exit : Z := 0x15a84.
Definition src0_A_ofl_lock : Z := 0x15a84.  Definition src0_E_ofl_lock : Z := 0x15ab4.
Definition src0_A_ofl_unlock : Z := 0x15ab4.  Definition src0_E_ofl_unlock : Z := 0x15ac0.
Definition src0_A_ofl_add : Z := 0x16114.  Definition src0_E_ofl_add : Z := 0x15c88.
Definition src0_A_stdout_write : Z := 0x15c88.  Definition src0_E_stdout_write : Z := 0x15d28.
Definition src0_A_vfprintf : Z := 0x15d28.  Definition src0_E_vfprintf : Z := 0x15ed8.
Definition src0_A_printf_core : Z := 0x15ed8.  Definition src0_E_printf_core : Z := 0x16d08.
Definition src0_A_pop_arg : Z := 0x16d08.  Definition src0_E_pop_arg : Z := 0x16e3c.
Definition src0_A_pad : Z := 0x16e3c.  Definition src0_E_pad : Z := 0x16f10.
Definition src0_A_fmt_fp : Z := 0x16f10.  Definition src0_E_fmt_fp : Z := 0x185d8.
Definition src0_A_strerror : Z := 0x185d8.  Definition src0_E_strerror : Z := 0x18614.
Definition src0_A_lctrans_impl : Z := 0x18614.  Definition src0_E_lctrans_impl : Z := 0x18618.
Definition src0_A_lctrans : Z := 0x18618.  Definition src0_E_lctrans : Z := 0x1861c.
Definition src0_A_wctomb : Z := 0x1861c.  Definition src0_E_wctomb : Z := 0x18640.
Definition src0_A_wcrtomb : Z := 0x18640.  Definition src0_E_wcrtomb : Z := 0x1876c.
Definition src0_A_extenddftf2 : Z := 0x1876c.  Definition src0_E_extenddftf2 : Z := 0x188fc.
Definition src0_A_signbitl : Z := 0x188fc.  Definition src0_E_signbitl : Z := 0x18904.
Definition src0_A_fpclassifyl : Z := 0x18904.  Definition src0_E_fpclassifyl : Z := 0x18948.
Definition src0_A_frexpl : Z := 0x18948.  Definition src0_E_frexpl : Z := 0x18a20.
Definition src0_A_letf2 : Z := 0x18a20.  Definition src0_E_letf2 : Z := 0x18ae8.
Definition src0_A_multf3 : Z := 0x18ae8.  Definition src0_E_multf3 : Z := 0x191e8.
Definition src0_A_floatsitf : Z := 0x191e8.  Definition src0_E_floatsitf : Z := 0x192f0.
Definition src0_A_scalbn : Z := 0x192f0.  Definition src0_E_scalbn : Z := 0x19388.
Definition src0_A_subtf3 : Z := 0x19388.  Definition src0_E_subtf3 : Z := 0x19398.
Definition src0_A_addtf3 : Z := 0x19398.  Definition src0_E_addtf3 : Z := 0x19b64.
Definition src0_A_fe_getround : Z := 0x19b64.  Definition src0_E_fe_getround : Z := 0x19b94.
Definition src0_A_fe_raise_inexact : Z := 0x19b94.  Definition src0_E_fe_raise_inexact : Z := 0x19ba0.
Definition src0_A_fixunstfsi : Z := 0x19ba0.  Definition src0_E_fixunstfsi : Z := 0x19c34.
Definition src0_A_floatunsitf : Z := 0x19c34.  Definition src0_E_floatunsitf : Z := 0x19d20.
Definition src0_A_fixtfsi : Z := 0x19d20.  Definition src0_E_fixtfsi : Z := 0x19dc8.
Definition src0_A_divtf3 : Z := 0x19dc8.  Definition src0_E_divtf3 : Z := 0x1a6cc.
Definition src0_A_vprintf : Z := 0x1a6cc.  Definition src0_E_vprintf : Z := 0x1a6e8.
Definition src0_A_bcmp : Z := 0x1abb4.  Definition src0_E_bcmp : Z := 0x1abb8.
Definition src0_A_memcmp : Z := 0x1abb8.  Definition src0_E_memcmp : Z := 0x1a6e8.
Definition src0_A_memcpy : Z := 0x1a6e8.  Definition src0_E_memcpy : Z := 0x1aaec.
Definition src0_A_memset : Z := 0x1aaec.  Definition src0_E_memset : Z := 0x1abe4.
Definition src0_A_strchr : Z := 0x1d524.  Definition src0_E_strchr : Z := 0x1d560.
Definition src0_A_strchrnul : Z := 0x1d560.  Definition src0_E_strchrnul : Z := 0x1d640.
Definition src0_A_strlen : Z := 0x1d640.  Definition src0_E_strlen : Z := 0x1abe4.
Definition src0_A_strnlen : Z := 0x1abe4.  Definition src0_E_strnlen : Z := 0x1ac28.
Definition src0_A_memchr : Z := 0x1ac28.  Definition src0_E_memchr : Z := 0x1acf4.
Definition src0_A_lock : Z := 0x1acf4.  Definition src0_E_lock : Z := 0x1af7c.
Definition src0_A_unlock : Z := 0x1af7c.  Definition src0_E_unlock : Z := 0x1aff0.
Definition src0_A_syscall_cp_c : Z := 0x1aff0.  Definition src0_E_syscall_cp_c : Z := 0x1b014.
Definition src0_A_syscall_cp : Z := 0x1b014.  Definition src0_E_syscall_cp : Z := 0x1b018.
Definition src0_A_set_thread_area : Z := 0x1b018.  Definition src0_E_set_thread_area : Z := 0x1b024.
Definition src0_A_unistd_exit : Z := 0x1b024.  Definition src0_E_unistd_exit : Z := 0x1b030.
Definition src0_A_close : Z := 0x1b030.  Definition src0_E_close : Z := 0x1b084.
Definition src0_A_lseek : Z := 0x1b084.  Definition src0_E_lseek : Z := 0x1b090.
Definition src0_A_read : Z := 0x1b090.  Definition src0_E_read : Z := 0x1b0c4.
Definition src0_A_unlink : Z := 0x1dbb0.  Definition src0_E_unlink : Z := 0x1dbe0.
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
Definition src0_D_init_array_start : Z := 0x1c0c8.
Definition src0_D_fini_array_start : Z := 0x1c0d0.
Definition src0_D_stderr : Z := 0x1c0d8.
Definition src0_D_stdout : Z := 0x1c0e0.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1c0e8.
Definition src0_D_got_DYNAMIC : Z := 0x1c0f0.
Definition src0_D_got_main : Z := 0x1c0f8.
Definition src0_D_got_init : Z := 0x1c100.
Definition src0_D_got_fini : Z := 0x1c108.
Definition src0_D_got_register_frame_info : Z := 0x1c110.
Definition src0_D_got_cxa_finalize : Z := 0x1c118.
Definition src0_D_got_deregister_frame_info : Z := 0x1c120.
Definition src0_D_got_stderr : Z := 0x1c128.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1c130.
Definition src0_D_got_stdout : Z := 0x1c138.
Definition src0_D_got_environ : Z := 0x1c140.
Definition src0_D_got_progname_full : Z := 0x1c148.
Definition src0_D_got_progname : Z := 0x1c150.
Definition src0_D_got_init_array_end : Z := 0x1c158.
Definition src0_D_got_init_array_start : Z := 0x1c160.
Definition src0_D_got_stack_chk_guard : Z := 0x1c168.
Definition src0_D_got_fini_array_end : Z := 0x1c170.
Definition src0_D_got_fini_array_start : Z := 0x1c178.
Definition src0_D_dso_handle : Z := 0x1d180.
Definition src0_D_aef_argc : Z := 0x1d190.
Definition src0_D_stderr_FILE : Z := 0x1d1a8.
Definition src0_D_stderr_used : Z := 0x1d290.
Definition src0_D_stdout_FILE : Z := 0x1d298.
Definition src0_D_stdout_used : Z := 0x1d380.
Definition src0_D_default_stacksize : Z := 0x1d388.
Definition src0_D_do_init_initialized : Z := 0x1d390.
Definition src0_D_do_init_object : Z := 0x1d398.
Definition src0_D_do_fini_finalized : Z := 0x1d3d8.
Definition src0_D_read_stage : Z := 0x1d3d9.
Definition src0_D_target_run_initialized : Z := 0x2d3e0.
Definition src0_D_aef_in_callback : Z := 0x2d3e4.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2d3f0.
Definition src0_D_environ : Z := 0x2d410.
Definition src0_D_thread_list_lock : Z := 0x4d4e8.
Definition src0_D_main_tls : Z := 0x4d4f0.
Definition src0_D_builtin_tls : Z := 0x2d418.
Definition src0_D_finished_atexit : Z := 0x4d528.
Definition src0_D_atexit_lock : Z := 0x4d52c.
Definition src0_D_atexit_slot : Z := 0x4d530.
Definition src0_D_atexit_head : Z := 0x4d538.
Definition src0_D_atexit_builtin : Z := 0x4d540.
Definition src0_D_exit_exit_lock : Z := 0x4d748.
Definition src0_D_stack_chk_guard : Z := 0x4d750.
Definition src0_D_sysinfo : Z := 0x4d758.
Definition src0_D_progname : Z := 0x4d760.
Definition src0_D_progname_full : Z := 0x4d768.
Definition src0_D_libc : Z := 0x4d770.
Definition src0_D_hwcap : Z := 0x4d7d8.
Definition src0_D_malloc_lock : Z := 0x4d7e0.
Definition src0_D_malloc_context : Z := 0x4d7e8.
Definition src0_D_malloc_replaced : Z := 0x4db88.
Definition src0_D_stdin_used : Z := 0x4db90.
Definition src0_D_ofl_lock : Z := 0x4db98.
Definition src0_D_ofl_head : Z := 0x4dba0.
Definition src0_D_stderr_buf : Z := 0x4dba8.
Definition src0_D_stdout_buf : Z := 0x4dbb0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
