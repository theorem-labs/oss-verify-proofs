(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x128b4.  Definition src0_text_hi : Z := 0x1ce54.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11320.
Definition src0_eh_frame_lo : Z := 0x11440.  Definition src0_eh_frame_hi : Z := 0x118b4.
Definition src0_init_array_lo : Z := 0x1de58.  Definition src0_init_array_hi : Z := 0x1de60.
Definition src0_fini_array_lo : Z := 0x1de60.  Definition src0_fini_array_hi : Z := 0x1de68.
Definition src0_data_rel_ro_lo : Z := 0x1de68.  Definition src0_data_rel_ro_hi : Z := 0x1df30.
Definition src0_got_lo : Z := 0x1df30.  Definition src0_got_hi : Z := 0x1dfc8.
Definition src0_data_lo : Z := 0x1efc8.  Definition src0_data_hi : Z := 0x1f1d4.
Definition src0_bss_lo : Z := 0x1f1e0.  Definition src0_bss_hi : Z := 0x4fe08.
Definition src0_A_start : Z := 0x128b4.  Definition src0_E_start : Z := 0x128fc.
Definition src0_A_do_init : Z := 0x128fc.  Definition src0_E_do_init : Z := 0x12970.
Definition src0_A_do_fini : Z := 0x12970.  Definition src0_E_do_fini : Z := 0x12a00.
Definition src0_A_main : Z := 0x12a00.  Definition src0_E_main : Z := 0x12cc4.
Definition src0_A_target_alloc_init : Z := 0x12cc4.  Definition src0_E_target_alloc_init : Z := 0x12cc8.
Definition src0_A_target_alloc_count : Z := 0x12cc8.  Definition src0_E_target_alloc_count : Z := 0x12cd0.
Definition src0_A_target_run : Z := 0x12cd0.  Definition src0_E_target_run : Z := 0x12e28.
Definition src0_A_aef_exit_guard : Z := 0x12e28.  Definition src0_E_aef_exit_guard : Z := 0x12e58.
Definition src0_A_emit_printf : Z := 0x12e58.  Definition src0_E_emit_printf : Z := 0x12ea0.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x12ea0.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x141c0.
Definition src0_A_read_frameconfig : Z := 0x15540.  Definition src0_E_read_frameconfig : Z := 0x157a8.
Definition src0_A_cgif_newgif : Z := 0x157a8.  Definition src0_E_cgif_newgif : Z := 0x15960.
Definition src0_A_cgif_writecb : Z := 0x15960.  Definition src0_E_cgif_writecb : Z := 0x159d4.
Definition src0_A_freeCGIF : Z := 0x159d4.  Definition src0_E_freeCGIF : Z := 0x15a0c.
Definition src0_A_cgif_addframe : Z := 0x15a0c.  Definition src0_E_cgif_addframe : Z := 0x15d78.
Definition src0_A_cmpPixel : Z := 0x15d78.  Definition src0_E_cmpPixel : Z := 0x15e2c.
Definition src0_A_flushFrame : Z := 0x15e2c.  Definition src0_E_flushFrame : Z := 0x16728.
Definition src0_A_freeFrame : Z := 0x16728.  Definition src0_E_freeFrame : Z := 0x16770.
Definition src0_A_cgif_close : Z := 0x16770.  Definition src0_E_cgif_close : Z := 0x16838.
Definition src0_A_cgif_raw_newgif : Z := 0x16838.  Definition src0_E_cgif_raw_newgif : Z := 0x16aec.
Definition src0_A_cgif_raw_addframe : Z := 0x16aec.  Definition src0_E_cgif_raw_addframe : Z := 0x16f68.
Definition src0_A_LZW_GenerateStream : Z := 0x16f68.  Definition src0_E_LZW_GenerateStream : Z := 0x17508.
Definition src0_A_cgif_raw_close : Z := 0x17508.  Definition src0_E_cgif_raw_close : Z := 0x17568.
Definition src0_A_create_byte_list : Z := 0x17568.  Definition src0_E_create_byte_list : Z := 0x176e4.
Definition src0_A_create_byte_list_block : Z := 0x176e4.  Definition src0_E_create_byte_list_block : Z := 0x152a8.
Definition src0_A_init : Z := 0x152a8.  Definition src0_E_init : Z := 0x152ac.
Definition src0_A_init_libc : Z := 0x152ac.  Definition src0_E_init_libc : Z := 0x154d8.
Definition src0_A_libc_start_init : Z := 0x154d8.  Definition src0_E_libc_start_init : Z := 0x15524.
Definition src0_A_libc_start_main : Z := 0x15524.  Definition src0_E_libc_start_main : Z := 0x15584.
Definition src0_A_libc_start_main_stage2 : Z := 0x15584.  Definition src0_E_libc_start_main_stage2 : Z := 0x155cc.
Definition src0_A_init_tls : Z := 0x155cc.  Definition src0_E_init_tls : Z := 0x1587c.
Definition src0_A_funcs_on_exit : Z := 0x1592c.  Definition src0_E_funcs_on_exit : Z := 0x159f4.
Definition src0_A_cxa_finalize : Z := 0x159f4.  Definition src0_E_cxa_finalize : Z := 0x159f8.
Definition src0_A_atexit : Z := 0x159f8.  Definition src0_E_atexit : Z := 0x15abc.
Definition src0_A_atexit_call : Z := 0x15abc.  Definition src0_E_atexit_call : Z := 0x15ac0.
Definition src0_A_fini : Z := 0x15ac0.  Definition src0_E_fini : Z := 0x15ac4.
Definition src0_A_libc_exit_fini : Z := 0x15ac4.  Definition src0_E_libc_exit_fini : Z := 0x15b10.
Definition src0_A_exit : Z := 0x15b10.  Definition src0_E_exit : Z := 0x15b84.
Definition src0_A_Exit : Z := 0x15910.  Definition src0_E_Exit : Z := 0x1592c.
Definition src0_A_open : Z := 0x15b84.  Definition src0_E_open : Z := 0x15c68.
Definition src0_A_init_ssp : Z := 0x15c68.  Definition src0_E_init_ssp : Z := 0x15cc8.
Definition src0_A_stack_chk_fail : Z := 0x15cc8.  Definition src0_E_stack_chk_fail : Z := 0x15cd0.
Definition src0_A_syscall_ret : Z := 0x15cd0.  Definition src0_E_syscall_ret : Z := 0x15d08.
Definition src0_A_errno_location : Z := 0x15d08.  Definition src0_E_errno_location : Z := 0x15d14.
Definition src0_A_free : Z := 0x15d14.  Definition src0_E_free : Z := 0x15d18.
Definition src0_A_libc_calloc : Z := 0x15d18.  Definition src0_E_libc_calloc : Z := 0x15e50.
Definition src0_A_libc_malloc : Z := 0x15e50.  Definition src0_E_libc_malloc : Z := 0x15e54.
Definition src0_A_malloc : Z := 0x15e54.  Definition src0_E_malloc : Z := 0x15e58.
Definition src0_A_libc_free : Z := 0x15e58.  Definition src0_E_libc_free : Z := 0x16024.
Definition src0_A_get_meta : Z := 0x16024.  Definition src0_E_get_meta : Z := 0x16134.
Definition src0_A_nontrivial_free : Z := 0x16134.  Definition src0_E_nontrivial_free : Z := 0x1650c.
Definition src0_A_alloc_meta : Z := 0x1650c.  Definition src0_E_alloc_meta : Z := 0x167e4.
Definition src0_A_libc_malloc_impl : Z := 0x167e4.  Definition src0_E_libc_malloc_impl : Z := 0x16b54.
Definition src0_A_alloc_slot : Z := 0x16b54.  Definition src0_E_alloc_slot : Z := 0x173f8.
Definition src0_A_enframe : Z := 0x173f8.  Definition src0_E_enframe : Z := 0x17548.
Definition src0_A_malloc_allzerop : Z := 0x17548.  Definition src0_E_malloc_allzerop : Z := 0x176c0.
Definition src0_A_vm_wait : Z := 0x176c0.  Definition src0_E_vm_wait : Z := 0x176c4.
Definition src0_A_mmap : Z := 0x176c4.  Definition src0_E_mmap : Z := 0x177b0.
Definition src0_A_mprotect : Z := 0x177b0.  Definition src0_E_mprotect : Z := 0x177f8.
Definition src0_A_munmap : Z := 0x177f8.  Definition src0_E_munmap : Z := 0x17840.
Definition src0_A_unlist_locked_file : Z := 0x17850.  Definition src0_E_unlist_locked_file : Z := 0x17854.
Definition src0_A_fclose : Z := 0x17854.  Definition src0_E_fclose : Z := 0x17914.
Definition src0_A_fflush : Z := 0x17914.  Definition src0_E_fflush : Z := 0x17a84.
Definition src0_A_lockfile : Z := 0x17a84.  Definition src0_E_lockfile : Z := 0x17b80.
Definition src0_A_unlockfile : Z := 0x17b80.  Definition src0_E_unlockfile : Z := 0x17be0.
Definition src0_A_fopen : Z := 0x17bec.  Definition src0_E_fopen : Z := 0x17cc8.
Definition src0_A_fmodeflags : Z := 0x17cc8.  Definition src0_E_fmodeflags : Z := 0x17d7c.
Definition src0_A_fdopen : Z := 0x17d7c.  Definition src0_E_fdopen : Z := 0x17f54.
Definition src0_A_stdio_write : Z := 0x18098.  Definition src0_E_stdio_write : Z := 0x18228.
Definition src0_A_aio_close : Z := 0x18068.  Definition src0_E_aio_close : Z := 0x1806c.
Definition src0_A_stdio_close : Z := 0x1806c.  Definition src0_E_stdio_close : Z := 0x18098.
Definition src0_A_fprintf : Z := 0x17be0.  Definition src0_E_fprintf : Z := 0x17c44.
Definition src0_A_fwritex : Z := 0x17c44.  Definition src0_E_fwritex : Z := 0x17d7c.
Definition src0_A_fwrite : Z := 0x17d7c.  Definition src0_E_fwrite : Z := 0x17e34.
Definition src0_A_towrite : Z := 0x17e34.  Definition src0_E_towrite : Z := 0x17e88.
Definition src0_A_stdio_exit : Z := 0x17e88.  Definition src0_E_stdio_exit : Z := 0x1802c.
Definition src0_A_ofl_lock : Z := 0x1802c.  Definition src0_E_ofl_lock : Z := 0x1805c.
Definition src0_A_ofl_unlock : Z := 0x1805c.  Definition src0_E_ofl_unlock : Z := 0x18068.
Definition src0_A_ofl_add : Z := 0x186bc.  Definition src0_E_ofl_add : Z := 0x18230.
Definition src0_A_stdout_write : Z := 0x18230.  Definition src0_E_stdout_write : Z := 0x182d0.
Definition src0_A_vfprintf : Z := 0x182d0.  Definition src0_E_vfprintf : Z := 0x18480.
Definition src0_A_printf_core : Z := 0x18480.  Definition src0_E_printf_core : Z := 0x192b0.
Definition src0_A_pop_arg : Z := 0x192b0.  Definition src0_E_pop_arg : Z := 0x193e4.
Definition src0_A_pad : Z := 0x193e4.  Definition src0_E_pad : Z := 0x194b8.
Definition src0_A_fmt_fp : Z := 0x194b8.  Definition src0_E_fmt_fp : Z := 0x1ab80.
Definition src0_A_strerror : Z := 0x1ab80.  Definition src0_E_strerror : Z := 0x1abbc.
Definition src0_A_lctrans_impl : Z := 0x1abbc.  Definition src0_E_lctrans_impl : Z := 0x1abc0.
Definition src0_A_lctrans : Z := 0x1abc0.  Definition src0_E_lctrans : Z := 0x1abc4.
Definition src0_A_wctomb : Z := 0x1abc4.  Definition src0_E_wctomb : Z := 0x1abe8.
Definition src0_A_wcrtomb : Z := 0x1abe8.  Definition src0_E_wcrtomb : Z := 0x1ad14.
Definition src0_A_extenddftf2 : Z := 0x1ad14.  Definition src0_E_extenddftf2 : Z := 0x1aea4.
Definition src0_A_signbitl : Z := 0x1aea4.  Definition src0_E_signbitl : Z := 0x1aeac.
Definition src0_A_fpclassifyl : Z := 0x1aeac.  Definition src0_E_fpclassifyl : Z := 0x1aef0.
Definition src0_A_frexpl : Z := 0x1aef0.  Definition src0_E_frexpl : Z := 0x1afc8.
Definition src0_A_letf2 : Z := 0x1468c.  Definition src0_E_letf2 : Z := 0x14754.
Definition src0_A_multf3 : Z := 0x1afc8.  Definition src0_E_multf3 : Z := 0x1b6c8.
Definition src0_A_floatsitf : Z := 0x1b6c8.  Definition src0_E_floatsitf : Z := 0x1b7d0.
Definition src0_A_scalbn : Z := 0x1b7d0.  Definition src0_E_scalbn : Z := 0x1b868.
Definition src0_A_subtf3 : Z := 0x14a90.  Definition src0_E_subtf3 : Z := 0x14aa0.
Definition src0_A_addtf3 : Z := 0x14aa0.  Definition src0_E_addtf3 : Z := 0x1526c.
Definition src0_A_fe_getround : Z := 0x1526c.  Definition src0_E_fe_getround : Z := 0x1529c.
Definition src0_A_fe_raise_inexact : Z := 0x1529c.  Definition src0_E_fe_raise_inexact : Z := 0x152a8.
Definition src0_A_fixunstfsi : Z := 0x1b868.  Definition src0_E_fixunstfsi : Z := 0x1b8fc.
Definition src0_A_floatunsitf : Z := 0x1b8fc.  Definition src0_E_floatunsitf : Z := 0x1b9e8.
Definition src0_A_fixtfsi : Z := 0x1b9e8.  Definition src0_E_fixtfsi : Z := 0x1ba90.
Definition src0_A_divtf3 : Z := 0x1ba90.  Definition src0_E_divtf3 : Z := 0x1c394.
Definition src0_A_vprintf : Z := 0x1c394.  Definition src0_E_vprintf : Z := 0x1c3b0.
Definition src0_A_bcmp : Z := 0x1c87c.  Definition src0_E_bcmp : Z := 0x1c880.
Definition src0_A_memcmp : Z := 0x1c880.  Definition src0_E_memcmp : Z := 0x1c3b0.
Definition src0_A_memcpy : Z := 0x1c3b0.  Definition src0_E_memcpy : Z := 0x1c7b4.
Definition src0_A_memset : Z := 0x1c7b4.  Definition src0_E_memset : Z := 0x1c8ac.
Definition src0_A_strchr : Z := 0x1f3e4.  Definition src0_E_strchr : Z := 0x1f420.
Definition src0_A_strchrnul : Z := 0x1f420.  Definition src0_E_strchrnul : Z := 0x1f500.
Definition src0_A_strlen : Z := 0x1c8e4.  Definition src0_E_strlen : Z := 0x1c974.
Definition src0_A_strnlen : Z := 0x1c974.  Definition src0_E_strnlen : Z := 0x1c9b8.
Definition src0_A_memchr : Z := 0x1c9b8.  Definition src0_E_memchr : Z := 0x1ca84.
Definition src0_A_lock : Z := 0x1ca84.  Definition src0_E_lock : Z := 0x1cd0c.
Definition src0_A_unlock : Z := 0x1cd0c.  Definition src0_E_unlock : Z := 0x1cd80.
Definition src0_A_syscall_cp_c : Z := 0x1cd80.  Definition src0_E_syscall_cp_c : Z := 0x1cda4.
Definition src0_A_syscall_cp : Z := 0x1cda4.  Definition src0_E_syscall_cp : Z := 0x1cda8.
Definition src0_A_set_thread_area : Z := 0x1cda8.  Definition src0_E_set_thread_area : Z := 0x1cdb4.
Definition src0_A_unistd_exit : Z := 0x1cdb4.  Definition src0_E_unistd_exit : Z := 0x1cdc0.
Definition src0_A_close : Z := 0x1cdc0.  Definition src0_E_close : Z := 0x1ce14.
Definition src0_A_lseek : Z := 0x1ce14.  Definition src0_E_lseek : Z := 0x1ce20.
Definition src0_A_read : Z := 0x1ce20.  Definition src0_E_read : Z := 0x1ce54.
Definition src0_A_unlink : Z := 0x1fa70.  Definition src0_E_unlink : Z := 0x1faa0.
Definition src0_D_str_n0X0x : Z := 0x102ae.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10316.
Definition src0_D_str_d_n : Z := 0x1032a.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10350.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10361.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10399.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x1040c.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10421.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10464.
Definition src0_D_str_dev_null : Z := 0x104a9.
Definition src0_D_str_null : Z := 0x104b3.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x104e8.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x104f8.
Definition src0_D_debruijn32 : Z := 0x106a8.
Definition src0_D_size_classes : Z := 0x106c8.
Definition src0_D_small_cnt_tab : Z := 0x10728.
Definition src0_D_med_cnt_tab : Z := 0x10743.
Definition src0_D_states : Z := 0x108a0.
Definition src0_D_xdigits : Z := 0x105e8.
Definition src0_D_errmsgstr : Z := 0x10a70.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11218.
Definition src0_D_fe_getround : Z := 0x10640.
Definition src0_D_EH_FRAME_LIST : Z := 0x11440.
Definition src0_D_init_array_start : Z := 0x1de58.
Definition src0_D_fini_array_start : Z := 0x1de60.
Definition src0_D_stderr : Z := 0x1df20.
Definition src0_D_stdout : Z := 0x1df28.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1df30.
Definition src0_D_got_DYNAMIC : Z := 0x1df38.
Definition src0_D_got_main : Z := 0x1df40.
Definition src0_D_got_init : Z := 0x1df48.
Definition src0_D_got_fini : Z := 0x1df50.
Definition src0_D_got_register_frame_info : Z := 0x1df58.
Definition src0_D_got_cxa_finalize : Z := 0x1df60.
Definition src0_D_got_deregister_frame_info : Z := 0x1df68.
Definition src0_D_got_stderr : Z := 0x1df70.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1df78.
Definition src0_D_got_stdout : Z := 0x1df80.
Definition src0_D_got_environ : Z := 0x1df88.
Definition src0_D_got_progname_full : Z := 0x1df90.
Definition src0_D_got_progname : Z := 0x1df98.
Definition src0_D_got_init_array_end : Z := 0x1dfa0.
Definition src0_D_got_init_array_start : Z := 0x1dfa8.
Definition src0_D_got_stack_chk_guard : Z := 0x1dfb0.
Definition src0_D_got_fini_array_end : Z := 0x1dfb8.
Definition src0_D_got_fini_array_start : Z := 0x1dfc0.
Definition src0_D_dso_handle : Z := 0x1efc8.
Definition src0_D_aef_argc : Z := 0x1efd8.
Definition src0_D_stderr_FILE : Z := 0x1eff0.
Definition src0_D_stderr_used : Z := 0x1f0d8.
Definition src0_D_stdout_FILE : Z := 0x1f0e0.
Definition src0_D_stdout_used : Z := 0x1f1c8.
Definition src0_D_default_stacksize : Z := 0x1f1d0.
Definition src0_D_do_init_initialized : Z := 0x1f1e0.
Definition src0_D_do_init_object : Z := 0x1f1e8.
Definition src0_D_do_fini_finalized : Z := 0x1f228.
Definition src0_D_read_stage : Z := 0x1f229.
Definition src0_D_target_run_initialized : Z := 0x2f230.
Definition src0_D_aef_in_callback : Z := 0x2f234.
Definition src0_D_aef_aligned_copy_empty : Z := 0x2f240.
Definition src0_D_environ : Z := 0x2f260.
Definition src0_D_thread_list_lock : Z := 0x4f338.
Definition src0_D_main_tls : Z := 0x4f340.
Definition src0_D_builtin_tls : Z := 0x2f268.
Definition src0_D_finished_atexit : Z := 0x4f378.
Definition src0_D_atexit_lock : Z := 0x4f37c.
Definition src0_D_atexit_slot : Z := 0x4f380.
Definition src0_D_atexit_head : Z := 0x4f388.
Definition src0_D_atexit_builtin : Z := 0x4f390.
Definition src0_D_exit_exit_lock : Z := 0x4f598.
Definition src0_D_stack_chk_guard : Z := 0x4f5a0.
Definition src0_D_sysinfo : Z := 0x4f5a8.
Definition src0_D_progname : Z := 0x4f5b0.
Definition src0_D_progname_full : Z := 0x4f5b8.
Definition src0_D_libc : Z := 0x4f5c0.
Definition src0_D_hwcap : Z := 0x4f628.
Definition src0_D_malloc_lock : Z := 0x4f630.
Definition src0_D_malloc_context : Z := 0x4f638.
Definition src0_D_malloc_replaced : Z := 0x4f9d8.
Definition src0_D_stdin_used : Z := 0x4f9e0.
Definition src0_D_ofl_lock : Z := 0x4f9e8.
Definition src0_D_ofl_head : Z := 0x4f9f0.
Definition src0_D_stderr_buf : Z := 0x4f9f8.
Definition src0_D_stdout_buf : Z := 0x4fa00.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
