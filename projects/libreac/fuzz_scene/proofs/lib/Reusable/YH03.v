(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x148ac.  Definition src0_text_hi : Z := 0x1dee4.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x133bc.
Definition src0_eh_frame_lo : Z := 0x134a8.  Definition src0_eh_frame_hi : Z := 0x138ac.
Definition src0_init_array_lo : Z := 0x1eee8.  Definition src0_init_array_hi : Z := 0x1eef0.
Definition src0_fini_array_lo : Z := 0x1eef0.  Definition src0_fini_array_hi : Z := 0x1eef8.
Definition src0_data_rel_ro_lo : Z := 0x1eef8.  Definition src0_data_rel_ro_hi : Z := 0x1ef08.
Definition src0_got_lo : Z := 0x1ef08.  Definition src0_got_hi : Z := 0x1efa8.
Definition src0_data_lo : Z := 0x1ffa8.  Definition src0_data_hi : Z := 0x201b4.
Definition src0_bss_lo : Z := 0x201c0.  Definition src0_bss_hi : Z := 0x50de8.
Definition src0_A_do_init : Z := 0x148f4.  Definition src0_E_do_init : Z := 0x14968.
Definition src0_A_do_fini : Z := 0x14968.  Definition src0_E_do_fini : Z := 0x149f8.
Definition src0_A_main : Z := 0x149f8.  Definition src0_E_main : Z := 0x14cbc.
Definition src0_A_target_alloc_init : Z := 0x14cbc.  Definition src0_E_target_alloc_init : Z := 0x14cc0.
Definition src0_A_target_alloc_count : Z := 0x14cc0.  Definition src0_E_target_alloc_count : Z := 0x14cc8.
Definition src0_A_target_run : Z := 0x14cc8.  Definition src0_E_target_run : Z := 0x14e20.
Definition src0_A_aef_exit_guard : Z := 0x14e20.  Definition src0_E_aef_exit_guard : Z := 0x14e50.
Definition src0_A_emit_printf : Z := 0x14e50.  Definition src0_E_emit_printf : Z := 0x14e98.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x14e98.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x153ec.
Definition src0_A_init : Z := 0x15aec.  Definition src0_E_init : Z := 0x15af0.
Definition src0_A_init_libc : Z := 0x15af0.  Definition src0_E_init_libc : Z := 0x15d1c.
Definition src0_A_libc_start_init : Z := 0x15d1c.  Definition src0_E_libc_start_init : Z := 0x15d68.
Definition src0_A_libc_start_main : Z := 0x15d68.  Definition src0_E_libc_start_main : Z := 0x15dc8.
Definition src0_A_libc_start_main_stage2 : Z := 0x15dc8.  Definition src0_E_libc_start_main_stage2 : Z := 0x15e10.
Definition src0_A_init_tls : Z := 0x15e10.  Definition src0_E_init_tls : Z := 0x160c0.
Definition src0_A_funcs_on_exit : Z := 0x16170.  Definition src0_E_funcs_on_exit : Z := 0x16238.
Definition src0_A_cxa_finalize : Z := 0x16238.  Definition src0_E_cxa_finalize : Z := 0x1623c.
Definition src0_A_atexit : Z := 0x1623c.  Definition src0_E_atexit : Z := 0x16300.
Definition src0_A_atexit_call : Z := 0x16300.  Definition src0_E_atexit_call : Z := 0x16304.
Definition src0_A_fini : Z := 0x16304.  Definition src0_E_fini : Z := 0x16308.
Definition src0_A_libc_exit_fini : Z := 0x16308.  Definition src0_E_libc_exit_fini : Z := 0x16354.
Definition src0_A_exit : Z := 0x16354.  Definition src0_E_exit : Z := 0x163c8.
Definition src0_A_Exit : Z := 0x16154.  Definition src0_E_Exit : Z := 0x16170.
Definition src0_A_open : Z := 0x163c8.  Definition src0_E_open : Z := 0x164ac.
Definition src0_A_init_ssp : Z := 0x164ac.  Definition src0_E_init_ssp : Z := 0x1650c.
Definition src0_A_stack_chk_fail : Z := 0x1650c.  Definition src0_E_stack_chk_fail : Z := 0x16514.
Definition src0_A_syscall_ret : Z := 0x16514.  Definition src0_E_syscall_ret : Z := 0x1654c.
Definition src0_A_errno_location : Z := 0x1654c.  Definition src0_E_errno_location : Z := 0x16558.
Definition src0_A_free : Z := 0x16558.  Definition src0_E_free : Z := 0x1655c.
Definition src0_A_libc_calloc : Z := 0x1655c.  Definition src0_E_libc_calloc : Z := 0x16694.
Definition src0_A_libc_malloc : Z := 0x16694.  Definition src0_E_libc_malloc : Z := 0x16698.
Definition src0_A_malloc : Z := 0x16698.  Definition src0_E_malloc : Z := 0x1669c.
Definition src0_A_libc_free : Z := 0x1669c.  Definition src0_E_libc_free : Z := 0x16868.
Definition src0_A_get_meta : Z := 0x16868.  Definition src0_E_get_meta : Z := 0x16978.
Definition src0_A_nontrivial_free : Z := 0x16978.  Definition src0_E_nontrivial_free : Z := 0x16d50.
Definition src0_A_alloc_meta : Z := 0x16d50.  Definition src0_E_alloc_meta : Z := 0x17028.
Definition src0_A_libc_malloc_impl : Z := 0x17028.  Definition src0_E_libc_malloc_impl : Z := 0x17398.
Definition src0_A_alloc_slot : Z := 0x17398.  Definition src0_E_alloc_slot : Z := 0x17c3c.
Definition src0_A_enframe : Z := 0x17c3c.  Definition src0_E_enframe : Z := 0x17d8c.
Definition src0_A_malloc_allzerop : Z := 0x17d8c.  Definition src0_E_malloc_allzerop : Z := 0x17f04.
Definition src0_A_vm_wait : Z := 0x17f04.  Definition src0_E_vm_wait : Z := 0x17f08.
Definition src0_A_mmap : Z := 0x17f08.  Definition src0_E_mmap : Z := 0x17ff4.
Definition src0_A_mprotect : Z := 0x17ff4.  Definition src0_E_mprotect : Z := 0x1803c.
Definition src0_A_munmap : Z := 0x1803c.  Definition src0_E_munmap : Z := 0x18084.
Definition src0_A_fflush : Z := 0x18158.  Definition src0_E_fflush : Z := 0x182c8.
Definition src0_A_lockfile : Z := 0x182c8.  Definition src0_E_lockfile : Z := 0x183c4.
Definition src0_A_unlockfile : Z := 0x183c4.  Definition src0_E_unlockfile : Z := 0x18424.
Definition src0_A_stdio_write : Z := 0x188dc.  Definition src0_E_stdio_write : Z := 0x18a6c.
Definition src0_A_stdio_seek : Z := 0x18a6c.  Definition src0_E_stdio_seek : Z := 0x18a74.
Definition src0_A_aio_close : Z := 0x188ac.  Definition src0_E_aio_close : Z := 0x188b0.
Definition src0_A_stdio_close : Z := 0x188b0.  Definition src0_E_stdio_close : Z := 0x188dc.
Definition src0_A_fprintf : Z := 0x18424.  Definition src0_E_fprintf : Z := 0x18488.
Definition src0_A_fwritex : Z := 0x18488.  Definition src0_E_fwritex : Z := 0x185c0.
Definition src0_A_fwrite : Z := 0x185c0.  Definition src0_E_fwrite : Z := 0x18678.
Definition src0_A_towrite : Z := 0x18678.  Definition src0_E_towrite : Z := 0x186cc.
Definition src0_A_stdio_exit : Z := 0x186cc.  Definition src0_E_stdio_exit : Z := 0x18870.
Definition src0_A_ofl_lock : Z := 0x18870.  Definition src0_E_ofl_lock : Z := 0x188a0.
Definition src0_A_ofl_unlock : Z := 0x188a0.  Definition src0_E_ofl_unlock : Z := 0x188ac.
Definition src0_A_stdout_write : Z := 0x18a74.  Definition src0_E_stdout_write : Z := 0x18b14.
Definition src0_A_vfprintf : Z := 0x18b14.  Definition src0_E_vfprintf : Z := 0x18cc4.
Definition src0_A_printf_core : Z := 0x18cc4.  Definition src0_E_printf_core : Z := 0x19af4.
Definition src0_A_pop_arg : Z := 0x19af4.  Definition src0_E_pop_arg : Z := 0x19c28.
Definition src0_A_pad : Z := 0x19c28.  Definition src0_E_pad : Z := 0x19cfc.
Definition src0_A_fmt_fp : Z := 0x19cfc.  Definition src0_E_fmt_fp : Z := 0x1b3c4.
Definition src0_A_strerror : Z := 0x1b3c4.  Definition src0_E_strerror : Z := 0x1b400.
Definition src0_A_lctrans_impl : Z := 0x1b400.  Definition src0_E_lctrans_impl : Z := 0x1b404.
Definition src0_A_lctrans : Z := 0x1b404.  Definition src0_E_lctrans : Z := 0x1b408.
Definition src0_A_wctomb : Z := 0x1b408.  Definition src0_E_wctomb : Z := 0x1b42c.
Definition src0_A_wcrtomb : Z := 0x1b42c.  Definition src0_E_wcrtomb : Z := 0x1b558.
Definition src0_A_extenddftf2 : Z := 0x1b558.  Definition src0_E_extenddftf2 : Z := 0x1b6e8.
Definition src0_A_signbitl : Z := 0x1b6e8.  Definition src0_E_signbitl : Z := 0x1b6f0.
Definition src0_A_fpclassifyl : Z := 0x1b6f0.  Definition src0_E_fpclassifyl : Z := 0x1b734.
Definition src0_A_frexpl : Z := 0x1b734.  Definition src0_E_frexpl : Z := 0x1b80c.
Definition src0_A_letf2 : Z := 0x1b80c.  Definition src0_E_letf2 : Z := 0x1b8d4.
Definition src0_A_multf3 : Z := 0x1b8d4.  Definition src0_E_multf3 : Z := 0x1bfd4.
Definition src0_A_floatsitf : Z := 0x1bfd4.  Definition src0_E_floatsitf : Z := 0x1c0dc.
Definition src0_A_scalbn : Z := 0x1c0dc.  Definition src0_E_scalbn : Z := 0x1c174.
Definition src0_A_subtf3 : Z := 0x1c174.  Definition src0_E_subtf3 : Z := 0x1c184.
Definition src0_A_addtf3 : Z := 0x1c184.  Definition src0_E_addtf3 : Z := 0x1c950.
Definition src0_A_fe_getround : Z := 0x1c950.  Definition src0_E_fe_getround : Z := 0x1c980.
Definition src0_A_fe_raise_inexact : Z := 0x1c980.  Definition src0_E_fe_raise_inexact : Z := 0x1c98c.
Definition src0_A_fixunstfsi : Z := 0x1c98c.  Definition src0_E_fixunstfsi : Z := 0x1ca20.
Definition src0_A_floatunsitf : Z := 0x1ca20.  Definition src0_E_floatunsitf : Z := 0x1cb0c.
Definition src0_A_fixtfsi : Z := 0x1cb0c.  Definition src0_E_fixtfsi : Z := 0x1cbb4.
Definition src0_A_divtf3 : Z := 0x1cbb4.  Definition src0_E_divtf3 : Z := 0x1d4b8.
Definition src0_A_vprintf : Z := 0x1d4b8.  Definition src0_E_vprintf : Z := 0x1d4d4.
Definition src0_A_bcmp : Z := 0x1d4d4.  Definition src0_E_bcmp : Z := 0x1d4d8.
Definition src0_A_memcmp : Z := 0x1d4d8.  Definition src0_E_memcmp : Z := 0x1d508.
Definition src0_A_memcpy : Z := 0x1d508.  Definition src0_E_memcpy : Z := 0x1d90c.
Definition src0_A_memset : Z := 0x1d90c.  Definition src0_E_memset : Z := 0x1da04.
Definition src0_A_strnlen : Z := 0x1da04.  Definition src0_E_strnlen : Z := 0x1da48.
Definition src0_A_memchr : Z := 0x1da48.  Definition src0_E_memchr : Z := 0x1db14.
Definition src0_A_lock : Z := 0x1db14.  Definition src0_E_lock : Z := 0x1dd9c.
Definition src0_A_unlock : Z := 0x1dd9c.  Definition src0_E_unlock : Z := 0x1de10.
Definition src0_A_syscall_cp_c : Z := 0x1de10.  Definition src0_E_syscall_cp_c : Z := 0x1de34.
Definition src0_A_syscall_cp : Z := 0x1de34.  Definition src0_E_syscall_cp : Z := 0x1de38.
Definition src0_A_unistd_exit : Z := 0x1de44.  Definition src0_E_unistd_exit : Z := 0x1de50.
Definition src0_A_close : Z := 0x1de50.  Definition src0_E_close : Z := 0x1dea4.
Definition src0_A_lseek : Z := 0x1dea4.  Definition src0_E_lseek : Z := 0x1deb0.
Definition src0_A_read : Z := 0x1deb0.  Definition src0_E_read : Z := 0x1dee4.
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
Definition src0_D_str_NAN : Z := 0x1035d.
Definition src0_D_str_nan : Z := 0x10361.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x10365.
Definition src0_D_str_dev_null : Z := 0x10385.
Definition src0_D_str_null : Z := 0x1038f.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x128e0.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x128f0.
Definition src0_D_debruijn32 : Z := 0x126d2.
Definition src0_D_size_classes : Z := 0x126f2.
Definition src0_D_small_cnt_tab : Z := 0x12752.
Definition src0_D_med_cnt_tab : Z := 0x1276d.
Definition src0_D_states : Z := 0x12920.
Definition src0_D_xdigits : Z := 0x12af0.
Definition src0_D_errmsgstr : Z := 0x12b00.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x132a8.
Definition src0_D_fe_getround : Z := 0x133b0.
Definition src0_D_EH_FRAME_LIST : Z := 0x134a8.
Definition src0_D_init_array_start : Z := 0x1eee8.
Definition src0_D_fini_array_start : Z := 0x1eef0.
Definition src0_D_stderr : Z := 0x1eef8.
Definition src0_D_stdout : Z := 0x1ef00.
Definition src0_D_got_DYNAMIC : Z := 0x1ef10.
Definition src0_D_got_main : Z := 0x1ef18.
Definition src0_D_got_init : Z := 0x1ef20.
Definition src0_D_got_fini : Z := 0x1ef28.
Definition src0_D_got_register_frame_info : Z := 0x1ef30.
Definition src0_D_got_cxa_finalize : Z := 0x1ef38.
Definition src0_D_got_deregister_frame_info : Z := 0x1ef40.
Definition src0_D_got_stderr : Z := 0x1ef48.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1ef50.
Definition src0_D_got_stdout : Z := 0x1ef58.
Definition src0_D_got_environ : Z := 0x1ef68.
Definition src0_D_got_progname_full : Z := 0x1ef70.
Definition src0_D_got_progname : Z := 0x1ef78.
Definition src0_D_got_init_array_end : Z := 0x1ef80.
Definition src0_D_got_init_array_start : Z := 0x1ef88.
Definition src0_D_got_stack_chk_guard : Z := 0x1ef90.
Definition src0_D_got_fini_array_end : Z := 0x1ef98.
Definition src0_D_got_fini_array_start : Z := 0x1efa0.
Definition src0_D_dso_handle : Z := 0x1ffa8.
Definition src0_D_aef_argc : Z := 0x1ffb8.
Definition src0_D_stderr_FILE : Z := 0x1ffd0.
Definition src0_D_stderr_used : Z := 0x200b8.
Definition src0_D_stdout_FILE : Z := 0x200c0.
Definition src0_D_stdout_used : Z := 0x201a8.
Definition src0_D_default_stacksize : Z := 0x201b0.
Definition src0_D_do_init_initialized : Z := 0x201c0.
Definition src0_D_do_init_object : Z := 0x201c8.
Definition src0_D_do_fini_finalized : Z := 0x20208.
Definition src0_D_read_stage : Z := 0x20209.
Definition src0_D_target_run_initialized : Z := 0x30210.
Definition src0_D_aef_in_callback : Z := 0x30214.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30220.
Definition src0_D_environ : Z := 0x30240.
Definition src0_D_thread_list_lock : Z := 0x50318.
Definition src0_D_main_tls : Z := 0x50320.
Definition src0_D_builtin_tls : Z := 0x30248.
Definition src0_D_finished_atexit : Z := 0x50358.
Definition src0_D_atexit_lock : Z := 0x5035c.
Definition src0_D_atexit_slot : Z := 0x50360.
Definition src0_D_atexit_head : Z := 0x50368.
Definition src0_D_atexit_builtin : Z := 0x50370.
Definition src0_D_exit_exit_lock : Z := 0x50578.
Definition src0_D_stack_chk_guard : Z := 0x50580.
Definition src0_D_sysinfo : Z := 0x50588.
Definition src0_D_progname : Z := 0x50590.
Definition src0_D_progname_full : Z := 0x50598.
Definition src0_D_libc : Z := 0x505a0.
Definition src0_D_hwcap : Z := 0x50608.
Definition src0_D_malloc_lock : Z := 0x50610.
Definition src0_D_malloc_context : Z := 0x50618.
Definition src0_D_malloc_replaced : Z := 0x509b8.
Definition src0_D_stdin_used : Z := 0x509c0.
Definition src0_D_ofl_lock : Z := 0x509c8.
Definition src0_D_ofl_head : Z := 0x509d0.
Definition src0_D_stderr_buf : Z := 0x509d8.
Definition src0_D_stdout_buf : Z := 0x509e0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 32.
