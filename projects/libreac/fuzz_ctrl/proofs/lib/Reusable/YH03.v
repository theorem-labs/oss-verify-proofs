(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10-29 (a Theorem Labs lane): every src0_* value below is re-read from fuzz_ctrl's OWN v1.9.0 plain build, the one projects/libreac/fuzz_ctrl/harness.yaml pins by sha256 c6512ced9ff6bea807fb67d79cdee1a9e30e7f0d18169594cc16487709eddf52; the values were read from that build's unstripped twin (internal path), which differs from the pinned file in 25 loaded bytes only - 5 in the ELF header (e_shoff, e_shnum, e_shstrndx) and the 20 of .note.gnu.build-id - and in no byte of .text, .rodata, .data, .got or .bss, so no value named here can differ; read from .symtab, .rodata or the dispatch instructions, never from a cgif label name and never by adding a delta. 54 definitions naming symbols, strings or constants that fuzz_ctrl does not have were removed. src0_A_stdio_read, src0_D_str_tmp_out_gif, src0_D_str_wb, src0_D_str_rwa and src0_D_str_3 also name nothing fuzz_ctrl has and were removed once the FILE sink became option-typed (sk_file := None in Reusable/YI5c.v:18). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12c0c.  Definition src0_text_hi : Z := 0x1dd20.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x1144c.
Definition src0_eh_frame_lo : Z := 0x115b8.  Definition src0_eh_frame_hi : Z := 0x11c0c.
Definition src0_init_array_lo : Z := 0x1ed20.  Definition src0_init_array_hi : Z := 0x1ed28.
Definition src0_fini_array_lo : Z := 0x1ed28.  Definition src0_fini_array_hi : Z := 0x1ed30.
Definition src0_data_rel_ro_lo : Z := 0x1ed30.  Definition src0_data_rel_ro_hi : Z := 0x1fb00.
Definition src0_got_lo : Z := 0x1fb00.  Definition src0_got_hi : Z := 0x1fb98.
Definition src0_data_lo : Z := 0x20b98.  Definition src0_data_hi : Z := 0x20da4.
Definition src0_bss_lo : Z := 0x20db0.  Definition src0_bss_hi : Z := 0x519d8.
Definition src0_A_do_init : Z := 0x12c54.  Definition src0_E_do_init : Z := 0x12cc8.
Definition src0_A_do_fini : Z := 0x12cc8.  Definition src0_E_do_fini : Z := 0x12d58.
Definition src0_A_main : Z := 0x12d58.  Definition src0_E_main : Z := 0x1301c.
Definition src0_A_target_alloc_init : Z := 0x1301c.  Definition src0_E_target_alloc_init : Z := 0x13020.
Definition src0_A_target_alloc_count : Z := 0x13020.  Definition src0_E_target_alloc_count : Z := 0x13028.
Definition src0_A_target_run : Z := 0x13028.  Definition src0_E_target_run : Z := 0x13180.
Definition src0_A_aef_exit_guard : Z := 0x13180.  Definition src0_E_aef_exit_guard : Z := 0x131b0.
Definition src0_A_emit_printf : Z := 0x131b0.  Definition src0_E_emit_printf : Z := 0x131f8.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x131f8.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x13e1c.
Definition src0_A_init : Z := 0x158f0.  Definition src0_E_init : Z := 0x158f4.
Definition src0_A_init_libc : Z := 0x158f4.  Definition src0_E_init_libc : Z := 0x15b20.
Definition src0_A_libc_start_init : Z := 0x15b20.  Definition src0_E_libc_start_init : Z := 0x15b6c.
Definition src0_A_libc_start_main : Z := 0x15b6c.  Definition src0_E_libc_start_main : Z := 0x15bcc.
Definition src0_A_libc_start_main_stage2 : Z := 0x15bcc.  Definition src0_E_libc_start_main_stage2 : Z := 0x15c14.
Definition src0_A_init_tls : Z := 0x15c14.  Definition src0_E_init_tls : Z := 0x15ec4.
Definition src0_A_funcs_on_exit : Z := 0x15f74.  Definition src0_E_funcs_on_exit : Z := 0x1603c.
Definition src0_A_cxa_finalize : Z := 0x1603c.  Definition src0_E_cxa_finalize : Z := 0x16040.
Definition src0_A_atexit : Z := 0x16040.  Definition src0_E_atexit : Z := 0x16104.
Definition src0_A_atexit_call : Z := 0x16104.  Definition src0_E_atexit_call : Z := 0x16108.
Definition src0_A_fini : Z := 0x16108.  Definition src0_E_fini : Z := 0x1610c.
Definition src0_A_libc_exit_fini : Z := 0x1610c.  Definition src0_E_libc_exit_fini : Z := 0x16158.
Definition src0_A_exit : Z := 0x16158.  Definition src0_E_exit : Z := 0x161cc.
Definition src0_A_Exit : Z := 0x15f58.  Definition src0_E_Exit : Z := 0x15f74.
Definition src0_A_open : Z := 0x161cc.  Definition src0_E_open : Z := 0x162b0.
Definition src0_A_init_ssp : Z := 0x162b0.  Definition src0_E_init_ssp : Z := 0x16310.
Definition src0_A_stack_chk_fail : Z := 0x16310.  Definition src0_E_stack_chk_fail : Z := 0x16318.
Definition src0_A_syscall_ret : Z := 0x16318.  Definition src0_E_syscall_ret : Z := 0x16350.
Definition src0_A_errno_location : Z := 0x16350.  Definition src0_E_errno_location : Z := 0x1635c.
Definition src0_A_free : Z := 0x1635c.  Definition src0_E_free : Z := 0x16360.
Definition src0_A_libc_calloc : Z := 0x16360.  Definition src0_E_libc_calloc : Z := 0x16498.
Definition src0_A_libc_malloc : Z := 0x16498.  Definition src0_E_libc_malloc : Z := 0x1649c.
Definition src0_A_malloc : Z := 0x1649c.  Definition src0_E_malloc : Z := 0x164a0.
Definition src0_A_libc_free : Z := 0x164a0.  Definition src0_E_libc_free : Z := 0x1666c.
Definition src0_A_get_meta : Z := 0x1666c.  Definition src0_E_get_meta : Z := 0x1677c.
Definition src0_A_nontrivial_free : Z := 0x1677c.  Definition src0_E_nontrivial_free : Z := 0x16b54.
Definition src0_A_alloc_meta : Z := 0x16b54.  Definition src0_E_alloc_meta : Z := 0x16e2c.
Definition src0_A_libc_malloc_impl : Z := 0x16e2c.  Definition src0_E_libc_malloc_impl : Z := 0x1719c.
Definition src0_A_alloc_slot : Z := 0x1719c.  Definition src0_E_alloc_slot : Z := 0x17a40.
Definition src0_A_enframe : Z := 0x17a40.  Definition src0_E_enframe : Z := 0x17b90.
Definition src0_A_malloc_allzerop : Z := 0x17b90.  Definition src0_E_malloc_allzerop : Z := 0x17d08.
Definition src0_A_vm_wait : Z := 0x17d08.  Definition src0_E_vm_wait : Z := 0x17d0c.
Definition src0_A_mmap : Z := 0x17d0c.  Definition src0_E_mmap : Z := 0x17df8.
Definition src0_A_mprotect : Z := 0x17df8.  Definition src0_E_mprotect : Z := 0x17e40.
Definition src0_A_munmap : Z := 0x17e40.  Definition src0_E_munmap : Z := 0x17e88.
Definition src0_A_fflush : Z := 0x17f5c.  Definition src0_E_fflush : Z := 0x180cc.
Definition src0_A_lockfile : Z := 0x180cc.  Definition src0_E_lockfile : Z := 0x181c8.
Definition src0_A_unlockfile : Z := 0x181c8.  Definition src0_E_unlockfile : Z := 0x18228.
Definition src0_A_stdio_write : Z := 0x186e0.  Definition src0_E_stdio_write : Z := 0x18870.
Definition src0_A_aio_close : Z := 0x186b0.  Definition src0_E_aio_close : Z := 0x186b4.
Definition src0_A_stdio_close : Z := 0x186b4.  Definition src0_E_stdio_close : Z := 0x186e0.
Definition src0_A_fprintf : Z := 0x18228.  Definition src0_E_fprintf : Z := 0x1828c.
Definition src0_A_fwritex : Z := 0x1828c.  Definition src0_E_fwritex : Z := 0x183c4.
Definition src0_A_fwrite : Z := 0x183c4.  Definition src0_E_fwrite : Z := 0x1847c.
Definition src0_A_towrite : Z := 0x1847c.  Definition src0_E_towrite : Z := 0x184d0.
Definition src0_A_stdio_exit : Z := 0x184d0.  Definition src0_E_stdio_exit : Z := 0x18674.
Definition src0_A_ofl_lock : Z := 0x18674.  Definition src0_E_ofl_lock : Z := 0x186a4.
Definition src0_A_ofl_unlock : Z := 0x186a4.  Definition src0_E_ofl_unlock : Z := 0x186b0.
Definition src0_A_stdout_write : Z := 0x18878.  Definition src0_E_stdout_write : Z := 0x18918.
Definition src0_A_vfprintf : Z := 0x18918.  Definition src0_E_vfprintf : Z := 0x18ac8.
Definition src0_A_printf_core : Z := 0x18ac8.  Definition src0_E_printf_core : Z := 0x198f8.
Definition src0_A_pop_arg : Z := 0x198f8.  Definition src0_E_pop_arg : Z := 0x19a2c.
Definition src0_A_pad : Z := 0x19a2c.  Definition src0_E_pad : Z := 0x19b00.
Definition src0_A_fmt_fp : Z := 0x19b00.  Definition src0_E_fmt_fp : Z := 0x1b1c8.
Definition src0_A_strerror : Z := 0x1b1c8.  Definition src0_E_strerror : Z := 0x1b204.
Definition src0_A_lctrans_impl : Z := 0x1b204.  Definition src0_E_lctrans_impl : Z := 0x1b208.
Definition src0_A_lctrans : Z := 0x1b208.  Definition src0_E_lctrans : Z := 0x1b20c.
Definition src0_A_wctomb : Z := 0x1b20c.  Definition src0_E_wctomb : Z := 0x1b230.
Definition src0_A_wcrtomb : Z := 0x1b230.  Definition src0_E_wcrtomb : Z := 0x1b35c.
Definition src0_A_extenddftf2 : Z := 0x1b35c.  Definition src0_E_extenddftf2 : Z := 0x1b4ec.
Definition src0_A_signbitl : Z := 0x1b4ec.  Definition src0_E_signbitl : Z := 0x1b4f4.
Definition src0_A_fpclassifyl : Z := 0x1b4f4.  Definition src0_E_fpclassifyl : Z := 0x1b538.
Definition src0_A_frexpl : Z := 0x1b538.  Definition src0_E_frexpl : Z := 0x1b610.
Definition src0_A_letf2 : Z := 0x1b610.  Definition src0_E_letf2 : Z := 0x1b6d8.
Definition src0_A_multf3 : Z := 0x1b6d8.  Definition src0_E_multf3 : Z := 0x1bdd8.
Definition src0_A_floatsitf : Z := 0x1bdd8.  Definition src0_E_floatsitf : Z := 0x1bee0.
Definition src0_A_scalbn : Z := 0x1bee0.  Definition src0_E_scalbn : Z := 0x1bf78.
Definition src0_A_subtf3 : Z := 0x1bf78.  Definition src0_E_subtf3 : Z := 0x1bf88.
Definition src0_A_addtf3 : Z := 0x1bf88.  Definition src0_E_addtf3 : Z := 0x1c754.
Definition src0_A_fe_getround : Z := 0x1c754.  Definition src0_E_fe_getround : Z := 0x1c784.
Definition src0_A_fe_raise_inexact : Z := 0x1c784.  Definition src0_E_fe_raise_inexact : Z := 0x1c790.
Definition src0_A_fixunstfsi : Z := 0x1c790.  Definition src0_E_fixunstfsi : Z := 0x1c824.
Definition src0_A_floatunsitf : Z := 0x1c824.  Definition src0_E_floatunsitf : Z := 0x1c910.
Definition src0_A_fixtfsi : Z := 0x1c910.  Definition src0_E_fixtfsi : Z := 0x1c9b8.
Definition src0_A_divtf3 : Z := 0x1c9b8.  Definition src0_E_divtf3 : Z := 0x1d2bc.
Definition src0_A_vprintf : Z := 0x1d2bc.  Definition src0_E_vprintf : Z := 0x1d2d8.
Definition src0_A_bcmp : Z := 0x1d2d8.  Definition src0_E_bcmp : Z := 0x1d2dc.
Definition src0_A_memcmp : Z := 0x1d3a8.  Definition src0_E_memcmp : Z := 0x1d3d8.
Definition src0_A_memcpy : Z := 0x1d3d8.  Definition src0_E_memcpy : Z := 0x1d7dc.
Definition src0_A_memset : Z := 0x1d7dc.  Definition src0_E_memset : Z := 0x1d8d4.
Definition src0_A_strnlen : Z := 0x1d90c.  Definition src0_E_strnlen : Z := 0x1d950.
Definition src0_A_memchr : Z := 0x1d2dc.  Definition src0_E_memchr : Z := 0x1d3a8.
Definition src0_A_lock : Z := 0x1d950.  Definition src0_E_lock : Z := 0x1dbd8.
Definition src0_A_unlock : Z := 0x1dbd8.  Definition src0_E_unlock : Z := 0x1dc4c.
Definition src0_A_syscall_cp_c : Z := 0x1dc4c.  Definition src0_E_syscall_cp_c : Z := 0x1dc70.
Definition src0_A_syscall_cp : Z := 0x1dc70.  Definition src0_E_syscall_cp : Z := 0x1dc74.
Definition src0_A_unistd_exit : Z := 0x1dc80.  Definition src0_E_unistd_exit : Z := 0x1dc8c.
Definition src0_A_close : Z := 0x1dc8c.  Definition src0_E_close : Z := 0x1dce0.
Definition src0_A_lseek : Z := 0x1dce0.  Definition src0_E_lseek : Z := 0x1dcec.
Definition src0_A_read : Z := 0x1dcec.  Definition src0_E_read : Z := 0x1dd20.
Definition src0_D_str_n0X0x : Z := 0x102c6.
Definition src0_D_str_n0X_0X_0X_0x_0x_0x : Z := 0x1033d.
Definition src0_D_str_cli_out_of_memory_n : Z := 0x10350.
Definition src0_D_str_d_n : Z := 0x10364.
Definition src0_D_str_usage_s_INPUT_n : Z := 0x10388.
Definition src0_D_str_cli_config_len_overruns : Z := 0x10399.
Definition src0_D_str_inf : Z := 0x10404.
Definition src0_D_str_INF : Z := 0x10480.
Definition src0_D_str_cli_input_u_bytes_refuse : Z := 0x10484.
Definition src0_D_str_cli_cannot_open_s_n : Z := 0x10542.
Definition src0_D_str_cli_read_error_on_s_n : Z := 0x10557.
Definition src0_D_str_NAN : Z := 0x10583.
Definition src0_D_str_nan : Z := 0x10587.
Definition src0_D_str_cli_input_shorter_than_h : Z := 0x1058b.
Definition src0_D_str_dev_null : Z := 0x105b8.
Definition src0_D_str_null : Z := 0x105c2.
Definition src0_D_const_double_0x1p28 : Z := 0x10960.
Definition src0_D_const_double_1_0 : Z := 0x10968.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10970.
Definition src0_D_const_double_0_5 : Z := 0x10978.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10980.
Definition src0_D_const_double_0x1p1023 : Z := 0x10988.
Definition src0_D_const_double_1_5 : Z := 0x10990.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x10998.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x109a0.
Definition src0_D_const_double_0x1p120 : Z := 0x109a8.
Definition src0_D_debruijn32 : Z := 0x10704.
Definition src0_D_size_classes : Z := 0x10788.
Definition src0_D_small_cnt_tab : Z := 0x107e8.
Definition src0_D_med_cnt_tab : Z := 0x10728.
Definition src0_D_jt_printf_core_1 : Z := 0x10818.
Definition src0_D_jt_printf_core_2 : Z := 0x108f8.
Definition src0_D_jt_pop_arg : Z := 0x10918.
Definition src0_D_states : Z := 0x109b0.
Definition src0_D_xdigits : Z := 0x10b80.
Definition src0_D_errmsgstr : Z := 0x10b90.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11338.
Definition src0_D_fe_getround : Z := 0x11440.
Definition src0_D_EH_FRAME_LIST : Z := 0x115b8.
Definition src0_D_init_array_start : Z := 0x1ed20.
Definition src0_D_fini_array_start : Z := 0x1ed28.
Definition src0_D_stderr : Z := 0x1faf0.
Definition src0_D_stdout : Z := 0x1faf8.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x1fb00.
Definition src0_D_got_DYNAMIC : Z := 0x1fb08.
Definition src0_D_got_main : Z := 0x1fb10.
Definition src0_D_got_init : Z := 0x1fb18.
Definition src0_D_got_fini : Z := 0x1fb20.
Definition src0_D_got_register_frame_info : Z := 0x1fb28.
Definition src0_D_got_cxa_finalize : Z := 0x1fb30.
Definition src0_D_got_deregister_frame_info : Z := 0x1fb38.
Definition src0_D_got_stderr : Z := 0x1fb40.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x1fb48.
Definition src0_D_got_stdout : Z := 0x1fb50.
Definition src0_D_got_environ : Z := 0x1fb58.
Definition src0_D_got_progname_full : Z := 0x1fb60.
Definition src0_D_got_progname : Z := 0x1fb68.
Definition src0_D_got_init_array_end : Z := 0x1fb70.
Definition src0_D_got_init_array_start : Z := 0x1fb78.
Definition src0_D_got_stack_chk_guard : Z := 0x1fb80.
Definition src0_D_got_fini_array_end : Z := 0x1fb88.
Definition src0_D_got_fini_array_start : Z := 0x1fb90.
Definition src0_D_dso_handle : Z := 0x20b98.
Definition src0_D_aef_arg0 : Z := 0x20ba0.
Definition src0_D_aef_argc : Z := 0x20ba8.
Definition src0_D_aef_argv : Z := 0x20bb0.
Definition src0_D_stderr_FILE : Z := 0x20bc0.
Definition src0_D_stderr_used : Z := 0x20ca8.
Definition src0_D_stdout_FILE : Z := 0x20cb0.
Definition src0_D_stdout_used : Z := 0x20d98.
Definition src0_D_default_stacksize : Z := 0x20da0.
Definition src0_D_do_init_initialized : Z := 0x20db0.
Definition src0_D_do_init_object : Z := 0x20db8.
Definition src0_D_do_fini_finalized : Z := 0x20df8.
Definition src0_D_read_stage : Z := 0x20df9.
Definition src0_D_target_run_initialized : Z := 0x30e00.
Definition src0_D_aef_in_callback : Z := 0x30e04.
Definition src0_D_aef_aligned_copy_empty : Z := 0x30e10.
Definition src0_D_environ : Z := 0x30e30.
Definition src0_D_thread_list_lock : Z := 0x50f08.
Definition src0_D_main_tls : Z := 0x50f10.
Definition src0_D_builtin_tls : Z := 0x30e38.
Definition src0_D_finished_atexit : Z := 0x50f48.
Definition src0_D_atexit_lock : Z := 0x50f4c.
Definition src0_D_atexit_slot : Z := 0x50f50.
Definition src0_D_atexit_head : Z := 0x50f58.
Definition src0_D_atexit_builtin : Z := 0x50f60.
Definition src0_D_exit_exit_lock : Z := 0x51168.
Definition src0_D_stack_chk_guard : Z := 0x51170.
Definition src0_D_sysinfo : Z := 0x51178.
Definition src0_D_progname : Z := 0x51180.
Definition src0_D_progname_full : Z := 0x51188.
Definition src0_D_libc : Z := 0x51190.
Definition src0_D_hwcap : Z := 0x511f8.
Definition src0_D_malloc_lock : Z := 0x51200.
Definition src0_D_malloc_context : Z := 0x51208.
Definition src0_D_malloc_replaced : Z := 0x515a8.
Definition src0_D_stdin_used : Z := 0x515b0.
Definition src0_D_ofl_lock : Z := 0x515b8.
Definition src0_D_ofl_head : Z := 0x515c0.
Definition src0_D_stderr_buf : Z := 0x515c8.
Definition src0_D_stdout_buf : Z := 0x515d0.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 132.
