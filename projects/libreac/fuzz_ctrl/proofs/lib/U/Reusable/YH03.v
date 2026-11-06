(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YH03.v, with its addresses changed. *)
(* Modified by Theorem Labs, 2026-10-29 (a Theorem Labs lane): every src0_* value below is re-read from fuzz_ctrl's OWN v1.9.0 ubsan build, the one projects/libreac/fuzz_ctrl/harness.yaml pins by sha256 6f0dfa56f7107fa658c776643d812731b90da89c0d24f02e4ca59ad3a4c4911b; the values were read from that build's unstripped twin (internal path), which differs from the pinned file in 25 loaded bytes only - 5 in the ELF header (e_shoff, e_shnum, e_shstrndx) and the 20 of .note.gnu.build-id - and in no byte of .text, .rodata, .data, .got or .bss, so no value named here can differ; read from .symtab, .rodata or the dispatch instructions, never from a cgif label name and never by adding a delta. 54 definitions naming symbols, strings or constants that fuzz_ctrl does not have were removed. src0_A_stdio_read, src0_D_str_tmp_out_gif, src0_D_str_wb, src0_D_str_rwa and src0_D_str_3 also name nothing fuzz_ctrl has and were removed once the FILE sink became option-typed (sk_file := None in U/Reusable/YI5c.v:18). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition src0_text_lo : Z := 0x12cd8.  Definition src0_text_hi : Z := 0x1ec44.
Definition src0_rodata_lo : Z := 0x10298.  Definition src0_rodata_hi : Z := 0x11414.
Definition src0_eh_frame_lo : Z := 0x115b8.  Definition src0_eh_frame_hi : Z := 0x11cd8.
Definition src0_init_array_lo : Z := 0x1fc48.  Definition src0_init_array_hi : Z := 0x1fc50.
Definition src0_fini_array_lo : Z := 0x1fc50.  Definition src0_fini_array_hi : Z := 0x1fc58.
Definition src0_data_rel_ro_lo : Z := 0x1fc58.  Definition src0_data_rel_ro_hi : Z := 0x20a98.
Definition src0_got_lo : Z := 0x20a98.  Definition src0_got_hi : Z := 0x20b30.
Definition src0_data_lo : Z := 0x21b30.  Definition src0_data_hi : Z := 0x21d3c.
Definition src0_bss_lo : Z := 0x21d40.  Definition src0_bss_hi : Z := 0x52968.
Definition src0_A_do_init : Z := 0x12d20.  Definition src0_E_do_init : Z := 0x12d94.
Definition src0_A_do_fini : Z := 0x12d94.  Definition src0_E_do_fini : Z := 0x12e24.
Definition src0_A_main : Z := 0x12e24.  Definition src0_E_main : Z := 0x130e8.
Definition src0_A_target_alloc_init : Z := 0x130e8.  Definition src0_E_target_alloc_init : Z := 0x130ec.
Definition src0_A_target_alloc_count : Z := 0x130ec.  Definition src0_E_target_alloc_count : Z := 0x130f4.
Definition src0_A_target_run : Z := 0x130f4.  Definition src0_E_target_run : Z := 0x1324c.
Definition src0_A_aef_exit_guard : Z := 0x1324c.  Definition src0_E_aef_exit_guard : Z := 0x1327c.
Definition src0_A_emit_printf : Z := 0x1327c.  Definition src0_E_emit_printf : Z := 0x132c4.
Definition src0_A_LLVMFuzzerTestOneInput : Z := 0x132c4.  Definition src0_E_LLVMFuzzerTestOneInput : Z := 0x14160.
Definition src0_A_init : Z := 0x16814.  Definition src0_E_init : Z := 0x16818.
Definition src0_A_init_libc : Z := 0x16818.  Definition src0_E_init_libc : Z := 0x16a44.
Definition src0_A_libc_start_init : Z := 0x16a44.  Definition src0_E_libc_start_init : Z := 0x16a90.
Definition src0_A_libc_start_main : Z := 0x16a90.  Definition src0_E_libc_start_main : Z := 0x16af0.
Definition src0_A_libc_start_main_stage2 : Z := 0x16af0.  Definition src0_E_libc_start_main_stage2 : Z := 0x16b38.
Definition src0_A_init_tls : Z := 0x16b38.  Definition src0_E_init_tls : Z := 0x16de8.
Definition src0_A_funcs_on_exit : Z := 0x16e98.  Definition src0_E_funcs_on_exit : Z := 0x16f60.
Definition src0_A_cxa_finalize : Z := 0x16f60.  Definition src0_E_cxa_finalize : Z := 0x16f64.
Definition src0_A_atexit : Z := 0x16f64.  Definition src0_E_atexit : Z := 0x17028.
Definition src0_A_atexit_call : Z := 0x17028.  Definition src0_E_atexit_call : Z := 0x1702c.
Definition src0_A_fini : Z := 0x1702c.  Definition src0_E_fini : Z := 0x17030.
Definition src0_A_libc_exit_fini : Z := 0x17030.  Definition src0_E_libc_exit_fini : Z := 0x1707c.
Definition src0_A_exit : Z := 0x1707c.  Definition src0_E_exit : Z := 0x170f0.
Definition src0_A_Exit : Z := 0x16e7c.  Definition src0_E_Exit : Z := 0x16e98.
Definition src0_A_open : Z := 0x170f0.  Definition src0_E_open : Z := 0x171d4.
Definition src0_A_init_ssp : Z := 0x171d4.  Definition src0_E_init_ssp : Z := 0x17234.
Definition src0_A_stack_chk_fail : Z := 0x17234.  Definition src0_E_stack_chk_fail : Z := 0x1723c.
Definition src0_A_syscall_ret : Z := 0x1723c.  Definition src0_E_syscall_ret : Z := 0x17274.
Definition src0_A_errno_location : Z := 0x17274.  Definition src0_E_errno_location : Z := 0x17280.
Definition src0_A_free : Z := 0x17280.  Definition src0_E_free : Z := 0x17284.
Definition src0_A_libc_calloc : Z := 0x17284.  Definition src0_E_libc_calloc : Z := 0x173bc.
Definition src0_A_libc_malloc : Z := 0x173bc.  Definition src0_E_libc_malloc : Z := 0x173c0.
Definition src0_A_malloc : Z := 0x173c0.  Definition src0_E_malloc : Z := 0x173c4.
Definition src0_A_libc_free : Z := 0x173c4.  Definition src0_E_libc_free : Z := 0x17590.
Definition src0_A_get_meta : Z := 0x17590.  Definition src0_E_get_meta : Z := 0x176a0.
Definition src0_A_nontrivial_free : Z := 0x176a0.  Definition src0_E_nontrivial_free : Z := 0x17a78.
Definition src0_A_alloc_meta : Z := 0x17a78.  Definition src0_E_alloc_meta : Z := 0x17d50.
Definition src0_A_libc_malloc_impl : Z := 0x17d50.  Definition src0_E_libc_malloc_impl : Z := 0x180c0.
Definition src0_A_alloc_slot : Z := 0x180c0.  Definition src0_E_alloc_slot : Z := 0x18964.
Definition src0_A_enframe : Z := 0x18964.  Definition src0_E_enframe : Z := 0x18ab4.
Definition src0_A_malloc_allzerop : Z := 0x18ab4.  Definition src0_E_malloc_allzerop : Z := 0x18c2c.
Definition src0_A_vm_wait : Z := 0x18c2c.  Definition src0_E_vm_wait : Z := 0x18c30.
Definition src0_A_mmap : Z := 0x18c30.  Definition src0_E_mmap : Z := 0x18d1c.
Definition src0_A_mprotect : Z := 0x18d1c.  Definition src0_E_mprotect : Z := 0x18d64.
Definition src0_A_munmap : Z := 0x18d64.  Definition src0_E_munmap : Z := 0x18dac.
Definition src0_A_fflush : Z := 0x18e80.  Definition src0_E_fflush : Z := 0x18ff0.
Definition src0_A_lockfile : Z := 0x18ff0.  Definition src0_E_lockfile : Z := 0x190ec.
Definition src0_A_unlockfile : Z := 0x190ec.  Definition src0_E_unlockfile : Z := 0x1914c.
Definition src0_A_stdio_write : Z := 0x19604.  Definition src0_E_stdio_write : Z := 0x19794.
Definition src0_A_aio_close : Z := 0x195d4.  Definition src0_E_aio_close : Z := 0x195d8.
Definition src0_A_stdio_close : Z := 0x195d8.  Definition src0_E_stdio_close : Z := 0x19604.
Definition src0_A_fprintf : Z := 0x1914c.  Definition src0_E_fprintf : Z := 0x191b0.
Definition src0_A_fwritex : Z := 0x191b0.  Definition src0_E_fwritex : Z := 0x192e8.
Definition src0_A_fwrite : Z := 0x192e8.  Definition src0_E_fwrite : Z := 0x193a0.
Definition src0_A_towrite : Z := 0x193a0.  Definition src0_E_towrite : Z := 0x193f4.
Definition src0_A_stdio_exit : Z := 0x193f4.  Definition src0_E_stdio_exit : Z := 0x19598.
Definition src0_A_ofl_lock : Z := 0x19598.  Definition src0_E_ofl_lock : Z := 0x195c8.
Definition src0_A_ofl_unlock : Z := 0x195c8.  Definition src0_E_ofl_unlock : Z := 0x195d4.
Definition src0_A_stdout_write : Z := 0x1979c.  Definition src0_E_stdout_write : Z := 0x1983c.
Definition src0_A_vfprintf : Z := 0x1983c.  Definition src0_E_vfprintf : Z := 0x199ec.
Definition src0_A_printf_core : Z := 0x199ec.  Definition src0_E_printf_core : Z := 0x1a81c.
Definition src0_A_pop_arg : Z := 0x1a81c.  Definition src0_E_pop_arg : Z := 0x1a950.
Definition src0_A_pad : Z := 0x1a950.  Definition src0_E_pad : Z := 0x1aa24.
Definition src0_A_fmt_fp : Z := 0x1aa24.  Definition src0_E_fmt_fp : Z := 0x1c0ec.
Definition src0_A_strerror : Z := 0x1c0ec.  Definition src0_E_strerror : Z := 0x1c128.
Definition src0_A_lctrans_impl : Z := 0x1c128.  Definition src0_E_lctrans_impl : Z := 0x1c12c.
Definition src0_A_lctrans : Z := 0x1c12c.  Definition src0_E_lctrans : Z := 0x1c130.
Definition src0_A_wctomb : Z := 0x1c130.  Definition src0_E_wctomb : Z := 0x1c154.
Definition src0_A_wcrtomb : Z := 0x1c154.  Definition src0_E_wcrtomb : Z := 0x1c280.
Definition src0_A_extenddftf2 : Z := 0x1c280.  Definition src0_E_extenddftf2 : Z := 0x1c410.
Definition src0_A_signbitl : Z := 0x1c410.  Definition src0_E_signbitl : Z := 0x1c418.
Definition src0_A_fpclassifyl : Z := 0x1c418.  Definition src0_E_fpclassifyl : Z := 0x1c45c.
Definition src0_A_frexpl : Z := 0x1c45c.  Definition src0_E_frexpl : Z := 0x1c534.
Definition src0_A_letf2 : Z := 0x1c534.  Definition src0_E_letf2 : Z := 0x1c5fc.
Definition src0_A_multf3 : Z := 0x1c5fc.  Definition src0_E_multf3 : Z := 0x1ccfc.
Definition src0_A_floatsitf : Z := 0x1ccfc.  Definition src0_E_floatsitf : Z := 0x1ce04.
Definition src0_A_scalbn : Z := 0x1ce04.  Definition src0_E_scalbn : Z := 0x1ce9c.
Definition src0_A_subtf3 : Z := 0x1ce9c.  Definition src0_E_subtf3 : Z := 0x1ceac.
Definition src0_A_addtf3 : Z := 0x1ceac.  Definition src0_E_addtf3 : Z := 0x1d678.
Definition src0_A_fe_getround : Z := 0x1d678.  Definition src0_E_fe_getround : Z := 0x1d6a8.
Definition src0_A_fe_raise_inexact : Z := 0x1d6a8.  Definition src0_E_fe_raise_inexact : Z := 0x1d6b4.
Definition src0_A_fixunstfsi : Z := 0x1d6b4.  Definition src0_E_fixunstfsi : Z := 0x1d748.
Definition src0_A_floatunsitf : Z := 0x1d748.  Definition src0_E_floatunsitf : Z := 0x1d834.
Definition src0_A_fixtfsi : Z := 0x1d834.  Definition src0_E_fixtfsi : Z := 0x1d8dc.
Definition src0_A_divtf3 : Z := 0x1d8dc.  Definition src0_E_divtf3 : Z := 0x1e1e0.
Definition src0_A_vprintf : Z := 0x1e1e0.  Definition src0_E_vprintf : Z := 0x1e1fc.
Definition src0_A_bcmp : Z := 0x1e1fc.  Definition src0_E_bcmp : Z := 0x1e200.
Definition src0_A_memcmp : Z := 0x1e2cc.  Definition src0_E_memcmp : Z := 0x1e2fc.
Definition src0_A_memcpy : Z := 0x1e2fc.  Definition src0_E_memcpy : Z := 0x1e700.
Definition src0_A_memset : Z := 0x1e700.  Definition src0_E_memset : Z := 0x1e7f8.
Definition src0_A_strnlen : Z := 0x1e830.  Definition src0_E_strnlen : Z := 0x1e874.
Definition src0_A_memchr : Z := 0x1e200.  Definition src0_E_memchr : Z := 0x1e2cc.
Definition src0_A_lock : Z := 0x1e874.  Definition src0_E_lock : Z := 0x1eafc.
Definition src0_A_unlock : Z := 0x1eafc.  Definition src0_E_unlock : Z := 0x1eb70.
Definition src0_A_syscall_cp_c : Z := 0x1eb70.  Definition src0_E_syscall_cp_c : Z := 0x1eb94.
Definition src0_A_syscall_cp : Z := 0x1eb94.  Definition src0_E_syscall_cp : Z := 0x1eb98.
Definition src0_A_unistd_exit : Z := 0x1eba4.  Definition src0_E_unistd_exit : Z := 0x1ebb0.
Definition src0_A_close : Z := 0x1ebb0.  Definition src0_E_close : Z := 0x1ec04.
Definition src0_A_lseek : Z := 0x1ec04.  Definition src0_E_lseek : Z := 0x1ec10.
Definition src0_A_read : Z := 0x1ec10.  Definition src0_E_read : Z := 0x1ec44.
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
Definition src0_D_const_double_0x1p28 : Z := 0x10928.
Definition src0_D_const_double_1_0 : Z := 0x10930.
Definition src0_D_const_HIGHS_0x8080808080808080 : Z := 0x10938.
Definition src0_D_const_double_0_5 : Z := 0x10940.
Definition src0_D_const_ONES_0x0101010101010100 : Z := 0x10948.
Definition src0_D_const_double_0x1p1023 : Z := 0x10950.
Definition src0_D_const_double_1_5 : Z := 0x10958.
Definition src0_D_const_u64_fmt_fp_1e9_recip_misc : Z := 0x10960.
Definition src0_D_const_double_0x1p_969_0x1p_1022_0x1p : Z := 0x10968.
Definition src0_D_const_double_0x1p120 : Z := 0x10970.
Definition src0_D_debruijn32 : Z := 0x106cc.
Definition src0_D_size_classes : Z := 0x10750.
Definition src0_D_small_cnt_tab : Z := 0x107b0.
Definition src0_D_med_cnt_tab : Z := 0x106f0.
Definition src0_D_jt_printf_core_1 : Z := 0x107e0.
Definition src0_D_jt_printf_core_2 : Z := 0x108c0.
Definition src0_D_jt_pop_arg : Z := 0x108e0.
Definition src0_D_states : Z := 0x10978.
Definition src0_D_xdigits : Z := 0x10b48.
Definition src0_D_errmsgstr : Z := 0x10b58.
Definition src0_D_global_pointer : Z := 0x10800.
Definition src0_D_errmsgidx : Z := 0x11300.
Definition src0_D_fe_getround : Z := 0x11408.
Definition src0_D_EH_FRAME_LIST : Z := 0x115b8.
Definition src0_D_init_array_start : Z := 0x1fc48.
Definition src0_D_fini_array_start : Z := 0x1fc50.
Definition src0_D_stderr : Z := 0x20a88.
Definition src0_D_stdout : Z := 0x20a90.
Definition src0_D_got_DYNAMIC_reserved : Z := 0x20a98.
Definition src0_D_got_DYNAMIC : Z := 0x20aa0.
Definition src0_D_got_main : Z := 0x20aa8.
Definition src0_D_got_init : Z := 0x20ab0.
Definition src0_D_got_fini : Z := 0x20ab8.
Definition src0_D_got_register_frame_info : Z := 0x20ac0.
Definition src0_D_got_cxa_finalize : Z := 0x20ac8.
Definition src0_D_got_deregister_frame_info : Z := 0x20ad0.
Definition src0_D_got_stderr : Z := 0x20ad8.
Definition src0_D_got_LLVMFuzzerInitialize : Z := 0x20ae0.
Definition src0_D_got_stdout : Z := 0x20ae8.
Definition src0_D_got_environ : Z := 0x20af0.
Definition src0_D_got_progname_full : Z := 0x20af8.
Definition src0_D_got_progname : Z := 0x20b00.
Definition src0_D_got_init_array_end : Z := 0x20b08.
Definition src0_D_got_init_array_start : Z := 0x20b10.
Definition src0_D_got_stack_chk_guard : Z := 0x20b18.
Definition src0_D_got_fini_array_end : Z := 0x20b20.
Definition src0_D_got_fini_array_start : Z := 0x20b28.
Definition src0_D_dso_handle : Z := 0x21b30.
Definition src0_D_aef_arg0 : Z := 0x21b38.
Definition src0_D_aef_argc : Z := 0x21b40.
Definition src0_D_aef_argv : Z := 0x21b48.
Definition src0_D_stderr_FILE : Z := 0x21b58.
Definition src0_D_stderr_used : Z := 0x21c40.
Definition src0_D_stdout_FILE : Z := 0x21c48.
Definition src0_D_stdout_used : Z := 0x21d30.
Definition src0_D_default_stacksize : Z := 0x21d38.
Definition src0_D_do_init_initialized : Z := 0x21d40.
Definition src0_D_do_init_object : Z := 0x21d48.
Definition src0_D_do_fini_finalized : Z := 0x21d88.
Definition src0_D_read_stage : Z := 0x21d89.
Definition src0_D_target_run_initialized : Z := 0x31d90.
Definition src0_D_aef_in_callback : Z := 0x31d94.
Definition src0_D_aef_aligned_copy_empty : Z := 0x31da0.
Definition src0_D_environ : Z := 0x31dc0.
Definition src0_D_thread_list_lock : Z := 0x51e98.
Definition src0_D_main_tls : Z := 0x51ea0.
Definition src0_D_builtin_tls : Z := 0x31dc8.
Definition src0_D_finished_atexit : Z := 0x51ed8.
Definition src0_D_atexit_lock : Z := 0x51edc.
Definition src0_D_atexit_slot : Z := 0x51ee0.
Definition src0_D_atexit_head : Z := 0x51ee8.
Definition src0_D_atexit_builtin : Z := 0x51ef0.
Definition src0_D_exit_exit_lock : Z := 0x520f8.
Definition src0_D_stack_chk_guard : Z := 0x52100.
Definition src0_D_sysinfo : Z := 0x52108.
Definition src0_D_progname : Z := 0x52110.
Definition src0_D_progname_full : Z := 0x52118.
Definition src0_D_libc : Z := 0x52120.
Definition src0_D_hwcap : Z := 0x52188.
Definition src0_D_malloc_lock : Z := 0x52190.
Definition src0_D_malloc_context : Z := 0x52198.
Definition src0_D_malloc_replaced : Z := 0x52538.
Definition src0_D_stdin_used : Z := 0x52540.
Definition src0_D_ofl_lock : Z := 0x52548.
Definition src0_D_ofl_head : Z := 0x52550.
Definition src0_D_stderr_buf : Z := 0x52558.
Definition src0_D_stdout_buf : Z := 0x52560.
Definition src0_vmlock : option Z := None.
Definition src0_debruijn_len : Z := 132.
