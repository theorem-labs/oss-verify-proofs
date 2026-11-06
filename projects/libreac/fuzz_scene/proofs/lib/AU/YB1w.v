(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1w.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2530c.
Definition tfib_text_lo : Z := 0x32b44.  Definition tfib_text_hi : Z := 0x9a4a8.
Definition tfib_init_array_lo : Z := 0x9b4a8.  Definition tfib_init_array_hi : Z := 0x9b4c8.
Definition tfib_fini_array_lo : Z := 0x9b4c8.  Definition tfib_fini_array_hi : Z := 0x9b4d8.
Definition tfib_preinit_array_lo : Z := 0x9b4d8.  Definition tfib_preinit_array_hi : Z := 0x9b4e0.
Definition tfib_data_rel_ro_lo : Z := 0x9b4e0.  Definition tfib_data_rel_ro_hi : Z := 0x9b9e0.
Definition tfib_got_lo : Z := 0x9b9e0.  Definition tfib_got_hi : Z := 0x9c740.
Definition tfib_data_lo : Z := 0x9d740.  Definition tfib_data_hi : Z := 0xa02f8.
Definition tfib_asan_globals_lo : Z := 0xa0300.  Definition tfib_asan_globals_hi : Z := 0xa0440.
Definition tfib_bss_lo : Z := 0xa0440.  Definition tfib_bss_hi : Z := 0x5f8378.
Definition tfib_tbss_lo : Z := 0x9a4a8.  Definition tfib_tbss_hi : Z := 0x9a4bc.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f9000.
Definition tfib_entry : Z := 0x32b44.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x32b44.
Definition tfib_A_do_init : Z := 0x32b8c.  Definition tfib_E_do_init : Z := 0x32c00.
Definition tfib_A_do_fini : Z := 0x32c00.  Definition tfib_E_do_fini : Z := 0x32c90.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x32c90.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x32ccc.
Definition tfib_A_InitializeAllocator : Z := 0x32e3c.  Definition tfib_E_InitializeAllocator : Z := 0x32e54.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x32e54.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x32fc0.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x3351c.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x33678.
Definition tfib_A_asan_free : Z := 0x33a4c.  Definition tfib_E_asan_free : Z := 0x33a74.
Definition tfib_A_Allocator_Deallocate : Z := 0x33a74.  Definition tfib_E_Allocator_Deallocate : Z := 0x33d2c.
Definition tfib_A_asan_malloc : Z := 0x33d2c.  Definition tfib_E_asan_malloc : Z := 0x33d88.
Definition tfib_A_Allocator_Allocate : Z := 0x33d88.  Definition tfib_E_Allocator_Allocate : Z := 0x34710.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34e48.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34f8c.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x35078.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x350d4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x350d4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x35324.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35324.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35418.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x35dd4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x36058.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x36058.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x361d8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x361d8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x363a0.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x363a0.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3656c.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x3660c.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x36710.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x36a38.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x36b80.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x36b80.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x36bb8.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37350.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37638.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x37d10.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x37e88.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x37e88.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x38038.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x38038.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3821c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x3821c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x384f4.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x384f4.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x3896c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3896c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x38a6c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x38a6c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x38d74.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x38d74.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x390e4.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x39600.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x396e8.
Definition tfib_A_AsanActivate : Z := 0x396e8.  Definition tfib_E_AsanActivate : Z := 0x397c4.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x39ca0.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x39d88.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3e840.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3e918.
Definition tfib_A_FakeStack_Create : Z := 0x3e918.  Definition tfib_E_FakeStack_Create : Z := 0x3ea04.
Definition tfib_A_SetTLSFakeStack : Z := 0x3f0dc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3f10c.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3f10c.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3f29c.
Definition tfib_A_asan_stack_malloc_B : Z := 0x3f29c.  Definition tfib_E_asan_stack_malloc_B : Z := 0x3f438.
Definition tfib_A_asan_InitializeFlags : Z := 0x3f740.  Definition tfib_E_asan_InitializeFlags : Z := 0x4076c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40e78.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x41c94.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x41c94.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x42260.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x429b4.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x42c24.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42c24.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42f2c.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x436a0.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x437f0.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x4420c.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x44324.
Definition tfib_A_thunk_417bc : Z := 0x44364.  Definition tfib_E_thunk_417bc : Z := 0x44368.
Definition tfib_A_thunk_417cc : Z := 0x44374.  Definition tfib_E_thunk_417cc : Z := 0x4437c.
Definition tfib_A_tls_get_addr_thunk : Z := 0x44380.  Definition tfib_E_tls_get_addr_thunk : Z := 0x44384.
Definition tfib_A_check_step : Z := 0x83294.  Definition tfib_E_check_step : Z := 0x838c8.  Definition tfib_A_reac_ctrl_block_cksum_stamp : Z := 0x83930.  Definition tfib_E_reac_ctrl_block_cksum_stamp : Z := 0x839e8.  Definition tfib_A_reac_ctrl_checksum_verify : Z := 0x839e8.  Definition tfib_E_reac_ctrl_checksum_verify : Z := 0x83a70.  Definition tfib_A_reac_ctrl_build_scene_step : Z := 0x83a70.  Definition tfib_E_reac_ctrl_build_scene_step : Z := 0x83e04.  Definition tfib_A_reac_ctrl_scene_set_mac : Z := 0x83e04.  Definition tfib_E_reac_ctrl_scene_set_mac : Z := 0x83e58.  Definition tfib_A_reac_ctrl_scene_build : Z := 0x83e58.  Definition tfib_E_reac_ctrl_scene_build : Z := 0x84028.  Definition tfib_A_reac_ctrl_parse : Z := 0x84028.  Definition tfib_E_reac_ctrl_parse : Z := 0x84aac.  Definition tfib_A_kind_of_link1 : Z := 0x84aac.  Definition tfib_E_kind_of_link1 : Z := 0x84b20.
Definition tfib_A_thunk_417dc : Z := 0x44384.  Definition tfib_E_thunk_417dc : Z := 0x44388.

Definition tfib_A_thunk_417e4 : Z := 0x44388.  Definition tfib_E_thunk_417e4 : Z := 0x4438c.
Definition tfib_A_thunk_417e8 : Z := 0x4438c.  Definition tfib_E_thunk_417e8 : Z := 0x44390.
Definition tfib_A_thunk_417ec : Z := 0x44390.  Definition tfib_E_thunk_417ec : Z := 0x44394.
Definition tfib_A_thunk_417f0 : Z := 0x44394.  Definition tfib_E_thunk_417f0 : Z := 0x44398.
Definition tfib_A_thunk_417f8 : Z := 0x4439c.  Definition tfib_E_thunk_417f8 : Z := 0x443a0.
Definition tfib_A_thunk_4180c : Z := 0x443b0.  Definition tfib_E_thunk_4180c : Z := 0x443b4.
Definition tfib_A_icpt_strlen : Z := 0x443b4.  Definition tfib_E_icpt_strlen : Z := 0x44648.
Definition tfib_A_icpt_strnlen : Z := 0x44648.  Definition tfib_E_icpt_strnlen : Z := 0x448dc.
Definition tfib_A_icpt_strcmp : Z := 0x448e0.  Definition tfib_E_icpt_strcmp : Z := 0x44e10.
Definition tfib_A_icpt_strchr : Z := 0x44e10.  Definition tfib_E_icpt_strchr : Z := 0x450f0.
Definition tfib_A_icpt_memcmp : Z := 0x45988.  Definition tfib_E_icpt_memcmp : Z := 0x45a44.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x45a44.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x45b00.
Definition tfib_A_icpt_memchr : Z := 0x45b00.  Definition tfib_E_icpt_memchr : Z := 0x45dd0.
Definition tfib_A_icpt_frexpl : Z := 0x45dd0.  Definition tfib_E_icpt_frexpl : Z := 0x46048.
Definition tfib_A_icpt_read : Z := 0x46048.  Definition tfib_E_icpt_read : Z := 0x462b8.
Definition tfib_A_icpt_fwrite : Z := 0x462b8.  Definition tfib_E_icpt_fwrite : Z := 0x4652c.
Definition tfib_A_icpt_time : Z := 0x4652c.  Definition tfib_E_icpt_time : Z := 0x467c8.
Definition tfib_A_icpt_gmtime_r : Z := 0x469d0.  Definition tfib_E_icpt_gmtime_r : Z := 0x46c10.
Definition tfib_A_icpt_vprintf : Z := 0x46c10.  Definition tfib_E_icpt_vprintf : Z := 0x46cac.
Definition tfib_A_printf_common_format_interceptor : Z := 0x46cac.  Definition tfib_E_printf_common_format_interceptor : Z := 0x47774.
Definition tfib_A_icpt_vfprintf : Z := 0x47774.  Definition tfib_E_icpt_vfprintf : Z := 0x47828.
Definition tfib_A_icpt_vsnprintf : Z := 0x47828.  Definition tfib_E_icpt_vsnprintf : Z := 0x47b40.
Definition tfib_A_icpt_clock_gettime : Z := 0x47cbc.  Definition tfib_E_icpt_clock_gettime : Z := 0x47f14.
Definition tfib_A_icpt_wcrtomb : Z := 0x47f14.  Definition tfib_E_icpt_wcrtomb : Z := 0x48484.
Definition tfib_A_icpt_wctomb : Z := 0x48484.  Definition tfib_E_icpt_wctomb : Z := 0x487e0.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x488ac.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x48c94.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x48ca0.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x48d1c.


Definition tfib_A_icpt_sem_timedwait : Z := 0x48f28.  Definition tfib_E_icpt_sem_timedwait : Z := 0x491c0.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x491f0.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x49418.
Definition tfib_A_icpt_send : Z := 0x49418.  Definition tfib_E_icpt_send : Z := 0x496cc.
Definition tfib_A_icpt_sendto : Z := 0x496cc.  Definition tfib_E_icpt_sendto : Z := 0x49990.
Definition tfib_A_icpt_sigaltstack : Z := 0x49990.  Definition tfib_E_icpt_sigaltstack : Z := 0x49bec.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x49cc0.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x49e70.
Definition tfib_A_icpt_diouxXn : Z := 0x49e70.  Definition tfib_E_icpt_diouxXn : Z := 0x4a008.
Definition tfib_A_asan_memcpy : Z := 0x539f0.  Definition tfib_E_asan_memcpy : Z := 0x53e8c.
Definition tfib_A_asan_memset : Z := 0x53e8c.  Definition tfib_E_asan_memset : Z := 0x540cc.
Definition tfib_A_icpt_memset : Z := 0x540cc.  Definition tfib_E_icpt_memset : Z := 0x543bc.
Definition tfib_A_icpt_memcpy : Z := 0x543bc.  Definition tfib_E_icpt_memcpy : Z := 0x549ac.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x549ac.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x549e4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x549e4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x549e8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x549e8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x549ec.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x549ec.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x54a4c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x54a98.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x54bd4.
Definition tfib_A_free : Z := 0x54d40.  Definition tfib_E_free : Z := 0x54d44.
Definition tfib_A_malloc : Z := 0x54d44.  Definition tfib_E_malloc : Z := 0x54d48.
Definition tfib_A_icpt_free : Z := 0x54d48.  Definition tfib_E_icpt_free : Z := 0x54f18.
Definition tfib_A_icpt_malloc : Z := 0x54f18.  Definition tfib_E_icpt_malloc : Z := 0x55074.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x55140.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x55144.
Definition tfib_A_SetCanPoisonMemory : Z := 0x55bc0.  Definition tfib_E_SetCanPoisonMemory : Z := 0x55bd0.
Definition tfib_A_CanPoisonMemory : Z := 0x55bd0.  Definition tfib_E_CanPoisonMemory : Z := 0x55be4.
Definition tfib_A_PoisonShadow : Z := 0x55be4.  Definition tfib_E_PoisonShadow : Z := 0x560e0.
Definition tfib_A_MemToShadow_checked : Z := 0x560e0.  Definition tfib_E_MemToShadow_checked : Z := 0x5621c.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5656c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x568b0.
Definition tfib_A_AsanTSDInit : Z := 0x56cd0.  Definition tfib_E_AsanTSDInit : Z := 0x56d4c.
Definition tfib_A_AsanTSDGet : Z := 0x56d4c.  Definition tfib_E_AsanTSDGet : Z := 0x56d8c.
Definition tfib_A_AsanTSDSet : Z := 0x56d8c.  Definition tfib_E_AsanTSDSet : Z := 0x56dcc.
Definition tfib_A_PlatformTSDDtor : Z := 0x56dcc.  Definition tfib_E_PlatformTSDDtor : Z := 0x56e50.
Definition tfib_A_InstallAtForkHandler : Z := 0x56e50.  Definition tfib_E_InstallAtForkHandler : Z := 0x56e6c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x56ecc.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x56f10.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x57628.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x57834.
Definition tfib_A_ReportDoubleFree : Z := 0x57f3c.  Definition tfib_E_ReportDoubleFree : Z := 0x581cc.
Definition tfib_A_ReportGenericError : Z := 0x59aa8.  Definition tfib_E_ReportGenericError : Z := 0x5a364.
Definition tfib_A_AsanInited : Z := 0x5aaf0.  Definition tfib_E_AsanInited : Z := 0x5ab08.
Definition tfib_A_asan_report_load1 : Z := 0x5ab08.  Definition tfib_E_asan_report_load1 : Z := 0x5ab58.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5ab58.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5aba8.
Definition tfib_A_asan_report_load2 : Z := 0x5aba8.  Definition tfib_E_asan_report_load2 : Z := 0x5abf8.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5abf8.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5ac48.
Definition tfib_A_asan_report_load4 : Z := 0x5ac48.  Definition tfib_E_asan_report_load4 : Z := 0x5ac98.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5ac98.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5ace8.
Definition tfib_A_asan_report_load8 : Z := 0x5ace8.  Definition tfib_E_asan_report_load8 : Z := 0x5ad38.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5ad38.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5ad88.
Definition tfib_A_asan_report_load16 : Z := 0x5ad88.  Definition tfib_E_asan_report_load16 : Z := 0x5add8.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5add8.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5ae28.
Definition tfib_A_asan_report_store1 : Z := 0x5ae28.  Definition tfib_E_asan_report_store1 : Z := 0x5ae78.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5ae78.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5aec8.
Definition tfib_A_asan_report_store2 : Z := 0x5aec8.  Definition tfib_E_asan_report_store2 : Z := 0x5af18.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5af18.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5af68.
Definition tfib_A_asan_report_store4 : Z := 0x5af68.  Definition tfib_E_asan_report_store4 : Z := 0x5afb8.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5afb8.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5b008.
Definition tfib_A_asan_report_store8 : Z := 0x5b008.  Definition tfib_E_asan_report_store8 : Z := 0x5b058.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5b058.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5b0a8.
Definition tfib_A_asan_report_store16 : Z := 0x5b0a8.  Definition tfib_E_asan_report_store16 : Z := 0x5b0f8.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5b0f8.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5b148.
Definition tfib_A_asan_report_load_n : Z := 0x5b148.  Definition tfib_E_asan_report_load_n : Z := 0x5b198.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5b198.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5b1e8.
Definition tfib_A_asan_report_store_n : Z := 0x5b1e8.  Definition tfib_E_asan_report_store_n : Z := 0x5b238.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5b238.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5b288.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5b288.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5b308.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5b308.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5b6bc.
Definition tfib_A_AsanInitInternal : Z := 0x5b74c.  Definition tfib_E_AsanInitInternal : Z := 0x5ba00.
Definition tfib_A_thunk_59674 : Z := 0x5bc68.  Definition tfib_E_thunk_59674 : Z := 0x5bc6c.
Definition tfib_A_asan_init : Z := 0x5bc6c.  Definition tfib_E_asan_init : Z := 0x5bd00.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5bd00.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5bd04.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5bd04.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5bd68.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5bf68.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5c290.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5c290.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5c470.
Definition tfib_A_InitializeShadowMemory : Z := 0x5c470.  Definition tfib_E_InitializeShadowMemory : Z := 0x5c778.
Definition tfib_A_SetMallocContextSize : Z := 0x5c778.  Definition tfib_E_SetMallocContextSize : Z := 0x5c788.
Definition tfib_A_GetMallocContextSize : Z := 0x5c788.  Definition tfib_E_GetMallocContextSize : Z := 0x5c798.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5c798.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5c8e8.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5d3cc.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5d404.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5d6ac.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5d6b8.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5d6b8.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5d744.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5d744.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5d7ac.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5d7ac.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5d824.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5d824.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5d88c.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5dc64.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5dc70.
Definition tfib_A_AsanThread_Create : Z := 0x5ddf0.  Definition tfib_E_AsanThread_Create : Z := 0x5df8c.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5dfe8.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5e200.
Definition tfib_A_GetCurrentThread : Z := 0x5e200.  Definition tfib_E_GetCurrentThread : Z := 0x5e220.
Definition tfib_A_AsanThread_stack_top : Z := 0x5e3c4.  Definition tfib_E_AsanThread_stack_top : Z := 0x5e41c.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5e41c.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5e474.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5e474.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5e6a4.
Definition tfib_A_AsanThread_Init : Z := 0x5e6a4.  Definition tfib_E_AsanThread_Init : Z := 0x5ea98.
Definition tfib_A_CreateMainThread : Z := 0x5ebd8.  Definition tfib_E_CreateMainThread : Z := 0x5ece8.
Definition tfib_A_SetCurrentThread : Z := 0x5ece8.  Definition tfib_E_SetCurrentThread : Z := 0x5edc8.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5efcc.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5f108.
Definition tfib_A_weak_default_hook_ret : Z := 0x5fddc.  Definition tfib_E_weak_default_hook_ret : Z := 0x5fde0.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x605cc.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x60718.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x60718.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x60764.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x60764.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x60770.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x607a0.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x607ac.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x607ac.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x607b8.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x607d4.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x60aa0.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x60aa0.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x60e60.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x61dbc.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x61dc8.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x61dc8.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x61ea0.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x61ea0.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x61f3c.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x62460.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x624a4.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x6271c.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x62830.
Definition tfib_A_RunMallocHooks : Z := 0x629d4.  Definition tfib_E_RunMallocHooks : Z := 0x62a8c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x62a8c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x62a90.
Definition tfib_A_RunFreeHooks : Z := 0x62a90.  Definition tfib_E_RunFreeHooks : Z := 0x62b3c.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x62b70.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x62bbc.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x62e80.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x630c0.
Definition tfib_A_sanitizer_set_report_path : Z := 0x636bc.  Definition tfib_E_sanitizer_set_report_path : Z := 0x636d4.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x652e4.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x655f4.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x655f4.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x65738.
Definition tfib_A_FlagParser_ParseString : Z := 0x65738.  Definition tfib_E_FlagParser_ParseString : Z := 0x6582c.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x659c0.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x65a20.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x65a20.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x65a60.
Definition tfib_A_internal_atoll : Z := 0x65a60.  Definition tfib_E_internal_atoll : Z := 0x65b4c.
Definition tfib_A_internal_simple_strtoll : Z := 0x65b4c.  Definition tfib_E_internal_simple_strtoll : Z := 0x65ca8.
Definition tfib_A_internal_memchr : Z := 0x65ca8.  Definition tfib_E_internal_memchr : Z := 0x65cc8.
Definition tfib_A_internal_memcmp : Z := 0x65cc8.  Definition tfib_E_internal_memcmp : Z := 0x65d00.
Definition tfib_A_internal_memcpy : Z := 0x65d00.  Definition tfib_E_internal_memcpy : Z := 0x65d24.
Definition tfib_A_internal_memmove : Z := 0x65d24.  Definition tfib_E_internal_memmove : Z := 0x65d7c.
Definition tfib_A_internal_memset : Z := 0x65d7c.  Definition tfib_E_internal_memset : Z := 0x65ddc.
Definition tfib_A_internal_strcspn : Z := 0x65ddc.  Definition tfib_E_internal_strcspn : Z := 0x65e30.
Definition tfib_A_internal_strdup : Z := 0x65e64.  Definition tfib_E_internal_strdup : Z := 0x65ed0.
Definition tfib_A_internal_strlen : Z := 0x65ed0.  Definition tfib_E_internal_strlen : Z := 0x65eec.
Definition tfib_A_internal_strchrnul : Z := 0x65f7c.  Definition tfib_E_internal_strchrnul : Z := 0x65fc4.
Definition tfib_A_internal_strrchr : Z := 0x65fc4.  Definition tfib_E_internal_strrchr : Z := 0x66004.
Definition tfib_A_internal_strnlen : Z := 0x66134.  Definition tfib_E_internal_strnlen : Z := 0x66164.
Definition tfib_A_internal_strncpy : Z := 0x661a8.  Definition tfib_E_internal_strncpy : Z := 0x66218.
Definition tfib_A_internal_strstr : Z := 0x66218.  Definition tfib_E_internal_strstr : Z := 0x662ac.
Definition tfib_A_mem_is_zero : Z := 0x662ac.  Definition tfib_E_mem_is_zero : Z := 0x66360.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x66360.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x66370.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x66370.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x66550.
Definition tfib_A_internal_iserror : Z := 0x6655c.  Definition tfib_E_internal_iserror : Z := 0x6657c.
Definition tfib_A_internal_mmap : Z := 0x6657c.  Definition tfib_E_internal_mmap : Z := 0x66588.
Definition tfib_A_internal_munmap : Z := 0x66588.  Definition tfib_E_internal_munmap : Z := 0x66594.
Definition tfib_A_internal_mprotect : Z := 0x66594.  Definition tfib_E_internal_mprotect : Z := 0x665a4.
Definition tfib_A_internal_madvise : Z := 0x665a4.  Definition tfib_E_internal_madvise : Z := 0x665d0.
Definition tfib_A_internal_close : Z := 0x665d0.  Definition tfib_E_internal_close : Z := 0x665dc.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x665dc.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x66600.
Definition tfib_A_internal_read : Z := 0x66600.  Definition tfib_E_internal_read : Z := 0x66638.
Definition tfib_A_internal_write : Z := 0x66638.  Definition tfib_E_internal_write : Z := 0x66670.
Definition tfib_A_internal_ftruncate : Z := 0x66670.  Definition tfib_E_internal_ftruncate : Z := 0x666a8.
Definition tfib_A_internal_dup : Z := 0x666a8.  Definition tfib_E_internal_dup : Z := 0x666b4.
Definition tfib_A_internal_dup2_dup3 : Z := 0x666b4.  Definition tfib_E_internal_dup2_dup3 : Z := 0x666c4.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x666c4.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x666dc.
Definition tfib_A_internal_sched_yield : Z := 0x666dc.  Definition tfib_E_internal_sched_yield : Z := 0x666e8.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x666e8.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x66734.
Definition tfib_A_internal_execve : Z := 0x66734.  Definition tfib_E_internal_execve : Z := 0x66740.
Definition tfib_A_internal_exit_exit_group : Z := 0x66740.  Definition tfib_E_internal_exit_exit_group : Z := 0x66754.
Definition tfib_A_FileExists_newfstatat : Z := 0x66754.  Definition tfib_E_FileExists_newfstatat : Z := 0x667d4.
Definition tfib_A_DirExists_newfstatat : Z := 0x667d4.  Definition tfib_E_DirExists_newfstatat : Z := 0x66838.
Definition tfib_A_GetTid_gettid : Z := 0x66838.  Definition tfib_E_GetTid_gettid : Z := 0x66844.
Definition tfib_A_GetEnv : Z := 0x66844.  Definition tfib_E_GetEnv : Z := 0x66974.
Definition tfib_A_FutexWait : Z := 0x66a78.  Definition tfib_E_FutexWait : Z := 0x66a9c.
Definition tfib_A_FutexWake : Z := 0x66a9c.  Definition tfib_E_FutexWake : Z := 0x66ac0.
Definition tfib_A_internal_ptrace : Z := 0x66ac0.  Definition tfib_E_internal_ptrace : Z := 0x66acc.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x66acc.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x66adc.
Definition tfib_A_internal_getpid : Z := 0x66adc.  Definition tfib_E_internal_getpid : Z := 0x66ae8.
Definition tfib_A_internal_getppid : Z := 0x66ae8.  Definition tfib_E_internal_getppid : Z := 0x66af4.
Definition tfib_A_internal_prctl : Z := 0x66af4.  Definition tfib_E_internal_prctl : Z := 0x66b00.
Definition tfib_A_internal_sigaltstack : Z := 0x66b00.  Definition tfib_E_internal_sigaltstack : Z := 0x66b0c.
Definition tfib_A_internal_fork_clone : Z := 0x66b0c.  Definition tfib_E_internal_fork_clone : Z := 0x66b24.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x66b24.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x66c50.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x67390.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x674a8.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x674b0.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6755c.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x6755c.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x6767c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x67744.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x677c4.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x67820.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x678ec.
Definition tfib_A_thunk_653ec : Z := 0x679e8.  Definition tfib_E_thunk_653ec : Z := 0x679ec.
Definition tfib_A_CheckASLR : Z := 0x679ec.  Definition tfib_E_CheckASLR : Z := 0x679f0.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x67c3c.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x67c40.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x67c40.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x67c4c.
Definition tfib_A_MmapOrDie : Z := 0x67c4c.  Definition tfib_E_MmapOrDie : Z := 0x67d58.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x67d58.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x67dcc.
Definition tfib_A_UnmapOrDie : Z := 0x67dcc.  Definition tfib_E_UnmapOrDie : Z := 0x67e48.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x67e48.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x67f58.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x68184.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x68288.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x68294.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6840c.
Definition tfib_A_thunk_66008 : Z := 0x68604.  Definition tfib_E_thunk_66008 : Z := 0x68608.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x68928.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x68b34.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x690ec.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x690f8.
Definition tfib_A_Printf : Z := 0x690fc.  Definition tfib_E_Printf : Z := 0x69148.
Definition tfib_A_SharedPrintfCode : Z := 0x69148.  Definition tfib_E_SharedPrintfCode : Z := 0x691a4.
Definition tfib_A_Report : Z := 0x691a4.  Definition tfib_E_Report : Z := 0x691f0.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6ace8.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6ad44.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6ad44.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6af80.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6af80.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6b2a4.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b844.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b914.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6b914.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6bc64.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6bef4.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6bf54.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6bf54.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6c3cc.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6cc8c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6cfb0.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6cfb8.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6d0bc.
Definition tfib_A_AddDieCallback : Z := 0x6d86c.  Definition tfib_E_AddDieCallback : Z := 0x6d8f4.
Definition tfib_A_Die : Z := 0x6d9b8.  Definition tfib_E_Die : Z := 0x6da78.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6da78.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6da84.
Definition tfib_A_CheckFailed : Z := 0x6da84.  Definition tfib_E_CheckFailed : Z := 0x6db3c.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6e194.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6e28c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6e28c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6e3b8.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6e5e0.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6e65c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6e690.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6e978.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6e978.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6e97c.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6ed6c.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6ee3c.
Definition tfib_A_AndroidLogInit : Z := 0x6f220.  Definition tfib_E_AndroidLogInit : Z := 0x6f224.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6f254.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6f29c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6f29c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6f4e8.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6f4e8.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6f4ec.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6f5f8.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6f6fc.
Definition tfib_A_thunk_6d37c : Z := 0x6f978.  Definition tfib_E_thunk_6d37c : Z := 0x6f97c.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6fa20.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6fa40.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6fa40.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6fae0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6fb6c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6fc30.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6fc30.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6fcb8.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6fcb8.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6fd30.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6fd30.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6fe14.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6fed0.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x70004.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x7023c.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x7036c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x703cc.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x70498.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x722c8.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x723ec.
Definition tfib_A_StackStore_Alloc : Z := 0x723ec.  Definition tfib_E_StackStore_Alloc : Z := 0x72520.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x72dd4.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x72e88.

Definition tfib_A_StackDepotPut : Z := 0x748c4.  Definition tfib_E_StackDepotPut : Z := 0x748e4.
Definition tfib_A_StackDepotBase_Put : Z := 0x748e4.  Definition tfib_E_StackDepotBase_Put : Z := 0x74b68.
Definition tfib_A_StackDepotBase_Get : Z := 0x74b68.  Definition tfib_E_StackDepotBase_Get : Z := 0x74c78.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x75248.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x75250.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x75250.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x753b0.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x753b0.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x75424.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x758ac.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x759c4.
Definition tfib_A_thunk_762d8 : Z := 0x78a10.  Definition tfib_E_thunk_762d8 : Z := 0x78a14.
Definition tfib_A_thunk_77ab0 : Z := 0x7a1e8.  Definition tfib_E_thunk_77ab0 : Z := 0x7a1ec.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7bc14.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7bcd0.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7bcd0.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7bda8.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7bda8.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7c01c.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7c348.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7c38c.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7c38c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7c75c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7ca2c.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7cae4.
Definition tfib_A_thunk_7b6f8 : Z := 0x7de3c.  Definition tfib_E_thunk_7b6f8 : Z := 0x7de40.
Definition tfib_A_lsan_register_root_region : Z := 0x7ea48.  Definition tfib_E_lsan_register_root_region : Z := 0x7ed78.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7ed78.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7f200.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7f200.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7f20c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x82160.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x821dc.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x821dc.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x8228c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x822a4.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x823ec.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x823ec.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x823f8.
Definition tfib_A_asan_default_options_cli_c : Z := 0x823f8.  Definition tfib_E_asan_default_options_cli_c : Z := 0x82404.
Definition tfib_A_main : Z := 0x82404.  Definition tfib_E_main : Z := 0x826c8.
Definition tfib_A_target_alloc_init : Z := 0x826c8.  Definition tfib_E_target_alloc_init : Z := 0x826cc.
Definition tfib_A_target_alloc_count : Z := 0x826cc.  Definition tfib_E_target_alloc_count : Z := 0x826d4.
Definition tfib_A_target_run : Z := 0x826d4.
Definition tfib_A_emit_printf : Z := 0x8285c.  Definition tfib_E_emit_printf : Z := 0x828a4.


Definition tfib_A_asan_module_ctor : Z := 0x838c8.  Definition tfib_E_asan_module_ctor : Z := 0x83900.








Definition tfib_A_asan_module_dtor : Z := 0x83900.  Definition tfib_E_asan_module_dtor : Z := 0x83930.






Definition tfib_A_extenddftf2 : Z := 0x84b30.  Definition tfib_E_extenddftf2 : Z := 0x84cc0.
Definition tfib_A_sysconf : Z := 0x8a910.  Definition tfib_E_sysconf : Z := 0x8ab38.
Definition tfib_A_init : Z := 0x8ab38.  Definition tfib_E_init : Z := 0x8ab3c.
Definition tfib_A_init_libc : Z := 0x8ab3c.  Definition tfib_E_init_libc : Z := 0x8ad68.
Definition tfib_A_libc_start_init : Z := 0x8ad68.  Definition tfib_E_libc_start_init : Z := 0x8adb4.
Definition tfib_A_libc_start_main : Z := 0x8adb4.  Definition tfib_E_libc_start_main : Z := 0x8ae14.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8ae14.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8ae5c.
Definition tfib_A_init_tls : Z := 0x8af34.  Definition tfib_E_init_tls : Z := 0x8b1e4.
Definition tfib_A_init_ssp : Z := 0x8b1e4.  Definition tfib_E_init_ssp : Z := 0x8b244.
Definition tfib_A_stack_chk_fail : Z := 0x8b244.  Definition tfib_E_stack_chk_fail : Z := 0x8b24c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8b294.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8b328.
Definition tfib_A_Exit : Z := 0x8b328.  Definition tfib_E_Exit : Z := 0x8b344.
Definition tfib_A_funcs_on_exit : Z := 0x8b374.  Definition tfib_E_funcs_on_exit : Z := 0x8b43c.
Definition tfib_A_fini_stub_ret : Z := 0x8b43c.  Definition tfib_E_fini_stub_ret : Z := 0x8b440.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8b440.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8b504.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8b508.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8b50c.
Definition tfib_A_libc_exit_fini : Z := 0x8b50c.  Definition tfib_E_libc_exit_fini : Z := 0x8b558.
Definition tfib_A_exit : Z := 0x8b558.  Definition tfib_E_exit : Z := 0x8b5cc.
Definition tfib_A_open : Z := 0x8b7cc.  Definition tfib_E_open : Z := 0x8b8b0.
Definition tfib_A_syscall_ret : Z := 0x8b8b0.  Definition tfib_E_syscall_ret : Z := 0x8b8e8.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8b8e8.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8ba90.
Definition tfib_A_calloc : Z := 0x8c054.  Definition tfib_E_calloc : Z := 0x8c18c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8c18c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8c190.
Definition tfib_A_libc_free : Z := 0x8c190.  Definition tfib_E_libc_free : Z := 0x8c35c.
Definition tfib_A_get_meta : Z := 0x8c35c.  Definition tfib_E_get_meta : Z := 0x8c46c.
Definition tfib_A_alloc_meta : Z := 0x8c844.  Definition tfib_E_alloc_meta : Z := 0x8cb1c.
Definition tfib_A_libc_malloc_impl : Z := 0x8cb1c.  Definition tfib_E_libc_malloc_impl : Z := 0x8ce8c.
Definition tfib_A_alloc_slot : Z := 0x8ce8c.  Definition tfib_E_alloc_slot : Z := 0x8d730.
Definition tfib_A_enframe : Z := 0x8d730.  Definition tfib_E_enframe : Z := 0x8d880.
Definition tfib_A_malloc_allzerop : Z := 0x8d880.  Definition tfib_E_malloc_allzerop : Z := 0x8d9f8.
Definition tfib_A_getrlimit : Z := 0x8f6a8.  Definition tfib_E_getrlimit : Z := 0x8f7a0.
Definition tfib_A_getrusage : Z := 0x8f7a0.  Definition tfib_E_getrusage : Z := 0x8f7c8.
Definition tfib_A_setrlimit : Z := 0x8f7c8.  Definition tfib_E_setrlimit : Z := 0x8f890.
Definition tfib_A_mmap : Z := 0x8fcb8.  Definition tfib_E_mmap : Z := 0x8fda4.
Definition tfib_A_mprotect : Z := 0x8fda4.  Definition tfib_E_mprotect : Z := 0x8fdec.
Definition tfib_A_munmap : Z := 0x8fec0.  Definition tfib_E_munmap : Z := 0x8ff08.
Definition tfib_A_sched_yield : Z := 0x901cc.  Definition tfib_E_sched_yield : Z := 0x901f0.
Definition tfib_A_raise_tkill_path : Z := 0x9024c.  Definition tfib_E_raise_tkill_path : Z := 0x902c4.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x902c4.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x90498.
Definition tfib_A_musl_sigaltstack : Z := 0x90590.  Definition tfib_E_musl_sigaltstack : Z := 0x9061c.

Definition tfib_A_lockfile : Z := 0x90c5c.  Definition tfib_E_lockfile : Z := 0x90d58.
Definition tfib_A_unlockfile : Z := 0x90d58.  Definition tfib_E_unlockfile : Z := 0x90db8.



Definition tfib_A_stdio_read : Z := 0x90948.  Definition tfib_E_stdio_read : Z := 0x90a60.
Definition tfib_A_stdio_write : Z := 0x90a68.  Definition tfib_E_stdio_write : Z := 0x90bf8.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x90918.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9091c.
Definition tfib_A_stdio_close : Z := 0x9091c.  Definition tfib_E_stdio_close : Z := 0x90948.
Definition tfib_A_fwritex : Z := 0x911ec.  Definition tfib_E_fwritex : Z := 0x91324.
Definition tfib_A_musl_fwrite : Z := 0x91324.  Definition tfib_E_musl_fwrite : Z := 0x913dc.
Definition tfib_A_towrite : Z := 0x913dc.  Definition tfib_E_towrite : Z := 0x91430.
Definition tfib_A_stdio_exit : Z := 0x91048.  Definition tfib_E_stdio_exit : Z := 0x911ec.
Definition tfib_A_ofl_lock : Z := 0x91430.  Definition tfib_E_ofl_lock : Z := 0x91460.

Definition tfib_A_musl_vfprintf : Z := 0x915ac.  Definition tfib_E_musl_vfprintf : Z := 0x9175c.
Definition tfib_A_printf_core : Z := 0x9175c.  Definition tfib_E_printf_core : Z := 0x9258c.
Definition tfib_A_pop_arg : Z := 0x9258c.  Definition tfib_E_pop_arg : Z := 0x926c0.
Definition tfib_A_pad : Z := 0x926c0.  Definition tfib_E_pad : Z := 0x92794.
Definition tfib_A_fmt_fp : Z := 0x92794.  Definition tfib_E_fmt_fp : Z := 0x93e5c.
Definition tfib_A_thunk_931e0 : Z := 0x8bca8.  Definition tfib_E_thunk_931e0 : Z := 0x8bcac.
Definition tfib_A_musl_wctomb : Z := 0x90034.  Definition tfib_E_musl_wctomb : Z := 0x90058.
Definition tfib_A_musl_wcrtomb : Z := 0x8ff08.  Definition tfib_E_musl_wcrtomb : Z := 0x90034.
Definition tfib_A_fpclassifyl : Z := 0x8e298.  Definition tfib_E_fpclassifyl : Z := 0x8e2dc.
Definition tfib_A_letf2 : Z := 0x8dad0.  Definition tfib_E_letf2 : Z := 0x8db98.
Definition tfib_A_multf3 : Z := 0x8db98.  Definition tfib_E_multf3 : Z := 0x8e298.
Definition tfib_A_floatsitf : Z := 0x8eaf4.  Definition tfib_E_floatsitf : Z := 0x8ebfc.
Definition tfib_A_scalbn : Z := 0x8f500.  Definition tfib_E_scalbn : Z := 0x8f598.
Definition tfib_A_subtf3 : Z := 0x8eae4.  Definition tfib_E_subtf3 : Z := 0x8eaf4.
Definition tfib_A_addtf3 : Z := 0x8e2dc.  Definition tfib_E_addtf3 : Z := 0x8eaa8.
Definition tfib_A_fe_getround : Z := 0x8eaa8.  Definition tfib_E_fe_getround : Z := 0x8ead8.
Definition tfib_A_fixunstfsi : Z := 0x93e64.  Definition tfib_E_fixunstfsi : Z := 0x93ef8.
Definition tfib_A_floatunsitf : Z := 0x93ef8.  Definition tfib_E_floatunsitf : Z := 0x93fe4.
Definition tfib_A_fixtfsi : Z := 0x8f598.  Definition tfib_E_fixtfsi : Z := 0x8f640.
Definition tfib_A_divtf3 : Z := 0x8ebfc.  Definition tfib_E_divtf3 : Z := 0x8f500.
Definition tfib_A_musl_vprintf : Z := 0x946bc.  Definition tfib_E_musl_vprintf : Z := 0x946d8.
Definition tfib_A_stdout_write : Z := 0x9146c.  Definition tfib_E_stdout_write : Z := 0x9150c.
Definition tfib_A_thunk_95368 : Z := 0x94c70.  Definition tfib_E_thunk_95368 : Z := 0x94c74.
Definition tfib_A_musl_memcmp : Z := 0x94d40.  Definition tfib_E_musl_memcmp : Z := 0x94d70.
Definition tfib_A_musl_memcpy : Z := 0x94d70.  Definition tfib_E_musl_memcpy : Z := 0x95174.
Definition tfib_A_musl_memset : Z := 0x95174.  Definition tfib_E_musl_memset : Z := 0x9526c.
Definition tfib_A_musl_strchr : Z := 0x9526c.  Definition tfib_E_musl_strchr : Z := 0x952a8.
Definition tfib_A_strchrnul : Z := 0x952a8.  Definition tfib_E_strchrnul : Z := 0x95388.
Definition tfib_A_musl_strlen : Z := 0x953c0.  Definition tfib_E_musl_strlen : Z := 0x95450.
Definition tfib_A_musl_strnlen : Z := 0x955fc.  Definition tfib_E_musl_strnlen : Z := 0x95640.
Definition tfib_A_musl_memchr : Z := 0x94c74.  Definition tfib_E_musl_memchr : Z := 0x94d40.
Definition tfib_A_lock : Z := 0x95640.  Definition tfib_E_lock : Z := 0x958c8.
Definition tfib_A_unlock : Z := 0x958c8.  Definition tfib_E_unlock : Z := 0x9593c.
Definition tfib_A_syscall_cp_c : Z := 0x9593c.  Definition tfib_E_syscall_cp_c : Z := 0x95960.
Definition tfib_A_syscall_cp_sccp : Z := 0x95960.  Definition tfib_E_syscall_cp_sccp : Z := 0x95964.
Definition tfib_A_pthread_atfork : Z := 0x959a0.  Definition tfib_E_pthread_atfork : Z := 0x95a44.
Definition tfib_A_mremap : Z := 0x8fdec.  Definition tfib_E_mremap : Z := 0x8fec0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x96a18.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x96a34.
Definition tfib_A_pthread_key_create : Z := 0x96dc0.  Definition tfib_E_pthread_key_create : Z := 0x96e94.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x97138.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x971dc.
Definition tfib_A_pthread_setspecific : Z := 0x9735c.  Definition tfib_E_pthread_setspecific : Z := 0x97390.
Definition tfib_A_set_thread_area : Z := 0x97398.
Definition tfib_A_thunk_96f9c : Z := 0x97390.  Definition tfib_E_thunk_96f9c : Z := 0x97398.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97cc4.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97d7c.
Definition tfib_A_close : Z := 0x9a394.  Definition tfib_E_close : Z := 0x9a3e8.
Definition tfib_A_musl_read : Z := 0x9a474.  Definition tfib_E_musl_read : Z := 0x9a4a8.
Definition tfib_A_vm_wait : Z := 0x979d4.  Definition tfib_E_vm_wait : Z := 0x97a24.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x9b4a8.
Definition tfib_D_fini_array_0_1 : Z := 0x9b4c8.
Definition tfib_D_GOT_common_flags : Z := 0x9ba30.
Definition tfib_D_GOT_flags : Z := 0x9ba38.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9ba40.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9ba48.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9ba50.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9ba58.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9c5a8.
Definition tfib_D_environ_musl : Z := 0x9c6d8.
Definition tfib_D_REAL_read : Z := 0x9d780.
Definition tfib_D_REAL_memcpy : Z := 0x9d8a8.
Definition tfib_D_REAL_memset : Z := 0x9d8b0.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa0498.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa12f8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa3af8.
Definition tfib_D_asan_inited : Z := 0xa47d8.
Definition tfib_D_replace_intrin_cached : Z := 0xa47d9.
Definition tfib_D_kHighMemEnd : Z := 0xa47e0.
Definition tfib_D_kMidMemBeg : Z := 0xa47e8.
Definition tfib_D_kMidMemEnd : Z := 0xa47f0.
Definition tfib_D_malloc_context_size : Z := 0xa47fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x135628.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f6d28.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f9000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x32b44.
Definition tfib_at_rw_lo : Z := 0x9d000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x65d7c.
Definition tfib_at_x_imemcpy : Z := 0x65d00.
Definition tfib_at_x_memset : Z := 0x95174.
Definition tfib_at_x_memcpy : Z := 0x94d70.
Definition tfib_at_x_memiszero : Z := 0x662ac.
Definition tfib_at_x_istrncpy : Z := 0x661a8.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x38f30.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8ab74.
Definition tfib_at_x_envscan_k : Z := 0x8ab80.
Definition tfib_at_x_pnscan : Z := 0x8ac38.
Definition tfib_at_x_pnscan_k : Z := 0x8ac44.
Definition tfib_at_stops_more : list Z := (0x36ba4 :: 0x381c8 :: 0x56088 :: 0x5c440 :: 0x5c454 :: 0x5c468 :: 0x61df8 :: 0x61ec8 :: 0x6f3f4 :: 0x70300 :: 0x70490 :: 0x7a1e8 :: nil)%list.
