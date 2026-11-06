(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2530c.
Definition tfib_text_lo : Z := 0x32b18.
Definition tfib_init_array_lo : Z := 0x9b178.  Definition tfib_init_array_hi : Z := 0x9b198.
Definition tfib_fini_array_lo : Z := 0x9b198.  Definition tfib_fini_array_hi : Z := 0x9b1a8.
Definition tfib_preinit_array_lo : Z := 0x9b1a8.  Definition tfib_preinit_array_hi : Z := 0x9b1b0.
Definition tfib_data_rel_ro_lo : Z := 0x9b1b0.  Definition tfib_data_rel_ro_hi : Z := 0x9b6b0.
Definition tfib_got_lo : Z := 0x9b6b0.  Definition tfib_got_hi : Z := 0x9c410.
Definition tfib_data_lo : Z := 0x9d410.  Definition tfib_data_hi : Z := 0x9ffc8.
Definition tfib_asan_globals_lo : Z := 0x9ffd0.  Definition tfib_asan_globals_hi : Z := 0xa0110.
Definition tfib_bss_lo : Z := 0xa0140.  Definition tfib_bss_hi : Z := 0x5f8078.
Definition tfib_tbss_lo : Z := 0x9a178.  Definition tfib_tbss_hi : Z := 0x9a18c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f9000.
Definition tfib_entry : Z := 0x32b18.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x32b18.
Definition tfib_A_do_init : Z := 0x32b60.  Definition tfib_E_do_init : Z := 0x32bd4.
Definition tfib_A_do_fini : Z := 0x32bd4.  Definition tfib_E_do_fini : Z := 0x32c64.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x32c64.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x32ca0.
Definition tfib_A_InitializeAllocator : Z := 0x32e10.  Definition tfib_E_InitializeAllocator : Z := 0x32e28.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x32e28.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x32f94.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x334f0.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x3364c.
Definition tfib_A_asan_free : Z := 0x33a20.  Definition tfib_E_asan_free : Z := 0x33a48.
Definition tfib_A_Allocator_Deallocate : Z := 0x33a48.  Definition tfib_E_Allocator_Deallocate : Z := 0x33d00.
Definition tfib_A_asan_malloc : Z := 0x33d00.  Definition tfib_E_asan_malloc : Z := 0x33d5c.
Definition tfib_A_Allocator_Allocate : Z := 0x33d5c.  Definition tfib_E_Allocator_Allocate : Z := 0x346e4.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34e1c.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34f60.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x3504c.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x350a8.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x350a8.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x352f8.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x352f8.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x353ec.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x35da8.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x3602c.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x3602c.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x361ac.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x361ac.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x36374.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x36374.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x36540.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x365e0.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x366e4.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x36a0c.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x36b54.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x36b54.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x36b8c.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37324.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x3760c.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x37ce4.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x37e5c.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x37e5c.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x3800c.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x3800c.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x381f0.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x381f0.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x384c8.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x384c8.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x38940.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x38940.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x38a40.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x38a40.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x38d48.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x38d48.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x390b8.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x395d4.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x396bc.
Definition tfib_A_AsanActivate : Z := 0x396bc.  Definition tfib_E_AsanActivate : Z := 0x39798.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x39c74.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x39d5c.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3e814.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3e8ec.
Definition tfib_A_FakeStack_Create : Z := 0x3e8ec.  Definition tfib_E_FakeStack_Create : Z := 0x3e9d8.
Definition tfib_A_SetTLSFakeStack : Z := 0x3f0b0.  Definition tfib_E_SetTLSFakeStack : Z := 0x3f0e0.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3f0e0.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3f270.
Definition tfib_A_asan_stack_malloc_B : Z := 0x3f270.  Definition tfib_E_asan_stack_malloc_B : Z := 0x3f40c.
Definition tfib_A_asan_InitializeFlags : Z := 0x3f714.  Definition tfib_E_asan_InitializeFlags : Z := 0x40740.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40e4c.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x41c68.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x41c68.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x42234.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x42988.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x42bf8.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42bf8.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42f00.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x43674.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x437c4.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x441e0.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x442f8.
Definition tfib_A_thunk_417bc : Z := 0x44338.  Definition tfib_E_thunk_417bc : Z := 0x4433c.
Definition tfib_A_thunk_417cc : Z := 0x44348.  Definition tfib_E_thunk_417cc : Z := 0x44350.
Definition tfib_A_tls_get_addr_thunk : Z := 0x44354.  Definition tfib_E_tls_get_addr_thunk : Z := 0x44358.
Definition tfib_A_check_step : Z := 0x8319c.  Definition tfib_E_check_step : Z := 0x83758.  Definition tfib_A_reac_ctrl_checksum_verify : Z := 0x837c0.  Definition tfib_E_reac_ctrl_checksum_verify : Z := 0x83834.  Definition tfib_A_reac_ctrl_build_scene_step : Z := 0x83834.  Definition tfib_E_reac_ctrl_build_scene_step : Z := 0x83bdc.  Definition tfib_A_reac_ctrl_scene_set_mac : Z := 0x83bdc.  Definition tfib_E_reac_ctrl_scene_set_mac : Z := 0x83c24.  Definition tfib_A_reac_ctrl_scene_build : Z := 0x83c24.  Definition tfib_E_reac_ctrl_scene_build : Z := 0x83dd8.  Definition tfib_A_reac_ctrl_parse : Z := 0x83dd8.  Definition tfib_E_reac_ctrl_parse : Z := 0x84778.  Definition tfib_A_kind_of_link1 : Z := 0x84778.  Definition tfib_E_kind_of_link1 : Z := 0x847ec.
Definition tfib_A_thunk_417dc : Z := 0x44358.  Definition tfib_E_thunk_417dc : Z := 0x4435c.

Definition tfib_A_thunk_417e4 : Z := 0x4435c.  Definition tfib_E_thunk_417e4 : Z := 0x44360.
Definition tfib_A_thunk_417e8 : Z := 0x44360.  Definition tfib_E_thunk_417e8 : Z := 0x44364.
Definition tfib_A_thunk_417ec : Z := 0x44364.  Definition tfib_E_thunk_417ec : Z := 0x44368.
Definition tfib_A_thunk_417f0 : Z := 0x44368.  Definition tfib_E_thunk_417f0 : Z := 0x4436c.
Definition tfib_A_thunk_417f8 : Z := 0x44370.  Definition tfib_E_thunk_417f8 : Z := 0x44374.
Definition tfib_A_thunk_4180c : Z := 0x44384.  Definition tfib_E_thunk_4180c : Z := 0x44388.
Definition tfib_A_icpt_strlen : Z := 0x44388.  Definition tfib_E_icpt_strlen : Z := 0x4461c.
Definition tfib_A_icpt_strnlen : Z := 0x4461c.  Definition tfib_E_icpt_strnlen : Z := 0x448b0.
Definition tfib_A_icpt_strcmp : Z := 0x448b4.  Definition tfib_E_icpt_strcmp : Z := 0x44de4.
Definition tfib_A_icpt_strchr : Z := 0x44de4.  Definition tfib_E_icpt_strchr : Z := 0x450c4.
Definition tfib_A_icpt_memcmp : Z := 0x4595c.  Definition tfib_E_icpt_memcmp : Z := 0x45a18.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x45a18.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x45ad4.
Definition tfib_A_icpt_memchr : Z := 0x45ad4.  Definition tfib_E_icpt_memchr : Z := 0x45da4.
Definition tfib_A_icpt_frexpl : Z := 0x45da4.  Definition tfib_E_icpt_frexpl : Z := 0x4601c.
Definition tfib_A_icpt_read : Z := 0x4601c.  Definition tfib_E_icpt_read : Z := 0x4628c.
Definition tfib_A_icpt_fwrite : Z := 0x4628c.  Definition tfib_E_icpt_fwrite : Z := 0x46500.
Definition tfib_A_icpt_time : Z := 0x46500.  Definition tfib_E_icpt_time : Z := 0x4679c.
Definition tfib_A_icpt_gmtime_r : Z := 0x469a4.  Definition tfib_E_icpt_gmtime_r : Z := 0x46be4.
Definition tfib_A_icpt_vprintf : Z := 0x46be4.  Definition tfib_E_icpt_vprintf : Z := 0x46c80.
Definition tfib_A_printf_common_format_interceptor : Z := 0x46c80.  Definition tfib_E_printf_common_format_interceptor : Z := 0x47748.
Definition tfib_A_icpt_vfprintf : Z := 0x47748.  Definition tfib_E_icpt_vfprintf : Z := 0x477fc.
Definition tfib_A_icpt_vsnprintf : Z := 0x477fc.  Definition tfib_E_icpt_vsnprintf : Z := 0x47b14.
Definition tfib_A_icpt_clock_gettime : Z := 0x47c90.  Definition tfib_E_icpt_clock_gettime : Z := 0x47ee8.
Definition tfib_A_icpt_wcrtomb : Z := 0x47ee8.  Definition tfib_E_icpt_wcrtomb : Z := 0x48458.
Definition tfib_A_icpt_wctomb : Z := 0x48458.  Definition tfib_E_icpt_wctomb : Z := 0x487b4.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x48880.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x48c68.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x48c74.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x48cf0.


Definition tfib_A_icpt_sem_timedwait : Z := 0x48efc.  Definition tfib_E_icpt_sem_timedwait : Z := 0x49194.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x491c4.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x493ec.
Definition tfib_A_icpt_send : Z := 0x493ec.  Definition tfib_E_icpt_send : Z := 0x496a0.
Definition tfib_A_icpt_sendto : Z := 0x496a0.  Definition tfib_E_icpt_sendto : Z := 0x49964.
Definition tfib_A_icpt_sigaltstack : Z := 0x49964.  Definition tfib_E_icpt_sigaltstack : Z := 0x49bc0.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x49c94.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x49e44.
Definition tfib_A_icpt_diouxXn : Z := 0x49e44.  Definition tfib_E_icpt_diouxXn : Z := 0x49fdc.
Definition tfib_A_asan_memcpy : Z := 0x539c4.  Definition tfib_E_asan_memcpy : Z := 0x53e60.
Definition tfib_A_asan_memset : Z := 0x53e60.  Definition tfib_E_asan_memset : Z := 0x540a0.
Definition tfib_A_icpt_memset : Z := 0x540a0.  Definition tfib_E_icpt_memset : Z := 0x54390.
Definition tfib_A_icpt_memcpy : Z := 0x54390.  Definition tfib_E_icpt_memcpy : Z := 0x54980.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x54980.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x549b8.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x549b8.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x549bc.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x549bc.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x549c0.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x549c0.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x54a20.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x54a6c.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x54ba8.
Definition tfib_A_free : Z := 0x54d14.  Definition tfib_E_free : Z := 0x54d18.
Definition tfib_A_malloc : Z := 0x54d18.  Definition tfib_E_malloc : Z := 0x54d1c.
Definition tfib_A_icpt_free : Z := 0x54d1c.  Definition tfib_E_icpt_free : Z := 0x54eec.
Definition tfib_A_icpt_malloc : Z := 0x54eec.  Definition tfib_E_icpt_malloc : Z := 0x55048.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x55114.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x55118.
Definition tfib_A_SetCanPoisonMemory : Z := 0x55b94.  Definition tfib_E_SetCanPoisonMemory : Z := 0x55ba4.
Definition tfib_A_CanPoisonMemory : Z := 0x55ba4.  Definition tfib_E_CanPoisonMemory : Z := 0x55bb8.
Definition tfib_A_PoisonShadow : Z := 0x55bb8.  Definition tfib_E_PoisonShadow : Z := 0x560b4.
Definition tfib_A_MemToShadow_checked : Z := 0x560b4.  Definition tfib_E_MemToShadow_checked : Z := 0x561f0.
Definition tfib_A_asan_region_is_poisoned : Z := 0x56540.  Definition tfib_E_asan_region_is_poisoned : Z := 0x56884.
Definition tfib_A_AsanTSDInit : Z := 0x56ca4.  Definition tfib_E_AsanTSDInit : Z := 0x56d20.
Definition tfib_A_AsanTSDGet : Z := 0x56d20.  Definition tfib_E_AsanTSDGet : Z := 0x56d60.
Definition tfib_A_AsanTSDSet : Z := 0x56d60.  Definition tfib_E_AsanTSDSet : Z := 0x56da0.
Definition tfib_A_PlatformTSDDtor : Z := 0x56da0.  Definition tfib_E_PlatformTSDDtor : Z := 0x56e24.
Definition tfib_A_InstallAtForkHandler : Z := 0x56e24.  Definition tfib_E_InstallAtForkHandler : Z := 0x56e40.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x56ea0.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x56ee4.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x575fc.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x57808.
Definition tfib_A_ReportDoubleFree : Z := 0x57f10.  Definition tfib_E_ReportDoubleFree : Z := 0x581a0.
Definition tfib_A_ReportGenericError : Z := 0x59a7c.  Definition tfib_E_ReportGenericError : Z := 0x5a338.
Definition tfib_A_AsanInited : Z := 0x5aac4.  Definition tfib_E_AsanInited : Z := 0x5aadc.
Definition tfib_A_asan_report_load1 : Z := 0x5aadc.  Definition tfib_E_asan_report_load1 : Z := 0x5ab2c.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5ab2c.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5ab7c.
Definition tfib_A_asan_report_load2 : Z := 0x5ab7c.  Definition tfib_E_asan_report_load2 : Z := 0x5abcc.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5abcc.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5ac1c.
Definition tfib_A_asan_report_load4 : Z := 0x5ac1c.  Definition tfib_E_asan_report_load4 : Z := 0x5ac6c.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5ac6c.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5acbc.
Definition tfib_A_asan_report_load8 : Z := 0x5acbc.  Definition tfib_E_asan_report_load8 : Z := 0x5ad0c.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5ad0c.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5ad5c.
Definition tfib_A_asan_report_load16 : Z := 0x5ad5c.  Definition tfib_E_asan_report_load16 : Z := 0x5adac.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5adac.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5adfc.
Definition tfib_A_asan_report_store1 : Z := 0x5adfc.  Definition tfib_E_asan_report_store1 : Z := 0x5ae4c.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5ae4c.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5ae9c.
Definition tfib_A_asan_report_store2 : Z := 0x5ae9c.  Definition tfib_E_asan_report_store2 : Z := 0x5aeec.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5aeec.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5af3c.
Definition tfib_A_asan_report_store4 : Z := 0x5af3c.  Definition tfib_E_asan_report_store4 : Z := 0x5af8c.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5af8c.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5afdc.
Definition tfib_A_asan_report_store8 : Z := 0x5afdc.  Definition tfib_E_asan_report_store8 : Z := 0x5b02c.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5b02c.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5b07c.
Definition tfib_A_asan_report_store16 : Z := 0x5b07c.  Definition tfib_E_asan_report_store16 : Z := 0x5b0cc.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5b0cc.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5b11c.
Definition tfib_A_asan_report_load_n : Z := 0x5b11c.  Definition tfib_E_asan_report_load_n : Z := 0x5b16c.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5b16c.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5b1bc.
Definition tfib_A_asan_report_store_n : Z := 0x5b1bc.  Definition tfib_E_asan_report_store_n : Z := 0x5b20c.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5b20c.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5b25c.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5b25c.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5b2dc.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5b2dc.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5b690.
Definition tfib_A_AsanInitInternal : Z := 0x5b720.  Definition tfib_E_AsanInitInternal : Z := 0x5b9d4.
Definition tfib_A_thunk_59674 : Z := 0x5bc3c.  Definition tfib_E_thunk_59674 : Z := 0x5bc40.
Definition tfib_A_asan_init : Z := 0x5bc40.  Definition tfib_E_asan_init : Z := 0x5bcd4.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5bcd4.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5bcd8.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5bcd8.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5bd3c.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5bf3c.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5c264.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5c264.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5c444.
Definition tfib_A_InitializeShadowMemory : Z := 0x5c444.  Definition tfib_E_InitializeShadowMemory : Z := 0x5c74c.
Definition tfib_A_SetMallocContextSize : Z := 0x5c74c.  Definition tfib_E_SetMallocContextSize : Z := 0x5c75c.
Definition tfib_A_GetMallocContextSize : Z := 0x5c75c.  Definition tfib_E_GetMallocContextSize : Z := 0x5c76c.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5c76c.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5c8bc.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5d3a0.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5d3d8.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5d680.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5d68c.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5d68c.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5d718.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5d718.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5d780.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5d780.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5d7f8.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5d7f8.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5d860.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5dc38.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5dc44.
Definition tfib_A_AsanThread_Create : Z := 0x5ddc4.  Definition tfib_E_AsanThread_Create : Z := 0x5df60.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5dfbc.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5e1d4.
Definition tfib_A_GetCurrentThread : Z := 0x5e1d4.  Definition tfib_E_GetCurrentThread : Z := 0x5e1f4.
Definition tfib_A_AsanThread_stack_top : Z := 0x5e398.  Definition tfib_E_AsanThread_stack_top : Z := 0x5e3f0.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5e3f0.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5e448.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5e448.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5e678.
Definition tfib_A_AsanThread_Init : Z := 0x5e678.  Definition tfib_E_AsanThread_Init : Z := 0x5ea6c.
Definition tfib_A_CreateMainThread : Z := 0x5ebac.  Definition tfib_E_CreateMainThread : Z := 0x5ecbc.
Definition tfib_A_SetCurrentThread : Z := 0x5ecbc.  Definition tfib_E_SetCurrentThread : Z := 0x5ed9c.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5efa0.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5f0dc.
Definition tfib_A_weak_default_hook_ret : Z := 0x5fdb0.  Definition tfib_E_weak_default_hook_ret : Z := 0x5fdb4.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x605a0.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x606ec.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x606ec.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x60738.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x60738.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x60744.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x60774.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x60780.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x60780.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x6078c.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x607a8.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x60a74.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x60a74.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x60e34.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x61d90.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x61d9c.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x61d9c.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x61e74.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x61e74.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x61f10.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x62434.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x62478.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x626f0.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x62804.
Definition tfib_A_RunMallocHooks : Z := 0x629a8.  Definition tfib_E_RunMallocHooks : Z := 0x62a60.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x62a60.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x62a64.
Definition tfib_A_RunFreeHooks : Z := 0x62a64.  Definition tfib_E_RunFreeHooks : Z := 0x62b10.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x62b44.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x62b90.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x62e54.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x63094.
Definition tfib_A_sanitizer_set_report_path : Z := 0x63690.  Definition tfib_E_sanitizer_set_report_path : Z := 0x636a8.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x652b8.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x655c8.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x655c8.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x6570c.
Definition tfib_A_FlagParser_ParseString : Z := 0x6570c.  Definition tfib_E_FlagParser_ParseString : Z := 0x65800.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x65994.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x659f4.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x659f4.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x65a34.
Definition tfib_A_internal_atoll : Z := 0x65a34.  Definition tfib_E_internal_atoll : Z := 0x65b20.
Definition tfib_A_internal_simple_strtoll : Z := 0x65b20.  Definition tfib_E_internal_simple_strtoll : Z := 0x65c7c.
Definition tfib_A_internal_memchr : Z := 0x65c7c.  Definition tfib_E_internal_memchr : Z := 0x65c9c.
Definition tfib_A_internal_memcmp : Z := 0x65c9c.  Definition tfib_E_internal_memcmp : Z := 0x65cd4.
Definition tfib_A_internal_memcpy : Z := 0x65cd4.  Definition tfib_E_internal_memcpy : Z := 0x65cf8.
Definition tfib_A_internal_memmove : Z := 0x65cf8.  Definition tfib_E_internal_memmove : Z := 0x65d50.
Definition tfib_A_internal_memset : Z := 0x65d50.  Definition tfib_E_internal_memset : Z := 0x65db0.
Definition tfib_A_internal_strcspn : Z := 0x65db0.  Definition tfib_E_internal_strcspn : Z := 0x65e04.
Definition tfib_A_internal_strdup : Z := 0x65e38.  Definition tfib_E_internal_strdup : Z := 0x65ea4.
Definition tfib_A_internal_strlen : Z := 0x65ea4.  Definition tfib_E_internal_strlen : Z := 0x65ec0.
Definition tfib_A_internal_strchrnul : Z := 0x65f50.  Definition tfib_E_internal_strchrnul : Z := 0x65f98.
Definition tfib_A_internal_strrchr : Z := 0x65f98.  Definition tfib_E_internal_strrchr : Z := 0x65fd8.
Definition tfib_A_internal_strnlen : Z := 0x66108.  Definition tfib_E_internal_strnlen : Z := 0x66138.
Definition tfib_A_internal_strncpy : Z := 0x6617c.  Definition tfib_E_internal_strncpy : Z := 0x661ec.
Definition tfib_A_internal_strstr : Z := 0x661ec.  Definition tfib_E_internal_strstr : Z := 0x66280.
Definition tfib_A_mem_is_zero : Z := 0x66280.  Definition tfib_E_mem_is_zero : Z := 0x66334.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x66334.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x66344.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x66344.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x66524.
Definition tfib_A_internal_iserror : Z := 0x66530.  Definition tfib_E_internal_iserror : Z := 0x66550.
Definition tfib_A_internal_mmap : Z := 0x66550.  Definition tfib_E_internal_mmap : Z := 0x6655c.
Definition tfib_A_internal_munmap : Z := 0x6655c.  Definition tfib_E_internal_munmap : Z := 0x66568.
Definition tfib_A_internal_mprotect : Z := 0x66568.  Definition tfib_E_internal_mprotect : Z := 0x66578.
Definition tfib_A_internal_madvise : Z := 0x66578.  Definition tfib_E_internal_madvise : Z := 0x665a4.
Definition tfib_A_internal_close : Z := 0x665a4.  Definition tfib_E_internal_close : Z := 0x665b0.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x665b0.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x665d4.
Definition tfib_A_internal_read : Z := 0x665d4.  Definition tfib_E_internal_read : Z := 0x6660c.
Definition tfib_A_internal_write : Z := 0x6660c.  Definition tfib_E_internal_write : Z := 0x66644.
Definition tfib_A_internal_ftruncate : Z := 0x66644.  Definition tfib_E_internal_ftruncate : Z := 0x6667c.
Definition tfib_A_internal_dup : Z := 0x6667c.  Definition tfib_E_internal_dup : Z := 0x66688.
Definition tfib_A_internal_dup2_dup3 : Z := 0x66688.  Definition tfib_E_internal_dup2_dup3 : Z := 0x66698.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x66698.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x666b0.
Definition tfib_A_internal_sched_yield : Z := 0x666b0.  Definition tfib_E_internal_sched_yield : Z := 0x666bc.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x666bc.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x66708.
Definition tfib_A_internal_execve : Z := 0x66708.  Definition tfib_E_internal_execve : Z := 0x66714.
Definition tfib_A_internal_exit_exit_group : Z := 0x66714.  Definition tfib_E_internal_exit_exit_group : Z := 0x66728.
Definition tfib_A_FileExists_newfstatat : Z := 0x66728.  Definition tfib_E_FileExists_newfstatat : Z := 0x667a8.
Definition tfib_A_DirExists_newfstatat : Z := 0x667a8.  Definition tfib_E_DirExists_newfstatat : Z := 0x6680c.
Definition tfib_A_GetTid_gettid : Z := 0x6680c.  Definition tfib_E_GetTid_gettid : Z := 0x66818.
Definition tfib_A_GetEnv : Z := 0x66818.  Definition tfib_E_GetEnv : Z := 0x66948.
Definition tfib_A_FutexWait : Z := 0x66a4c.  Definition tfib_E_FutexWait : Z := 0x66a70.
Definition tfib_A_FutexWake : Z := 0x66a70.  Definition tfib_E_FutexWake : Z := 0x66a94.
Definition tfib_A_internal_ptrace : Z := 0x66a94.  Definition tfib_E_internal_ptrace : Z := 0x66aa0.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x66aa0.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x66ab0.
Definition tfib_A_internal_getpid : Z := 0x66ab0.  Definition tfib_E_internal_getpid : Z := 0x66abc.
Definition tfib_A_internal_getppid : Z := 0x66abc.  Definition tfib_E_internal_getppid : Z := 0x66ac8.
Definition tfib_A_internal_prctl : Z := 0x66ac8.  Definition tfib_E_internal_prctl : Z := 0x66ad4.
Definition tfib_A_internal_sigaltstack : Z := 0x66ad4.  Definition tfib_E_internal_sigaltstack : Z := 0x66ae0.
Definition tfib_A_internal_fork_clone : Z := 0x66ae0.  Definition tfib_E_internal_fork_clone : Z := 0x66af8.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x66af8.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x66c24.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x67364.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6747c.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x67484.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x67530.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x67530.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x67650.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x67718.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x67798.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x677f4.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x678c0.
Definition tfib_A_thunk_653ec : Z := 0x679bc.  Definition tfib_E_thunk_653ec : Z := 0x679c0.
Definition tfib_A_CheckASLR : Z := 0x679c0.  Definition tfib_E_CheckASLR : Z := 0x679c4.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x67c10.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x67c14.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x67c14.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x67c20.
Definition tfib_A_MmapOrDie : Z := 0x67c20.  Definition tfib_E_MmapOrDie : Z := 0x67d2c.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x67d2c.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x67da0.
Definition tfib_A_UnmapOrDie : Z := 0x67da0.  Definition tfib_E_UnmapOrDie : Z := 0x67e1c.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x67e1c.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x67f2c.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x68158.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6825c.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x68268.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x683e0.
Definition tfib_A_thunk_66008 : Z := 0x685d8.  Definition tfib_E_thunk_66008 : Z := 0x685dc.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x688fc.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x68b08.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x690c0.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x690cc.
Definition tfib_A_Printf : Z := 0x690d0.  Definition tfib_E_Printf : Z := 0x6911c.
Definition tfib_A_SharedPrintfCode : Z := 0x6911c.  Definition tfib_E_SharedPrintfCode : Z := 0x69178.
Definition tfib_A_Report : Z := 0x69178.  Definition tfib_E_Report : Z := 0x691c4.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6acbc.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6ad18.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6ad18.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6af54.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6af54.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6b278.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b818.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b8e8.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6b8e8.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6bc38.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6bec8.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6bf28.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6bf28.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6c3a0.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6cc60.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6cf84.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6cf8c.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6d090.
Definition tfib_A_AddDieCallback : Z := 0x6d840.  Definition tfib_E_AddDieCallback : Z := 0x6d8c8.
Definition tfib_A_Die : Z := 0x6d98c.  Definition tfib_E_Die : Z := 0x6da4c.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6da4c.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6da58.
Definition tfib_A_CheckFailed : Z := 0x6da58.  Definition tfib_E_CheckFailed : Z := 0x6db10.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6e168.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6e260.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6e260.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6e38c.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6e5b4.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6e630.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6e664.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6e94c.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6e94c.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6e950.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6ed40.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6ee10.
Definition tfib_A_AndroidLogInit : Z := 0x6f1f4.  Definition tfib_E_AndroidLogInit : Z := 0x6f1f8.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6f228.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6f270.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6f270.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6f4bc.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6f4bc.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6f4c0.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6f5cc.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6f6d0.
Definition tfib_A_thunk_6d37c : Z := 0x6f94c.  Definition tfib_E_thunk_6d37c : Z := 0x6f950.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6f9f4.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6fa14.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6fa14.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6fab4.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6fb40.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6fc04.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6fc04.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6fc8c.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6fc8c.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6fd04.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6fd04.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6fde8.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6fea4.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6ffd8.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x70210.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x70340.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x703a0.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x7046c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x7229c.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x723c0.
Definition tfib_A_StackStore_Alloc : Z := 0x723c0.  Definition tfib_E_StackStore_Alloc : Z := 0x724f4.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x72da8.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x72e5c.

Definition tfib_A_StackDepotPut : Z := 0x74898.  Definition tfib_E_StackDepotPut : Z := 0x748b8.
Definition tfib_A_StackDepotBase_Put : Z := 0x748b8.  Definition tfib_E_StackDepotBase_Put : Z := 0x74b3c.
Definition tfib_A_StackDepotBase_Get : Z := 0x74b3c.  Definition tfib_E_StackDepotBase_Get : Z := 0x74c4c.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x7521c.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x75224.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x75224.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x75384.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x75384.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x753f8.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x75880.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x75998.
Definition tfib_A_thunk_762d8 : Z := 0x789e4.  Definition tfib_E_thunk_762d8 : Z := 0x789e8.
Definition tfib_A_thunk_77ab0 : Z := 0x7a1bc.  Definition tfib_E_thunk_77ab0 : Z := 0x7a1c0.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7bbe8.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7bca4.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7bca4.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7bd7c.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7bd7c.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7bff0.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7c31c.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7c360.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7c360.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7c730.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7ca00.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7cab8.
Definition tfib_A_thunk_7b6f8 : Z := 0x7de10.  Definition tfib_E_thunk_7b6f8 : Z := 0x7de14.
Definition tfib_A_lsan_register_root_region : Z := 0x7ea1c.  Definition tfib_E_lsan_register_root_region : Z := 0x7ed4c.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7ed4c.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7f1d4.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7f1d4.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7f1e0.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x82134.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x821b0.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x821b0.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x82260.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x82278.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x823c0.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x823c0.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x823cc.
Definition tfib_A_asan_default_options_cli_c : Z := 0x823cc.  Definition tfib_E_asan_default_options_cli_c : Z := 0x823d8.
Definition tfib_A_main : Z := 0x823d8.  Definition tfib_E_main : Z := 0x8269c.
Definition tfib_A_target_alloc_init : Z := 0x8269c.  Definition tfib_E_target_alloc_init : Z := 0x826a0.
Definition tfib_A_target_alloc_count : Z := 0x826a0.  Definition tfib_E_target_alloc_count : Z := 0x826a8.
Definition tfib_A_target_run : Z := 0x826a8.
Definition tfib_A_emit_printf : Z := 0x82830.  Definition tfib_E_emit_printf : Z := 0x82878.


Definition tfib_A_asan_module_ctor : Z := 0x83758.  Definition tfib_E_asan_module_ctor : Z := 0x83790.








Definition tfib_A_asan_module_dtor : Z := 0x83790.  Definition tfib_E_asan_module_dtor : Z := 0x837c0.






Definition tfib_A_extenddftf2 : Z := 0x847fc.  Definition tfib_E_extenddftf2 : Z := 0x8498c.
Definition tfib_A_sysconf : Z := 0x8a5dc.  Definition tfib_E_sysconf : Z := 0x8a804.
Definition tfib_A_init : Z := 0x8a804.  Definition tfib_E_init : Z := 0x8a808.
Definition tfib_A_init_libc : Z := 0x8a808.  Definition tfib_E_init_libc : Z := 0x8aa34.
Definition tfib_A_libc_start_init : Z := 0x8aa34.  Definition tfib_E_libc_start_init : Z := 0x8aa80.
Definition tfib_A_libc_start_main : Z := 0x8aa80.  Definition tfib_E_libc_start_main : Z := 0x8aae0.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8aae0.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8ab28.
Definition tfib_A_init_tls : Z := 0x8ac00.  Definition tfib_E_init_tls : Z := 0x8aeb0.
Definition tfib_A_init_ssp : Z := 0x8aeb0.  Definition tfib_E_init_ssp : Z := 0x8af10.
Definition tfib_A_stack_chk_fail : Z := 0x8af10.  Definition tfib_E_stack_chk_fail : Z := 0x8af18.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8af60.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8aff4.
Definition tfib_A_Exit : Z := 0x8aff4.  Definition tfib_E_Exit : Z := 0x8b010.
Definition tfib_A_funcs_on_exit : Z := 0x8b040.  Definition tfib_E_funcs_on_exit : Z := 0x8b108.
Definition tfib_A_fini_stub_ret : Z := 0x8b108.  Definition tfib_E_fini_stub_ret : Z := 0x8b10c.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8b10c.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8b1d0.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8b1d4.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8b1d8.
Definition tfib_A_libc_exit_fini : Z := 0x8b1d8.  Definition tfib_E_libc_exit_fini : Z := 0x8b224.
Definition tfib_A_exit : Z := 0x8b224.  Definition tfib_E_exit : Z := 0x8b298.
Definition tfib_A_open : Z := 0x8b498.  Definition tfib_E_open : Z := 0x8b57c.
Definition tfib_A_syscall_ret : Z := 0x8b57c.  Definition tfib_E_syscall_ret : Z := 0x8b5b4.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8b5b4.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8b75c.
Definition tfib_A_calloc : Z := 0x8bd20.  Definition tfib_E_calloc : Z := 0x8be58.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8be58.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8be5c.
Definition tfib_A_libc_free : Z := 0x8be5c.  Definition tfib_E_libc_free : Z := 0x8c028.
Definition tfib_A_get_meta : Z := 0x8c028.  Definition tfib_E_get_meta : Z := 0x8c138.
Definition tfib_A_alloc_meta : Z := 0x8c510.  Definition tfib_E_alloc_meta : Z := 0x8c7e8.
Definition tfib_A_libc_malloc_impl : Z := 0x8c7e8.  Definition tfib_E_libc_malloc_impl : Z := 0x8cb58.
Definition tfib_A_alloc_slot : Z := 0x8cb58.  Definition tfib_E_alloc_slot : Z := 0x8d3fc.
Definition tfib_A_enframe : Z := 0x8d3fc.  Definition tfib_E_enframe : Z := 0x8d54c.
Definition tfib_A_malloc_allzerop : Z := 0x8d54c.  Definition tfib_E_malloc_allzerop : Z := 0x8d6c4.
Definition tfib_A_getrlimit : Z := 0x8f374.  Definition tfib_E_getrlimit : Z := 0x8f46c.
Definition tfib_A_getrusage : Z := 0x8f46c.  Definition tfib_E_getrusage : Z := 0x8f494.
Definition tfib_A_setrlimit : Z := 0x8f494.  Definition tfib_E_setrlimit : Z := 0x8f55c.
Definition tfib_A_mmap : Z := 0x8f984.  Definition tfib_E_mmap : Z := 0x8fa70.
Definition tfib_A_mprotect : Z := 0x8fa70.  Definition tfib_E_mprotect : Z := 0x8fab8.
Definition tfib_A_munmap : Z := 0x8fb8c.  Definition tfib_E_munmap : Z := 0x8fbd4.
Definition tfib_A_sched_yield : Z := 0x8fe98.  Definition tfib_E_sched_yield : Z := 0x8febc.
Definition tfib_A_raise_tkill_path : Z := 0x8ff18.  Definition tfib_E_raise_tkill_path : Z := 0x8ff90.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8ff90.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x90164.
Definition tfib_A_musl_sigaltstack : Z := 0x9025c.  Definition tfib_E_musl_sigaltstack : Z := 0x902e8.

Definition tfib_A_lockfile : Z := 0x90928.  Definition tfib_E_lockfile : Z := 0x90a24.
Definition tfib_A_unlockfile : Z := 0x90a24.  Definition tfib_E_unlockfile : Z := 0x90a84.



Definition tfib_A_stdio_read : Z := 0x90614.  Definition tfib_E_stdio_read : Z := 0x9072c.
Definition tfib_A_stdio_write : Z := 0x90734.  Definition tfib_E_stdio_write : Z := 0x908c4.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x905e4.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x905e8.
Definition tfib_A_stdio_close : Z := 0x905e8.  Definition tfib_E_stdio_close : Z := 0x90614.
Definition tfib_A_fwritex : Z := 0x90eb8.  Definition tfib_E_fwritex : Z := 0x90ff0.
Definition tfib_A_musl_fwrite : Z := 0x90ff0.  Definition tfib_E_musl_fwrite : Z := 0x910a8.
Definition tfib_A_towrite : Z := 0x910a8.  Definition tfib_E_towrite : Z := 0x910fc.
Definition tfib_A_stdio_exit : Z := 0x90d14.  Definition tfib_E_stdio_exit : Z := 0x90eb8.
Definition tfib_A_ofl_lock : Z := 0x910fc.  Definition tfib_E_ofl_lock : Z := 0x9112c.

Definition tfib_A_musl_vfprintf : Z := 0x91278.  Definition tfib_E_musl_vfprintf : Z := 0x91428.
Definition tfib_A_printf_core : Z := 0x91428.  Definition tfib_E_printf_core : Z := 0x92258.
Definition tfib_A_pop_arg : Z := 0x92258.  Definition tfib_E_pop_arg : Z := 0x9238c.
Definition tfib_A_pad : Z := 0x9238c.  Definition tfib_E_pad : Z := 0x92460.
Definition tfib_A_fmt_fp : Z := 0x92460.  Definition tfib_E_fmt_fp : Z := 0x93b28.
Definition tfib_A_thunk_931e0 : Z := 0x8b974.  Definition tfib_E_thunk_931e0 : Z := 0x8b978.
Definition tfib_A_musl_wctomb : Z := 0x8fd00.  Definition tfib_E_musl_wctomb : Z := 0x8fd24.
Definition tfib_A_musl_wcrtomb : Z := 0x8fbd4.  Definition tfib_E_musl_wcrtomb : Z := 0x8fd00.
Definition tfib_A_fpclassifyl : Z := 0x8df64.  Definition tfib_E_fpclassifyl : Z := 0x8dfa8.
Definition tfib_A_letf2 : Z := 0x8d79c.  Definition tfib_E_letf2 : Z := 0x8d864.
Definition tfib_A_multf3 : Z := 0x8d864.  Definition tfib_E_multf3 : Z := 0x8df64.
Definition tfib_A_floatsitf : Z := 0x8e7c0.  Definition tfib_E_floatsitf : Z := 0x8e8c8.
Definition tfib_A_scalbn : Z := 0x8f1cc.  Definition tfib_E_scalbn : Z := 0x8f264.
Definition tfib_A_subtf3 : Z := 0x8e7b0.  Definition tfib_E_subtf3 : Z := 0x8e7c0.
Definition tfib_A_addtf3 : Z := 0x8dfa8.  Definition tfib_E_addtf3 : Z := 0x8e774.
Definition tfib_A_fe_getround : Z := 0x8e774.  Definition tfib_E_fe_getround : Z := 0x8e7a4.
Definition tfib_A_fixunstfsi : Z := 0x93b30.  Definition tfib_E_fixunstfsi : Z := 0x93bc4.
Definition tfib_A_floatunsitf : Z := 0x93bc4.  Definition tfib_E_floatunsitf : Z := 0x93cb0.
Definition tfib_A_fixtfsi : Z := 0x8f264.  Definition tfib_E_fixtfsi : Z := 0x8f30c.
Definition tfib_A_divtf3 : Z := 0x8e8c8.  Definition tfib_E_divtf3 : Z := 0x8f1cc.
Definition tfib_A_musl_vprintf : Z := 0x94388.  Definition tfib_E_musl_vprintf : Z := 0x943a4.
Definition tfib_A_stdout_write : Z := 0x91138.  Definition tfib_E_stdout_write : Z := 0x911d8.
Definition tfib_A_thunk_95368 : Z := 0x9493c.  Definition tfib_E_thunk_95368 : Z := 0x94940.
Definition tfib_A_musl_memcmp : Z := 0x94a0c.  Definition tfib_E_musl_memcmp : Z := 0x94a3c.
Definition tfib_A_musl_memcpy : Z := 0x94a3c.  Definition tfib_E_musl_memcpy : Z := 0x94e40.
Definition tfib_A_musl_memset : Z := 0x94e40.  Definition tfib_E_musl_memset : Z := 0x94f38.
Definition tfib_A_musl_strchr : Z := 0x94f38.  Definition tfib_E_musl_strchr : Z := 0x94f74.
Definition tfib_A_strchrnul : Z := 0x94f74.  Definition tfib_E_strchrnul : Z := 0x95054.
Definition tfib_A_musl_strlen : Z := 0x9508c.  Definition tfib_E_musl_strlen : Z := 0x9511c.
Definition tfib_A_musl_strnlen : Z := 0x952c8.  Definition tfib_E_musl_strnlen : Z := 0x9530c.
Definition tfib_A_musl_memchr : Z := 0x94940.  Definition tfib_E_musl_memchr : Z := 0x94a0c.
Definition tfib_A_lock : Z := 0x9530c.  Definition tfib_E_lock : Z := 0x95594.
Definition tfib_A_unlock : Z := 0x95594.  Definition tfib_E_unlock : Z := 0x95608.
Definition tfib_A_syscall_cp_c : Z := 0x95608.  Definition tfib_E_syscall_cp_c : Z := 0x9562c.
Definition tfib_A_syscall_cp_sccp : Z := 0x9562c.  Definition tfib_E_syscall_cp_sccp : Z := 0x95630.
Definition tfib_A_pthread_atfork : Z := 0x9566c.  Definition tfib_E_pthread_atfork : Z := 0x95710.
Definition tfib_A_mremap : Z := 0x8fab8.  Definition tfib_E_mremap : Z := 0x8fb8c.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x966e4.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x96700.
Definition tfib_A_pthread_key_create : Z := 0x96a8c.  Definition tfib_E_pthread_key_create : Z := 0x96b60.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x96e04.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x96ea8.
Definition tfib_A_pthread_setspecific : Z := 0x97028.  Definition tfib_E_pthread_setspecific : Z := 0x9705c.
Definition tfib_A_set_thread_area : Z := 0x97064.
Definition tfib_A_thunk_96f9c : Z := 0x9705c.  Definition tfib_E_thunk_96f9c : Z := 0x97064.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97990.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97a48.
Definition tfib_A_close : Z := 0x9a060.  Definition tfib_E_close : Z := 0x9a0b4.
Definition tfib_A_musl_read : Z := 0x9a140.  Definition tfib_E_musl_read : Z := 0x9a174.
Definition tfib_A_vm_wait : Z := 0x976a0.  Definition tfib_E_vm_wait : Z := 0x976f0.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x9b178.
Definition tfib_D_fini_array_0_1 : Z := 0x9b198.
Definition tfib_D_GOT_common_flags : Z := 0x9b700.
Definition tfib_D_GOT_flags : Z := 0x9b708.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9b710.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9b718.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9b720.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9b728.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9c278.
Definition tfib_D_environ_musl : Z := 0x9c3a8.
Definition tfib_D_REAL_read : Z := 0x9d450.
Definition tfib_D_REAL_memcpy : Z := 0x9d578.
Definition tfib_D_REAL_memset : Z := 0x9d580.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa0198.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa0ff8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa37f8.
Definition tfib_D_asan_inited : Z := 0xa44d8.
Definition tfib_D_replace_intrin_cached : Z := 0xa44d9.
Definition tfib_D_kHighMemEnd : Z := 0xa44e0.
Definition tfib_D_kMidMemBeg : Z := 0xa44e8.
Definition tfib_D_kMidMemEnd : Z := 0xa44f0.
Definition tfib_D_malloc_context_size : Z := 0xa44fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x135328.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f6a28.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f9000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x32b18.
Definition tfib_at_rw_lo : Z := 0x9d000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x65d50.
Definition tfib_at_x_imemcpy : Z := 0x65cd4.
Definition tfib_at_x_memset : Z := 0x94e40.
Definition tfib_at_x_memcpy : Z := 0x94a3c.
Definition tfib_at_x_memiszero : Z := 0x66280.
Definition tfib_at_x_istrncpy : Z := 0x6617c.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x38f04.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8a840.
Definition tfib_at_x_envscan_k : Z := 0x8a84c.
Definition tfib_at_x_pnscan : Z := 0x8a904.
Definition tfib_at_x_pnscan_k : Z := 0x8a910.
Definition tfib_at_stops_more : list Z := (0x36b78 :: 0x3819c :: 0x5605c :: 0x5c414 :: 0x5c428 :: 0x5c43c :: 0x61dcc :: 0x61e9c :: 0x6f3c8 :: 0x702d4 :: 0x70464 :: 0x7a1bc :: nil)%list.
