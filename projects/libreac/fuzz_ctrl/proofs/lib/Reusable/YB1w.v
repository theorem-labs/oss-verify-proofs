(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1w.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x233b4.
Definition tfib_text_lo : Z := 0x3112c.  Definition tfib_text_hi : Z := 0x9e168.
Definition tfib_init_array_lo : Z := 0x9f168.  Definition tfib_init_array_hi : Z := 0x9f188.
Definition tfib_fini_array_lo : Z := 0x9f188.  Definition tfib_fini_array_hi : Z := 0x9f198.
Definition tfib_preinit_array_lo : Z := 0x9f198.  Definition tfib_preinit_array_hi : Z := 0x9f1a0.
Definition tfib_data_rel_ro_lo : Z := 0x9f1a0.  Definition tfib_data_rel_ro_hi : Z := 0xa0890.
Definition tfib_got_lo : Z := 0xa0890.  Definition tfib_got_hi : Z := 0xa15e8.
Definition tfib_data_lo : Z := 0xa25e8.  Definition tfib_data_hi : Z := 0xa51a0.
Definition tfib_asan_globals_lo : Z := 0xa51a0.  Definition tfib_asan_globals_hi : Z := 0xa5fe0.
Definition tfib_bss_lo : Z := 0xa6000.  Definition tfib_bss_hi : Z := 0x5fdf30.
Definition tfib_tbss_lo : Z := 0x9e168.  Definition tfib_tbss_hi : Z := 0x9e17c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fe000.
Definition tfib_entry : Z := 0x3112c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_do_init : Z := 0x31174.  Definition tfib_E_do_init : Z := 0x311e8.
Definition tfib_A_do_fini : Z := 0x311e8.  Definition tfib_E_do_fini : Z := 0x31278.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x31278.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x312b4.
Definition tfib_A_InitializeAllocator : Z := 0x31424.  Definition tfib_E_InitializeAllocator : Z := 0x3143c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3143c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x315a8.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31b04.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31c60.
Definition tfib_A_asan_free : Z := 0x32034.  Definition tfib_E_asan_free : Z := 0x3205c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3205c.  Definition tfib_E_Allocator_Deallocate : Z := 0x32314.
Definition tfib_A_asan_malloc : Z := 0x32314.  Definition tfib_E_asan_malloc : Z := 0x32370.
Definition tfib_A_Allocator_Allocate : Z := 0x32370.  Definition tfib_E_Allocator_Allocate : Z := 0x32cf8.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x336bc.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3390c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3390c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33a00.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x33a00.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33ae8.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x34100.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x34284.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x343bc.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34640.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34640.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x347c0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x347c0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34988.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34988.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34b54.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34bf4.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34cf8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35020.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35168.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x35168.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x351a0.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35938.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35c20.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x362f8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36470.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36620.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x36804.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x36804.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36adc.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36adc.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36f54.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36f54.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x37054.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x37054.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x3735c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x3735c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x376cc.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37aec.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37be8.
Definition tfib_A_AsanActivate : Z := 0x37cd0.  Definition tfib_E_AsanActivate : Z := 0x37dac.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3ce28.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3cf00.
Definition tfib_A_FakeStack_Create : Z := 0x3cf00.  Definition tfib_E_FakeStack_Create : Z := 0x3cfec.
Definition tfib_A_FakeStack_Allocate : Z := 0x3d2a8.  Definition tfib_E_FakeStack_Allocate : Z := 0x3d590.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d6c4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d6f4.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d6f4.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d868.
Definition tfib_A_asan_stack_malloc_6 : Z := 0x3db94.  Definition tfib_E_asan_stack_malloc_6 : Z := 0x3dd30.
Definition tfib_A_asan_stack_free_6 : Z := 0x3dd30.  Definition tfib_E_asan_stack_free_6 : Z := 0x3dd78.

Definition tfib_A_asan_InitializeFlags : Z := 0x3deb4.  Definition tfib_E_asan_InitializeFlags : Z := 0x3eee0.
Definition tfib_A_printf_common_format_interceptor : Z := 0x45420.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45ee8.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x48434.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x485e4.
Definition tfib_A_asan_memcpy : Z := 0x52164.  Definition tfib_E_asan_memcpy : Z := 0x52600.
Definition tfib_A_asan_memset : Z := 0x52600.  Definition tfib_E_asan_memset : Z := 0x52840.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x53158.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x5315c.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x5315c.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x53160.
Definition tfib_A_free : Z := 0x534b4.  Definition tfib_E_free : Z := 0x534b8.
Definition tfib_A_malloc : Z := 0x534b8.  Definition tfib_E_malloc : Z := 0x534bc.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x538b4.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x538b8.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x53ce0.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x53e4c.
Definition tfib_A_SetCanPoisonMemory : Z := 0x54334.  Definition tfib_E_SetCanPoisonMemory : Z := 0x54344.
Definition tfib_A_CanPoisonMemory : Z := 0x54344.  Definition tfib_E_CanPoisonMemory : Z := 0x54358.
Definition tfib_A_PoisonShadow : Z := 0x54358.  Definition tfib_E_PoisonShadow : Z := 0x54854.
Definition tfib_A_MemToShadow_checked : Z := 0x54854.  Definition tfib_E_MemToShadow_checked : Z := 0x54990.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54ce0.  Definition tfib_E_asan_region_is_poisoned : Z := 0x55024.
Definition tfib_A_AsanTSDInit : Z := 0x55444.  Definition tfib_E_AsanTSDInit : Z := 0x554c0.
Definition tfib_A_AsanTSDGet : Z := 0x554c0.  Definition tfib_E_AsanTSDGet : Z := 0x55500.
Definition tfib_A_AsanTSDSet : Z := 0x55500.  Definition tfib_E_AsanTSDSet : Z := 0x55540.
Definition tfib_A_PlatformTSDDtor : Z := 0x55540.  Definition tfib_E_PlatformTSDDtor : Z := 0x555c4.
Definition tfib_A_InstallAtForkHandler : Z := 0x555c4.  Definition tfib_E_InstallAtForkHandler : Z := 0x555e0.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x55640.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x55684.
Definition tfib_A_ReportDoubleFree : Z := 0x566b0.  Definition tfib_E_ReportDoubleFree : Z := 0x56940.
Definition tfib_A_ReportGenericError : Z := 0x5821c.  Definition tfib_E_ReportGenericError : Z := 0x58ad8.
Definition tfib_A_AsanInited : Z := 0x59264.  Definition tfib_E_AsanInited : Z := 0x5927c.
Definition tfib_A_asan_report_load1 : Z := 0x5927c.  Definition tfib_E_asan_report_load1 : Z := 0x592cc.
Definition tfib_A_asan_report_exp_load1 : Z := 0x592cc.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5931c.
Definition tfib_A_asan_report_load2 : Z := 0x5931c.  Definition tfib_E_asan_report_load2 : Z := 0x5936c.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5936c.  Definition tfib_E_asan_report_exp_load2 : Z := 0x593bc.
Definition tfib_A_asan_report_load4 : Z := 0x593bc.  Definition tfib_E_asan_report_load4 : Z := 0x5940c.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5940c.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5945c.
Definition tfib_A_asan_report_load8 : Z := 0x5945c.  Definition tfib_E_asan_report_load8 : Z := 0x594ac.
Definition tfib_A_asan_report_exp_load8 : Z := 0x594ac.  Definition tfib_E_asan_report_exp_load8 : Z := 0x594fc.
Definition tfib_A_asan_report_load16 : Z := 0x594fc.  Definition tfib_E_asan_report_load16 : Z := 0x5954c.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5954c.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5959c.
Definition tfib_A_asan_report_store1 : Z := 0x5959c.  Definition tfib_E_asan_report_store1 : Z := 0x595ec.
Definition tfib_A_asan_report_exp_store1 : Z := 0x595ec.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5963c.
Definition tfib_A_asan_report_store2 : Z := 0x5963c.  Definition tfib_E_asan_report_store2 : Z := 0x5968c.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5968c.  Definition tfib_E_asan_report_exp_store2 : Z := 0x596dc.
Definition tfib_A_asan_report_store4 : Z := 0x596dc.  Definition tfib_E_asan_report_store4 : Z := 0x5972c.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5972c.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5977c.
Definition tfib_A_asan_report_store8 : Z := 0x5977c.  Definition tfib_E_asan_report_store8 : Z := 0x597cc.
Definition tfib_A_asan_report_exp_store8 : Z := 0x597cc.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5981c.
Definition tfib_A_asan_report_store16 : Z := 0x5981c.  Definition tfib_E_asan_report_store16 : Z := 0x5986c.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5986c.  Definition tfib_E_asan_report_exp_store16 : Z := 0x598bc.
Definition tfib_A_asan_report_load_n : Z := 0x598bc.  Definition tfib_E_asan_report_load_n : Z := 0x5990c.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5990c.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5995c.
Definition tfib_A_asan_report_store_n : Z := 0x5995c.  Definition tfib_E_asan_report_store_n : Z := 0x599ac.
Definition tfib_A_asan_report_exp_store_n : Z := 0x599ac.  Definition tfib_E_asan_report_exp_store_n : Z := 0x599fc.
Definition tfib_A_InitializeHighMemEnd : Z := 0x599fc.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59a7c.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59a7c.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59e30.
Definition tfib_A_AsanInitInternal : Z := 0x59ec0.  Definition tfib_E_AsanInitInternal : Z := 0x5a174.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a174.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a214.
Definition tfib_A_asan_init : Z := 0x5a3e0.  Definition tfib_E_asan_init : Z := 0x5a474.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a474.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a478.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a478.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a4dc.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a6dc.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5aa04.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5aa04.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5abe4.
Definition tfib_A_InitializeShadowMemory : Z := 0x5abe4.  Definition tfib_E_InitializeShadowMemory : Z := 0x5aeec.
Definition tfib_A_SetMallocContextSize : Z := 0x5aeec.  Definition tfib_E_SetMallocContextSize : Z := 0x5aefc.
Definition tfib_A_GetMallocContextSize : Z := 0x5aefc.  Definition tfib_E_GetMallocContextSize : Z := 0x5af0c.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5af0c.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b05c.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5bb40.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5bb78.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5be2c.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5beb8.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5beb8.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5bf20.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5bf20.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5bf98.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5bf98.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5c000.
Definition tfib_A_AsanThread_Create : Z := 0x5c564.  Definition tfib_E_AsanThread_Create : Z := 0x5c700.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c75c.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c974.
Definition tfib_A_GetCurrentThread : Z := 0x5c974.  Definition tfib_E_GetCurrentThread : Z := 0x5c994.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c994.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5cb38.
Definition tfib_A_AsanThread_stack_top : Z := 0x5cb38.  Definition tfib_E_AsanThread_stack_top : Z := 0x5cb90.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5cb90.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5cbe8.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5cbe8.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ce18.
Definition tfib_A_AsanThread_Init : Z := 0x5ce18.  Definition tfib_E_AsanThread_Init : Z := 0x5d20c.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d20c.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d318.
Definition tfib_A_CreateMainThread : Z := 0x5d34c.  Definition tfib_E_CreateMainThread : Z := 0x5d45c.
Definition tfib_A_SetCurrentThread : Z := 0x5d45c.  Definition tfib_E_SetCurrentThread : Z := 0x5d53c.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ed40.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ee8c.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ee8c.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5eed8.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5eed8.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5eee4.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5ef14.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5ef20.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5ef20.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5ef2c.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5ef48.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f214.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f214.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f5d4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x6053c.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x60614.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x60614.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x606b0.
Definition tfib_A_RunMallocHooks : Z := 0x61148.  Definition tfib_E_RunMallocHooks : Z := 0x61200.
Definition tfib_A_RunFreeHooks : Z := 0x61204.  Definition tfib_E_RunFreeHooks : Z := 0x612b0.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x612e4.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x61330.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61e30.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61e48.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x622dc.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x63580.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63a58.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63d68.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63d68.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63eac.
Definition tfib_A_FlagParser_ParseString : Z := 0x63eac.  Definition tfib_E_FlagParser_ParseString : Z := 0x63fa0.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64134.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64194.
Definition tfib_A_internal_atoll : Z := 0x641d4.  Definition tfib_E_internal_atoll : Z := 0x642c0.
Definition tfib_A_internal_simple_strtoll : Z := 0x642c0.  Definition tfib_E_internal_simple_strtoll : Z := 0x6441c.
Definition tfib_A_internal_memchr : Z := 0x6441c.  Definition tfib_E_internal_memchr : Z := 0x6443c.
Definition tfib_A_internal_memcmp : Z := 0x6443c.  Definition tfib_E_internal_memcmp : Z := 0x64474.
Definition tfib_A_internal_strcspn : Z := 0x64550.  Definition tfib_E_internal_strcspn : Z := 0x645a4.
Definition tfib_A_internal_strcmp : Z := 0x645a4.  Definition tfib_E_internal_strcmp : Z := 0x645d8.
Definition tfib_A_internal_strdup : Z := 0x645d8.  Definition tfib_E_internal_strdup : Z := 0x64644.
Definition tfib_A_internal_strlen : Z := 0x64644.  Definition tfib_E_internal_strlen : Z := 0x64660.
Definition tfib_A_internal_strncmp : Z := 0x64660.  Definition tfib_E_internal_strncmp : Z := 0x646a4.
Definition tfib_A_internal_strchr : Z := 0x646a4.  Definition tfib_E_internal_strchr : Z := 0x646f0.
Definition tfib_A_internal_strchrnul : Z := 0x646f0.  Definition tfib_E_internal_strchrnul : Z := 0x64738.
Definition tfib_A_internal_strrchr : Z := 0x64738.  Definition tfib_E_internal_strrchr : Z := 0x64778.
Definition tfib_A_internal_strnlen : Z := 0x648a8.  Definition tfib_E_internal_strnlen : Z := 0x648d8.
Definition tfib_A_internal_strncpy : Z := 0x6491c.  Definition tfib_E_internal_strncpy : Z := 0x6498c.
Definition tfib_A_internal_strstr : Z := 0x6498c.  Definition tfib_E_internal_strstr : Z := 0x64a20.
Definition tfib_A_mem_is_zero : Z := 0x64a20.  Definition tfib_E_mem_is_zero : Z := 0x64ad4.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64ad4.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64ae4.
Definition tfib_A_internal_iserror : Z := 0x64cd0.  Definition tfib_E_internal_iserror : Z := 0x64cf0.
Definition tfib_A_internal_mmap : Z := 0x64cf0.  Definition tfib_E_internal_mmap : Z := 0x64cfc.
Definition tfib_A_internal_munmap : Z := 0x64cfc.  Definition tfib_E_internal_munmap : Z := 0x64d08.
Definition tfib_A_internal_mprotect : Z := 0x64d08.  Definition tfib_E_internal_mprotect : Z := 0x64d18.
Definition tfib_A_internal_madvise : Z := 0x64d18.  Definition tfib_E_internal_madvise : Z := 0x64d44.
Definition tfib_A_internal_close : Z := 0x64d44.  Definition tfib_E_internal_close : Z := 0x64d50.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64d50.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64d74.
Definition tfib_A_internal_read : Z := 0x64d74.  Definition tfib_E_internal_read : Z := 0x64dac.
Definition tfib_A_internal_write : Z := 0x64dac.  Definition tfib_E_internal_write : Z := 0x64de4.
Definition tfib_A_internal_ftruncate : Z := 0x64de4.  Definition tfib_E_internal_ftruncate : Z := 0x64e1c.
Definition tfib_A_internal_dup : Z := 0x64e1c.  Definition tfib_E_internal_dup : Z := 0x64e28.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64e28.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64e38.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64e38.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64e50.
Definition tfib_A_internal_sched_yield : Z := 0x64e50.  Definition tfib_E_internal_sched_yield : Z := 0x64e5c.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64e5c.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64ea8.
Definition tfib_A_internal_execve : Z := 0x64ea8.  Definition tfib_E_internal_execve : Z := 0x64eb4.
Definition tfib_A_internal_exit_exit_group : Z := 0x64eb4.  Definition tfib_E_internal_exit_exit_group : Z := 0x64ec8.
Definition tfib_A_FileExists_newfstatat : Z := 0x64ec8.  Definition tfib_E_FileExists_newfstatat : Z := 0x64f48.
Definition tfib_A_DirExists_newfstatat : Z := 0x64f48.  Definition tfib_E_DirExists_newfstatat : Z := 0x64fac.
Definition tfib_A_GetTid_gettid : Z := 0x64fac.  Definition tfib_E_GetTid_gettid : Z := 0x64fb8.
Definition tfib_A_GetEnv : Z := 0x64fb8.  Definition tfib_E_GetEnv : Z := 0x650e8.
Definition tfib_A_FutexWait : Z := 0x651ec.  Definition tfib_E_FutexWait : Z := 0x65210.
Definition tfib_A_FutexWake : Z := 0x65210.  Definition tfib_E_FutexWake : Z := 0x65234.
Definition tfib_A_internal_ptrace : Z := 0x65234.  Definition tfib_E_internal_ptrace : Z := 0x65240.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x65240.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x65250.
Definition tfib_A_internal_getpid : Z := 0x65250.  Definition tfib_E_internal_getpid : Z := 0x6525c.
Definition tfib_A_internal_getppid : Z := 0x6525c.  Definition tfib_E_internal_getppid : Z := 0x65268.
Definition tfib_A_internal_prctl : Z := 0x65268.  Definition tfib_E_internal_prctl : Z := 0x65274.
Definition tfib_A_internal_sigaltstack : Z := 0x65274.  Definition tfib_E_internal_sigaltstack : Z := 0x65280.
Definition tfib_A_internal_fork_clone : Z := 0x65280.  Definition tfib_E_internal_fork_clone : Z := 0x65298.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x65298.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x653c4.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65cd0.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65df0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65f94.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x66060.
Definition tfib_A_thunk_653ec : Z := 0x6615c.  Definition tfib_E_thunk_653ec : Z := 0x66160.
Definition tfib_A_CheckASLR : Z := 0x66160.  Definition tfib_E_CheckASLR : Z := 0x66164.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x663b0.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x663b4.
Definition tfib_A_MmapOrDie : Z := 0x663c0.  Definition tfib_E_MmapOrDie : Z := 0x664cc.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x664cc.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x66540.
Definition tfib_A_UnmapOrDie : Z := 0x66540.  Definition tfib_E_UnmapOrDie : Z := 0x665bc.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x665bc.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x666cc.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x668f8.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x669fc.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66b80.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66b8c.
Definition tfib_A_thunk_66008 : Z := 0x66d78.  Definition tfib_E_thunk_66008 : Z := 0x66d7c.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6709c.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x672a8.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67860.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6786c.
Definition tfib_A_Printf : Z := 0x67870.  Definition tfib_E_Printf : Z := 0x678bc.
Definition tfib_A_SharedPrintfCode : Z := 0x678bc.  Definition tfib_E_SharedPrintfCode : Z := 0x67918.
Definition tfib_A_Report : Z := 0x67918.  Definition tfib_E_Report : Z := 0x67964.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6945c.  Definition tfib_E_SuppressionContext_ctor : Z := 0x694b8.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x694b8.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x696f4.
Definition tfib_A_SuppressionContext_Parse : Z := 0x696f4.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69a18.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a088.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a3d8.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a6c8.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6ab40.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b400.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b724.
Definition tfib_A_AddDieCallback : Z := 0x6bfe0.  Definition tfib_E_AddDieCallback : Z := 0x6c068.
Definition tfib_A_Die : Z := 0x6c12c.  Definition tfib_E_Die : Z := 0x6c1ec.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c1ec.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c1f8.
Definition tfib_A_CheckFailed : Z := 0x6c1f8.  Definition tfib_E_CheckFailed : Z := 0x6c2b0.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c908.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6ca00.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6ca00.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6cb2c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6ce04.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6d0ec.
Definition tfib_A_AndroidLogInit : Z := 0x6d994.  Definition tfib_E_AndroidLogInit : Z := 0x6d998.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d9c8.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6da10.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6da10.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dc5c.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dd6c.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6de70.
Definition tfib_A_thunk_6d37c : Z := 0x6e0ec.  Definition tfib_E_thunk_6d37c : Z := 0x6e0f0.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e1b4.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e254.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e2e0.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e3a4.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e3a4.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e42c.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e42c.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e4a4.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e4a4.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e588.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e644.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e778.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6eb40.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ec0c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70a3c.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70b60.
Definition tfib_A_StackStore_Alloc : Z := 0x70b60.  Definition tfib_E_StackStore_Alloc : Z := 0x70c94.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x71548.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x715fc.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72d50.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72dac.
Definition tfib_A_StackDepotPut : Z := 0x73038.  Definition tfib_E_StackDepotPut : Z := 0x73058.
Definition tfib_A_StackDepotBase_Put : Z := 0x73058.  Definition tfib_E_StackDepotBase_Put : Z := 0x732dc.
Definition tfib_A_StackDepotBase_Get : Z := 0x732dc.  Definition tfib_E_StackDepotBase_Get : Z := 0x733ec.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x739bc.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x739c4.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73b24.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73b98.
Definition tfib_A_thunk_762d8 : Z := 0x77184.  Definition tfib_E_thunk_762d8 : Z := 0x77188.
Definition tfib_A_thunk_77ab0 : Z := 0x7895c.  Definition tfib_E_thunk_77ab0 : Z := 0x78960.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a388.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a444.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a444.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a51c.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7a51c.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7a790.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7aabc.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7ab00.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ab00.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7aed0.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b1a0.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b258.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c5b0.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c5b4.
Definition tfib_A_lsan_register_root_region : Z := 0x7d1bc.  Definition tfib_E_lsan_register_root_region : Z := 0x7d4ec.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d4ec.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d974.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x808d4.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80950.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80950.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80a00.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80a00.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80a18.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80a18.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80b60.
Definition tfib_A_main : Z := 0x80b78.  Definition tfib_E_main : Z := 0x80e3c.
Definition tfib_A_target_alloc_init : Z := 0x80e3c.  Definition tfib_E_target_alloc_init : Z := 0x80e40.
Definition tfib_A_target_alloc_count : Z := 0x80e40.  Definition tfib_E_target_alloc_count : Z := 0x80e48.
Definition tfib_A_target_run : Z := 0x80e48.
Definition tfib_A_emit_printf : Z := 0x80fd0.  Definition tfib_E_emit_printf : Z := 0x81018.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x81018.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83114.
Definition tfib_A_extenddftf2 : Z := 0x887f0.  Definition tfib_E_extenddftf2 : Z := 0x88980.
Definition tfib_A_sysconf : Z := 0x8e5d0.  Definition tfib_E_sysconf : Z := 0x8e7f8.
Definition tfib_A_init : Z := 0x8e7f8.  Definition tfib_E_init : Z := 0x8e7fc.
Definition tfib_A_init_libc : Z := 0x8e7fc.  Definition tfib_E_init_libc : Z := 0x8ea28.
Definition tfib_A_libc_start_init : Z := 0x8ea28.  Definition tfib_E_libc_start_init : Z := 0x8ea74.
Definition tfib_A_libc_start_main : Z := 0x8ea74.  Definition tfib_E_libc_start_main : Z := 0x8ead4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8ead4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8eb1c.
Definition tfib_A_init_tls : Z := 0x8ebf4.  Definition tfib_E_init_tls : Z := 0x8eea4.
Definition tfib_A_init_ssp : Z := 0x8eea4.  Definition tfib_E_init_ssp : Z := 0x8ef04.
Definition tfib_A_stack_chk_fail : Z := 0x8ef04.  Definition tfib_E_stack_chk_fail : Z := 0x8ef0c.
Definition tfib_A_Exit : Z := 0x8efe8.  Definition tfib_E_Exit : Z := 0x8f004.
Definition tfib_A_funcs_on_exit : Z := 0x8f034.  Definition tfib_E_funcs_on_exit : Z := 0x8f0fc.
Definition tfib_A_libc_exit_fini : Z := 0x8f1cc.  Definition tfib_E_libc_exit_fini : Z := 0x8f218.
Definition tfib_A_exit : Z := 0x8f218.  Definition tfib_E_exit : Z := 0x8f28c.
Definition tfib_A_open : Z := 0x8f48c.  Definition tfib_E_open : Z := 0x8f570.
Definition tfib_A_syscall_ret : Z := 0x8f570.  Definition tfib_E_syscall_ret : Z := 0x8f5a8.
Definition tfib_A_libc_free : Z := 0x8fe50.  Definition tfib_E_libc_free : Z := 0x9001c.
Definition tfib_A_get_meta : Z := 0x9001c.  Definition tfib_E_get_meta : Z := 0x9012c.
Definition tfib_A_libc_malloc_impl : Z := 0x907dc.  Definition tfib_E_libc_malloc_impl : Z := 0x90b4c.
Definition tfib_A_alloc_slot : Z := 0x90b4c.  Definition tfib_E_alloc_slot : Z := 0x913f0.
Definition tfib_A_enframe : Z := 0x913f0.  Definition tfib_E_enframe : Z := 0x91540.
Definition tfib_A_malloc_allzerop : Z := 0x91540.  Definition tfib_E_malloc_allzerop : Z := 0x916b8.
Definition tfib_A_getrlimit : Z := 0x93368.  Definition tfib_E_getrlimit : Z := 0x93460.
Definition tfib_A_getrusage : Z := 0x93460.  Definition tfib_E_getrusage : Z := 0x93488.
Definition tfib_A_setrlimit : Z := 0x93488.  Definition tfib_E_setrlimit : Z := 0x93550.
Definition tfib_A_mmap : Z := 0x93978.  Definition tfib_E_mmap : Z := 0x93a64.
Definition tfib_A_mprotect : Z := 0x93a64.  Definition tfib_E_mprotect : Z := 0x93aac.
Definition tfib_A_munmap : Z := 0x93b80.  Definition tfib_E_munmap : Z := 0x93bc8.
Definition tfib_A_sched_yield : Z := 0x93e8c.  Definition tfib_E_sched_yield : Z := 0x93eb0.
Definition tfib_A_lockfile : Z := 0x9491c.  Definition tfib_E_lockfile : Z := 0x94a18.
Definition tfib_A_unlockfile : Z := 0x94a18.  Definition tfib_E_unlockfile : Z := 0x94a78.
Definition tfib_A_stdio_read : Z := 0x94608.  Definition tfib_E_stdio_read : Z := 0x94720.
Definition tfib_A_stdio_write : Z := 0x94728.  Definition tfib_E_stdio_write : Z := 0x948b8.
Definition tfib_A_stdio_close : Z := 0x945dc.  Definition tfib_E_stdio_close : Z := 0x94608.
Definition tfib_A_fwritex : Z := 0x94eac.  Definition tfib_E_fwritex : Z := 0x94fe4.
Definition tfib_A_towrite : Z := 0x9509c.  Definition tfib_E_towrite : Z := 0x950f0.
Definition tfib_A_stdio_exit : Z := 0x94d08.  Definition tfib_E_stdio_exit : Z := 0x94eac.
Definition tfib_A_printf_core : Z := 0x9541c.  Definition tfib_E_printf_core : Z := 0x9624c.
Definition tfib_A_pop_arg : Z := 0x9624c.  Definition tfib_E_pop_arg : Z := 0x96380.
Definition tfib_A_pad : Z := 0x96380.  Definition tfib_E_pad : Z := 0x96454.
Definition tfib_A_fmt_fp : Z := 0x96454.  Definition tfib_E_fmt_fp : Z := 0x97b1c.
Definition tfib_A_fpclassifyl : Z := 0x91f58.  Definition tfib_E_fpclassifyl : Z := 0x91f9c.
Definition tfib_A_letf2 : Z := 0x91790.  Definition tfib_E_letf2 : Z := 0x91858.
Definition tfib_A_multf3 : Z := 0x91858.  Definition tfib_E_multf3 : Z := 0x91f58.
Definition tfib_A_floatsitf : Z := 0x927b4.  Definition tfib_E_floatsitf : Z := 0x928bc.
Definition tfib_A_scalbn : Z := 0x931c0.  Definition tfib_E_scalbn : Z := 0x93258.
Definition tfib_A_subtf3 : Z := 0x927a4.  Definition tfib_E_subtf3 : Z := 0x927b4.
Definition tfib_A_addtf3 : Z := 0x91f9c.  Definition tfib_E_addtf3 : Z := 0x92768.
Definition tfib_A_fe_getround : Z := 0x92768.  Definition tfib_E_fe_getround : Z := 0x92798.
Definition tfib_A_fixunstfsi : Z := 0x97b24.  Definition tfib_E_fixunstfsi : Z := 0x97bb8.
Definition tfib_A_floatunsitf : Z := 0x97bb8.  Definition tfib_E_floatunsitf : Z := 0x97ca4.
Definition tfib_A_fixtfsi : Z := 0x93258.  Definition tfib_E_fixtfsi : Z := 0x93300.
Definition tfib_A_divtf3 : Z := 0x928bc.  Definition tfib_E_divtf3 : Z := 0x931c0.
Definition tfib_A_stdout_write : Z := 0x9512c.  Definition tfib_E_stdout_write : Z := 0x951cc.
Definition tfib_A_musl_memcmp : Z := 0x98a00.  Definition tfib_E_musl_memcmp : Z := 0x98a30.
Definition tfib_A_musl_memcpy : Z := 0x98a30.  Definition tfib_E_musl_memcpy : Z := 0x98e34.
Definition tfib_A_musl_memset : Z := 0x98e34.  Definition tfib_E_musl_memset : Z := 0x98f2c.
Definition tfib_A_strchrnul : Z := 0x98f68.  Definition tfib_E_strchrnul : Z := 0x99048.
Definition tfib_A_musl_strnlen : Z := 0x992bc.  Definition tfib_E_musl_strnlen : Z := 0x99300.
Definition tfib_A_musl_memchr : Z := 0x98934.  Definition tfib_E_musl_memchr : Z := 0x98a00.
Definition tfib_A_unlock : Z := 0x99588.  Definition tfib_E_unlock : Z := 0x995fc.
Definition tfib_A_syscall_cp_c : Z := 0x995fc.  Definition tfib_E_syscall_cp_c : Z := 0x99620.
Definition tfib_A_pthread_atfork : Z := 0x99660.  Definition tfib_E_pthread_atfork : Z := 0x99704.
Definition tfib_A_mremap : Z := 0x93aac.  Definition tfib_E_mremap : Z := 0x93b80.
Definition tfib_A_pthread_key_create : Z := 0x9aa80.  Definition tfib_E_pthread_key_create : Z := 0x9ab54.
Definition tfib_A_pthread_setspecific : Z := 0x9b01c.  Definition tfib_E_pthread_setspecific : Z := 0x9b050.
Definition tfib_A_set_thread_area : Z := 0x9b058.  Definition tfib_E_set_thread_area : Z := 0x9b064.
Definition tfib_A_close : Z := 0x9e054.  Definition tfib_E_close : Z := 0x9e0a8.
Definition tfib_A_vm_wait : Z := 0x9b694.  Definition tfib_E_vm_wait : Z := 0x9b6e4.
Definition tfib_D_str_sealed : Z := 0x11835.
Definition tfib_D_init_array_0_3 : Z := 0x9f168.
Definition tfib_D_fini_array_0_1 : Z := 0x9f188.
Definition tfib_D_GOT_common_flags : Z := 0xa08e0.
Definition tfib_D_GOT_flags : Z := 0xa08e8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa08f0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa08f8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa0900.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa0908.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa1458.
Definition tfib_D_environ_musl : Z := 0xa1580.
Definition tfib_D_REAL_read : Z := 0xa2628.
Definition tfib_D_REAL_memcpy : Z := 0xa2750.
Definition tfib_D_REAL_memset : Z := 0xa2758.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa6058.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa6eb8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa96b8.
Definition tfib_D_asan_inited : Z := 0xaa398.
Definition tfib_D_replace_intrin_cached : Z := 0xaa399.
Definition tfib_D_kHighMemEnd : Z := 0xaa3a0.
Definition tfib_D_kMidMemBeg : Z := 0xaa3a8.
Definition tfib_D_kMidMemEnd : Z := 0xaa3b0.
Definition tfib_D_malloc_context_size : Z := 0xaa3bc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13b1e8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5fc8e0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fe000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x3112c.
Definition tfib_at_rw_lo : Z := 0xa2000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x644f0.
Definition tfib_at_x_imemcpy : Z := 0x64474.
Definition tfib_at_x_memset : Z := 0x98e34.
Definition tfib_at_x_memcpy : Z := 0x98a30.
Definition tfib_at_x_memiszero : Z := 0x64a20.
Definition tfib_at_x_istrncpy : Z := 0x6491c.
Definition tfib_at_x_sealed : Z := 0x11835.
Definition tfib_at_x_popfree : Z := 0x37518.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8e834.
Definition tfib_at_x_envscan_k : Z := 0x8e840.
Definition tfib_at_x_pnscan : Z := 0x8e8f8.
Definition tfib_at_x_pnscan_k : Z := 0x8e904.
Definition tfib_at_stops_more : list Z := (0x3518c :: 0x367b0 :: 0x547fc :: 0x5abb4 :: 0x5abc8 :: 0x5abdc :: 0x6056c :: 0x6063c :: 0x6db68 :: 0x6ea74 :: 0x6ec04 :: 0x7895c :: nil)%list.
