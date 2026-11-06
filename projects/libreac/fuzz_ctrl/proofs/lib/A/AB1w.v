(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the port's unresolved relocations are settled against fuzz_ctrl v1.9's ASan image (pin sha256 aac16e1f..., unstripped twin 78efaeda..., loaded sections identical): 197 references take the measured v1.9 value (a Theorem Labs lane's AB1w-overrides-A.tsv (a working note, not in this delivery), spot-checked here on the symtab), and the definitions of the cgif-only symbols that have NO twin in fuzz_ctrl are deleted (the fopen / fclose interceptors and cgif's own program functions: cgif_newgif, cgif_addframe, cmpPixel, flushFrame, freeFrame, cgif_close, cgif_raw_*, LZW_GenerateStream, create_byte_list*, musl fopen / fclose / fmodeflags / fdopen / ofl_add; tfib_A_musl_fopen is dropped too, as a Theorem Labs lane's table would have given it 0x94088 = __fwritex, a wrong symbol: ctrl has no fopen). Every applied row was checked against the symbol its value lands on in the v1.9 symtab: the A rows land on that symbol's entry and the E rows on its end (an E equals the next function's start, which is why it reads as the next symbol); tfib_E_stdio_exit = 0x94088 is __stdio_exit 0x93ee4 + size 420, correct. No file outside this one and its image-B twin Reusable/YB1w.v names any of them. Added: tfib_A_asan_stack_free_6 / tfib_E_asan_stack_free_6 = 0x3dbf4 / 0x3dc3c (v1.9 __asan_stack_free_6, start 0x3dbf4 size 72, end = MemToShadow's start), read by name from a Theorem Labs lane's relocated disco StackFree6Tbl.v (a working note, not in this delivery). *)
(* Modified by Theorem Labs, 2026-10-29 (fuzz_ctrl core post-pass, STEP 4; porter a Theorem Labs lane's "GO" at 08:09Z): the donor table from cgif carried only two ASan fake-stack size classes (the rows named asan_stack_malloc_A / _B = v1.9's __asan_stack_malloc_1 / _2); ctrl's start-up calls classes 0, 1, 2 and 6, so the rows tfib_A/E_asan_stack_malloc_0 and _6 are added here, measured on fuzz_ctrl v1.9's ASan symtab (fuzz_ctrl.nm.txt (a working note, not in this delivery)): __asan_stack_malloc_0 start 0x3d5b8 size 0x174 (end 0x3d72c), __asan_stack_malloc_1 0x3d72c size 0x190 (0x3d8bc), __asan_stack_malloc_2 0x3d8bc size 0x19c (0x3da58), __asan_stack_malloc_6 0x3da58 size 0x19c (0x3dbf4), __asan_stack_free_6 0x3dbf4 size 0x48 (0x3dc3c). The donor's row tfib_A/E_FakeStack_SetShadow, whose range [0x3dc3c, 0x3dd78) = 0x3dc3c + 0x13c is in ctrl the local _ZN6__asanL11MemToShadowEm (__asan::MemToShadow(unsigned long)) - the image holds five copies of that local, at 0x3befc, 0x3dc3c, 0x530d0, 0x54718 and 0x5d604 - not FakeStack::SetShadow, is deleted from this table. *)
(* Modified by Theorem Labs, 2026-10-29 (same STEP 4 pass): the deletion of the cgif-only rows that the comment above describes had left five halves behind, which the comparison with the tagged release's emission (a Theorem Labs lane's AB1w.v) found. They are removed here: tfib_A_read_frameconfig (0x82d58, a cgif-only function; that address is ctrl's declaration_of, start 0x82d58 size 0x3f8), tfib_E_musl_fclose (0x93af8 = lockfile's start), tfib_E_fmodeflags (0x94088 = __stdio_exit's end), tfib_E_fdopen (0x937b4 = the aio close stub) and tfib_E_ofl_add (0x94308, inside ofl_lock's neighbourhood). None of the five names its own function in ctrl's symtab, and no file in the tree reads any of them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x233b4.
Definition tfib_text_lo : Z := 0x30ff0.
Definition tfib_init_array_lo : Z := 0x9e348.  Definition tfib_init_array_hi : Z := 0x9e368.
Definition tfib_fini_array_lo : Z := 0x9e368.  Definition tfib_fini_array_hi : Z := 0x9e378.
Definition tfib_preinit_array_lo : Z := 0x9e378.  Definition tfib_preinit_array_hi : Z := 0x9e380.
Definition tfib_data_rel_ro_lo : Z := 0x9e380.  Definition tfib_data_rel_ro_hi : Z := 0x9fa70.
Definition tfib_got_lo : Z := 0x9fa70.  Definition tfib_got_hi : Z := 0xa07c8.
Definition tfib_data_lo : Z := 0xa17c8.  Definition tfib_data_hi : Z := 0xa4380.
Definition tfib_asan_globals_lo : Z := 0xa4380.  Definition tfib_asan_globals_hi : Z := 0xa51c0.
Definition tfib_bss_lo : Z := 0xa51c0.  Definition tfib_bss_hi : Z := 0x5fd0f0.
Definition tfib_tbss_lo : Z := 0x9d348.  Definition tfib_tbss_hi : Z := 0x9d35c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fe000.
Definition tfib_entry : Z := 0x30ff0.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_do_init : Z := 0x31038.  Definition tfib_E_do_init : Z := 0x310ac.
Definition tfib_A_do_fini : Z := 0x310ac.  Definition tfib_E_do_fini : Z := 0x3113c.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x3113c.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x31178.
Definition tfib_A_InitializeAllocator : Z := 0x312e8.  Definition tfib_E_InitializeAllocator : Z := 0x31300.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x31300.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x3146c.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x319c8.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31b24.
Definition tfib_A_asan_free : Z := 0x31ef8.  Definition tfib_E_asan_free : Z := 0x31f20.
Definition tfib_A_Allocator_Deallocate : Z := 0x31f20.  Definition tfib_E_Allocator_Deallocate : Z := 0x321d8.
Definition tfib_A_asan_malloc : Z := 0x321d8.  Definition tfib_E_asan_malloc : Z := 0x32234.
Definition tfib_A_Allocator_Allocate : Z := 0x32234.  Definition tfib_E_Allocator_Allocate : Z := 0x32bbc.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x33580.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x337d0.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x337d0.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x338c4.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x338c4.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x339ac.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x33fc4.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x34148.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x34280.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34504.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34504.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34684.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34684.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3484c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x3484c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34a18.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34ab8.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34bbc.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34ee4.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x3502c.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x3502c.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x35064.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x357fc.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35ae4.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x361bc.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36334.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x364e4.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x366c8.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x366c8.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x369a0.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x369a0.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36e18.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36e18.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36f18.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36f18.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x37220.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x37220.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x37590.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x379b0.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37aac.
Definition tfib_A_AsanActivate : Z := 0x37b94.  Definition tfib_E_AsanActivate : Z := 0x37c70.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3ccec.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3cdc4.
Definition tfib_A_FakeStack_Create : Z := 0x3cdc4.  Definition tfib_E_FakeStack_Create : Z := 0x3ceb0.
Definition tfib_A_FakeStack_Allocate : Z := 0x3d16c.  Definition tfib_E_FakeStack_Allocate : Z := 0x3d454.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d588.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d5b8.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d5b8.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d72c.
Definition tfib_A_asan_stack_malloc_6 : Z := 0x3da58.  Definition tfib_E_asan_stack_malloc_6 : Z := 0x3dbf4.
Definition tfib_A_asan_stack_free_6 : Z := 0x3dbf4.  Definition tfib_E_asan_stack_free_6 : Z := 0x3dc3c.
Definition tfib_A_asan_InitializeFlags : Z := 0x3dd78.  Definition tfib_E_asan_InitializeFlags : Z := 0x3eda4.
Definition tfib_A_printf_common_format_interceptor : Z := 0x452e4.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45dac.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x482f8.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x484a8.
Definition tfib_A_asan_memcpy : Z := 0x52028.  Definition tfib_E_asan_memcpy : Z := 0x524c4.
Definition tfib_A_asan_memset : Z := 0x524c4.  Definition tfib_E_asan_memset : Z := 0x52704.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x5301c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x53020.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x53020.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x53024.
Definition tfib_A_free : Z := 0x53378.  Definition tfib_E_free : Z := 0x5337c.
Definition tfib_A_malloc : Z := 0x5337c.  Definition tfib_E_malloc : Z := 0x53380.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53778.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x5377c.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x53ba4.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x53d10.
Definition tfib_A_SetCanPoisonMemory : Z := 0x541f8.  Definition tfib_E_SetCanPoisonMemory : Z := 0x54208.
Definition tfib_A_CanPoisonMemory : Z := 0x54208.  Definition tfib_E_CanPoisonMemory : Z := 0x5421c.
Definition tfib_A_PoisonShadow : Z := 0x5421c.  Definition tfib_E_PoisonShadow : Z := 0x54718.
Definition tfib_A_MemToShadow_checked : Z := 0x54718.  Definition tfib_E_MemToShadow_checked : Z := 0x54854.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54ba4.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54ee8.
Definition tfib_A_AsanTSDInit : Z := 0x55308.  Definition tfib_E_AsanTSDInit : Z := 0x55384.
Definition tfib_A_AsanTSDGet : Z := 0x55384.  Definition tfib_E_AsanTSDGet : Z := 0x553c4.
Definition tfib_A_AsanTSDSet : Z := 0x553c4.  Definition tfib_E_AsanTSDSet : Z := 0x55404.
Definition tfib_A_PlatformTSDDtor : Z := 0x55404.  Definition tfib_E_PlatformTSDDtor : Z := 0x55488.
Definition tfib_A_InstallAtForkHandler : Z := 0x55488.  Definition tfib_E_InstallAtForkHandler : Z := 0x554a4.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x55504.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x55548.
Definition tfib_A_ReportDoubleFree : Z := 0x56574.  Definition tfib_E_ReportDoubleFree : Z := 0x56804.
Definition tfib_A_ReportGenericError : Z := 0x580e0.  Definition tfib_E_ReportGenericError : Z := 0x5899c.
Definition tfib_A_AsanInited : Z := 0x59128.  Definition tfib_E_AsanInited : Z := 0x59140.
Definition tfib_A_asan_report_load1 : Z := 0x59140.  Definition tfib_E_asan_report_load1 : Z := 0x59190.
Definition tfib_A_asan_report_exp_load1 : Z := 0x59190.  Definition tfib_E_asan_report_exp_load1 : Z := 0x591e0.
Definition tfib_A_asan_report_load2 : Z := 0x591e0.  Definition tfib_E_asan_report_load2 : Z := 0x59230.
Definition tfib_A_asan_report_exp_load2 : Z := 0x59230.  Definition tfib_E_asan_report_exp_load2 : Z := 0x59280.
Definition tfib_A_asan_report_load4 : Z := 0x59280.  Definition tfib_E_asan_report_load4 : Z := 0x592d0.
Definition tfib_A_asan_report_exp_load4 : Z := 0x592d0.  Definition tfib_E_asan_report_exp_load4 : Z := 0x59320.
Definition tfib_A_asan_report_load8 : Z := 0x59320.  Definition tfib_E_asan_report_load8 : Z := 0x59370.
Definition tfib_A_asan_report_exp_load8 : Z := 0x59370.  Definition tfib_E_asan_report_exp_load8 : Z := 0x593c0.
Definition tfib_A_asan_report_load16 : Z := 0x593c0.  Definition tfib_E_asan_report_load16 : Z := 0x59410.
Definition tfib_A_asan_report_exp_load16 : Z := 0x59410.  Definition tfib_E_asan_report_exp_load16 : Z := 0x59460.
Definition tfib_A_asan_report_store1 : Z := 0x59460.  Definition tfib_E_asan_report_store1 : Z := 0x594b0.
Definition tfib_A_asan_report_exp_store1 : Z := 0x594b0.  Definition tfib_E_asan_report_exp_store1 : Z := 0x59500.
Definition tfib_A_asan_report_store2 : Z := 0x59500.  Definition tfib_E_asan_report_store2 : Z := 0x59550.
Definition tfib_A_asan_report_exp_store2 : Z := 0x59550.  Definition tfib_E_asan_report_exp_store2 : Z := 0x595a0.
Definition tfib_A_asan_report_store4 : Z := 0x595a0.  Definition tfib_E_asan_report_store4 : Z := 0x595f0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x595f0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x59640.
Definition tfib_A_asan_report_store8 : Z := 0x59640.  Definition tfib_E_asan_report_store8 : Z := 0x59690.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59690.  Definition tfib_E_asan_report_exp_store8 : Z := 0x596e0.
Definition tfib_A_asan_report_store16 : Z := 0x596e0.  Definition tfib_E_asan_report_store16 : Z := 0x59730.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59730.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59780.
Definition tfib_A_asan_report_load_n : Z := 0x59780.  Definition tfib_E_asan_report_load_n : Z := 0x597d0.
Definition tfib_A_asan_report_exp_load_n : Z := 0x597d0.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59820.
Definition tfib_A_asan_report_store_n : Z := 0x59820.  Definition tfib_E_asan_report_store_n : Z := 0x59870.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59870.  Definition tfib_E_asan_report_exp_store_n : Z := 0x598c0.
Definition tfib_A_InitializeHighMemEnd : Z := 0x598c0.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59940.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59940.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59cf4.
Definition tfib_A_AsanInitInternal : Z := 0x59d84.  Definition tfib_E_AsanInitInternal : Z := 0x5a038.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a038.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a0d8.
Definition tfib_A_asan_init : Z := 0x5a2a4.  Definition tfib_E_asan_init : Z := 0x5a338.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a338.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a33c.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a33c.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a3a0.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a5a0.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a8c8.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a8c8.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5aaa8.
Definition tfib_A_InitializeShadowMemory : Z := 0x5aaa8.  Definition tfib_E_InitializeShadowMemory : Z := 0x5adb0.
Definition tfib_A_SetMallocContextSize : Z := 0x5adb0.  Definition tfib_E_SetMallocContextSize : Z := 0x5adc0.
Definition tfib_A_GetMallocContextSize : Z := 0x5adc0.  Definition tfib_E_GetMallocContextSize : Z := 0x5add0.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5add0.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5af20.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5ba04.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5ba3c.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5bcf0.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5bd7c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5bd7c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5bde4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5bde4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5be5c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5be5c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5bec4.
Definition tfib_A_AsanThread_Create : Z := 0x5c428.  Definition tfib_E_AsanThread_Create : Z := 0x5c5c4.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c620.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c838.
Definition tfib_A_GetCurrentThread : Z := 0x5c838.  Definition tfib_E_GetCurrentThread : Z := 0x5c858.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c858.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5c9fc.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c9fc.  Definition tfib_E_AsanThread_stack_top : Z := 0x5ca54.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5ca54.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5caac.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5caac.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ccdc.
Definition tfib_A_AsanThread_Init : Z := 0x5ccdc.  Definition tfib_E_AsanThread_Init : Z := 0x5d0d0.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d0d0.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d1dc.
Definition tfib_A_CreateMainThread : Z := 0x5d210.  Definition tfib_E_CreateMainThread : Z := 0x5d320.
Definition tfib_A_SetCurrentThread : Z := 0x5d320.  Definition tfib_E_SetCurrentThread : Z := 0x5d400.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ec04.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ed50.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ed50.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5ed9c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5ed9c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5eda8.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5edd8.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5ede4.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5ede4.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5edf0.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5ee0c.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f0d8.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f0d8.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f498.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x60400.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x604d8.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x604d8.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x60574.
Definition tfib_A_RunMallocHooks : Z := 0x6100c.  Definition tfib_E_RunMallocHooks : Z := 0x610c4.
Definition tfib_A_RunFreeHooks : Z := 0x610c8.  Definition tfib_E_RunFreeHooks : Z := 0x61174.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x611a8.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x611f4.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61cf4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61d0c.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x621a0.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x63444.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x6391c.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63c2c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63c2c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63d70.
Definition tfib_A_FlagParser_ParseString : Z := 0x63d70.  Definition tfib_E_FlagParser_ParseString : Z := 0x63e64.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63ff8.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64058.
Definition tfib_A_internal_atoll : Z := 0x64098.  Definition tfib_E_internal_atoll : Z := 0x64184.
Definition tfib_A_internal_simple_strtoll : Z := 0x64184.  Definition tfib_E_internal_simple_strtoll : Z := 0x642e0.
Definition tfib_A_internal_memchr : Z := 0x642e0.  Definition tfib_E_internal_memchr : Z := 0x64300.
Definition tfib_A_internal_memcmp : Z := 0x64300.  Definition tfib_E_internal_memcmp : Z := 0x64338.
Definition tfib_A_internal_strcspn : Z := 0x64414.  Definition tfib_E_internal_strcspn : Z := 0x64468.
Definition tfib_A_internal_strcmp : Z := 0x64468.  Definition tfib_E_internal_strcmp : Z := 0x6449c.
Definition tfib_A_internal_strdup : Z := 0x6449c.  Definition tfib_E_internal_strdup : Z := 0x64508.
Definition tfib_A_internal_strlen : Z := 0x64508.  Definition tfib_E_internal_strlen : Z := 0x64524.
Definition tfib_A_internal_strncmp : Z := 0x64524.  Definition tfib_E_internal_strncmp : Z := 0x64568.
Definition tfib_A_internal_strchr : Z := 0x64568.  Definition tfib_E_internal_strchr : Z := 0x645b4.
Definition tfib_A_internal_strchrnul : Z := 0x645b4.  Definition tfib_E_internal_strchrnul : Z := 0x645fc.
Definition tfib_A_internal_strrchr : Z := 0x645fc.  Definition tfib_E_internal_strrchr : Z := 0x6463c.
Definition tfib_A_internal_strnlen : Z := 0x6476c.  Definition tfib_E_internal_strnlen : Z := 0x6479c.
Definition tfib_A_internal_strncpy : Z := 0x647e0.  Definition tfib_E_internal_strncpy : Z := 0x64850.
Definition tfib_A_internal_strstr : Z := 0x64850.  Definition tfib_E_internal_strstr : Z := 0x648e4.
Definition tfib_A_mem_is_zero : Z := 0x648e4.  Definition tfib_E_mem_is_zero : Z := 0x64998.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64998.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x649a8.
Definition tfib_A_internal_iserror : Z := 0x64b94.  Definition tfib_E_internal_iserror : Z := 0x64bb4.
Definition tfib_A_internal_mmap : Z := 0x64bb4.  Definition tfib_E_internal_mmap : Z := 0x64bc0.
Definition tfib_A_internal_munmap : Z := 0x64bc0.  Definition tfib_E_internal_munmap : Z := 0x64bcc.
Definition tfib_A_internal_mprotect : Z := 0x64bcc.  Definition tfib_E_internal_mprotect : Z := 0x64bdc.
Definition tfib_A_internal_madvise : Z := 0x64bdc.  Definition tfib_E_internal_madvise : Z := 0x64c08.
Definition tfib_A_internal_close : Z := 0x64c08.  Definition tfib_E_internal_close : Z := 0x64c14.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64c14.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64c38.
Definition tfib_A_internal_read : Z := 0x64c38.  Definition tfib_E_internal_read : Z := 0x64c70.
Definition tfib_A_internal_write : Z := 0x64c70.  Definition tfib_E_internal_write : Z := 0x64ca8.
Definition tfib_A_internal_ftruncate : Z := 0x64ca8.  Definition tfib_E_internal_ftruncate : Z := 0x64ce0.
Definition tfib_A_internal_dup : Z := 0x64ce0.  Definition tfib_E_internal_dup : Z := 0x64cec.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64cec.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64cfc.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64cfc.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64d14.
Definition tfib_A_internal_sched_yield : Z := 0x64d14.  Definition tfib_E_internal_sched_yield : Z := 0x64d20.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64d20.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64d6c.
Definition tfib_A_internal_execve : Z := 0x64d6c.  Definition tfib_E_internal_execve : Z := 0x64d78.
Definition tfib_A_internal_exit_exit_group : Z := 0x64d78.  Definition tfib_E_internal_exit_exit_group : Z := 0x64d8c.
Definition tfib_A_FileExists_newfstatat : Z := 0x64d8c.  Definition tfib_E_FileExists_newfstatat : Z := 0x64e0c.
Definition tfib_A_DirExists_newfstatat : Z := 0x64e0c.  Definition tfib_E_DirExists_newfstatat : Z := 0x64e70.
Definition tfib_A_GetTid_gettid : Z := 0x64e70.  Definition tfib_E_GetTid_gettid : Z := 0x64e7c.
Definition tfib_A_GetEnv : Z := 0x64e7c.  Definition tfib_E_GetEnv : Z := 0x64fac.
Definition tfib_A_FutexWait : Z := 0x650b0.  Definition tfib_E_FutexWait : Z := 0x650d4.
Definition tfib_A_FutexWake : Z := 0x650d4.  Definition tfib_E_FutexWake : Z := 0x650f8.
Definition tfib_A_internal_ptrace : Z := 0x650f8.  Definition tfib_E_internal_ptrace : Z := 0x65104.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x65104.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x65114.
Definition tfib_A_internal_getpid : Z := 0x65114.  Definition tfib_E_internal_getpid : Z := 0x65120.
Definition tfib_A_internal_getppid : Z := 0x65120.  Definition tfib_E_internal_getppid : Z := 0x6512c.
Definition tfib_A_internal_prctl : Z := 0x6512c.  Definition tfib_E_internal_prctl : Z := 0x65138.
Definition tfib_A_internal_sigaltstack : Z := 0x65138.  Definition tfib_E_internal_sigaltstack : Z := 0x65144.
Definition tfib_A_internal_fork_clone : Z := 0x65144.  Definition tfib_E_internal_fork_clone : Z := 0x6515c.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6515c.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x65288.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65b94.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65cb4.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65e58.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65f24.
Definition tfib_A_thunk_653ec : Z := 0x66020.  Definition tfib_E_thunk_653ec : Z := 0x66024.
Definition tfib_A_CheckASLR : Z := 0x66024.  Definition tfib_E_CheckASLR : Z := 0x66028.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x66274.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x66278.
Definition tfib_A_MmapOrDie : Z := 0x66284.  Definition tfib_E_MmapOrDie : Z := 0x66390.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x66390.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x66404.
Definition tfib_A_UnmapOrDie : Z := 0x66404.  Definition tfib_E_UnmapOrDie : Z := 0x66480.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x66480.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66590.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x667bc.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x668c0.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66a44.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66a50.
Definition tfib_A_thunk_66008 : Z := 0x66c3c.  Definition tfib_E_thunk_66008 : Z := 0x66c40.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66f60.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6716c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67724.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67730.
Definition tfib_A_Printf : Z := 0x67734.  Definition tfib_E_Printf : Z := 0x67780.
Definition tfib_A_SharedPrintfCode : Z := 0x67780.  Definition tfib_E_SharedPrintfCode : Z := 0x677dc.
Definition tfib_A_Report : Z := 0x677dc.  Definition tfib_E_Report : Z := 0x67828.
Definition tfib_A_SuppressionContext_ctor : Z := 0x69320.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6937c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6937c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x695b8.
Definition tfib_A_SuppressionContext_Parse : Z := 0x695b8.  Definition tfib_E_SuppressionContext_Parse : Z := 0x698dc.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69f4c.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a29c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a58c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6aa04.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b2c4.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b5e8.
Definition tfib_A_AddDieCallback : Z := 0x6bea4.  Definition tfib_E_AddDieCallback : Z := 0x6bf2c.
Definition tfib_A_Die : Z := 0x6bff0.  Definition tfib_E_Die : Z := 0x6c0b0.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c0b0.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c0bc.
Definition tfib_A_CheckFailed : Z := 0x6c0bc.  Definition tfib_E_CheckFailed : Z := 0x6c174.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c7cc.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c8c4.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c8c4.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c9f0.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6ccc8.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6cfb0.
Definition tfib_A_AndroidLogInit : Z := 0x6d858.  Definition tfib_E_AndroidLogInit : Z := 0x6d85c.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d88c.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d8d4.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d8d4.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6db20.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dc30.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6dd34.
Definition tfib_A_thunk_6d37c : Z := 0x6dfb0.  Definition tfib_E_thunk_6d37c : Z := 0x6dfb4.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e078.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e118.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e1a4.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e268.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e268.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e2f0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e2f0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e368.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e368.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e44c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e508.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e63c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ea04.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ead0.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70900.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70a24.
Definition tfib_A_StackStore_Alloc : Z := 0x70a24.  Definition tfib_E_StackStore_Alloc : Z := 0x70b58.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x7140c.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x714c0.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72c14.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72c70.
Definition tfib_A_StackDepotPut : Z := 0x72efc.  Definition tfib_E_StackDepotPut : Z := 0x72f1c.
Definition tfib_A_StackDepotBase_Put : Z := 0x72f1c.  Definition tfib_E_StackDepotBase_Put : Z := 0x731a0.
Definition tfib_A_StackDepotBase_Get : Z := 0x731a0.  Definition tfib_E_StackDepotBase_Get : Z := 0x732b0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73880.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73888.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x739e8.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73a5c.
Definition tfib_A_thunk_762d8 : Z := 0x77048.  Definition tfib_E_thunk_762d8 : Z := 0x7704c.
Definition tfib_A_thunk_77ab0 : Z := 0x78820.  Definition tfib_E_thunk_77ab0 : Z := 0x78824.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a24c.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a308.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a308.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a3e0.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7a3e0.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7a654.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7a980.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7a9c4.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a9c4.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ad94.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b064.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b11c.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c474.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c478.
Definition tfib_A_lsan_register_root_region : Z := 0x7d080.  Definition tfib_E_lsan_register_root_region : Z := 0x7d3b0.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d3b0.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d838.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80798.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80814.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80814.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x808c4.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x808c4.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x808dc.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x808dc.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80a24.
Definition tfib_A_main : Z := 0x80a3c.  Definition tfib_E_main : Z := 0x80d00.
Definition tfib_A_target_alloc_init : Z := 0x80d00.  Definition tfib_E_target_alloc_init : Z := 0x80d04.
Definition tfib_A_target_alloc_count : Z := 0x80d04.  Definition tfib_E_target_alloc_count : Z := 0x80d0c.
Definition tfib_A_target_run : Z := 0x80d0c.
Definition tfib_A_emit_printf : Z := 0x80e94.  Definition tfib_E_emit_printf : Z := 0x80edc.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80edc.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82d58.
Definition tfib_A_extenddftf2 : Z := 0x879cc.  Definition tfib_E_extenddftf2 : Z := 0x87b5c.
Definition tfib_A_sysconf : Z := 0x8d7ac.  Definition tfib_E_sysconf : Z := 0x8d9d4.
Definition tfib_A_init : Z := 0x8d9d4.  Definition tfib_E_init : Z := 0x8d9d8.
Definition tfib_A_init_libc : Z := 0x8d9d8.  Definition tfib_E_init_libc : Z := 0x8dc04.
Definition tfib_A_libc_start_init : Z := 0x8dc04.  Definition tfib_E_libc_start_init : Z := 0x8dc50.
Definition tfib_A_libc_start_main : Z := 0x8dc50.  Definition tfib_E_libc_start_main : Z := 0x8dcb0.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8dcb0.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8dcf8.
Definition tfib_A_init_tls : Z := 0x8ddd0.  Definition tfib_E_init_tls : Z := 0x8e080.
Definition tfib_A_init_ssp : Z := 0x8e080.  Definition tfib_E_init_ssp : Z := 0x8e0e0.
Definition tfib_A_stack_chk_fail : Z := 0x8e0e0.  Definition tfib_E_stack_chk_fail : Z := 0x8e0e8.
Definition tfib_A_Exit : Z := 0x8e1c4.  Definition tfib_E_Exit : Z := 0x8e1e0.
Definition tfib_A_funcs_on_exit : Z := 0x8e210.  Definition tfib_E_funcs_on_exit : Z := 0x8e2d8.
Definition tfib_A_libc_exit_fini : Z := 0x8e3a8.  Definition tfib_E_libc_exit_fini : Z := 0x8e3f4.
Definition tfib_A_exit : Z := 0x8e3f4.  Definition tfib_E_exit : Z := 0x8e468.
Definition tfib_A_open : Z := 0x8e668.  Definition tfib_E_open : Z := 0x8e74c.
Definition tfib_A_syscall_ret : Z := 0x8e74c.  Definition tfib_E_syscall_ret : Z := 0x8e784.
Definition tfib_A_libc_free : Z := 0x8f02c.  Definition tfib_E_libc_free : Z := 0x8f1f8.
Definition tfib_A_get_meta : Z := 0x8f1f8.  Definition tfib_E_get_meta : Z := 0x8f308.
Definition tfib_A_libc_malloc_impl : Z := 0x8f9b8.  Definition tfib_E_libc_malloc_impl : Z := 0x8fd28.
Definition tfib_A_alloc_slot : Z := 0x8fd28.  Definition tfib_E_alloc_slot : Z := 0x905cc.
Definition tfib_A_enframe : Z := 0x905cc.  Definition tfib_E_enframe : Z := 0x9071c.
Definition tfib_A_malloc_allzerop : Z := 0x9071c.  Definition tfib_E_malloc_allzerop : Z := 0x90894.
Definition tfib_A_getrlimit : Z := 0x92544.  Definition tfib_E_getrlimit : Z := 0x9263c.
Definition tfib_A_getrusage : Z := 0x9263c.  Definition tfib_E_getrusage : Z := 0x92664.
Definition tfib_A_setrlimit : Z := 0x92664.  Definition tfib_E_setrlimit : Z := 0x9272c.
Definition tfib_A_mmap : Z := 0x92b54.  Definition tfib_E_mmap : Z := 0x92c40.
Definition tfib_A_mprotect : Z := 0x92c40.  Definition tfib_E_mprotect : Z := 0x92c88.
Definition tfib_A_munmap : Z := 0x92d5c.  Definition tfib_E_munmap : Z := 0x92da4.
Definition tfib_A_sched_yield : Z := 0x93068.  Definition tfib_E_sched_yield : Z := 0x9308c.
Definition tfib_A_lockfile : Z := 0x93af8.  Definition tfib_E_lockfile : Z := 0x93bf4.
Definition tfib_A_unlockfile : Z := 0x93bf4.  Definition tfib_E_unlockfile : Z := 0x93c54.
Definition tfib_A_stdio_read : Z := 0x937e4.  Definition tfib_E_stdio_read : Z := 0x938fc.
Definition tfib_A_stdio_write : Z := 0x93904.  Definition tfib_E_stdio_write : Z := 0x93a94.
Definition tfib_A_stdio_close : Z := 0x937b8.  Definition tfib_E_stdio_close : Z := 0x937e4.
Definition tfib_A_fwritex : Z := 0x94088.  Definition tfib_E_fwritex : Z := 0x941c0.
Definition tfib_A_towrite : Z := 0x94278.  Definition tfib_E_towrite : Z := 0x942cc.
Definition tfib_A_stdio_exit : Z := 0x93ee4.  Definition tfib_E_stdio_exit : Z := 0x94088.
Definition tfib_A_printf_core : Z := 0x945f8.  Definition tfib_E_printf_core : Z := 0x95428.
Definition tfib_A_pop_arg : Z := 0x95428.  Definition tfib_E_pop_arg : Z := 0x9555c.
Definition tfib_A_pad : Z := 0x9555c.  Definition tfib_E_pad : Z := 0x95630.
Definition tfib_A_fmt_fp : Z := 0x95630.  Definition tfib_E_fmt_fp : Z := 0x96cf8.
Definition tfib_A_fpclassifyl : Z := 0x91134.  Definition tfib_E_fpclassifyl : Z := 0x91178.
Definition tfib_A_letf2 : Z := 0x9096c.  Definition tfib_E_letf2 : Z := 0x90a34.
Definition tfib_A_multf3 : Z := 0x90a34.  Definition tfib_E_multf3 : Z := 0x91134.
Definition tfib_A_floatsitf : Z := 0x91990.  Definition tfib_E_floatsitf : Z := 0x91a98.
Definition tfib_A_scalbn : Z := 0x9239c.  Definition tfib_E_scalbn : Z := 0x92434.
Definition tfib_A_subtf3 : Z := 0x91980.  Definition tfib_E_subtf3 : Z := 0x91990.
Definition tfib_A_addtf3 : Z := 0x91178.  Definition tfib_E_addtf3 : Z := 0x91944.
Definition tfib_A_fe_getround : Z := 0x91944.  Definition tfib_E_fe_getround : Z := 0x91974.
Definition tfib_A_fixunstfsi : Z := 0x96d00.  Definition tfib_E_fixunstfsi : Z := 0x96d94.
Definition tfib_A_floatunsitf : Z := 0x96d94.  Definition tfib_E_floatunsitf : Z := 0x96e80.
Definition tfib_A_fixtfsi : Z := 0x92434.  Definition tfib_E_fixtfsi : Z := 0x924dc.
Definition tfib_A_divtf3 : Z := 0x91a98.  Definition tfib_E_divtf3 : Z := 0x9239c.
Definition tfib_A_stdout_write : Z := 0x94308.  Definition tfib_E_stdout_write : Z := 0x943a8.
Definition tfib_A_musl_memcmp : Z := 0x97bdc.  Definition tfib_E_musl_memcmp : Z := 0x97c0c.
Definition tfib_A_musl_memcpy : Z := 0x97c0c.  Definition tfib_E_musl_memcpy : Z := 0x98010.
Definition tfib_A_musl_memset : Z := 0x98010.  Definition tfib_E_musl_memset : Z := 0x98108.
Definition tfib_A_strchrnul : Z := 0x98144.  Definition tfib_E_strchrnul : Z := 0x98224.
Definition tfib_A_musl_strnlen : Z := 0x98498.  Definition tfib_E_musl_strnlen : Z := 0x984dc.
Definition tfib_A_musl_memchr : Z := 0x97b10.  Definition tfib_E_musl_memchr : Z := 0x97bdc.
Definition tfib_A_unlock : Z := 0x98764.  Definition tfib_E_unlock : Z := 0x987d8.
Definition tfib_A_syscall_cp_c : Z := 0x987d8.  Definition tfib_E_syscall_cp_c : Z := 0x987fc.
Definition tfib_A_pthread_atfork : Z := 0x9883c.  Definition tfib_E_pthread_atfork : Z := 0x988e0.
Definition tfib_A_mremap : Z := 0x92c88.  Definition tfib_E_mremap : Z := 0x92d5c.
Definition tfib_A_pthread_key_create : Z := 0x99c5c.  Definition tfib_E_pthread_key_create : Z := 0x99d30.
Definition tfib_A_pthread_setspecific : Z := 0x9a1f8.  Definition tfib_E_pthread_setspecific : Z := 0x9a22c.
Definition tfib_A_set_thread_area : Z := 0x9a234.  Definition tfib_E_set_thread_area : Z := 0x9a240.
Definition tfib_A_close : Z := 0x9d230.  Definition tfib_E_close : Z := 0x9d284.
Definition tfib_A_vm_wait : Z := 0x9a870.  Definition tfib_E_vm_wait : Z := 0x9a8c0.
Definition tfib_D_str_sealed : Z := 0x11835.
Definition tfib_D_init_array_0_3 : Z := 0x9e348.
Definition tfib_D_fini_array_0_1 : Z := 0x9e368.
Definition tfib_D_GOT_common_flags : Z := 0x9fac0.
Definition tfib_D_GOT_flags : Z := 0x9fac8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9fad0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9fad8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9fae0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9fae8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa0638.
Definition tfib_D_environ_musl : Z := 0xa0760.
Definition tfib_D_REAL_read : Z := 0xa1808.
Definition tfib_D_REAL_memcpy : Z := 0xa1930.
Definition tfib_D_REAL_memset : Z := 0xa1938.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa5218.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa6078.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa8878.
Definition tfib_D_asan_inited : Z := 0xa9558.
Definition tfib_D_replace_intrin_cached : Z := 0xa9559.
Definition tfib_D_kHighMemEnd : Z := 0xa9560.
Definition tfib_D_kMidMemBeg : Z := 0xa9568.
Definition tfib_D_kMidMemEnd : Z := 0xa9570.
Definition tfib_D_malloc_context_size : Z := 0xa957c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13a3a8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5fbaa0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fe000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30ff0.
Definition tfib_at_rw_lo : Z := 0xa1000.
Definition tfib_at_rw_len : Z := 0x55d000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x643b4.
Definition tfib_at_x_imemcpy : Z := 0x64338.
Definition tfib_at_x_memset : Z := 0x98010.
Definition tfib_at_x_memcpy : Z := 0x97c0c.
Definition tfib_at_x_memiszero : Z := 0x648e4.
Definition tfib_at_x_istrncpy : Z := 0x647e0.
Definition tfib_at_x_sealed : Z := 0x11835.
Definition tfib_at_x_popfree : Z := 0x373dc.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8da10.
Definition tfib_at_x_envscan_k : Z := 0x8da1c.
Definition tfib_at_x_pnscan : Z := 0x8dad4.
Definition tfib_at_x_pnscan_k : Z := 0x8dae0.
Definition tfib_at_stops_more : list Z := (0x35050 :: 0x36674 :: 0x546c0 :: 0x5aa78 :: 0x5aa8c :: 0x5aaa0 :: 0x60430 :: 0x60500 :: 0x6da2c :: 0x6e938 :: 0x6eac8 :: 0x78820 :: nil)%list.
