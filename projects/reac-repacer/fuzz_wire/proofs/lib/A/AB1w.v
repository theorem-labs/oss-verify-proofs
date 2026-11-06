(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v at 25e3d17bdb50, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AB1w.v at 4f87de75d67 (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build; 186 of the donor's function rows (among them fuzz_grant's own reac_ functions, __asan_stack_malloc_2 and _4 and the globals registration functions), the asan_globals range, the rodata/text upper bounds, three data rows and the end addresses of _start, target_run and set_thread_area are removed, and rows for fuzz_wire's own program (its check_, rp_ and reac_frame_ functions) and for StackStore::Store, StackStore::BlockInfo::Create and TwoLevelMap::Create are added. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102d0.
Definition tfib_text_lo : Z := 0x2ff7c.
Definition tfib_init_array_lo : Z := 0x98250.  Definition tfib_init_array_hi : Z := 0x98270.
Definition tfib_fini_array_lo : Z := 0x98270.  Definition tfib_fini_array_hi : Z := 0x98280.
Definition tfib_preinit_array_lo : Z := 0x98280.  Definition tfib_preinit_array_hi : Z := 0x98288.
Definition tfib_data_rel_ro_lo : Z := 0x98288.  Definition tfib_data_rel_ro_hi : Z := 0x98788.
Definition tfib_got_lo : Z := 0x98788.  Definition tfib_got_hi : Z := 0x994e0.
Definition tfib_data_lo : Z := 0x9a4e0.  Definition tfib_data_hi : Z := 0x9d098.
  
Definition tfib_bss_lo : Z := 0x9d0c0.  Definition tfib_bss_hi : Z := 0x5f4ff0.
Definition tfib_tbss_lo : Z := 0x97250.  Definition tfib_tbss_hi : Z := 0x97264.
Definition tfib_img_lo : Z := IMG_LO.  Definition tfib_img_hi : Z := IMG_TOP.
Definition tfib_entry : Z := 0x2ff7c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2ff7c.
Definition tfib_A_do_init : Z := 0x2ffc4.  Definition tfib_E_do_init : Z := 0x30038.
Definition tfib_A_do_fini : Z := 0x30038.  Definition tfib_E_do_fini : Z := 0x300c8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x300c8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30104.
Definition tfib_A_InitializeAllocator : Z := 0x30274.  Definition tfib_E_InitializeAllocator : Z := 0x3028c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3028c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x303f8.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x30954.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30ab0.
Definition tfib_A_asan_free : Z := 0x30e84.  Definition tfib_E_asan_free : Z := 0x30eac.
Definition tfib_A_Allocator_Deallocate : Z := 0x30eac.  Definition tfib_E_Allocator_Deallocate : Z := 0x31164.
Definition tfib_A_asan_malloc : Z := 0x31164.  Definition tfib_E_asan_malloc : Z := 0x311c0.
Definition tfib_A_Allocator_Allocate : Z := 0x311c0.  Definition tfib_E_Allocator_Allocate : Z := 0x31b48.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x324b0.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x3250c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x3250c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3275c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3275c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32850.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x3320c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33490.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33490.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33610.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33610.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x337d8.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x337d8.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x339a4.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33a44.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33b48.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33e70.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33fb8.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35148.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x352c0.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35470.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35654.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35654.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x3592c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x3592c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35da4.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35da4.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35ea4.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35ea4.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x361ac.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x361ac.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x3651c.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36a38.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36b20.
Definition tfib_A_AsanActivate : Z := 0x36b20.  Definition tfib_E_AsanActivate : Z := 0x36bfc.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3bc78.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bd50.
Definition tfib_A_FakeStack_Create : Z := 0x3bd50.  Definition tfib_E_FakeStack_Create : Z := 0x3be3c.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c514.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c544.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3c544.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3c6b8.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3c6b8.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3c848.


Definition tfib_A_asan_InitializeFlags : Z := 0x3c984.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d9b0.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e0bc.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3eed8.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3eed8.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f4a4.
Definition tfib_A_icpt_strlen : Z := 0x415f8.  Definition tfib_E_icpt_strlen : Z := 0x4188c.
Definition tfib_A_icpt_strnlen : Z := 0x4188c.  Definition tfib_E_icpt_strnlen : Z := 0x41b20.
Definition tfib_A_icpt_strcmp : Z := 0x41b24.  Definition tfib_E_icpt_strcmp : Z := 0x42054.
Definition tfib_A_icpt_strchr : Z := 0x42054.  Definition tfib_E_icpt_strchr : Z := 0x42334.
Definition tfib_A_icpt_memcmp : Z := 0x42bcc.  Definition tfib_E_icpt_memcmp : Z := 0x42c88.
Definition tfib_A_icpt_memchr : Z := 0x42d44.  Definition tfib_E_icpt_memchr : Z := 0x43014.
Definition tfib_A_icpt_frexpl : Z := 0x43014.  Definition tfib_E_icpt_frexpl : Z := 0x4328c.
Definition tfib_A_icpt_read : Z := 0x4328c.  Definition tfib_E_icpt_read : Z := 0x434fc.
Definition tfib_A_icpt_fwrite : Z := 0x434fc.  Definition tfib_E_icpt_fwrite : Z := 0x43770.
Definition tfib_A_icpt_time : Z := 0x43770.  Definition tfib_E_icpt_time : Z := 0x43a0c.
Definition tfib_A_icpt_gmtime_r : Z := 0x43c14.  Definition tfib_E_icpt_gmtime_r : Z := 0x43e54.
Definition tfib_A_icpt_vprintf : Z := 0x43e54.  Definition tfib_E_icpt_vprintf : Z := 0x43ef0.
Definition tfib_A_printf_common_format_interceptor : Z := 0x43ef0.  Definition tfib_E_printf_common_format_interceptor : Z := 0x449b8.
Definition tfib_A_icpt_vfprintf : Z := 0x449b8.  Definition tfib_E_icpt_vfprintf : Z := 0x44a6c.
Definition tfib_A_icpt_vsnprintf : Z := 0x44a6c.  Definition tfib_E_icpt_vsnprintf : Z := 0x44d84.
Definition tfib_A_icpt_clock_gettime : Z := 0x44f00.  Definition tfib_E_icpt_clock_gettime : Z := 0x45158.
Definition tfib_A_icpt_wcrtomb : Z := 0x45158.  Definition tfib_E_icpt_wcrtomb : Z := 0x456c8.
Definition tfib_A_icpt_wctomb : Z := 0x456c8.  Definition tfib_E_icpt_wctomb : Z := 0x45a24.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45af0.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45ed8.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45ee4.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45f60.
Definition tfib_A_icpt_sem_timedwait : Z := 0x4616c.  Definition tfib_E_icpt_sem_timedwait : Z := 0x46404.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46434.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4665c.
Definition tfib_A_icpt_send : Z := 0x4665c.  Definition tfib_E_icpt_send : Z := 0x46910.
Definition tfib_A_icpt_sendto : Z := 0x46910.  Definition tfib_E_icpt_sendto : Z := 0x46bd4.
Definition tfib_A_icpt_sigaltstack : Z := 0x46bd4.  Definition tfib_E_icpt_sigaltstack : Z := 0x46e30.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46f04.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x470b4.
Definition tfib_A_asan_memcpy : Z := 0x50c34.  Definition tfib_E_asan_memcpy : Z := 0x510d0.
Definition tfib_A_asan_memset : Z := 0x510d0.  Definition tfib_E_asan_memset : Z := 0x51310.
Definition tfib_A_icpt_memset : Z := 0x51680.  Definition tfib_E_icpt_memset : Z := 0x51970.
Definition tfib_A_icpt_memcpy : Z := 0x51970.  Definition tfib_E_icpt_memcpy : Z := 0x51f60.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51f60.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51f98.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51f98.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x51f9c.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x51f9c.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51fa0.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x5204c.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52188.
Definition tfib_A_free : Z := 0x522f4.  Definition tfib_E_free : Z := 0x522f8.
Definition tfib_A_malloc : Z := 0x522f8.  Definition tfib_E_malloc : Z := 0x522fc.
Definition tfib_A_icpt_free : Z := 0x522fc.  Definition tfib_E_icpt_free : Z := 0x524cc.
Definition tfib_A_icpt_malloc : Z := 0x524cc.  Definition tfib_E_icpt_malloc : Z := 0x52628.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x526f4.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x526f8.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53174.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53184.
Definition tfib_A_CanPoisonMemory : Z := 0x53184.  Definition tfib_E_CanPoisonMemory : Z := 0x53198.
Definition tfib_A_PoisonShadow : Z := 0x53198.  Definition tfib_E_PoisonShadow : Z := 0x53694.
Definition tfib_A_MemToShadow_checked : Z := 0x53694.  Definition tfib_E_MemToShadow_checked : Z := 0x537d0.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53b20.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53e64.
Definition tfib_A_AsanTSDInit : Z := 0x54284.  Definition tfib_E_AsanTSDInit : Z := 0x54300.
Definition tfib_A_AsanTSDGet : Z := 0x54300.  Definition tfib_E_AsanTSDGet : Z := 0x54340.
Definition tfib_A_AsanTSDSet : Z := 0x54340.  Definition tfib_E_AsanTSDSet : Z := 0x54380.
Definition tfib_A_PlatformTSDDtor : Z := 0x54380.  Definition tfib_E_PlatformTSDDtor : Z := 0x54404.
Definition tfib_A_InstallAtForkHandler : Z := 0x54404.  Definition tfib_E_InstallAtForkHandler : Z := 0x54420.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54480.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x544c4.
Definition tfib_A_ReportDoubleFree : Z := 0x554f0.  Definition tfib_E_ReportDoubleFree : Z := 0x55780.
Definition tfib_A_ReportGenericError : Z := 0x5705c.  Definition tfib_E_ReportGenericError : Z := 0x57918.
Definition tfib_A_AsanInited : Z := 0x580a4.  Definition tfib_E_AsanInited : Z := 0x580bc.
Definition tfib_A_asan_report_load1 : Z := 0x580bc.  Definition tfib_E_asan_report_load1 : Z := 0x5810c.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5810c.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5815c.
Definition tfib_A_asan_report_load2 : Z := 0x5815c.  Definition tfib_E_asan_report_load2 : Z := 0x581ac.
Definition tfib_A_asan_report_exp_load2 : Z := 0x581ac.  Definition tfib_E_asan_report_exp_load2 : Z := 0x581fc.
Definition tfib_A_asan_report_load4 : Z := 0x581fc.  Definition tfib_E_asan_report_load4 : Z := 0x5824c.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5824c.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5829c.
Definition tfib_A_asan_report_load8 : Z := 0x5829c.  Definition tfib_E_asan_report_load8 : Z := 0x582ec.
Definition tfib_A_asan_report_exp_load8 : Z := 0x582ec.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5833c.
Definition tfib_A_asan_report_load16 : Z := 0x5833c.  Definition tfib_E_asan_report_load16 : Z := 0x5838c.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5838c.  Definition tfib_E_asan_report_exp_load16 : Z := 0x583dc.
Definition tfib_A_asan_report_store1 : Z := 0x583dc.  Definition tfib_E_asan_report_store1 : Z := 0x5842c.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5842c.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5847c.
Definition tfib_A_asan_report_store2 : Z := 0x5847c.  Definition tfib_E_asan_report_store2 : Z := 0x584cc.
Definition tfib_A_asan_report_exp_store2 : Z := 0x584cc.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5851c.
Definition tfib_A_asan_report_store4 : Z := 0x5851c.  Definition tfib_E_asan_report_store4 : Z := 0x5856c.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5856c.  Definition tfib_E_asan_report_exp_store4 : Z := 0x585bc.
Definition tfib_A_asan_report_store8 : Z := 0x585bc.  Definition tfib_E_asan_report_store8 : Z := 0x5860c.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5860c.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5865c.
Definition tfib_A_asan_report_store16 : Z := 0x5865c.  Definition tfib_E_asan_report_store16 : Z := 0x586ac.
Definition tfib_A_asan_report_exp_store16 : Z := 0x586ac.  Definition tfib_E_asan_report_exp_store16 : Z := 0x586fc.
Definition tfib_A_asan_report_load_n : Z := 0x586fc.  Definition tfib_E_asan_report_load_n : Z := 0x5874c.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5874c.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5879c.
Definition tfib_A_asan_report_store_n : Z := 0x5879c.  Definition tfib_E_asan_report_store_n : Z := 0x587ec.
Definition tfib_A_asan_report_exp_store_n : Z := 0x587ec.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5883c.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5883c.  Definition tfib_E_InitializeHighMemEnd : Z := 0x588bc.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x588bc.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58c70.
Definition tfib_A_AsanInitInternal : Z := 0x58d00.  Definition tfib_E_AsanInitInternal : Z := 0x58fb4.
Definition tfib_A_asan_init : Z := 0x59220.  Definition tfib_E_asan_init : Z := 0x592b4.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x592b4.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x592b8.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5951c.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59844.
Definition tfib_A_InitializeShadowMemory : Z := 0x59a24.  Definition tfib_E_InitializeShadowMemory : Z := 0x59d2c.
Definition tfib_A_SetMallocContextSize : Z := 0x59d2c.  Definition tfib_E_SetMallocContextSize : Z := 0x59d3c.
Definition tfib_A_GetMallocContextSize : Z := 0x59d3c.  Definition tfib_E_GetMallocContextSize : Z := 0x59d4c.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59d4c.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59e9c.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5a980.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5a9b8.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ac6c.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5acf8.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5acf8.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5ad60.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5ad60.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5add8.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5add8.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5ae40.
Definition tfib_A_AsanThread_Create : Z := 0x5b3a4.  Definition tfib_E_AsanThread_Create : Z := 0x5b540.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b59c.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b7b4.
Definition tfib_A_GetCurrentThread : Z := 0x5b7b4.  Definition tfib_E_GetCurrentThread : Z := 0x5b7d4.
Definition tfib_A_AsanThread_stack_top : Z := 0x5b978.  Definition tfib_E_AsanThread_stack_top : Z := 0x5b9d0.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5b9d0.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5ba28.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ba28.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bc58.
Definition tfib_A_AsanThread_Init : Z := 0x5bc58.  Definition tfib_E_AsanThread_Init : Z := 0x5c04c.
Definition tfib_A_CreateMainThread : Z := 0x5c18c.  Definition tfib_E_CreateMainThread : Z := 0x5c29c.
Definition tfib_A_SetCurrentThread : Z := 0x5c29c.  Definition tfib_E_SetCurrentThread : Z := 0x5c37c.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c580.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c6bc.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5dccc.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5dd18.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5dd18.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5dd24.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5dd54.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5dd60.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5dd60.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5dd6c.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f37c.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f454.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f454.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f4f0.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fa14.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fa58.
Definition tfib_A_RunMallocHooks : Z := 0x5ff88.  Definition tfib_E_RunMallocHooks : Z := 0x60040.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60040.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60044.
Definition tfib_A_RunFreeHooks : Z := 0x60044.  Definition tfib_E_RunFreeHooks : Z := 0x600f0.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60434.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60674.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60c70.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60c88.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x62898.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62ba8.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62ba8.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62cec.
Definition tfib_A_FlagParser_ParseString : Z := 0x62cec.  Definition tfib_E_FlagParser_ParseString : Z := 0x62de0.
Definition tfib_A_internal_atoll : Z := 0x63014.  Definition tfib_E_internal_atoll : Z := 0x63100.
Definition tfib_A_internal_simple_strtoll : Z := 0x63100.  Definition tfib_E_internal_simple_strtoll : Z := 0x6325c.
Definition tfib_A_internal_memchr : Z := 0x6325c.  Definition tfib_E_internal_memchr : Z := 0x6327c.
Definition tfib_A_internal_memcmp : Z := 0x6327c.  Definition tfib_E_internal_memcmp : Z := 0x632b4.
Definition tfib_A_internal_memcpy : Z := 0x632b4.  Definition tfib_E_internal_memcpy : Z := 0x632d8.
Definition tfib_A_internal_memmove : Z := 0x632d8.  Definition tfib_E_internal_memmove : Z := 0x63330.
Definition tfib_A_internal_memset : Z := 0x63330.  Definition tfib_E_internal_memset : Z := 0x63390.
Definition tfib_A_internal_strcspn : Z := 0x63390.  Definition tfib_E_internal_strcspn : Z := 0x633e4.
Definition tfib_A_internal_strdup : Z := 0x63418.  Definition tfib_E_internal_strdup : Z := 0x63484.
Definition tfib_A_internal_strlen : Z := 0x63484.  Definition tfib_E_internal_strlen : Z := 0x634a0.
Definition tfib_A_internal_strchrnul : Z := 0x63530.  Definition tfib_E_internal_strchrnul : Z := 0x63578.
Definition tfib_A_internal_strrchr : Z := 0x63578.  Definition tfib_E_internal_strrchr : Z := 0x635b8.
Definition tfib_A_internal_strnlen : Z := 0x636e8.  Definition tfib_E_internal_strnlen : Z := 0x63718.
Definition tfib_A_internal_strncpy : Z := 0x6375c.  Definition tfib_E_internal_strncpy : Z := 0x637cc.
Definition tfib_A_internal_strstr : Z := 0x637cc.  Definition tfib_E_internal_strstr : Z := 0x63860.
Definition tfib_A_mem_is_zero : Z := 0x63860.  Definition tfib_E_mem_is_zero : Z := 0x63914.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63914.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63924.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63924.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63b04.
Definition tfib_A_internal_iserror : Z := 0x63b10.  Definition tfib_E_internal_iserror : Z := 0x63b30.
Definition tfib_A_internal_mmap : Z := 0x63b30.  Definition tfib_E_internal_mmap : Z := 0x63b3c.
Definition tfib_A_internal_munmap : Z := 0x63b3c.  Definition tfib_E_internal_munmap : Z := 0x63b48.
Definition tfib_A_internal_mprotect : Z := 0x63b48.  Definition tfib_E_internal_mprotect : Z := 0x63b58.
Definition tfib_A_internal_madvise : Z := 0x63b58.  Definition tfib_E_internal_madvise : Z := 0x63b84.
Definition tfib_A_internal_close : Z := 0x63b84.  Definition tfib_E_internal_close : Z := 0x63b90.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63b90.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63bb4.
Definition tfib_A_internal_read : Z := 0x63bb4.  Definition tfib_E_internal_read : Z := 0x63bec.
Definition tfib_A_internal_write : Z := 0x63bec.  Definition tfib_E_internal_write : Z := 0x63c24.
Definition tfib_A_internal_ftruncate : Z := 0x63c24.  Definition tfib_E_internal_ftruncate : Z := 0x63c5c.
Definition tfib_A_internal_dup : Z := 0x63c5c.  Definition tfib_E_internal_dup : Z := 0x63c68.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63c68.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63c78.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63c78.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63c90.
Definition tfib_A_internal_sched_yield : Z := 0x63c90.  Definition tfib_E_internal_sched_yield : Z := 0x63c9c.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63c9c.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63ce8.
Definition tfib_A_internal_execve : Z := 0x63ce8.  Definition tfib_E_internal_execve : Z := 0x63cf4.
Definition tfib_A_internal_exit_exit_group : Z := 0x63cf4.  Definition tfib_E_internal_exit_exit_group : Z := 0x63d08.
Definition tfib_A_FileExists_newfstatat : Z := 0x63d08.  Definition tfib_E_FileExists_newfstatat : Z := 0x63d88.
Definition tfib_A_DirExists_newfstatat : Z := 0x63d88.  Definition tfib_E_DirExists_newfstatat : Z := 0x63dec.
Definition tfib_A_GetTid_gettid : Z := 0x63dec.  Definition tfib_E_GetTid_gettid : Z := 0x63df8.
Definition tfib_A_GetEnv : Z := 0x63df8.  Definition tfib_E_GetEnv : Z := 0x63f28.
Definition tfib_A_FutexWait : Z := 0x6402c.  Definition tfib_E_FutexWait : Z := 0x64050.
Definition tfib_A_FutexWake : Z := 0x64050.  Definition tfib_E_FutexWake : Z := 0x64074.
Definition tfib_A_internal_ptrace : Z := 0x64074.  Definition tfib_E_internal_ptrace : Z := 0x64080.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64080.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64090.
Definition tfib_A_internal_getpid : Z := 0x64090.  Definition tfib_E_internal_getpid : Z := 0x6409c.
Definition tfib_A_internal_getppid : Z := 0x6409c.  Definition tfib_E_internal_getppid : Z := 0x640a8.
Definition tfib_A_internal_prctl : Z := 0x640a8.  Definition tfib_E_internal_prctl : Z := 0x640b4.
Definition tfib_A_internal_sigaltstack : Z := 0x640b4.  Definition tfib_E_internal_sigaltstack : Z := 0x640c0.
Definition tfib_A_internal_fork_clone : Z := 0x640c0.  Definition tfib_E_internal_fork_clone : Z := 0x640d8.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x640d8.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64204.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64944.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64a5c.
Definition tfib_A_GetPageSizeCached : Z := 0x64a5c.  Definition tfib_E_GetPageSizeCached : Z := 0x64a64.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64a64.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64b10.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64b10.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64c30.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64cf8.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64d78.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64dd4.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64ea0.
Definition tfib_A_CheckASLR : Z := 0x64fa0.  Definition tfib_E_CheckASLR : Z := 0x64fa4.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x651f0.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x651f4.
Definition tfib_A_MmapOrDie : Z := 0x65200.  Definition tfib_E_MmapOrDie : Z := 0x6530c.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6530c.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65380.
Definition tfib_A_UnmapOrDie : Z := 0x65380.  Definition tfib_E_UnmapOrDie : Z := 0x653fc.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x653fc.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6550c.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65738.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6583c.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x65edc.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x660e8.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x666a0.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x666ac.
Definition tfib_A_Printf : Z := 0x666b0.  Definition tfib_E_Printf : Z := 0x666fc.
Definition tfib_A_SharedPrintfCode : Z := 0x666fc.  Definition tfib_E_SharedPrintfCode : Z := 0x66758.
Definition tfib_A_Report : Z := 0x66758.  Definition tfib_E_Report : Z := 0x667a4.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x682f8.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68534.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68534.  Definition tfib_E_SuppressionContext_Parse : Z := 0x68858.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69508.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69980.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a240.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a564.
Definition tfib_A_AddDieCallback : Z := 0x6ae20.  Definition tfib_E_AddDieCallback : Z := 0x6aea8.
Definition tfib_A_Die : Z := 0x6af6c.  Definition tfib_E_Die : Z := 0x6b02c.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b02c.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b038.
Definition tfib_A_CheckFailed : Z := 0x6b038.  Definition tfib_E_CheckFailed : Z := 0x6b0f0.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b748.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6b840.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6b840.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6b96c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6bc44.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6bf2c.
Definition tfib_A_AndroidLogInit : Z := 0x6c7d4.  Definition tfib_E_AndroidLogInit : Z := 0x6c7d8.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c808.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6c850.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c850.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ca9c.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6cbac.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6ccb0.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6cff4.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d094.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d120.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d1e4.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d1e4.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d26c.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d26c.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d2e4.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d2e4.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d3c8.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d484.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d5b8.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6f87c.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6f9a0.
Definition tfib_A_StackStore_Alloc : Z := 0x6f9a0.  Definition tfib_E_StackStore_Alloc : Z := 0x6fad4.
Definition tfib_A_StackStore_Store : Z := 0x6f87c.  Definition tfib_E_StackStore_Store : Z := 0x6f9a0.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x70388.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x7043c.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x7269c.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x7279c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70388.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x7043c.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71b90.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x71bec.
Definition tfib_A_StackDepotPut : Z := 0x71e78.  Definition tfib_E_StackDepotPut : Z := 0x71e98.
Definition tfib_A_StackDepotBase_Put : Z := 0x71e98.  Definition tfib_E_StackDepotBase_Put : Z := 0x7211c.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x727fc.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x72804.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72964.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x729d8.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72e60.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72f78.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x791c8.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79284.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79284.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7935c.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79940.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79d10.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x79fe0.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a098.
Definition tfib_A_lsan_register_root_region : Z := 0x7bffc.  Definition tfib_E_lsan_register_root_region : Z := 0x7c32c.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c32c.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c7b4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f714.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f790.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f790.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7f840.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f858.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f9a0.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7f9a0.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7f9ac.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7f9ac.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7f9b8.
Definition tfib_A_main : Z := 0x7f9b8.  Definition tfib_E_main : Z := 0x7fc7c.
Definition tfib_A_target_alloc_init : Z := 0x7fc7c.  Definition tfib_E_target_alloc_init : Z := 0x7fc80.
Definition tfib_A_target_alloc_count : Z := 0x7fc80.  Definition tfib_E_target_alloc_count : Z := 0x7fc88.
Definition tfib_A_target_run : Z := 0x7fc88.
Definition tfib_A_emit_printf : Z := 0x7fe10.  Definition tfib_E_emit_printf : Z := 0x7fe58.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7fe58.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7fff0.  Definition tfib_A_check_forward : Z := 0x7fff0.  Definition tfib_E_check_forward : Z := 0x80154.  Definition tfib_A_check_ret : Z := 0x80154.  Definition tfib_E_check_ret : Z := 0x801fc.  Definition tfib_A_check_downstream : Z := 0x801fc.  Definition tfib_E_check_downstream : Z := 0x80340.  Definition tfib_A_check_meter : Z := 0x80340.  Definition tfib_E_check_meter : Z := 0x80660.  Definition tfib_A_check_counter : Z := 0x80660.  Definition tfib_E_check_counter : Z := 0x80708.  Definition tfib_A_check_width : Z := 0x80708.  Definition tfib_E_check_width : Z := 0x8077c.  Definition tfib_A_check_read : Z := 0x8077c.  Definition tfib_E_check_read : Z := 0x80c38.  Definition tfib_A_check_copy : Z := 0x80c38.  Definition tfib_E_check_copy : Z := 0x80e8c.  Definition tfib_A_rp_fwd_class : Z := 0x80ec4.  Definition tfib_E_rp_fwd_class : Z := 0x80fe0.  Definition tfib_A_rp_ret_accept : Z := 0x80fe0.  Definition tfib_E_rp_ret_accept : Z := 0x8106c.  Definition tfib_A_rp_ds_accept : Z := 0x8106c.  Definition tfib_E_rp_ds_accept : Z := 0x81168.  Definition tfib_A_rp_meter_counter : Z := 0x81168.  Definition tfib_E_rp_meter_counter : Z := 0x812f4.  Definition tfib_A_rp_counter : Z := 0x812f4.  Definition tfib_E_rp_counter : Z := 0x8136c.  Definition tfib_A_rp_frame_channels : Z := 0x8136c.  Definition tfib_E_rp_frame_channels : Z := 0x813e0.  Definition tfib_A_rp_copy_untag : Z := 0x813e0.  Definition tfib_E_rp_copy_untag : Z := 0x81554.  Definition tfib_A_rp_slot_width : Z := 0x81554.  Definition tfib_E_rp_slot_width : Z := 0x8160c.  Definition tfib_A_rp_slot_read : Z := 0x8160c.  Definition tfib_E_rp_slot_read : Z := 0x817bc.  Definition tfib_A_reac_frame_is_reac : Z := 0x817bc.  Definition tfib_E_reac_frame_is_reac : Z := 0x81854.  Definition tfib_A_reac_frame_clean_len : Z := 0x81854.  Definition tfib_E_reac_frame_clean_len : Z := 0x81894.

Definition tfib_A_asan_module_ctor : Z := 0x80e8c.  Definition tfib_E_asan_module_ctor : Z := 0x80ec4.
Definition tfib_A_asan_module_dtor : Z := 0x81894.  Definition tfib_E_asan_module_dtor : Z := 0x818c4.





















Definition tfib_A_extenddftf2 : Z := 0x818d4.  Definition tfib_E_extenddftf2 : Z := 0x81a64.
Definition tfib_A_sysconf : Z := 0x876b4.  Definition tfib_E_sysconf : Z := 0x878dc.
Definition tfib_A_init : Z := 0x878dc.  Definition tfib_E_init : Z := 0x878e0.
Definition tfib_A_init_libc : Z := 0x878e0.  Definition tfib_E_init_libc : Z := 0x87b0c.
Definition tfib_A_libc_start_init : Z := 0x87b0c.  Definition tfib_E_libc_start_init : Z := 0x87b58.
Definition tfib_A_libc_start_main : Z := 0x87b58.  Definition tfib_E_libc_start_main : Z := 0x87bb8.
Definition tfib_A_libc_start_main_stage2 : Z := 0x87bb8.  Definition tfib_E_libc_start_main_stage2 : Z := 0x87c00.
Definition tfib_A_init_tls : Z := 0x87cd8.  Definition tfib_E_init_tls : Z := 0x87f88.
Definition tfib_A_init_ssp : Z := 0x87f88.  Definition tfib_E_init_ssp : Z := 0x87fe8.
Definition tfib_A_stack_chk_fail : Z := 0x87fe8.  Definition tfib_E_stack_chk_fail : Z := 0x87ff0.
Definition tfib_A_Exit : Z := 0x880cc.  Definition tfib_E_Exit : Z := 0x880e8.
Definition tfib_A_funcs_on_exit : Z := 0x88118.  Definition tfib_E_funcs_on_exit : Z := 0x881e0.
Definition tfib_A_libc_exit_fini : Z := 0x882b0.  Definition tfib_E_libc_exit_fini : Z := 0x882fc.
Definition tfib_A_exit : Z := 0x882fc.  Definition tfib_E_exit : Z := 0x88370.
Definition tfib_A_open : Z := 0x88570.  Definition tfib_E_open : Z := 0x88654.
Definition tfib_A_syscall_ret : Z := 0x88654.  Definition tfib_E_syscall_ret : Z := 0x8868c.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8868c.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x88834.
Definition tfib_A_calloc : Z := 0x88df8.  Definition tfib_E_calloc : Z := 0x88f30.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x88f30.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x88f34.
Definition tfib_A_libc_free : Z := 0x88f34.  Definition tfib_E_libc_free : Z := 0x89100.
Definition tfib_A_get_meta : Z := 0x89100.  Definition tfib_E_get_meta : Z := 0x89210.
Definition tfib_A_alloc_meta : Z := 0x895e8.  Definition tfib_E_alloc_meta : Z := 0x898c0.
Definition tfib_A_libc_malloc_impl : Z := 0x898c0.  Definition tfib_E_libc_malloc_impl : Z := 0x89c30.
Definition tfib_A_alloc_slot : Z := 0x89c30.  Definition tfib_E_alloc_slot : Z := 0x8a4d4.
Definition tfib_A_enframe : Z := 0x8a4d4.  Definition tfib_E_enframe : Z := 0x8a624.
Definition tfib_A_malloc_allzerop : Z := 0x8a624.  Definition tfib_E_malloc_allzerop : Z := 0x8a79c.
Definition tfib_A_getrlimit : Z := 0x8c44c.  Definition tfib_E_getrlimit : Z := 0x8c544.
Definition tfib_A_getrusage : Z := 0x8c544.  Definition tfib_E_getrusage : Z := 0x8c56c.
Definition tfib_A_setrlimit : Z := 0x8c56c.  Definition tfib_E_setrlimit : Z := 0x8c634.
Definition tfib_A_mmap : Z := 0x8ca5c.  Definition tfib_E_mmap : Z := 0x8cb48.
Definition tfib_A_mprotect : Z := 0x8cb48.  Definition tfib_E_mprotect : Z := 0x8cb90.
Definition tfib_A_munmap : Z := 0x8cc64.  Definition tfib_E_munmap : Z := 0x8ccac.
Definition tfib_A_sched_yield : Z := 0x8cf70.  Definition tfib_E_sched_yield : Z := 0x8cf94.
Definition tfib_A_raise_tkill_path : Z := 0x8cff0.  Definition tfib_E_raise_tkill_path : Z := 0x8d068.
Definition tfib_A_musl_sigaltstack : Z := 0x8d334.  Definition tfib_E_musl_sigaltstack : Z := 0x8d3c0.
Definition tfib_A_lockfile : Z := 0x8da00.  Definition tfib_E_lockfile : Z := 0x8dafc.
Definition tfib_A_unlockfile : Z := 0x8dafc.  Definition tfib_E_unlockfile : Z := 0x8db5c.
Definition tfib_A_stdio_read : Z := 0x8d6ec.  Definition tfib_E_stdio_read : Z := 0x8d804.
Definition tfib_A_stdio_write : Z := 0x8d80c.  Definition tfib_E_stdio_write : Z := 0x8d99c.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8d6bc.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8d6c0.
Definition tfib_A_stdio_close : Z := 0x8d6c0.  Definition tfib_E_stdio_close : Z := 0x8d6ec.
Definition tfib_A_fwritex : Z := 0x8df90.  Definition tfib_E_fwritex : Z := 0x8e0c8.
Definition tfib_A_musl_fwrite : Z := 0x8e0c8.  Definition tfib_E_musl_fwrite : Z := 0x8e180.
Definition tfib_A_towrite : Z := 0x8e180.  Definition tfib_E_towrite : Z := 0x8e1d4.
Definition tfib_A_stdio_exit : Z := 0x8ddec.  Definition tfib_E_stdio_exit : Z := 0x8df90.
Definition tfib_A_ofl_lock : Z := 0x8e1d4.  Definition tfib_E_ofl_lock : Z := 0x8e204.
Definition tfib_A_musl_vfprintf : Z := 0x8e350.  Definition tfib_E_musl_vfprintf : Z := 0x8e500.
Definition tfib_A_printf_core : Z := 0x8e500.  Definition tfib_E_printf_core : Z := 0x8f330.
Definition tfib_A_pop_arg : Z := 0x8f330.  Definition tfib_E_pop_arg : Z := 0x8f464.
Definition tfib_A_pad : Z := 0x8f464.  Definition tfib_E_pad : Z := 0x8f538.
Definition tfib_A_fmt_fp : Z := 0x8f538.  Definition tfib_E_fmt_fp : Z := 0x90c00.
Definition tfib_A_musl_wctomb : Z := 0x8cdd8.  Definition tfib_E_musl_wctomb : Z := 0x8cdfc.
Definition tfib_A_musl_wcrtomb : Z := 0x8ccac.  Definition tfib_E_musl_wcrtomb : Z := 0x8cdd8.
Definition tfib_A_fpclassifyl : Z := 0x8b03c.  Definition tfib_E_fpclassifyl : Z := 0x8b080.
Definition tfib_A_letf2 : Z := 0x8a874.  Definition tfib_E_letf2 : Z := 0x8a93c.
Definition tfib_A_multf3 : Z := 0x8a93c.  Definition tfib_E_multf3 : Z := 0x8b03c.
Definition tfib_A_floatsitf : Z := 0x8b898.  Definition tfib_E_floatsitf : Z := 0x8b9a0.
Definition tfib_A_scalbn : Z := 0x8c2a4.  Definition tfib_E_scalbn : Z := 0x8c33c.
Definition tfib_A_subtf3 : Z := 0x8b888.  Definition tfib_E_subtf3 : Z := 0x8b898.
Definition tfib_A_addtf3 : Z := 0x8b080.  Definition tfib_E_addtf3 : Z := 0x8b84c.
Definition tfib_A_fe_getround : Z := 0x8b84c.  Definition tfib_E_fe_getround : Z := 0x8b87c.
Definition tfib_A_fixunstfsi : Z := 0x90c08.  Definition tfib_E_fixunstfsi : Z := 0x90c9c.
Definition tfib_A_floatunsitf : Z := 0x90c9c.  Definition tfib_E_floatunsitf : Z := 0x90d88.
Definition tfib_A_fixtfsi : Z := 0x8c33c.  Definition tfib_E_fixtfsi : Z := 0x8c3e4.
Definition tfib_A_divtf3 : Z := 0x8b9a0.  Definition tfib_E_divtf3 : Z := 0x8c2a4.
Definition tfib_A_musl_vprintf : Z := 0x91460.  Definition tfib_E_musl_vprintf : Z := 0x9147c.
Definition tfib_A_stdout_write : Z := 0x8e210.  Definition tfib_E_stdout_write : Z := 0x8e2b0.
Definition tfib_A_musl_memcmp : Z := 0x91ae4.  Definition tfib_E_musl_memcmp : Z := 0x91b14.
Definition tfib_A_musl_memcpy : Z := 0x91b14.  Definition tfib_E_musl_memcpy : Z := 0x91f18.
Definition tfib_A_musl_memset : Z := 0x91f18.  Definition tfib_E_musl_memset : Z := 0x92010.
Definition tfib_A_musl_strchr : Z := 0x92010.  Definition tfib_E_musl_strchr : Z := 0x9204c.
Definition tfib_A_strchrnul : Z := 0x9204c.  Definition tfib_E_strchrnul : Z := 0x9212c.
Definition tfib_A_musl_strlen : Z := 0x92164.  Definition tfib_E_musl_strlen : Z := 0x921f4.
Definition tfib_A_musl_strnlen : Z := 0x923a0.  Definition tfib_E_musl_strnlen : Z := 0x923e4.
Definition tfib_A_musl_memchr : Z := 0x91a18.  Definition tfib_E_musl_memchr : Z := 0x91ae4.
Definition tfib_A_lock : Z := 0x923e4.  Definition tfib_E_lock : Z := 0x9266c.
Definition tfib_A_unlock : Z := 0x9266c.  Definition tfib_E_unlock : Z := 0x926e0.
Definition tfib_A_syscall_cp_c : Z := 0x926e0.  Definition tfib_E_syscall_cp_c : Z := 0x92704.
Definition tfib_A_syscall_cp_sccp : Z := 0x92704.  Definition tfib_E_syscall_cp_sccp : Z := 0x92708.
Definition tfib_A_pthread_atfork : Z := 0x92744.  Definition tfib_E_pthread_atfork : Z := 0x927e8.
Definition tfib_A_mremap : Z := 0x8cb90.  Definition tfib_E_mremap : Z := 0x8cc64.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x937bc.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x937d8.
Definition tfib_A_pthread_key_create : Z := 0x93b64.  Definition tfib_E_pthread_key_create : Z := 0x93c38.
Definition tfib_A_pthread_setspecific : Z := 0x94100.  Definition tfib_E_pthread_setspecific : Z := 0x94134.
Definition tfib_A_set_thread_area : Z := 0x9413c.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x94a68.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x94b20.
Definition tfib_A_close : Z := 0x97138.  Definition tfib_E_close : Z := 0x9718c.
Definition tfib_A_musl_read : Z := 0x97218.  Definition tfib_E_musl_read : Z := 0x9724c.
Definition tfib_A_vm_wait : Z := 0x94778.  Definition tfib_E_vm_wait : Z := 0x947c8.
Definition tfib_D_str_sealed : Z := 0x11806.
Definition tfib_D_init_array_0_3 : Z := 0x98250.
Definition tfib_D_fini_array_0_1 : Z := 0x98270.
Definition tfib_D_GOT_common_flags : Z := 0x987d8.
Definition tfib_D_GOT_flags : Z := 0x987e0.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x987e8.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x987f0.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x987f8.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x98800.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x99350.
Definition tfib_D_environ_musl : Z := 0x99478.
Definition tfib_D_REAL_read : Z := 0x9a520.
Definition tfib_D_REAL_memcpy : Z := 0x9a648.
Definition tfib_D_REAL_memset : Z := 0x9a650.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa0778.
Definition tfib_D_asan_inited : Z := 0xa1458.
Definition tfib_D_replace_intrin_cached : Z := 0xa1459.
Definition tfib_D_kHighMemEnd : Z := 0xa1460.
Definition tfib_D_kMidMemBeg : Z := 0xa1468.
Definition tfib_D_kMidMemEnd : Z := 0xa1470.
Definition tfib_D_malloc_context_size : Z := 0xa147c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1322a8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f5000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2ff7c.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55b000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63330.
Definition tfib_at_x_imemcpy : Z := 0x632b4.
Definition tfib_at_x_memset : Z := 0x91f18.
Definition tfib_at_x_memcpy : Z := 0x91b14.
Definition tfib_at_x_memiszero : Z := 0x63860.
Definition tfib_at_x_istrncpy : Z := 0x6375c.
Definition tfib_at_x_sealed : Z := 0x11806.
Definition tfib_at_x_popfree : Z := 0x36368.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x87918.
Definition tfib_at_x_envscan_k : Z := 0x87924.
Definition tfib_at_x_pnscan : Z := 0x879dc.
Definition tfib_at_x_pnscan_k : Z := 0x879e8.
Definition tfib_at_stops_more : list Z := (0x33fdc :: 0x35600 :: 0x5363c :: 0x599f4 :: 0x59a08 :: 0x59a1c :: 0x5f3ac :: 0x5f47c :: 0x6c9a8 :: 0x6d8b4 :: 0x6da44 :: 0x7779c :: nil)%list.
