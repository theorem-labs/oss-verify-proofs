(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.
Definition tfib_text_lo : Z := 0x307dc.
Definition tfib_init_array_lo : Z := 0x9c168.  Definition tfib_init_array_hi : Z := 0x9c188.
Definition tfib_fini_array_lo : Z := 0x9c188.  Definition tfib_fini_array_hi : Z := 0x9c198.
Definition tfib_preinit_array_lo : Z := 0x9c198.  Definition tfib_preinit_array_hi : Z := 0x9c1a0.
Definition tfib_data_rel_ro_lo : Z := 0x9c1a0.  Definition tfib_data_rel_ro_hi : Z := 0x9c810.
Definition tfib_got_lo : Z := 0x9c810.  Definition tfib_got_hi : Z := 0x9d568.
Definition tfib_data_lo : Z := 0x9e568.  Definition tfib_data_hi : Z := 0xa1120.
Definition tfib_asan_globals_lo : Z := 0xa1120.  Definition tfib_asan_globals_hi : Z := 0xa1460.
Definition tfib_bss_lo : Z := 0xa1480.  Definition tfib_bss_hi : Z := 0x5f93b0.
Definition tfib_tbss_lo : Z := 0x9b168.  Definition tfib_tbss_hi : Z := 0x9b17c.
Definition tfib_img_lo : Z := IMG_LO.  Definition tfib_img_hi : Z := IMG_TOP.
Definition tfib_entry : Z := 0x307dc.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x307dc.
Definition tfib_A_do_init : Z := 0x30824.  Definition tfib_E_do_init : Z := 0x30898.
Definition tfib_A_do_fini : Z := 0x30898.  Definition tfib_E_do_fini : Z := 0x30928.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30928.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30964.
Definition tfib_A_InitializeAllocator : Z := 0x30ad4.  Definition tfib_E_InitializeAllocator : Z := 0x30aec.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30aec.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30c58.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x311b4.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31310.
Definition tfib_A_asan_free : Z := 0x316e4.  Definition tfib_E_asan_free : Z := 0x3170c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3170c.  Definition tfib_E_Allocator_Deallocate : Z := 0x319c4.
Definition tfib_A_asan_malloc : Z := 0x319c4.  Definition tfib_E_asan_malloc : Z := 0x31a20.
Definition tfib_A_Allocator_Allocate : Z := 0x31a20.  Definition tfib_E_Allocator_Allocate : Z := 0x323a8.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32d10.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32d6c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32d6c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32fbc.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32fbc.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x330b0.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33a6c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33cf0.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33cf0.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33e70.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33e70.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34038.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34038.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34204.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x342a4.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x343a8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x346d0.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34818.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x359a8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35b20.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35cd0.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35eb4.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35eb4.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x3618c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x3618c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36604.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36604.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36704.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36704.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36a0c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36a0c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36d7c.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37298.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37380.
Definition tfib_A_AsanActivate : Z := 0x37380.  Definition tfib_E_AsanActivate : Z := 0x3745c.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c4d8.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c5b0.
Definition tfib_A_FakeStack_Create : Z := 0x3c5b0.  Definition tfib_E_FakeStack_Create : Z := 0x3c69c.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cd74.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cda4.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3cda4.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3cf18.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3cf18.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d0a8.
Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d0a8.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3d244.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3d244.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3d410.
Definition tfib_A_asan_InitializeFlags : Z := 0x3d54c.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e578.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ec84.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3faa0.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3faa0.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x4006c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x407c0.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40a30.
Definition tfib_A_thunk_417bc : Z := 0x42170.  Definition tfib_E_thunk_417bc : Z := 0x42174.
Definition tfib_A_thunk_417cc : Z := 0x42180.  Definition tfib_E_thunk_417cc : Z := 0x42188.
Definition tfib_A_thunk_417dc : Z := 0x42190.  Definition tfib_E_thunk_417dc : Z := 0x42194.
Definition tfib_A_thunk_417e4 : Z := 0x42194.  Definition tfib_E_thunk_417e4 : Z := 0x42198.
Definition tfib_A_thunk_417e8 : Z := 0x42198.  Definition tfib_E_thunk_417e8 : Z := 0x4219c.
Definition tfib_A_thunk_417ec : Z := 0x4219c.  Definition tfib_E_thunk_417ec : Z := 0x421a0.
Definition tfib_A_thunk_417f0 : Z := 0x421a0.  Definition tfib_E_thunk_417f0 : Z := 0x421a4.
Definition tfib_A_thunk_417f8 : Z := 0x421a8.  Definition tfib_E_thunk_417f8 : Z := 0x421ac.
Definition tfib_A_thunk_4180c : Z := 0x421bc.  Definition tfib_E_thunk_4180c : Z := 0x421c0.
Definition tfib_A_icpt_strlen : Z := 0x421c0.  Definition tfib_E_icpt_strlen : Z := 0x42454.
Definition tfib_A_icpt_strnlen : Z := 0x42454.  Definition tfib_E_icpt_strnlen : Z := 0x426e8.
Definition tfib_A_icpt_strcmp : Z := 0x426ec.  Definition tfib_E_icpt_strcmp : Z := 0x42c1c.
Definition tfib_A_icpt_strchr : Z := 0x42c1c.  Definition tfib_E_icpt_strchr : Z := 0x42efc.
Definition tfib_A_icpt_memcmp : Z := 0x43794.  Definition tfib_E_icpt_memcmp : Z := 0x43850.
Definition tfib_A_icpt_memchr : Z := 0x4390c.  Definition tfib_E_icpt_memchr : Z := 0x43bdc.
Definition tfib_A_icpt_frexpl : Z := 0x43bdc.  Definition tfib_E_icpt_frexpl : Z := 0x43e54.
Definition tfib_A_icpt_read : Z := 0x43e54.  Definition tfib_E_icpt_read : Z := 0x440c4.
Definition tfib_A_icpt_fwrite : Z := 0x440c4.  Definition tfib_E_icpt_fwrite : Z := 0x44338.
Definition tfib_A_icpt_time : Z := 0x44338.  Definition tfib_E_icpt_time : Z := 0x445d4.
Definition tfib_A_icpt_gmtime_r : Z := 0x447dc.  Definition tfib_E_icpt_gmtime_r : Z := 0x44a1c.
Definition tfib_A_icpt_vprintf : Z := 0x44a1c.  Definition tfib_E_icpt_vprintf : Z := 0x44ab8.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44ab8.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45580.
Definition tfib_A_icpt_vfprintf : Z := 0x45580.  Definition tfib_E_icpt_vfprintf : Z := 0x45634.
Definition tfib_A_icpt_vsnprintf : Z := 0x45634.  Definition tfib_E_icpt_vsnprintf : Z := 0x4594c.
Definition tfib_A_icpt_clock_gettime : Z := 0x45ac8.  Definition tfib_E_icpt_clock_gettime : Z := 0x45d20.
Definition tfib_A_icpt_wcrtomb : Z := 0x45d20.  Definition tfib_E_icpt_wcrtomb : Z := 0x46290.
Definition tfib_A_icpt_wctomb : Z := 0x46290.  Definition tfib_E_icpt_wctomb : Z := 0x465ec.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x466b8.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46aa0.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46aac.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b28.
Definition tfib_A_icpt_sem_timedwait : Z := 0x46d34.  Definition tfib_E_icpt_sem_timedwait : Z := 0x46fcc.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46ffc.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47224.
Definition tfib_A_icpt_send : Z := 0x47224.  Definition tfib_E_icpt_send : Z := 0x474d8.
Definition tfib_A_icpt_sendto : Z := 0x474d8.  Definition tfib_E_icpt_sendto : Z := 0x4779c.
Definition tfib_A_icpt_sigaltstack : Z := 0x4779c.  Definition tfib_E_icpt_sigaltstack : Z := 0x479f8.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47acc.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47c7c.
Definition tfib_A_asan_memcpy : Z := 0x517fc.  Definition tfib_E_asan_memcpy : Z := 0x51c98.
Definition tfib_A_asan_memset : Z := 0x51c98.  Definition tfib_E_asan_memset : Z := 0x51ed8.
Definition tfib_A_icpt_memset : Z := 0x51ed8.  Definition tfib_E_icpt_memset : Z := 0x521c8.
Definition tfib_A_icpt_memcpy : Z := 0x521c8.  Definition tfib_E_icpt_memcpy : Z := 0x527b8.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x527b8.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x527f0.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x527f0.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x527f4.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x527f4.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x527f8.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x528a4.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x529e0.
Definition tfib_A_icpt_free : Z := 0x52b54.  Definition tfib_E_icpt_free : Z := 0x52d24.
Definition tfib_A_icpt_malloc : Z := 0x52d24.  Definition tfib_E_icpt_malloc : Z := 0x52e80.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52f4c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52f50.
Definition tfib_A_SetCanPoisonMemory : Z := 0x539cc.  Definition tfib_E_SetCanPoisonMemory : Z := 0x539dc.
Definition tfib_A_CanPoisonMemory : Z := 0x539dc.  Definition tfib_E_CanPoisonMemory : Z := 0x539f0.
Definition tfib_A_PoisonShadow : Z := 0x539f0.  Definition tfib_E_PoisonShadow : Z := 0x53eec.
Definition tfib_A_MemToShadow_checked : Z := 0x53eec.  Definition tfib_E_MemToShadow_checked : Z := 0x54028.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54378.  Definition tfib_E_asan_region_is_poisoned : Z := 0x546bc.
Definition tfib_A_AsanTSDInit : Z := 0x54adc.  Definition tfib_E_AsanTSDInit : Z := 0x54b58.
Definition tfib_A_AsanTSDGet : Z := 0x54b58.  Definition tfib_E_AsanTSDGet : Z := 0x54b98.
Definition tfib_A_AsanTSDSet : Z := 0x54b98.  Definition tfib_E_AsanTSDSet : Z := 0x54bd8.
Definition tfib_A_PlatformTSDDtor : Z := 0x54bd8.  Definition tfib_E_PlatformTSDDtor : Z := 0x54c5c.
Definition tfib_A_InstallAtForkHandler : Z := 0x54c5c.  Definition tfib_E_InstallAtForkHandler : Z := 0x54c78.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54cd8.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54d1c.
Definition tfib_A_ReportDoubleFree : Z := 0x55d48.  Definition tfib_E_ReportDoubleFree : Z := 0x55fd8.
Definition tfib_A_ReportGenericError : Z := 0x578b4.  Definition tfib_E_ReportGenericError : Z := 0x58170.
Definition tfib_A_AsanInited : Z := 0x588fc.  Definition tfib_E_AsanInited : Z := 0x58914.
Definition tfib_A_asan_report_load1 : Z := 0x58914.  Definition tfib_E_asan_report_load1 : Z := 0x58964.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58964.  Definition tfib_E_asan_report_exp_load1 : Z := 0x589b4.
Definition tfib_A_asan_report_load2 : Z := 0x589b4.  Definition tfib_E_asan_report_load2 : Z := 0x58a04.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58a04.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58a54.
Definition tfib_A_asan_report_load4 : Z := 0x58a54.  Definition tfib_E_asan_report_load4 : Z := 0x58aa4.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58aa4.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58af4.
Definition tfib_A_asan_report_load8 : Z := 0x58af4.  Definition tfib_E_asan_report_load8 : Z := 0x58b44.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58b44.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58b94.
Definition tfib_A_asan_report_load16 : Z := 0x58b94.  Definition tfib_E_asan_report_load16 : Z := 0x58be4.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58be4.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58c34.
Definition tfib_A_asan_report_store1 : Z := 0x58c34.  Definition tfib_E_asan_report_store1 : Z := 0x58c84.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58c84.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58cd4.
Definition tfib_A_asan_report_store2 : Z := 0x58cd4.  Definition tfib_E_asan_report_store2 : Z := 0x58d24.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58d24.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58d74.
Definition tfib_A_asan_report_store4 : Z := 0x58d74.  Definition tfib_E_asan_report_store4 : Z := 0x58dc4.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58dc4.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58e14.
Definition tfib_A_asan_report_store8 : Z := 0x58e14.  Definition tfib_E_asan_report_store8 : Z := 0x58e64.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58e64.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58eb4.
Definition tfib_A_asan_report_store16 : Z := 0x58eb4.  Definition tfib_E_asan_report_store16 : Z := 0x58f04.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58f04.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58f54.
Definition tfib_A_asan_report_load_n : Z := 0x58f54.  Definition tfib_E_asan_report_load_n : Z := 0x58fa4.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58fa4.  Definition tfib_E_asan_report_exp_load_n : Z := 0x58ff4.
Definition tfib_A_asan_report_store_n : Z := 0x58ff4.  Definition tfib_E_asan_report_store_n : Z := 0x59044.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59044.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59094.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59094.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59114.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59114.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x594c8.
Definition tfib_A_AsanInitInternal : Z := 0x59558.  Definition tfib_E_AsanInitInternal : Z := 0x5980c.
Definition tfib_A_thunk_59674 : Z := 0x59a74.  Definition tfib_E_thunk_59674 : Z := 0x59a78.
Definition tfib_A_asan_init : Z := 0x59a78.  Definition tfib_E_asan_init : Z := 0x59b0c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59b0c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59b10.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59d74.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a09c.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a27c.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a584.
Definition tfib_A_SetMallocContextSize : Z := 0x5a584.  Definition tfib_E_SetMallocContextSize : Z := 0x5a594.
Definition tfib_A_GetMallocContextSize : Z := 0x5a594.  Definition tfib_E_GetMallocContextSize : Z := 0x5a5a4.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a5a4.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a6f4.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b1d8.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b210.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b4c4.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b550.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b550.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b5b8.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b5b8.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b630.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b630.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b698.
Definition tfib_A_AsanThread_Create : Z := 0x5bbfc.  Definition tfib_E_AsanThread_Create : Z := 0x5bd98.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5bdf4.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c00c.
Definition tfib_A_GetCurrentThread : Z := 0x5c00c.  Definition tfib_E_GetCurrentThread : Z := 0x5c02c.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c1d0.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c228.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c228.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c280.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c280.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c4b0.
Definition tfib_A_AsanThread_Init : Z := 0x5c4b0.  Definition tfib_E_AsanThread_Init : Z := 0x5c8a4.
Definition tfib_A_CreateMainThread : Z := 0x5c9e4.  Definition tfib_E_CreateMainThread : Z := 0x5caf4.
Definition tfib_A_SetCurrentThread : Z := 0x5caf4.  Definition tfib_E_SetCurrentThread : Z := 0x5cbd4.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5cdd8.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5cf14.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e524.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e570.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e570.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e57c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e5ac.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e5b8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e5b8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e5c4.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e5e0.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e8ac.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e8ac.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ec6c.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fbd4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fcac.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fcac.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fd48.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6026c.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x602b0.
Definition tfib_A_RunMallocHooks : Z := 0x607e0.  Definition tfib_E_RunMallocHooks : Z := 0x60898.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60898.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x6089c.
Definition tfib_A_RunFreeHooks : Z := 0x6089c.  Definition tfib_E_RunFreeHooks : Z := 0x60948.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60c8c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60ecc.
Definition tfib_A_sanitizer_set_report_path : Z := 0x614c8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x614e0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x630f0.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63400.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63400.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63544.
Definition tfib_A_FlagParser_ParseString : Z := 0x63544.  Definition tfib_E_FlagParser_ParseString : Z := 0x63638.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x6382c.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x6386c.
Definition tfib_A_internal_atoll : Z := 0x6386c.  Definition tfib_E_internal_atoll : Z := 0x63958.
Definition tfib_A_internal_simple_strtoll : Z := 0x63958.  Definition tfib_E_internal_simple_strtoll : Z := 0x63ab4.
Definition tfib_A_internal_memchr : Z := 0x63ab4.  Definition tfib_E_internal_memchr : Z := 0x63ad4.
Definition tfib_A_internal_memcmp : Z := 0x63ad4.  Definition tfib_E_internal_memcmp : Z := 0x63b0c.
Definition tfib_A_internal_memcpy : Z := 0x63b0c.  Definition tfib_E_internal_memcpy : Z := 0x63b30.
Definition tfib_A_internal_memmove : Z := 0x63b30.  Definition tfib_E_internal_memmove : Z := 0x63b88.
Definition tfib_A_internal_memset : Z := 0x63b88.  Definition tfib_E_internal_memset : Z := 0x63be8.
Definition tfib_A_internal_strcspn : Z := 0x63be8.  Definition tfib_E_internal_strcspn : Z := 0x63c3c.
Definition tfib_A_internal_strdup : Z := 0x63c70.  Definition tfib_E_internal_strdup : Z := 0x63cdc.
Definition tfib_A_internal_strlen : Z := 0x63cdc.  Definition tfib_E_internal_strlen : Z := 0x63cf8.
Definition tfib_A_internal_strchrnul : Z := 0x63d88.  Definition tfib_E_internal_strchrnul : Z := 0x63dd0.
Definition tfib_A_internal_strrchr : Z := 0x63dd0.  Definition tfib_E_internal_strrchr : Z := 0x63e10.
Definition tfib_A_internal_strnlen : Z := 0x63f40.  Definition tfib_E_internal_strnlen : Z := 0x63f70.
Definition tfib_A_internal_strncpy : Z := 0x63fb4.  Definition tfib_E_internal_strncpy : Z := 0x64024.
Definition tfib_A_internal_strstr : Z := 0x64024.  Definition tfib_E_internal_strstr : Z := 0x640b8.
Definition tfib_A_mem_is_zero : Z := 0x640b8.  Definition tfib_E_mem_is_zero : Z := 0x6416c.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6416c.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6417c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6417c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6435c.
Definition tfib_A_internal_iserror : Z := 0x64368.  Definition tfib_E_internal_iserror : Z := 0x64388.
Definition tfib_A_internal_mmap : Z := 0x64388.  Definition tfib_E_internal_mmap : Z := 0x64394.
Definition tfib_A_internal_munmap : Z := 0x64394.  Definition tfib_E_internal_munmap : Z := 0x643a0.
Definition tfib_A_internal_mprotect : Z := 0x643a0.  Definition tfib_E_internal_mprotect : Z := 0x643b0.
Definition tfib_A_internal_madvise : Z := 0x643b0.  Definition tfib_E_internal_madvise : Z := 0x643dc.
Definition tfib_A_internal_close : Z := 0x643dc.  Definition tfib_E_internal_close : Z := 0x643e8.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x643e8.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x6440c.
Definition tfib_A_internal_read : Z := 0x6440c.  Definition tfib_E_internal_read : Z := 0x64444.
Definition tfib_A_internal_write : Z := 0x64444.  Definition tfib_E_internal_write : Z := 0x6447c.
Definition tfib_A_internal_ftruncate : Z := 0x6447c.  Definition tfib_E_internal_ftruncate : Z := 0x644b4.
Definition tfib_A_internal_dup : Z := 0x644b4.  Definition tfib_E_internal_dup : Z := 0x644c0.
Definition tfib_A_internal_dup2_dup3 : Z := 0x644c0.  Definition tfib_E_internal_dup2_dup3 : Z := 0x644d0.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x644d0.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x644e8.
Definition tfib_A_internal_sched_yield : Z := 0x644e8.  Definition tfib_E_internal_sched_yield : Z := 0x644f4.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x644f4.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64540.
Definition tfib_A_internal_execve : Z := 0x64540.  Definition tfib_E_internal_execve : Z := 0x6454c.
Definition tfib_A_internal_exit_exit_group : Z := 0x6454c.  Definition tfib_E_internal_exit_exit_group : Z := 0x64560.
Definition tfib_A_FileExists_newfstatat : Z := 0x64560.  Definition tfib_E_FileExists_newfstatat : Z := 0x645e0.
Definition tfib_A_DirExists_newfstatat : Z := 0x645e0.  Definition tfib_E_DirExists_newfstatat : Z := 0x64644.
Definition tfib_A_GetTid_gettid : Z := 0x64644.  Definition tfib_E_GetTid_gettid : Z := 0x64650.
Definition tfib_A_GetEnv : Z := 0x64650.  Definition tfib_E_GetEnv : Z := 0x64780.
Definition tfib_A_FutexWait : Z := 0x64884.  Definition tfib_E_FutexWait : Z := 0x648a8.
Definition tfib_A_FutexWake : Z := 0x648a8.  Definition tfib_E_FutexWake : Z := 0x648cc.
Definition tfib_A_internal_ptrace : Z := 0x648cc.  Definition tfib_E_internal_ptrace : Z := 0x648d8.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x648d8.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x648e8.
Definition tfib_A_internal_getpid : Z := 0x648e8.  Definition tfib_E_internal_getpid : Z := 0x648f4.
Definition tfib_A_internal_getppid : Z := 0x648f4.  Definition tfib_E_internal_getppid : Z := 0x64900.
Definition tfib_A_internal_prctl : Z := 0x64900.  Definition tfib_E_internal_prctl : Z := 0x6490c.
Definition tfib_A_internal_sigaltstack : Z := 0x6490c.  Definition tfib_E_internal_sigaltstack : Z := 0x64918.
Definition tfib_A_internal_fork_clone : Z := 0x64918.  Definition tfib_E_internal_fork_clone : Z := 0x64930.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64930.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64a5c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6519c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x652b4.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x652bc.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65368.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65368.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65488.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65550.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x655d0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6562c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x656f8.
Definition tfib_A_thunk_653ec : Z := 0x657f4.  Definition tfib_E_thunk_653ec : Z := 0x657f8.
Definition tfib_A_CheckASLR : Z := 0x657f8.  Definition tfib_E_CheckASLR : Z := 0x657fc.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65a48.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65a4c.
Definition tfib_A_MmapOrDie : Z := 0x65a58.  Definition tfib_E_MmapOrDie : Z := 0x65b64.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65b64.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65bd8.
Definition tfib_A_UnmapOrDie : Z := 0x65bd8.  Definition tfib_E_UnmapOrDie : Z := 0x65c54.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65c54.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65d64.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65f90.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66094.
Definition tfib_A_thunk_66008 : Z := 0x66410.  Definition tfib_E_thunk_66008 : Z := 0x66414.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66734.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66940.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66ef8.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66f04.
Definition tfib_A_Printf : Z := 0x66f08.  Definition tfib_E_Printf : Z := 0x66f54.
Definition tfib_A_SharedPrintfCode : Z := 0x66f54.  Definition tfib_E_SharedPrintfCode : Z := 0x66fb0.
Definition tfib_A_Report : Z := 0x66fb0.  Definition tfib_E_Report : Z := 0x66ffc.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68af4.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68b50.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68b50.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68d8c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68d8c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x690b0.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69d60.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a1d8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6aa98.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6adbc.
Definition tfib_A_AddDieCallback : Z := 0x6b678.  Definition tfib_E_AddDieCallback : Z := 0x6b700.
Definition tfib_A_Die : Z := 0x6b7c4.  Definition tfib_E_Die : Z := 0x6b884.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b884.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b890.
Definition tfib_A_CheckFailed : Z := 0x6b890.  Definition tfib_E_CheckFailed : Z := 0x6b948.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6bfa0.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c098.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c098.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c1c4.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c49c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c784.
Definition tfib_A_AndroidLogInit : Z := 0x6d02c.  Definition tfib_E_AndroidLogInit : Z := 0x6d030.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d060.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d0a8.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d0a8.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d2f4.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d404.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d508.
Definition tfib_A_thunk_6d37c : Z := 0x6d784.  Definition tfib_E_thunk_6d37c : Z := 0x6d788.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d84c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d8ec.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d978.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6da3c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6da3c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6dac4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6dac4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6db3c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6db3c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dc20.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dcdc.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6de10.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x700d4.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x701f8.
Definition tfib_A_StackStore_Alloc : Z := 0x701f8.  Definition tfib_E_StackStore_Alloc : Z := 0x7032c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70be0.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70c94.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x723e8.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72444.
Definition tfib_A_StackDepotPut : Z := 0x726d0.  Definition tfib_E_StackDepotPut : Z := 0x726f0.
Definition tfib_A_StackDepotBase_Put : Z := 0x726f0.  Definition tfib_E_StackDepotBase_Put : Z := 0x72974.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73054.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x7305c.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x731bc.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73230.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x736b8.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x737d0.
Definition tfib_A_thunk_762d8 : Z := 0x7681c.  Definition tfib_E_thunk_762d8 : Z := 0x76820.
Definition tfib_A_thunk_77ab0 : Z := 0x77ff4.  Definition tfib_E_thunk_77ab0 : Z := 0x77ff8.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79a20.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79adc.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79adc.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79bb4.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a198.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a568.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a838.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a8f0.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bc48.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bc4c.
Definition tfib_A_lsan_register_root_region : Z := 0x7c854.  Definition tfib_E_lsan_register_root_region : Z := 0x7cb84.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cb84.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d00c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7ff6c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7ffe8.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7ffe8.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80098.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x800b0.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x801f8.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x801f8.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80204.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80204.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80210.
Definition tfib_A_main : Z := 0x80210.  Definition tfib_E_main : Z := 0x804d4.
Definition tfib_A_target_alloc_init : Z := 0x804d4.  Definition tfib_E_target_alloc_init : Z := 0x804d8.
Definition tfib_A_target_alloc_count : Z := 0x804d8.  Definition tfib_E_target_alloc_count : Z := 0x804e0.
Definition tfib_A_target_run : Z := 0x804e0.
Definition tfib_A_emit_printf : Z := 0x80668.  Definition tfib_E_emit_printf : Z := 0x806b0.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x806b0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x81b70.
Definition tfib_A_check_groupa : Z := 0x81b70.  Definition tfib_E_check_groupa : Z := 0x81f24.
Definition tfib_A_asan_module_ctor : Z := 0x81f24.  Definition tfib_E_asan_module_ctor : Z := 0x81f5c.
Definition tfib_A_asan_module_dtor : Z := 0x81f5c.  Definition tfib_E_asan_module_dtor : Z := 0x81f8c.
Definition tfib_A_reac_ctrl_checksum_verify : Z := 0x81f8c.  Definition tfib_E_reac_ctrl_checksum_verify : Z := 0x82000.
Definition tfib_A_reac_ctrl_parse : Z := 0x82000.  Definition tfib_E_reac_ctrl_parse : Z := 0x829a0.
Definition tfib_A_kind_of_link1 : Z := 0x829a0.  Definition tfib_E_kind_of_link1 : Z := 0x82a14.
Definition tfib_A_reac_ctrl_stamp_headamp : Z := 0x82a14.  Definition tfib_E_reac_ctrl_stamp_headamp : Z := 0x82c60.
Definition tfib_A_reac_ctrl_headamp_record_verify : Z := 0x82c60.  Definition tfib_E_reac_ctrl_headamp_record_verify : Z := 0x82d3c.
Definition tfib_A_reac_ctrl_identity_poll_block : Z := 0x82d3c.  Definition tfib_E_reac_ctrl_identity_poll_block : Z := 0x82d8c.
Definition tfib_A_reac_ctrl_build_grant_sweep : Z := 0x82d8c.  Definition tfib_E_reac_ctrl_build_grant_sweep : Z := 0x82ffc.
Definition tfib_A_ctrl_lay_block : Z := 0x82ffc.  Definition tfib_E_ctrl_lay_block : Z := 0x8339c.
Definition tfib_A_ctrl_finish : Z := 0x8339c.  Definition tfib_E_ctrl_finish : Z := 0x8354c.
Definition tfib_A_reac_box_model_block : Z := 0x8354c.  Definition tfib_E_reac_box_model_block : Z := 0x843cc.
Definition tfib_A_build_dt1_single : Z := 0x843cc.  Definition tfib_E_build_dt1_single : Z := 0x8483c.
Definition tfib_A_reac_grant_alloc_fits : Z := 0x8483c.  Definition tfib_E_reac_grant_alloc_fits : Z := 0x84860.
Definition tfib_A_reac_grant_allocate : Z := 0x84860.  Definition tfib_E_reac_grant_allocate : Z := 0x848f0.
Definition tfib_A_reac_grant_build_sweep : Z := 0x848f0.  Definition tfib_E_reac_grant_build_sweep : Z := 0x84d1c.
Definition tfib_A_reac_headamp_tx_init : Z := 0x84d1c.  Definition tfib_E_reac_headamp_tx_init : Z := 0x84d3c.
Definition tfib_A_reac_headamp_tx_set : Z := 0x84d3c.  Definition tfib_E_reac_headamp_tx_set : Z := 0x84e54.
Definition tfib_A_reac_headamp_default : Z := 0x84e54.  Definition tfib_E_reac_headamp_default : Z := 0x84e64.
Definition tfib_A_reac_headamp_tx_effective : Z := 0x84e64.  Definition tfib_E_reac_headamp_tx_effective : Z := 0x84f1c.
Definition tfib_A_reac_headamp_tx_arm_scene : Z := 0x84f1c.  Definition tfib_E_reac_headamp_tx_arm_scene : Z := 0x85058.
Definition tfib_A_reac_headamp_tx_set_resweep : Z := 0x85058.  Definition tfib_E_reac_headamp_tx_set_resweep : Z := 0x850cc.
Definition tfib_A_reac_headamp_tx_next : Z := 0x850cc.  Definition tfib_E_reac_headamp_tx_next : Z := 0x857dc.
Definition tfib_A_extenddftf2 : Z := 0x857ec.  Definition tfib_E_extenddftf2 : Z := 0x8597c.
Definition tfib_A_sysconf : Z := 0x8b5cc.  Definition tfib_E_sysconf : Z := 0x8b7f4.
Definition tfib_A_init : Z := 0x8b7f4.  Definition tfib_E_init : Z := 0x8b7f8.
Definition tfib_A_init_libc : Z := 0x8b7f8.  Definition tfib_E_init_libc : Z := 0x8ba24.
Definition tfib_A_libc_start_init : Z := 0x8ba24.  Definition tfib_E_libc_start_init : Z := 0x8ba70.
Definition tfib_A_libc_start_main : Z := 0x8ba70.  Definition tfib_E_libc_start_main : Z := 0x8bad0.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8bad0.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8bb18.
Definition tfib_A_init_tls : Z := 0x8bbf0.  Definition tfib_E_init_tls : Z := 0x8bea0.
Definition tfib_A_init_ssp : Z := 0x8bea0.  Definition tfib_E_init_ssp : Z := 0x8bf00.
Definition tfib_A_stack_chk_fail : Z := 0x8bf00.  Definition tfib_E_stack_chk_fail : Z := 0x8bf08.
Definition tfib_A_Exit : Z := 0x8bfe4.  Definition tfib_E_Exit : Z := 0x8c000.
Definition tfib_A_funcs_on_exit : Z := 0x8c030.  Definition tfib_E_funcs_on_exit : Z := 0x8c0f8.
Definition tfib_A_libc_exit_fini : Z := 0x8c1c8.  Definition tfib_E_libc_exit_fini : Z := 0x8c214.
Definition tfib_A_exit : Z := 0x8c214.  Definition tfib_E_exit : Z := 0x8c288.
Definition tfib_A_open : Z := 0x8c488.  Definition tfib_E_open : Z := 0x8c56c.
Definition tfib_A_syscall_ret : Z := 0x8c56c.  Definition tfib_E_syscall_ret : Z := 0x8c5a4.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8c5a4.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8c74c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8ce48.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8ce4c.
Definition tfib_A_libc_free : Z := 0x8ce4c.  Definition tfib_E_libc_free : Z := 0x8d018.
Definition tfib_A_get_meta : Z := 0x8d018.  Definition tfib_E_get_meta : Z := 0x8d128.
Definition tfib_A_alloc_meta : Z := 0x8d500.  Definition tfib_E_alloc_meta : Z := 0x8d7d8.
Definition tfib_A_libc_malloc_impl : Z := 0x8d7d8.  Definition tfib_E_libc_malloc_impl : Z := 0x8db48.
Definition tfib_A_alloc_slot : Z := 0x8db48.  Definition tfib_E_alloc_slot : Z := 0x8e3ec.
Definition tfib_A_enframe : Z := 0x8e3ec.  Definition tfib_E_enframe : Z := 0x8e53c.
Definition tfib_A_malloc_allzerop : Z := 0x8e53c.  Definition tfib_E_malloc_allzerop : Z := 0x8e6b4.
Definition tfib_A_getrlimit : Z := 0x90364.  Definition tfib_E_getrlimit : Z := 0x9045c.
Definition tfib_A_getrusage : Z := 0x9045c.  Definition tfib_E_getrusage : Z := 0x90484.
Definition tfib_A_setrlimit : Z := 0x90484.  Definition tfib_E_setrlimit : Z := 0x9054c.
Definition tfib_A_mmap : Z := 0x90974.  Definition tfib_E_mmap : Z := 0x90a60.
Definition tfib_A_mprotect : Z := 0x90a60.  Definition tfib_E_mprotect : Z := 0x90aa8.
Definition tfib_A_munmap : Z := 0x90b7c.  Definition tfib_E_munmap : Z := 0x90bc4.
Definition tfib_A_sched_yield : Z := 0x90e88.  Definition tfib_E_sched_yield : Z := 0x90eac.
Definition tfib_A_raise_tkill_path : Z := 0x90f08.  Definition tfib_E_raise_tkill_path : Z := 0x90f80.
Definition tfib_A_musl_sigaltstack : Z := 0x9124c.  Definition tfib_E_musl_sigaltstack : Z := 0x912d8.
Definition tfib_A_lockfile : Z := 0x91918.  Definition tfib_E_lockfile : Z := 0x91a14.
Definition tfib_A_unlockfile : Z := 0x91a14.  Definition tfib_E_unlockfile : Z := 0x91a74.
Definition tfib_A_stdio_read : Z := 0x91604.  Definition tfib_E_stdio_read : Z := 0x9171c.
Definition tfib_A_stdio_write : Z := 0x91724.  Definition tfib_E_stdio_write : Z := 0x918b4.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x915d4.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x915d8.
Definition tfib_A_stdio_close : Z := 0x915d8.  Definition tfib_E_stdio_close : Z := 0x91604.
Definition tfib_A_fwritex : Z := 0x91ea8.  Definition tfib_E_fwritex : Z := 0x91fe0.
Definition tfib_A_musl_fwrite : Z := 0x91fe0.  Definition tfib_E_musl_fwrite : Z := 0x92098.
Definition tfib_A_towrite : Z := 0x92098.  Definition tfib_E_towrite : Z := 0x920ec.
Definition tfib_A_stdio_exit : Z := 0x91d04.  Definition tfib_E_stdio_exit : Z := 0x91ea8.
Definition tfib_A_ofl_lock : Z := 0x920ec.  Definition tfib_E_ofl_lock : Z := 0x9211c.
Definition tfib_A_musl_vfprintf : Z := 0x92268.  Definition tfib_E_musl_vfprintf : Z := 0x92418.
Definition tfib_A_printf_core : Z := 0x92418.  Definition tfib_E_printf_core : Z := 0x93248.
Definition tfib_A_pop_arg : Z := 0x93248.  Definition tfib_E_pop_arg : Z := 0x9337c.
Definition tfib_A_pad : Z := 0x9337c.  Definition tfib_E_pad : Z := 0x93450.
Definition tfib_A_fmt_fp : Z := 0x93450.  Definition tfib_E_fmt_fp : Z := 0x94b18.
Definition tfib_A_thunk_931e0 : Z := 0x8c964.  Definition tfib_E_thunk_931e0 : Z := 0x8c968.
Definition tfib_A_musl_wctomb : Z := 0x90cf0.  Definition tfib_E_musl_wctomb : Z := 0x90d14.
Definition tfib_A_musl_wcrtomb : Z := 0x90bc4.  Definition tfib_E_musl_wcrtomb : Z := 0x90cf0.
Definition tfib_A_fpclassifyl : Z := 0x8ef54.  Definition tfib_E_fpclassifyl : Z := 0x8ef98.
Definition tfib_A_letf2 : Z := 0x8e78c.  Definition tfib_E_letf2 : Z := 0x8e854.
Definition tfib_A_multf3 : Z := 0x8e854.  Definition tfib_E_multf3 : Z := 0x8ef54.
Definition tfib_A_floatsitf : Z := 0x8f7b0.  Definition tfib_E_floatsitf : Z := 0x8f8b8.
Definition tfib_A_scalbn : Z := 0x901bc.  Definition tfib_E_scalbn : Z := 0x90254.
Definition tfib_A_subtf3 : Z := 0x8f7a0.  Definition tfib_E_subtf3 : Z := 0x8f7b0.
Definition tfib_A_addtf3 : Z := 0x8ef98.  Definition tfib_E_addtf3 : Z := 0x8f764.
Definition tfib_A_fe_getround : Z := 0x8f764.  Definition tfib_E_fe_getround : Z := 0x8f794.
Definition tfib_A_fixunstfsi : Z := 0x94b20.  Definition tfib_E_fixunstfsi : Z := 0x94bb4.
Definition tfib_A_floatunsitf : Z := 0x94bb4.  Definition tfib_E_floatunsitf : Z := 0x94ca0.
Definition tfib_A_fixtfsi : Z := 0x90254.  Definition tfib_E_fixtfsi : Z := 0x902fc.
Definition tfib_A_divtf3 : Z := 0x8f8b8.  Definition tfib_E_divtf3 : Z := 0x901bc.
Definition tfib_A_musl_vprintf : Z := 0x95378.  Definition tfib_E_musl_vprintf : Z := 0x95394.
Definition tfib_A_stdout_write : Z := 0x92128.  Definition tfib_E_stdout_write : Z := 0x921c8.
Definition tfib_A_thunk_95368 : Z := 0x9592c.  Definition tfib_E_thunk_95368 : Z := 0x95930.
Definition tfib_A_musl_memcmp : Z := 0x959fc.  Definition tfib_E_musl_memcmp : Z := 0x95a2c.
Definition tfib_A_musl_memcpy : Z := 0x95a2c.  Definition tfib_E_musl_memcpy : Z := 0x95e30.
Definition tfib_A_musl_memset : Z := 0x95e30.  Definition tfib_E_musl_memset : Z := 0x95f28.
Definition tfib_A_musl_strchr : Z := 0x95f28.  Definition tfib_E_musl_strchr : Z := 0x95f64.
Definition tfib_A_strchrnul : Z := 0x95f64.  Definition tfib_E_strchrnul : Z := 0x96044.
Definition tfib_A_musl_strlen : Z := 0x9607c.  Definition tfib_E_musl_strlen : Z := 0x9610c.
Definition tfib_A_musl_strnlen : Z := 0x962b8.  Definition tfib_E_musl_strnlen : Z := 0x962fc.
Definition tfib_A_musl_memchr : Z := 0x95930.  Definition tfib_E_musl_memchr : Z := 0x959fc.
Definition tfib_A_lock : Z := 0x962fc.  Definition tfib_E_lock : Z := 0x96584.
Definition tfib_A_unlock : Z := 0x96584.  Definition tfib_E_unlock : Z := 0x965f8.
Definition tfib_A_syscall_cp_c : Z := 0x965f8.  Definition tfib_E_syscall_cp_c : Z := 0x9661c.
Definition tfib_A_syscall_cp_sccp : Z := 0x9661c.  Definition tfib_E_syscall_cp_sccp : Z := 0x96620.
Definition tfib_A_pthread_atfork : Z := 0x9665c.  Definition tfib_E_pthread_atfork : Z := 0x96700.
Definition tfib_A_mremap : Z := 0x90aa8.  Definition tfib_E_mremap : Z := 0x90b7c.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x976d4.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x976f0.
Definition tfib_A_pthread_key_create : Z := 0x97a7c.  Definition tfib_E_pthread_key_create : Z := 0x97b50.
Definition tfib_A_pthread_setspecific : Z := 0x98018.  Definition tfib_E_pthread_setspecific : Z := 0x9804c.
Definition tfib_A_set_thread_area : Z := 0x98054.
Definition tfib_A_thunk_96f9c : Z := 0x9804c.  Definition tfib_E_thunk_96f9c : Z := 0x98054.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98980.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98a38.
Definition tfib_A_close : Z := 0x9b050.  Definition tfib_E_close : Z := 0x9b0a4.
Definition tfib_A_musl_read : Z := 0x9b130.  Definition tfib_E_musl_read : Z := 0x9b164.
Definition tfib_A_vm_wait : Z := 0x98690.  Definition tfib_E_vm_wait : Z := 0x986e0.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x9c168.
Definition tfib_D_fini_array_0_1 : Z := 0x9c188.
Definition tfib_D_GOT_common_flags : Z := 0x9c860.
Definition tfib_D_GOT_flags : Z := 0x9c868.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c870.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c878.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c880.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c888.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9d3d8.
Definition tfib_D_environ_musl : Z := 0x9d500.
Definition tfib_D_REAL_read : Z := 0x9e5a8.
Definition tfib_D_REAL_memcpy : Z := 0x9e6d0.
Definition tfib_D_REAL_memset : Z := 0x9e6d8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa14d8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa2338.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa4b38.
Definition tfib_D_asan_inited : Z := 0xa5818.
Definition tfib_D_replace_intrin_cached : Z := 0xa5819.
Definition tfib_D_kHighMemEnd : Z := 0xa5820.
Definition tfib_D_kMidMemBeg : Z := 0xa5828.
Definition tfib_D_kMidMemEnd : Z := 0xa5830.
Definition tfib_D_malloc_context_size : Z := 0xa583c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136668.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f7d60.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x307dc.
Definition tfib_at_rw_lo : Z := 0x9e000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63b88.
Definition tfib_at_x_imemcpy : Z := 0x63b0c.
Definition tfib_at_x_memset : Z := 0x95e30.
Definition tfib_at_x_memcpy : Z := 0x95a2c.
Definition tfib_at_x_memiszero : Z := 0x640b8.
Definition tfib_at_x_istrncpy : Z := 0x63fb4.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x36bc8.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8b830.
Definition tfib_at_x_envscan_k : Z := 0x8b83c.
Definition tfib_at_x_pnscan : Z := 0x8b8f4.
Definition tfib_at_x_pnscan_k : Z := 0x8b900.
Definition tfib_at_stops_more : list Z := (0x3483c :: 0x35e60 :: 0x53e94 :: 0x5a24c :: 0x5a260 :: 0x5a274 :: 0x5fc04 :: 0x5fcd4 :: 0x6d200 :: 0x6e10c :: 0x6e29c :: 0x77ff4 :: nil)%list.
