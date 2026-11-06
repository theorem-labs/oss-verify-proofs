(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its rows regenerated for plugin-hostd/fuzz_command's ASan build by the AB1w row regenerator: each start is the fuzz_command function paired by code with cgif's, each end the pair of cgif's last instruction plus its length; a row whose label is a FUNC symbol of fuzz_command's image takes that symbol's range (LLVMFuzzerTestOneInput); the side-stack class rows are fuzz_command's own __asan_stack_malloc_0, _1, _3, _4, _5 and _7 (symbol address and size; class 1 keeps cgif's row name asan_stack_malloc_A, the others are named by class); six rows are set from the image by hand (HaveStackTraceBasedSuppressions, set_thread_area, two jump stubs by their target, the self-loop stub, and the ends of __stdio_exit and musl memset, whose code differs); section bounds come from fuzz_command's section headers; the rows of cgif functions fuzz_command does not have (cgif's program and GIF library, fopen/fclose/fdopen/ofl_add/fmodeflags and their interceptors, stack_malloc_2) are dropped; thirteen rows whose cgif label names another function than the code of their range take the name of the image symbol at their start (internal_strchr / _strcmp / _strncmp, AsanCheckIncompatibleRT / AsanCheckDynamicRTPrereqs, IsAddrSuppressed, IsRssLimitExceeded, DecreaseTotalMmap, GetTls, MmapFixedSuperNoReserve, MmapNoAccess, ReservedAddressRange_MapOrDie, and MmapFixedOrDie for cgif's shim row). *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x246a4.
Definition tfib_text_lo : Z := 0x33340.  Definition tfib_text_hi : Z := 0xa46fc.
Definition tfib_init_array_lo : Z := 0xa5700.  Definition tfib_init_array_hi : Z := 0xa5720.
Definition tfib_fini_array_lo : Z := 0xa5720.  Definition tfib_fini_array_hi : Z := 0xa5730.
Definition tfib_preinit_array_lo : Z := 0xa5730.  Definition tfib_preinit_array_hi : Z := 0xa5738.
Definition tfib_data_rel_ro_lo : Z := 0xa5740.  Definition tfib_data_rel_ro_hi : Z := 0xa6390.
Definition tfib_got_lo : Z := 0xa6390.  Definition tfib_got_hi : Z := 0xa7108.
Definition tfib_data_lo : Z := 0xa8108.  Definition tfib_data_hi : Z := 0xaacf8.
Definition tfib_asan_globals_lo : Z := 0xaad00.  Definition tfib_asan_globals_hi : Z := 0xada00.
Definition tfib_bss_lo : Z := 0xada00.  Definition tfib_bss_hi : Z := 0x605e78.
Definition tfib_tbss_lo : Z := 0xa4700.  Definition tfib_tbss_hi : Z := 0xa4714.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x606000.
Definition tfib_entry : Z := 0x33340.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x33340.  Definition tfib_E_start : Z := 0x33388.
Definition tfib_A_do_init : Z := 0x33388.  Definition tfib_E_do_init : Z := 0x333fc.
Definition tfib_A_do_fini : Z := 0x333fc.  Definition tfib_E_do_fini : Z := 0x3348c.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x3348c.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x334c8.
Definition tfib_A_InitializeAllocator : Z := 0x33638.  Definition tfib_E_InitializeAllocator : Z := 0x33650.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x33650.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x337bc.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x33d18.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x33e74.
Definition tfib_A_asan_free : Z := 0x34248.  Definition tfib_E_asan_free : Z := 0x34270.
Definition tfib_A_Allocator_Deallocate : Z := 0x34270.  Definition tfib_E_Allocator_Deallocate : Z := 0x34528.
Definition tfib_A_asan_malloc : Z := 0x34528.  Definition tfib_E_asan_malloc : Z := 0x34584.
Definition tfib_A_Allocator_Allocate : Z := 0x34584.  Definition tfib_E_Allocator_Allocate : Z := 0x34f0c.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x35644.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x35788.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x35874.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x358d0.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x358d0.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x35b20.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35b20.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35c14.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x35c14.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x35cfc.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x36130.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x36314.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x36314.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x36498.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x365d0.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x36854.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x36854.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x369d4.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x369d4.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x36b9c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x36b9c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x36d68.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x36d68.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x36e08.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x36e08.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x36f0c.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x37234.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x3737c.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x3737c.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x373b4.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37b4c.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37e34.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x3850c.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x38684.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x38684.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x38834.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x38834.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x38a18.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x38a18.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x38cf0.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x38cf0.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x39168.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x39168.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x39268.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x39268.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x39570.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x39570.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x398e0.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x398e0.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x399f8.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x39d00.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x39dfc.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x39dfc.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x39ee4.
Definition tfib_A_AsanActivate : Z := 0x39ee4.  Definition tfib_E_AsanActivate : Z := 0x39fc0.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x3a49c.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x3a584.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3f03c.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3f114.
Definition tfib_A_FakeStack_Create : Z := 0x3f114.  Definition tfib_E_FakeStack_Create : Z := 0x3f200.
Definition tfib_A_FakeStack_Allocate : Z := 0x3f4bc.  Definition tfib_E_FakeStack_Allocate : Z := 0x3f7a4.
Definition tfib_A_SetTLSFakeStack : Z := 0x3f8d8.  Definition tfib_E_SetTLSFakeStack : Z := 0x3f908.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3fa7c.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3fc0c.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3f908.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3fa7c.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3fc0c.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3fdb8.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3fdb8.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3ff84.
Definition tfib_A_asan_stack_malloc_5 : Z := 0x3ff84.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x40190.
Definition tfib_A_asan_stack_malloc_7 : Z := 0x40244.  Definition tfib_E_asan_stack_malloc_7 : Z := 0x403c0.
Definition tfib_A_FakeStack_SetShadow : Z := 0x40410.  Definition tfib_E_FakeStack_SetShadow : Z := 0x4054c.
Definition tfib_A_asan_InitializeFlags : Z := 0x4054c.  Definition tfib_E_asan_InitializeFlags : Z := 0x41578.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x41c84.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x42aa0.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x42aa0.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x4306c.
Definition tfib_A_asan_register_globals : Z := 0x4306c.  Definition tfib_E_asan_register_globals : Z := 0x430d8.
Definition tfib_A_asan_unregister_globals : Z := 0x430d8.  Definition tfib_E_asan_unregister_globals : Z := 0x43140.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x437c0.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x43a30.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x43a30.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x43d38.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x444ac.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x445fc.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x45018.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x45130.
Definition tfib_A_strlen : Z := 0x45130.  Definition tfib_E_strlen : Z := 0x45134.
Definition tfib_A_strnlen : Z := 0x45134.  Definition tfib_E_strnlen : Z := 0x45138.
Definition tfib_A_strcmp : Z := 0x4513c.  Definition tfib_E_strcmp : Z := 0x45140.
Definition tfib_A_strchr : Z := 0x45144.  Definition tfib_E_strchr : Z := 0x45148.
Definition tfib_A_memcmp : Z := 0x45150.  Definition tfib_E_memcmp : Z := 0x45154.
Definition tfib_A_memcmp_2 : Z := 0x45154.  Definition tfib_E_memcmp_2 : Z := 0x45158.
Definition tfib_A_memchr : Z := 0x45158.  Definition tfib_E_memchr : Z := 0x4515c.
Definition tfib_A_frexpl : Z := 0x4515c.  Definition tfib_E_frexpl : Z := 0x45160.
Definition tfib_A_read : Z := 0x45160.  Definition tfib_E_read : Z := 0x45164.
Definition tfib_A_fwrite : Z := 0x45164.  Definition tfib_E_fwrite : Z := 0x45168.
Definition tfib_A_time : Z := 0x45168.  Definition tfib_E_time : Z := 0x4516c.
Definition tfib_A_gmtime_r : Z := 0x4516c.  Definition tfib_E_gmtime_r : Z := 0x45170.
Definition tfib_A_vprintf : Z := 0x45170.  Definition tfib_E_vprintf : Z := 0x45174.
Definition tfib_A_vfprintf : Z := 0x45174.  Definition tfib_E_vfprintf : Z := 0x45178.
Definition tfib_A_vsnprintf : Z := 0x45178.  Definition tfib_E_vsnprintf : Z := 0x4517c.
Definition tfib_A_vfprintf_2 : Z := 0x4517c.  Definition tfib_E_vfprintf_2 : Z := 0x45180.
Definition tfib_A_thunk_417bc : Z := 0x45184.  Definition tfib_E_thunk_417bc : Z := 0x45188.
Definition tfib_A_clock_gettime : Z := 0x45188.  Definition tfib_E_clock_gettime : Z := 0x4518c.
Definition tfib_A_wcrtomb : Z := 0x4518c.  Definition tfib_E_wcrtomb : Z := 0x45190.
Definition tfib_A_wctomb : Z := 0x45190.  Definition tfib_E_wctomb : Z := 0x45194.
Definition tfib_A_thunk_417cc : Z := 0x45194.  Definition tfib_E_thunk_417cc : Z := 0x4519c.
Definition tfib_A_pthread_attr_getstack : Z := 0x4519c.  Definition tfib_E_pthread_attr_getstack : Z := 0x451a0.
Definition tfib_A_tls_get_addr_thunk : Z := 0x451a0.  Definition tfib_E_tls_get_addr_thunk : Z := 0x451a4.
Definition tfib_A_thunk_417dc : Z := 0x451a4.  Definition tfib_E_thunk_417dc : Z := 0x451a8.
Definition tfib_A_thunk_417e4 : Z := 0x451a8.  Definition tfib_E_thunk_417e4 : Z := 0x451ac.
Definition tfib_A_thunk_417e8 : Z := 0x451ac.  Definition tfib_E_thunk_417e8 : Z := 0x451b0.
Definition tfib_A_thunk_417ec : Z := 0x451b0.  Definition tfib_E_thunk_417ec : Z := 0x451b4.
Definition tfib_A_thunk_417f0 : Z := 0x451b4.  Definition tfib_E_thunk_417f0 : Z := 0x451b8.
Definition tfib_A_sem_timedwait : Z := 0x451b8.  Definition tfib_E_sem_timedwait : Z := 0x451bc.
Definition tfib_A_thunk_417f8 : Z := 0x451bc.  Definition tfib_E_thunk_417f8 : Z := 0x451c0.
Definition tfib_A_pthread_setcancelstate : Z := 0x451c0.  Definition tfib_E_pthread_setcancelstate : Z := 0x451c4.
Definition tfib_A_send : Z := 0x451c4.  Definition tfib_E_send : Z := 0x451c8.
Definition tfib_A_sendto : Z := 0x451c8.  Definition tfib_E_sendto : Z := 0x451cc.
Definition tfib_A_sigaltstack : Z := 0x451cc.  Definition tfib_E_sigaltstack : Z := 0x451d0.
Definition tfib_A_thunk_4180c : Z := 0x451d0.  Definition tfib_E_thunk_4180c : Z := 0x451d4.
Definition tfib_A_icpt_strlen : Z := 0x451e8.  Definition tfib_E_icpt_strlen : Z := 0x4547c.
Definition tfib_A_icpt_strnlen : Z := 0x4547c.  Definition tfib_E_icpt_strnlen : Z := 0x45710.
Definition tfib_A_icpt_strcmp : Z := 0x45a24.  Definition tfib_E_icpt_strcmp : Z := 0x45f54.
Definition tfib_A_icpt_strchr : Z := 0x46530.  Definition tfib_E_icpt_strchr : Z := 0x46810.
Definition tfib_A_icpt_memcmp : Z := 0x479b8.  Definition tfib_E_icpt_memcmp : Z := 0x47a74.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x47a74.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x47b30.
Definition tfib_A_icpt_memchr : Z := 0x47b30.  Definition tfib_E_icpt_memchr : Z := 0x47e00.
Definition tfib_A_icpt_frexpl : Z := 0x47e00.  Definition tfib_E_icpt_frexpl : Z := 0x48078.
Definition tfib_A_icpt_read : Z := 0x48078.  Definition tfib_E_icpt_read : Z := 0x482e8.
Definition tfib_A_icpt_fwrite : Z := 0x482e8.  Definition tfib_E_icpt_fwrite : Z := 0x4855c.
Definition tfib_A_icpt_time : Z := 0x4855c.  Definition tfib_E_icpt_time : Z := 0x487f8.
Definition tfib_A_icpt_gmtime_r : Z := 0x48a00.  Definition tfib_E_icpt_gmtime_r : Z := 0x48c40.
Definition tfib_A_icpt_vprintf : Z := 0x48c40.  Definition tfib_E_icpt_vprintf : Z := 0x48cdc.
Definition tfib_A_printf_common_format_interceptor : Z := 0x48cdc.  Definition tfib_E_printf_common_format_interceptor : Z := 0x497a4.
Definition tfib_A_icpt_vfprintf : Z := 0x497a4.  Definition tfib_E_icpt_vfprintf : Z := 0x49858.
Definition tfib_A_icpt_vsnprintf : Z := 0x49858.  Definition tfib_E_icpt_vsnprintf : Z := 0x49b70.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x49e50.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x49f28.
Definition tfib_A_icpt_clock_gettime : Z := 0x4a05c.  Definition tfib_E_icpt_clock_gettime : Z := 0x4a2b4.
Definition tfib_A_icpt_wcrtomb : Z := 0x4a2b4.  Definition tfib_E_icpt_wcrtomb : Z := 0x4a824.
Definition tfib_A_icpt_wctomb : Z := 0x4a824.  Definition tfib_E_icpt_wctomb : Z := 0x4ab80.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x4ac4c.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4b034.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4b040.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4b0bc.

Definition tfib_A_icpt_sem_timedwait : Z := 0x4b2c8.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4b560.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4b590.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4b7b8.
Definition tfib_A_icpt_send : Z := 0x4b7b8.  Definition tfib_E_icpt_send : Z := 0x4ba6c.
Definition tfib_A_icpt_sendto : Z := 0x4ba6c.  Definition tfib_E_icpt_sendto : Z := 0x4bd30.
Definition tfib_A_icpt_sigaltstack : Z := 0x4bd30.  Definition tfib_E_icpt_sigaltstack : Z := 0x4bf8c.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4d440.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4d5f0.
Definition tfib_A_icpt_diouxXn : Z := 0x4d5f0.  Definition tfib_E_icpt_diouxXn : Z := 0x4d788.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x4e334.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x5700c.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x5700c.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x57168.
Definition tfib_A_memset : Z := 0x57628.  Definition tfib_E_memset : Z := 0x5762c.
Definition tfib_A_memcpy : Z := 0x5762c.  Definition tfib_E_memcpy : Z := 0x57630.
Definition tfib_A_asan_memcpy : Z := 0x57630.  Definition tfib_E_asan_memcpy : Z := 0x57acc.
Definition tfib_A_asan_memset : Z := 0x57acc.  Definition tfib_E_asan_memset : Z := 0x57d0c.
Definition tfib_A_icpt_memset : Z := 0x57d0c.  Definition tfib_E_icpt_memset : Z := 0x57ffc.
Definition tfib_A_icpt_memcpy : Z := 0x57ffc.  Definition tfib_E_icpt_memcpy : Z := 0x585ec.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x585ec.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x58624.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x58624.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x58628.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x58628.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x5862c.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5862c.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5868c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x586d8.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x58814.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x58814.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x58818.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x58818.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x58980.
Definition tfib_A_free : Z := 0x58980.  Definition tfib_E_free : Z := 0x58984.
Definition tfib_A_malloc : Z := 0x58984.  Definition tfib_E_malloc : Z := 0x58988.
Definition tfib_A_icpt_free : Z := 0x58988.  Definition tfib_E_icpt_free : Z := 0x58b58.
Definition tfib_A_icpt_malloc : Z := 0x58b58.  Definition tfib_E_icpt_malloc : Z := 0x58cb4.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x58cb4.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x58d80.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x58d80.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x58d84.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x58d84.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x58e84.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x591ac.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x59318.
Definition tfib_A_SetCanPoisonMemory : Z := 0x59800.  Definition tfib_E_SetCanPoisonMemory : Z := 0x59810.
Definition tfib_A_CanPoisonMemory : Z := 0x59810.  Definition tfib_E_CanPoisonMemory : Z := 0x59824.
Definition tfib_A_PoisonShadow : Z := 0x59824.  Definition tfib_E_PoisonShadow : Z := 0x59d20.
Definition tfib_A_MemToShadow_checked : Z := 0x59d20.  Definition tfib_E_MemToShadow_checked : Z := 0x59e5c.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x59e5c.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x59ffc.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x59ffc.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x5a17c.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5a1ac.  Definition tfib_E_asan_region_is_poisoned : Z := 0x5a4f0.
Definition tfib_A_AsanTSDInit : Z := 0x5a910.  Definition tfib_E_AsanTSDInit : Z := 0x5a98c.
Definition tfib_A_AsanTSDGet : Z := 0x5a98c.  Definition tfib_E_AsanTSDGet : Z := 0x5a9cc.
Definition tfib_A_AsanTSDSet : Z := 0x5a9cc.  Definition tfib_E_AsanTSDSet : Z := 0x5aa0c.
Definition tfib_A_PlatformTSDDtor : Z := 0x5aa0c.  Definition tfib_E_PlatformTSDDtor : Z := 0x5aa90.
Definition tfib_A_InstallAtForkHandler : Z := 0x5aa90.  Definition tfib_E_InstallAtForkHandler : Z := 0x5aaac.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x5ab0c.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5ab50.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x5b268.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x5b474.
Definition tfib_A_ReportDoubleFree : Z := 0x5bb7c.  Definition tfib_E_ReportDoubleFree : Z := 0x5be0c.
Definition tfib_A_ReportGenericError : Z := 0x5d6e8.  Definition tfib_E_ReportGenericError : Z := 0x5dfa4.
Definition tfib_A_AsanInited : Z := 0x5e730.  Definition tfib_E_AsanInited : Z := 0x5e748.
Definition tfib_A_asan_report_load1 : Z := 0x5e748.  Definition tfib_E_asan_report_load1 : Z := 0x5e798.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5e798.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5e7e8.
Definition tfib_A_asan_report_load2 : Z := 0x5e7e8.  Definition tfib_E_asan_report_load2 : Z := 0x5e838.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5e838.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5e888.
Definition tfib_A_asan_report_load4 : Z := 0x5e888.  Definition tfib_E_asan_report_load4 : Z := 0x5e8d8.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5e8d8.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5e928.
Definition tfib_A_asan_report_load8 : Z := 0x5e928.  Definition tfib_E_asan_report_load8 : Z := 0x5e978.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5e978.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5e9c8.
Definition tfib_A_asan_report_load16 : Z := 0x5e9c8.  Definition tfib_E_asan_report_load16 : Z := 0x5ea18.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5ea18.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5ea68.
Definition tfib_A_asan_report_store1 : Z := 0x5ea68.  Definition tfib_E_asan_report_store1 : Z := 0x5eab8.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5eab8.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5eb08.
Definition tfib_A_asan_report_store2 : Z := 0x5eb08.  Definition tfib_E_asan_report_store2 : Z := 0x5eb58.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5eb58.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5eba8.
Definition tfib_A_asan_report_store4 : Z := 0x5eba8.  Definition tfib_E_asan_report_store4 : Z := 0x5ebf8.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5ebf8.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5ec48.
Definition tfib_A_asan_report_store8 : Z := 0x5ec48.  Definition tfib_E_asan_report_store8 : Z := 0x5ec98.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5ec98.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5ece8.
Definition tfib_A_asan_report_store16 : Z := 0x5ece8.  Definition tfib_E_asan_report_store16 : Z := 0x5ed38.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5ed38.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5ed88.
Definition tfib_A_asan_report_load_n : Z := 0x5ed88.  Definition tfib_E_asan_report_load_n : Z := 0x5edd8.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5edd8.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5ee28.
Definition tfib_A_asan_report_store_n : Z := 0x5ee28.  Definition tfib_E_asan_report_store_n : Z := 0x5ee78.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5ee78.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5eec8.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5eec8.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5ef48.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5ef48.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5f2fc.
Definition tfib_A_AsanInitInternal : Z := 0x5f38c.  Definition tfib_E_AsanInitInternal : Z := 0x5f640.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5f640.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5f6e0.
Definition tfib_A_thunk_59674 : Z := 0x5f8a8.  Definition tfib_E_thunk_59674 : Z := 0x5f8ac.
Definition tfib_A_asan_init : Z := 0x5f8ac.  Definition tfib_E_asan_init : Z := 0x5f940.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5f940.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5f944.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5f944.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5f9a8.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5fb1c.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5fb24.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5fba8.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5fed0.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5fed0.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x600b0.
Definition tfib_A_InitializeShadowMemory : Z := 0x600b0.  Definition tfib_E_InitializeShadowMemory : Z := 0x603b8.
Definition tfib_A_SetMallocContextSize : Z := 0x603b8.  Definition tfib_E_SetMallocContextSize : Z := 0x603c8.
Definition tfib_A_GetMallocContextSize : Z := 0x603c8.  Definition tfib_E_GetMallocContextSize : Z := 0x603d8.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x603d8.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x60528.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x60908.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x60ba8.
Definition tfib_A_GetCurrentThreadStats : Z := 0x6100c.  Definition tfib_E_GetCurrentThreadStats : Z := 0x61044.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x612ec.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x612f8.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x612f8.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x61384.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x61384.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x613ec.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x613ec.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x61464.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x61464.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x614cc.
Definition tfib_A_IsAddrSuppressed : Z := 0x614cc.  Definition tfib_E_IsAddrSuppressed : Z := 0x61618.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x618a4.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x618b0.
Definition tfib_A_AsanThread_Create : Z := 0x61a30.  Definition tfib_E_AsanThread_Create : Z := 0x61bcc.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x61c28.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x61e40.
Definition tfib_A_GetCurrentThread : Z := 0x61e40.  Definition tfib_E_GetCurrentThread : Z := 0x61e60.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x61e60.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x62004.
Definition tfib_A_AsanThread_stack_top : Z := 0x62004.  Definition tfib_E_AsanThread_stack_top : Z := 0x6205c.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x6205c.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x620b4.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x620b4.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x622e4.
Definition tfib_A_AsanThread_Init : Z := 0x622e4.  Definition tfib_E_AsanThread_Init : Z := 0x626d8.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x626d8.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x627e4.
Definition tfib_A_CreateMainThread : Z := 0x62818.  Definition tfib_E_CreateMainThread : Z := 0x62928.
Definition tfib_A_SetCurrentThread : Z := 0x62928.  Definition tfib_E_SetCurrentThread : Z := 0x62a08.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x62c0c.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x62d48.
Definition tfib_A_weak_default_hook_ret : Z := 0x63a1c.  Definition tfib_E_weak_default_hook_ret : Z := 0x63a20.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x63a28.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x63c68.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x63ebc.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x64014.
Definition tfib_A_internal_allocator_getter : Z := 0x64200.  Definition tfib_E_internal_allocator_getter : Z := 0x6420c.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x6420c.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x64358.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x64358.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x643a4.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x643a4.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x643b0.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x643e0.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x643ec.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x643ec.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x643f8.
Definition tfib_A_IsRssLimitExceeded : Z := 0x643f8.  Definition tfib_E_IsRssLimitExceeded : Z := 0x64408.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x64414.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x646e0.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x646e0.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x64aa0.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x659fc.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x65a08.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x65a08.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x65ae0.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x65ae0.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x65b7c.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x660a0.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x660e4.
Definition tfib_A_DecreaseTotalMmap : Z := 0x660e4.  Definition tfib_E_DecreaseTotalMmap : Z := 0x66108.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x6635c.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x66470.
Definition tfib_A_RunMallocHooks : Z := 0x66614.  Definition tfib_E_RunMallocHooks : Z := 0x666cc.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x666cc.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x666d0.
Definition tfib_A_RunFreeHooks : Z := 0x666d0.  Definition tfib_E_RunFreeHooks : Z := 0x6677c.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x6677c.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x66784.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x66784.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x66788.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x667b0.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x667fc.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x66ac0.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x66d00.
Definition tfib_A_sanitizer_set_report_path : Z := 0x672fc.  Definition tfib_E_sanitizer_set_report_path : Z := 0x67314.

Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x67458.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x67460.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x677a8.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x68a4c.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x68a4c.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x68a70.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x68f24.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x69234.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x69234.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x69378.
Definition tfib_A_FlagParser_ParseString : Z := 0x69378.  Definition tfib_E_FlagParser_ParseString : Z := 0x6946c.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x69600.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x69660.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x69660.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x696a0.
Definition tfib_A_internal_atoll : Z := 0x696a0.  Definition tfib_E_internal_atoll : Z := 0x6978c.
Definition tfib_A_internal_simple_strtoll : Z := 0x6978c.  Definition tfib_E_internal_simple_strtoll : Z := 0x698e8.
Definition tfib_A_internal_memchr : Z := 0x698e8.  Definition tfib_E_internal_memchr : Z := 0x69908.
Definition tfib_A_internal_memcmp : Z := 0x69908.  Definition tfib_E_internal_memcmp : Z := 0x69940.
Definition tfib_A_internal_memcpy : Z := 0x69940.  Definition tfib_E_internal_memcpy : Z := 0x69964.
Definition tfib_A_internal_memmove : Z := 0x69964.  Definition tfib_E_internal_memmove : Z := 0x699bc.
Definition tfib_A_internal_memset : Z := 0x699bc.  Definition tfib_E_internal_memset : Z := 0x69a1c.
Definition tfib_A_internal_strcspn : Z := 0x69a1c.  Definition tfib_E_internal_strcspn : Z := 0x69a70.
Definition tfib_A_internal_strchr : Z := 0x69a70.  Definition tfib_E_internal_strchr : Z := 0x69aa4.
Definition tfib_A_internal_strdup : Z := 0x69aa4.  Definition tfib_E_internal_strdup : Z := 0x69b10.
Definition tfib_A_internal_strlen : Z := 0x69b10.  Definition tfib_E_internal_strlen : Z := 0x69b2c.
Definition tfib_A_internal_strcmp : Z := 0x69b2c.  Definition tfib_E_internal_strcmp : Z := 0x69b70.
Definition tfib_A_internal_strncmp : Z := 0x69b70.  Definition tfib_E_internal_strncmp : Z := 0x69bbc.
Definition tfib_A_internal_strchrnul : Z := 0x69bbc.  Definition tfib_E_internal_strchrnul : Z := 0x69c04.
Definition tfib_A_internal_strrchr : Z := 0x69c04.  Definition tfib_E_internal_strrchr : Z := 0x69c44.
Definition tfib_A_internal_strnlen : Z := 0x69d74.  Definition tfib_E_internal_strnlen : Z := 0x69da4.
Definition tfib_A_internal_strncpy : Z := 0x69de8.  Definition tfib_E_internal_strncpy : Z := 0x69e58.
Definition tfib_A_internal_strstr : Z := 0x69e58.  Definition tfib_E_internal_strstr : Z := 0x69eec.
Definition tfib_A_mem_is_zero : Z := 0x69eec.  Definition tfib_E_mem_is_zero : Z := 0x69fa0.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x69fa0.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x69fb0.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x69fb0.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6a190.
Definition tfib_A_internal_iserror : Z := 0x6a19c.  Definition tfib_E_internal_iserror : Z := 0x6a1bc.
Definition tfib_A_internal_mmap : Z := 0x6a1bc.  Definition tfib_E_internal_mmap : Z := 0x6a1c8.
Definition tfib_A_internal_munmap : Z := 0x6a1c8.  Definition tfib_E_internal_munmap : Z := 0x6a1d4.
Definition tfib_A_internal_mprotect : Z := 0x6a1d4.  Definition tfib_E_internal_mprotect : Z := 0x6a1e4.
Definition tfib_A_internal_madvise : Z := 0x6a1e4.  Definition tfib_E_internal_madvise : Z := 0x6a210.
Definition tfib_A_internal_close : Z := 0x6a210.  Definition tfib_E_internal_close : Z := 0x6a21c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x6a21c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x6a240.
Definition tfib_A_internal_read : Z := 0x6a240.  Definition tfib_E_internal_read : Z := 0x6a278.
Definition tfib_A_internal_write : Z := 0x6a278.  Definition tfib_E_internal_write : Z := 0x6a2b0.
Definition tfib_A_internal_ftruncate : Z := 0x6a2b0.  Definition tfib_E_internal_ftruncate : Z := 0x6a2e8.
Definition tfib_A_internal_dup : Z := 0x6a2e8.  Definition tfib_E_internal_dup : Z := 0x6a2f4.
Definition tfib_A_internal_dup2_dup3 : Z := 0x6a2f4.  Definition tfib_E_internal_dup2_dup3 : Z := 0x6a304.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x6a304.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x6a31c.
Definition tfib_A_internal_sched_yield : Z := 0x6a31c.  Definition tfib_E_internal_sched_yield : Z := 0x6a328.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x6a328.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x6a374.
Definition tfib_A_internal_execve : Z := 0x6a374.  Definition tfib_E_internal_execve : Z := 0x6a380.
Definition tfib_A_internal_exit_exit_group : Z := 0x6a380.  Definition tfib_E_internal_exit_exit_group : Z := 0x6a394.
Definition tfib_A_FileExists_newfstatat : Z := 0x6a394.  Definition tfib_E_FileExists_newfstatat : Z := 0x6a414.
Definition tfib_A_DirExists_newfstatat : Z := 0x6a414.  Definition tfib_E_DirExists_newfstatat : Z := 0x6a478.
Definition tfib_A_GetTid_gettid : Z := 0x6a478.  Definition tfib_E_GetTid_gettid : Z := 0x6a484.
Definition tfib_A_GetEnv : Z := 0x6a484.  Definition tfib_E_GetEnv : Z := 0x6a5b4.
Definition tfib_A_FutexWait : Z := 0x6a6b8.  Definition tfib_E_FutexWait : Z := 0x6a6dc.
Definition tfib_A_FutexWake : Z := 0x6a6dc.  Definition tfib_E_FutexWake : Z := 0x6a700.
Definition tfib_A_internal_ptrace : Z := 0x6a700.  Definition tfib_E_internal_ptrace : Z := 0x6a70c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6a70c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6a71c.
Definition tfib_A_internal_getpid : Z := 0x6a71c.  Definition tfib_E_internal_getpid : Z := 0x6a728.
Definition tfib_A_internal_getppid : Z := 0x6a728.  Definition tfib_E_internal_getppid : Z := 0x6a734.
Definition tfib_A_internal_prctl : Z := 0x6a734.  Definition tfib_E_internal_prctl : Z := 0x6a740.
Definition tfib_A_internal_sigaltstack : Z := 0x6a740.  Definition tfib_E_internal_sigaltstack : Z := 0x6a74c.
Definition tfib_A_internal_fork_clone : Z := 0x6a74c.  Definition tfib_E_internal_fork_clone : Z := 0x6a764.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6a764.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x6a890.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6aa68.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6ae64.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6afd0.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6b0e8.
Definition tfib_A_GetPageSizeCached : Z := 0x6b0e8.  Definition tfib_E_GetPageSizeCached : Z := 0x6b0f0.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6b0f0.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6b19c.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x6b19c.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x6b2bc.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x6b384.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x6b404.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x6b404.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x6b460.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6b460.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6b52c.
Definition tfib_A_thunk_653ec : Z := 0x6b628.  Definition tfib_E_thunk_653ec : Z := 0x6b62c.
Definition tfib_A_CheckASLR : Z := 0x6b62c.  Definition tfib_E_CheckASLR : Z := 0x6b630.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x6b87c.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6b880.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x6b880.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x6b88c.
Definition tfib_A_MmapOrDie : Z := 0x6b88c.  Definition tfib_E_MmapOrDie : Z := 0x6b998.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6b998.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6ba0c.
Definition tfib_A_UnmapOrDie : Z := 0x6ba0c.  Definition tfib_E_UnmapOrDie : Z := 0x6ba88.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6ba88.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6bb98.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6bdc4.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6bec8.
Definition tfib_A_MmapFixedOrDie : Z := 0x6bec8.  Definition tfib_E_MmapFixedOrDie : Z := 0x6bed4.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6bed4.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6c04c.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6c04c.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6c058.
Definition tfib_A_thunk_66008 : Z := 0x6c244.  Definition tfib_E_thunk_66008 : Z := 0x6c248.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6c568.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6c774.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x6cd2c.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6cd38.
Definition tfib_A_Printf : Z := 0x6cd3c.  Definition tfib_E_Printf : Z := 0x6cd88.
Definition tfib_A_SharedPrintfCode : Z := 0x6cd88.  Definition tfib_E_SharedPrintfCode : Z := 0x6cde4.
Definition tfib_A_Report : Z := 0x6cde4.  Definition tfib_E_Report : Z := 0x6ce30.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6e928.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6e984.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6e984.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6ebc0.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6ebc0.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6eee4.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6f484.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6f554.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6f554.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6f8a4.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6f8a4.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6f8b4.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6faf0.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6fb34.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6fb34.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6fb94.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6fb94.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x7000c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x708cc.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x70bf0.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x70bf8.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x70cfc.
Definition tfib_A_AddDieCallback : Z := 0x714ac.  Definition tfib_E_AddDieCallback : Z := 0x71534.
Definition tfib_A_Die : Z := 0x715f8.  Definition tfib_E_Die : Z := 0x716b8.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x716b8.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x716c4.
Definition tfib_A_CheckFailed : Z := 0x716c4.  Definition tfib_E_CheckFailed : Z := 0x7177c.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x71dd4.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x71ecc.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x71ecc.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x71ff8.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x72220.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x7229c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x722d0.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x725b8.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x725b8.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x725bc.
Definition tfib_A_GetTls : Z := 0x725bc.  Definition tfib_E_GetTls : Z := 0x729ac.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x729ac.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x72a7c.
Definition tfib_A_AndroidLogInit : Z := 0x72e60.  Definition tfib_E_AndroidLogInit : Z := 0x72e64.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x72e94.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x72edc.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x72edc.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x73128.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x73128.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x7312c.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x7312c.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x73238.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x73238.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x7333c.
Definition tfib_A_thunk_6d37c : Z := 0x735b8.  Definition tfib_E_thunk_6d37c : Z := 0x735bc.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x73660.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x73680.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x73680.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x73720.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x7376c.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x73770.
Definition tfib_A_SetAlternateSignalStack : Z := 0x737ac.  Definition tfib_E_SetAlternateSignalStack : Z := 0x73870.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x73870.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x738f8.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x738f8.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x73970.
Definition tfib_A_MaybeInstallSigaction : Z := 0x73970.  Definition tfib_E_MaybeInstallSigaction : Z := 0x73a54.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x73b10.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x73c44.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x73e7c.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x73fac.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x73fac.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x7400c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x7400c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x740d8.
Definition tfib_A_MmapNoAccess : Z := 0x740ec.  Definition tfib_E_MmapNoAccess : Z := 0x7410c.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x7410c.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x74258.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x74258.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x74268.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x75a60.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x75aa4.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x75aa4.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x75ad4.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x75f08.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x7602c.
Definition tfib_A_StackStore_Alloc : Z := 0x7602c.  Definition tfib_E_StackStore_Alloc : Z := 0x76160.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x76a14.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x76ac8.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x7821c.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x78278.
Definition tfib_A_StackDepotPut : Z := 0x78504.  Definition tfib_E_StackDepotPut : Z := 0x78524.
Definition tfib_A_StackDepotBase_Put : Z := 0x78524.  Definition tfib_E_StackDepotBase_Put : Z := 0x787a8.
Definition tfib_A_StackDepotBase_Get : Z := 0x787a8.  Definition tfib_E_StackDepotBase_Get : Z := 0x788b8.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x78c98.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x78d28.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x78d28.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x78e28.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x78e88.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x78e90.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x78e90.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x78ff0.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x78ff0.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x79064.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x794ec.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x79604.
Definition tfib_A_thunk_762d8 : Z := 0x7c650.  Definition tfib_E_thunk_762d8 : Z := 0x7c654.
Definition tfib_A_thunk_77ab0 : Z := 0x7de28.  Definition tfib_E_thunk_77ab0 : Z := 0x7de2c.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7f854.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7f910.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7f910.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7f9e8.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7f9e8.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7fc5c.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7ff88.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7ffcc.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ffcc.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x8039c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x8066c.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x80724.
Definition tfib_A_thunk_7b6f8 : Z := 0x81a7c.  Definition tfib_E_thunk_7b6f8 : Z := 0x81a80.
Definition tfib_A_lsan_register_root_region : Z := 0x82688.  Definition tfib_E_lsan_register_root_region : Z := 0x829b8.
Definition tfib_A_lsan_unregister_root_region : Z := 0x829b8.  Definition tfib_E_lsan_unregister_root_region : Z := 0x82e40.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x82e40.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x82e4c.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x85a04.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x85a1c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x85da0.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x85e1c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x85e1c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x85ecc.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x85ecc.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x85ee4.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x85ee4.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8602c.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x8602c.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x86038.
Definition tfib_A_asan_default_options_cli_c : Z := 0x86038.  Definition tfib_E_asan_default_options_cli_c : Z := 0x86044.
Definition tfib_A_main : Z := 0x86044.  Definition tfib_E_main : Z := 0x86308.
Definition tfib_A_target_alloc_init : Z := 0x86308.  Definition tfib_E_target_alloc_init : Z := 0x8630c.
Definition tfib_A_target_alloc_count : Z := 0x8630c.  Definition tfib_E_target_alloc_count : Z := 0x86314.
Definition tfib_A_target_run : Z := 0x86314.  Definition tfib_E_target_run : Z := 0x8649c.
Definition tfib_A_emit_printf : Z := 0x8649c.  Definition tfib_E_emit_printf : Z := 0x864e4.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x864e4.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x86b10.
Definition tfib_A_asan_module_ctor : Z := 0x89108.  Definition tfib_E_asan_module_ctor : Z := 0x89140.




Definition tfib_A_asan_module_dtor : Z := 0x89140.  Definition tfib_E_asan_module_dtor : Z := 0x89170.



Definition tfib_A_extenddftf2 : Z := 0x8e8e8.  Definition tfib_E_extenddftf2 : Z := 0x8ea78.
Definition tfib_A_sysconf : Z := 0x946c8.  Definition tfib_E_sysconf : Z := 0x948f0.
Definition tfib_A_init : Z := 0x948f0.  Definition tfib_E_init : Z := 0x948f4.
Definition tfib_A_init_libc : Z := 0x948f4.  Definition tfib_E_init_libc : Z := 0x94b20.
Definition tfib_A_libc_start_init : Z := 0x94b20.  Definition tfib_E_libc_start_init : Z := 0x94b6c.
Definition tfib_A_libc_start_main : Z := 0x94b6c.  Definition tfib_E_libc_start_main : Z := 0x94bcc.
Definition tfib_A_libc_start_main_stage2 : Z := 0x94bcc.  Definition tfib_E_libc_start_main_stage2 : Z := 0x94c14.
Definition tfib_A_init_tls : Z := 0x94cec.  Definition tfib_E_init_tls : Z := 0x94f9c.
Definition tfib_A_init_ssp : Z := 0x94f9c.  Definition tfib_E_init_ssp : Z := 0x94ffc.
Definition tfib_A_stack_chk_fail : Z := 0x94ffc.  Definition tfib_E_stack_chk_fail : Z := 0x95004.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x9504c.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x950e0.
Definition tfib_A_Exit : Z := 0x950e0.  Definition tfib_E_Exit : Z := 0x950fc.
Definition tfib_A_funcs_on_exit : Z := 0x9512c.  Definition tfib_E_funcs_on_exit : Z := 0x951f4.
Definition tfib_A_fini_stub_ret : Z := 0x951f4.  Definition tfib_E_fini_stub_ret : Z := 0x951f8.
Definition tfib_A_cxa_atexit_atexit : Z := 0x951f8.  Definition tfib_E_cxa_atexit_atexit : Z := 0x952bc.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x952bc.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x952c0.
Definition tfib_A_musl_exit_helper_stub : Z := 0x952c0.  Definition tfib_E_musl_exit_helper_stub : Z := 0x952c4.
Definition tfib_A_libc_exit_fini : Z := 0x952c4.  Definition tfib_E_libc_exit_fini : Z := 0x95310.
Definition tfib_A_exit : Z := 0x95310.  Definition tfib_E_exit : Z := 0x95384.
Definition tfib_A_open : Z := 0x95584.  Definition tfib_E_open : Z := 0x95668.
Definition tfib_A_syscall_ret : Z := 0x95668.  Definition tfib_E_syscall_ret : Z := 0x956a0.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x956a0.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x95848.
Definition tfib_A_calloc : Z := 0x95e0c.  Definition tfib_E_calloc : Z := 0x95f44.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x95f44.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x95f48.
Definition tfib_A_libc_free : Z := 0x95f48.  Definition tfib_E_libc_free : Z := 0x96114.
Definition tfib_A_get_meta : Z := 0x96114.  Definition tfib_E_get_meta : Z := 0x96224.
Definition tfib_A_alloc_meta : Z := 0x965fc.  Definition tfib_E_alloc_meta : Z := 0x968d4.
Definition tfib_A_libc_malloc_impl : Z := 0x968d4.  Definition tfib_E_libc_malloc_impl : Z := 0x96c44.
Definition tfib_A_alloc_slot : Z := 0x96c44.  Definition tfib_E_alloc_slot : Z := 0x974e8.
Definition tfib_A_enframe : Z := 0x974e8.  Definition tfib_E_enframe : Z := 0x97638.
Definition tfib_A_malloc_allzerop : Z := 0x97638.  Definition tfib_E_malloc_allzerop : Z := 0x977b0.
Definition tfib_A_getrlimit : Z := 0x99460.  Definition tfib_E_getrlimit : Z := 0x99558.
Definition tfib_A_getrusage : Z := 0x99558.  Definition tfib_E_getrusage : Z := 0x99580.
Definition tfib_A_setrlimit : Z := 0x99580.  Definition tfib_E_setrlimit : Z := 0x99648.
Definition tfib_A_mmap : Z := 0x99a70.  Definition tfib_E_mmap : Z := 0x99b5c.
Definition tfib_A_mprotect : Z := 0x99b5c.  Definition tfib_E_mprotect : Z := 0x99ba4.
Definition tfib_A_munmap : Z := 0x99c78.  Definition tfib_E_munmap : Z := 0x99cc0.
Definition tfib_A_sched_yield : Z := 0x99f84.  Definition tfib_E_sched_yield : Z := 0x99fa8.
Definition tfib_A_raise_tkill_path : Z := 0x9a004.  Definition tfib_E_raise_tkill_path : Z := 0x9a07c.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x9a07c.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x9a250.
Definition tfib_A_musl_sigaltstack : Z := 0x9a348.  Definition tfib_E_musl_sigaltstack : Z := 0x9a3d4.
Definition tfib_A_fprintf : Z := 0x9a9b0.  Definition tfib_E_fprintf : Z := 0x9aa14.
Definition tfib_A_lockfile : Z := 0x9aa14.  Definition tfib_E_lockfile : Z := 0x9ab10.
Definition tfib_A_unlockfile : Z := 0x9ab10.  Definition tfib_E_unlockfile : Z := 0x9ab70.

Definition tfib_A_stdio_read : Z := 0x9a700.  Definition tfib_E_stdio_read : Z := 0x9a818.
Definition tfib_A_stdio_write : Z := 0x9a820.  Definition tfib_E_stdio_write : Z := 0x9a9b0.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9a6d0.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9a6d4.
Definition tfib_A_stdio_close : Z := 0x9a6d4.  Definition tfib_E_stdio_close : Z := 0x9a700.
Definition tfib_A_fwritex : Z := 0x9afa4.  Definition tfib_E_fwritex : Z := 0x9b0dc.
Definition tfib_A_musl_fwrite : Z := 0x9b0dc.  Definition tfib_E_musl_fwrite : Z := 0x9b194.
Definition tfib_A_towrite : Z := 0x9b194.  Definition tfib_E_towrite : Z := 0x9b1e8.
Definition tfib_A_stdio_exit : Z := 0x9ae00.  Definition tfib_E_stdio_exit : Z := 0x9afa4.
Definition tfib_A_ofl_lock : Z := 0x9b1e8.  Definition tfib_E_ofl_lock : Z := 0x9b218.
Definition tfib_A_musl_vfprintf : Z := 0x9b364.  Definition tfib_E_musl_vfprintf : Z := 0x9b514.
Definition tfib_A_printf_core : Z := 0x9b514.  Definition tfib_E_printf_core : Z := 0x9c344.
Definition tfib_A_pop_arg : Z := 0x9c344.  Definition tfib_E_pop_arg : Z := 0x9c478.
Definition tfib_A_pad : Z := 0x9c478.  Definition tfib_E_pad : Z := 0x9c54c.
Definition tfib_A_fmt_fp : Z := 0x9c54c.  Definition tfib_E_fmt_fp : Z := 0x9dc14.
Definition tfib_A_thunk_931e0 : Z := 0x95a60.  Definition tfib_E_thunk_931e0 : Z := 0x95a64.
Definition tfib_A_musl_wctomb : Z := 0x99dec.  Definition tfib_E_musl_wctomb : Z := 0x99e10.
Definition tfib_A_musl_wcrtomb : Z := 0x99cc0.  Definition tfib_E_musl_wcrtomb : Z := 0x99dec.
Definition tfib_A_fpclassifyl : Z := 0x98050.  Definition tfib_E_fpclassifyl : Z := 0x98094.
Definition tfib_A_letf2 : Z := 0x97888.  Definition tfib_E_letf2 : Z := 0x97950.
Definition tfib_A_multf3 : Z := 0x97950.  Definition tfib_E_multf3 : Z := 0x98050.
Definition tfib_A_floatsitf : Z := 0x988ac.  Definition tfib_E_floatsitf : Z := 0x989b4.
Definition tfib_A_scalbn : Z := 0x992b8.  Definition tfib_E_scalbn : Z := 0x99350.
Definition tfib_A_subtf3 : Z := 0x9889c.  Definition tfib_E_subtf3 : Z := 0x988ac.
Definition tfib_A_addtf3 : Z := 0x98094.  Definition tfib_E_addtf3 : Z := 0x98860.
Definition tfib_A_fe_getround : Z := 0x98860.  Definition tfib_E_fe_getround : Z := 0x98890.
Definition tfib_A_fixunstfsi : Z := 0x9dc1c.  Definition tfib_E_fixunstfsi : Z := 0x9dcb0.
Definition tfib_A_floatunsitf : Z := 0x9dcb0.  Definition tfib_E_floatunsitf : Z := 0x9dd9c.
Definition tfib_A_fixtfsi : Z := 0x99350.  Definition tfib_E_fixtfsi : Z := 0x993f8.
Definition tfib_A_divtf3 : Z := 0x989b4.  Definition tfib_E_divtf3 : Z := 0x992b8.
Definition tfib_A_musl_vprintf : Z := 0x9e474.  Definition tfib_E_musl_vprintf : Z := 0x9e490.
Definition tfib_A_stdout_write : Z := 0x9b224.  Definition tfib_E_stdout_write : Z := 0x9b2c4.
Definition tfib_A_thunk_95368 : Z := 0x9ea3c.  Definition tfib_E_thunk_95368 : Z := 0x9ea40.
Definition tfib_A_musl_memcmp : Z := 0x9eb0c.  Definition tfib_E_musl_memcmp : Z := 0x9eb3c.
Definition tfib_A_musl_memcpy : Z := 0x9eb3c.  Definition tfib_E_musl_memcpy : Z := 0x9ef40.
Definition tfib_A_musl_memset : Z := 0x9ef40.  Definition tfib_E_musl_memset : Z := 0x9f038.
Definition tfib_A_musl_strchr : Z := 0x9f078.  Definition tfib_E_musl_strchr : Z := 0x9f0b4.
Definition tfib_A_strchrnul : Z := 0x9f0b4.  Definition tfib_E_strchrnul : Z := 0x9f194.
Definition tfib_A_musl_strlen : Z := 0x9f3cc.  Definition tfib_E_musl_strlen : Z := 0x9f45c.
Definition tfib_A_musl_strnlen : Z := 0x9f6c8.  Definition tfib_E_musl_strnlen : Z := 0x9f70c.
Definition tfib_A_musl_memchr : Z := 0x9ea40.  Definition tfib_E_musl_memchr : Z := 0x9eb0c.
Definition tfib_A_lock : Z := 0x9f894.  Definition tfib_E_lock : Z := 0x9fb1c.
Definition tfib_A_unlock : Z := 0x9fb1c.  Definition tfib_E_unlock : Z := 0x9fb90.
Definition tfib_A_syscall_cp_c : Z := 0x9fb90.  Definition tfib_E_syscall_cp_c : Z := 0x9fbb4.
Definition tfib_A_syscall_cp_sccp : Z := 0x9fbb4.  Definition tfib_E_syscall_cp_sccp : Z := 0x9fbb8.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9fbb8.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9fbdc.
Definition tfib_A_pthread_atfork : Z := 0x9fbf4.  Definition tfib_E_pthread_atfork : Z := 0x9fc98.
Definition tfib_A_mremap : Z := 0x99ba4.  Definition tfib_E_mremap : Z := 0x99c78.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0xa0c6c.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0xa0c88.
Definition tfib_A_pthread_key_create : Z := 0xa1014.  Definition tfib_E_pthread_key_create : Z := 0xa10e8.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0xa138c.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0xa1430.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0xa1430.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0xa154c.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0xa154c.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0xa1578.
Definition tfib_A_pthread_setspecific : Z := 0xa15b0.  Definition tfib_E_pthread_setspecific : Z := 0xa15e4.
Definition tfib_A_set_thread_area : Z := 0xa15ec.  Definition tfib_E_set_thread_area : Z := 0xa15f8.
Definition tfib_A_thunk_96f9c : Z := 0xa15e4.  Definition tfib_E_thunk_96f9c : Z := 0xa15ec.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa1f18.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa1fd0.
Definition tfib_A_close : Z := 0xa45e8.  Definition tfib_E_close : Z := 0xa463c.
Definition tfib_A_musl_read : Z := 0xa46c8.  Definition tfib_E_musl_read : Z := 0xa46fc.
Definition tfib_A_vm_wait : Z := 0xa1c28.  Definition tfib_E_vm_wait : Z := 0xa1c78.
Definition tfib_D_str_sealed : Z := 0x11860.
Definition tfib_D_init_array_0_3 : Z := 0xa5700.
Definition tfib_D_fini_array_0_1 : Z := 0xa5720.
Definition tfib_D_GOT_common_flags : Z := 0xa63e0.
Definition tfib_D_GOT_flags : Z := 0xa63e8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa63f0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa63f8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa6400.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa6408.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa6f58.
Definition tfib_D_environ_musl : Z := 0xa70a0.
Definition tfib_D_REAL_read : Z := 0xa8168.
Definition tfib_D_REAL_memcpy : Z := 0xa82a8.
Definition tfib_D_REAL_memset : Z := 0xa82b0.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xada58.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xae8b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xb10b8.
Definition tfib_D_asan_inited : Z := 0xb1d98.
Definition tfib_D_replace_intrin_cached : Z := 0xb1d99.
Definition tfib_D_kHighMemEnd : Z := 0xb1da0.
Definition tfib_D_kMidMemBeg : Z := 0xb1da8.
Definition tfib_D_kMidMemEnd : Z := 0xb1db0.
Definition tfib_D_malloc_context_size : Z := 0xb1dbc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x142be8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x604828.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x606000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x33340.
Definition tfib_at_rw_lo : Z := 0xa8000.
Definition tfib_at_rw_len : Z := 0x55e000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x699bc.
Definition tfib_at_x_imemcpy : Z := 0x69940.
Definition tfib_at_x_memset : Z := 0x9ef40.
Definition tfib_at_x_memcpy : Z := 0x9eb3c.
Definition tfib_at_x_memiszero : Z := 0x69eec.
Definition tfib_at_x_istrncpy : Z := 0x69de8.
Definition tfib_at_x_sealed : Z := 0x11860.
Definition tfib_at_x_popfree : Z := 0x3972c.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x9492c.
Definition tfib_at_x_envscan_k : Z := 0x94938.
Definition tfib_at_x_pnscan : Z := 0x949f0.
Definition tfib_at_x_pnscan_k : Z := 0x949fc.
Definition tfib_at_stops_more : list Z := (0x373a0 :: 0x389c4 :: 0x59cc8 :: 0x60080 :: 0x60094 :: 0x600a8 :: 0x65a38 :: 0x65b08 :: 0x73034 :: 0x73f40 :: 0x740d0 :: 0x7de28 :: nil)%list.
