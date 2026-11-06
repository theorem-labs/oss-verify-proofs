(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1w.v and regenerated for libreac/fuzz_disco's ASan+UBSan build: section bounds from its section headers, function pairs bounded by its symbols (the 26 cgif_file functions it does not link are dropped), one fake-stack entry per __asan_stack_malloc_<k> / __asan_stack_free_<k> it links, and the image bounds cited from YImgTop. *)
From OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22fac.
Definition tfib_text_lo : Z := 0x30f24.  Definition tfib_text_hi : Z := 0x9f248.
Definition tfib_init_array_lo : Z := 0xa0248.  Definition tfib_init_array_hi : Z := 0xa0268.
Definition tfib_fini_array_lo : Z := 0xa0268.  Definition tfib_fini_array_hi : Z := 0xa0278.
Definition tfib_preinit_array_lo : Z := 0xa0278.  Definition tfib_preinit_array_hi : Z := 0xa0280.
Definition tfib_data_rel_ro_lo : Z := 0xa0280.  Definition tfib_data_rel_ro_hi : Z := 0xa0850.
Definition tfib_got_lo : Z := 0xa0850.  Definition tfib_got_hi : Z := 0xa15a8.
Definition tfib_data_lo : Z := 0xa25a8.  Definition tfib_data_hi : Z := 0xa5160.
Definition tfib_asan_globals_lo : Z := 0xa5160.  Definition tfib_asan_globals_hi : Z := 0xa5da0.
Definition tfib_bss_lo : Z := 0xa5dc0.  Definition tfib_bss_hi : Z := 0x5fdcf0.
Definition tfib_tbss_lo : Z := 0x9f248.  Definition tfib_tbss_hi : Z := 0x9f25c.
Definition tfib_img_lo : Z := YImgTop.IMG_LO.  Definition tfib_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_entry : Z := 0x30f24.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30f24.  Definition tfib_E_start : Z := 0x30f6c.
Definition tfib_A_do_init : Z := 0x30f6c.  Definition tfib_E_do_init : Z := 0x30fe0.
Definition tfib_A_do_fini : Z := 0x30fe0.  Definition tfib_E_do_fini : Z := 0x31070.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x31070.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x310ac.
Definition tfib_A_InitializeAllocator : Z := 0x3121c.  Definition tfib_E_InitializeAllocator : Z := 0x31234.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x31234.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x313a0.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x318fc.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31a58.
Definition tfib_A_asan_free : Z := 0x31e2c.  Definition tfib_E_asan_free : Z := 0x31e54.
Definition tfib_A_Allocator_Deallocate : Z := 0x31e54.  Definition tfib_E_Allocator_Deallocate : Z := 0x3210c.
Definition tfib_A_asan_malloc : Z := 0x3210c.  Definition tfib_E_asan_malloc : Z := 0x32168.
Definition tfib_A_Allocator_Allocate : Z := 0x32168.  Definition tfib_E_Allocator_Allocate : Z := 0x32af0.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x33228.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x3336c.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x33458.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x334b4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x334b4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33704.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33704.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x337f8.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x337f8.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x338e0.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x33d14.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x33ef8.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x33ef8.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x3407c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x341b4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34438.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34438.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x345b8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x345b8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34780.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34780.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3494c.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x3494c.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x349ec.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x349ec.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34af0.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34e18.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34f60.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34f60.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34f98.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35730.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35a18.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x360f0.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36268.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36268.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36418.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36418.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x365fc.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x365fc.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x368d4.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x368d4.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36d4c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36d4c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36e4c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36e4c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x37154.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x37154.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x374c4.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x374c4.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x375dc.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x378e4.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x379e0.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x379e0.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37ac8.
Definition tfib_A_AsanActivate : Z := 0x37ac8.  Definition tfib_E_AsanActivate : Z := 0x37ba4.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x38080.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x38168.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3cc20.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3ccf8.
Definition tfib_A_FakeStack_Create : Z := 0x3ccf8.  Definition tfib_E_FakeStack_Create : Z := 0x3cde4.
Definition tfib_A_FakeStack_Allocate : Z := 0x3d0a0.  Definition tfib_E_FakeStack_Allocate : Z := 0x3d388.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d4bc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d4ec.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d4ec.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d660.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d660.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d7f0.
Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d7f0.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3d98c.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3d98c.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3db38.
Definition tfib_A_asan_stack_malloc_6 : Z := 0x3db38.  Definition tfib_E_asan_stack_malloc_6 : Z := 0x3dcd4.
Definition tfib_A_asan_stack_free_6 : Z := 0x3dcd4.  Definition tfib_E_asan_stack_free_6 : Z := 0x3dd1c.
Definition tfib_A_FakeStack_SetShadow : Z := 0x3dd1c.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3de58.
Definition tfib_A_asan_InitializeFlags : Z := 0x3de58.  Definition tfib_E_asan_InitializeFlags : Z := 0x3ee84.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f590.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x403ac.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x403ac.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40978.
Definition tfib_A_asan_register_globals : Z := 0x40978.  Definition tfib_E_asan_register_globals : Z := 0x409e4.
Definition tfib_A_asan_unregister_globals : Z := 0x409e4.  Definition tfib_E_asan_unregister_globals : Z := 0x40a4c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x410cc.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x4133c.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x4133c.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x41644.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41db8.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41f08.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x42924.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x42a3c.
Definition tfib_A_strlen : Z := 0x42a3c.  Definition tfib_E_strlen : Z := 0x42a40.
Definition tfib_A_strnlen : Z := 0x42a40.  Definition tfib_E_strnlen : Z := 0x42a44.
Definition tfib_A_strcmp : Z := 0x42a44.  Definition tfib_E_strcmp : Z := 0x42a48.
Definition tfib_A_strchr : Z := 0x42a48.  Definition tfib_E_strchr : Z := 0x42a4c.
Definition tfib_A_memcmp : Z := 0x42a4c.  Definition tfib_E_memcmp : Z := 0x42a50.
Definition tfib_A_memcmp_2 : Z := 0x42a50.  Definition tfib_E_memcmp_2 : Z := 0x42a54.
Definition tfib_A_memchr : Z := 0x42a54.  Definition tfib_E_memchr : Z := 0x42a58.
Definition tfib_A_frexpl : Z := 0x42a58.  Definition tfib_E_frexpl : Z := 0x42a5c.
Definition tfib_A_read : Z := 0x42a5c.  Definition tfib_E_read : Z := 0x42a60.
Definition tfib_A_fwrite : Z := 0x42a60.  Definition tfib_E_fwrite : Z := 0x42a64.
Definition tfib_A_time : Z := 0x42a64.  Definition tfib_E_time : Z := 0x42a68.
Definition tfib_A_gmtime_r : Z := 0x42a68.  Definition tfib_E_gmtime_r : Z := 0x42a6c.
Definition tfib_A_vprintf : Z := 0x42a6c.  Definition tfib_E_vprintf : Z := 0x42a70.
Definition tfib_A_vfprintf : Z := 0x42a70.  Definition tfib_E_vfprintf : Z := 0x42a74.
Definition tfib_A_vsnprintf : Z := 0x42a74.  Definition tfib_E_vsnprintf : Z := 0x42a78.
Definition tfib_A_vfprintf_2 : Z := 0x42a78.  Definition tfib_E_vfprintf_2 : Z := 0x42a7c.
Definition tfib_A_thunk_417bc : Z := 0x42a7c.  Definition tfib_E_thunk_417bc : Z := 0x42a80.
Definition tfib_A_clock_gettime : Z := 0x42a80.  Definition tfib_E_clock_gettime : Z := 0x42a84.
Definition tfib_A_wcrtomb : Z := 0x42a84.  Definition tfib_E_wcrtomb : Z := 0x42a88.
Definition tfib_A_wctomb : Z := 0x42a88.  Definition tfib_E_wctomb : Z := 0x42a8c.
Definition tfib_A_thunk_417cc : Z := 0x42a8c.  Definition tfib_E_thunk_417cc : Z := 0x42a94.
Definition tfib_A_pthread_attr_getstack : Z := 0x42a94.  Definition tfib_E_pthread_attr_getstack : Z := 0x42a98.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42a98.  Definition tfib_E_tls_get_addr_thunk : Z := 0x42a9c.
Definition tfib_A_thunk_417dc : Z := 0x42a9c.  Definition tfib_E_thunk_417dc : Z := 0x42aa0.
Definition tfib_A_thunk_417e4 : Z := 0x42aa0.  Definition tfib_E_thunk_417e4 : Z := 0x42aa4.
Definition tfib_A_thunk_417e8 : Z := 0x42aa4.  Definition tfib_E_thunk_417e8 : Z := 0x42aa8.
Definition tfib_A_thunk_417ec : Z := 0x42aa8.  Definition tfib_E_thunk_417ec : Z := 0x42aac.
Definition tfib_A_thunk_417f0 : Z := 0x42aac.  Definition tfib_E_thunk_417f0 : Z := 0x42ab0.
Definition tfib_A_sem_timedwait : Z := 0x42ab0.  Definition tfib_E_sem_timedwait : Z := 0x42ab4.
Definition tfib_A_thunk_417f8 : Z := 0x42ab4.  Definition tfib_E_thunk_417f8 : Z := 0x42ab8.
Definition tfib_A_pthread_setcancelstate : Z := 0x42ab8.  Definition tfib_E_pthread_setcancelstate : Z := 0x42abc.
Definition tfib_A_send : Z := 0x42abc.  Definition tfib_E_send : Z := 0x42ac0.
Definition tfib_A_sendto : Z := 0x42ac0.  Definition tfib_E_sendto : Z := 0x42ac4.
Definition tfib_A_sigaltstack : Z := 0x42ac4.  Definition tfib_E_sigaltstack : Z := 0x42ac8.
Definition tfib_A_thunk_4180c : Z := 0x42ac8.  Definition tfib_E_thunk_4180c : Z := 0x42acc.
Definition tfib_A_icpt_strlen : Z := 0x42acc.  Definition tfib_E_icpt_strlen : Z := 0x42d60.
Definition tfib_A_icpt_strnlen : Z := 0x42d60.  Definition tfib_E_icpt_strnlen : Z := 0x42ff4.
Definition tfib_A_icpt_strcmp : Z := 0x42ff8.  Definition tfib_E_icpt_strcmp : Z := 0x43528.
Definition tfib_A_icpt_strchr : Z := 0x43528.  Definition tfib_E_icpt_strchr : Z := 0x43808.
Definition tfib_A_icpt_memcmp : Z := 0x440a0.  Definition tfib_E_icpt_memcmp : Z := 0x4415c.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x4415c.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x44218.
Definition tfib_A_icpt_memchr : Z := 0x44218.  Definition tfib_E_icpt_memchr : Z := 0x444e8.
Definition tfib_A_icpt_frexpl : Z := 0x444e8.  Definition tfib_E_icpt_frexpl : Z := 0x44760.
Definition tfib_A_icpt_read : Z := 0x44760.  Definition tfib_E_icpt_read : Z := 0x449d0.
Definition tfib_A_icpt_fwrite : Z := 0x449d0.  Definition tfib_E_icpt_fwrite : Z := 0x44c44.
Definition tfib_A_icpt_time : Z := 0x44c44.  Definition tfib_E_icpt_time : Z := 0x44ee0.
Definition tfib_A_icpt_gmtime_r : Z := 0x450e8.  Definition tfib_E_icpt_gmtime_r : Z := 0x45328.
Definition tfib_A_icpt_vprintf : Z := 0x45328.  Definition tfib_E_icpt_vprintf : Z := 0x453c4.
Definition tfib_A_printf_common_format_interceptor : Z := 0x453c4.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45e8c.
Definition tfib_A_icpt_vfprintf : Z := 0x45e8c.  Definition tfib_E_icpt_vfprintf : Z := 0x45f40.
Definition tfib_A_icpt_vsnprintf : Z := 0x45f40.  Definition tfib_E_icpt_vsnprintf : Z := 0x46258.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x46258.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x46330.
Definition tfib_A_icpt_clock_gettime : Z := 0x463d4.  Definition tfib_E_icpt_clock_gettime : Z := 0x4662c.
Definition tfib_A_icpt_wcrtomb : Z := 0x4662c.  Definition tfib_E_icpt_wcrtomb : Z := 0x46b9c.
Definition tfib_A_icpt_wctomb : Z := 0x46b9c.  Definition tfib_E_icpt_wctomb : Z := 0x46ef8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46fc4.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x473ac.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x473b8.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x47434.
Definition tfib_A_icpt_sem_timedwait : Z := 0x47640.  Definition tfib_E_icpt_sem_timedwait : Z := 0x478d8.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47908.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47b30.
Definition tfib_A_icpt_send : Z := 0x47b30.  Definition tfib_E_icpt_send : Z := 0x47de4.
Definition tfib_A_icpt_sendto : Z := 0x47de4.  Definition tfib_E_icpt_sendto : Z := 0x480a8.
Definition tfib_A_icpt_sigaltstack : Z := 0x480a8.  Definition tfib_E_icpt_sigaltstack : Z := 0x48304.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x483d8.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x48588.
Definition tfib_A_icpt_diouxXn : Z := 0x48588.  Definition tfib_E_icpt_diouxXn : Z := 0x48720.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x492cc.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x51fa4.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51fa4.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x52100.
Definition tfib_A_memset : Z := 0x52100.  Definition tfib_E_memset : Z := 0x52104.
Definition tfib_A_memcpy : Z := 0x52104.  Definition tfib_E_memcpy : Z := 0x52108.
Definition tfib_A_asan_memcpy : Z := 0x52108.  Definition tfib_E_asan_memcpy : Z := 0x525a4.
Definition tfib_A_asan_memset : Z := 0x525a4.  Definition tfib_E_asan_memset : Z := 0x527e4.
Definition tfib_A_icpt_memset : Z := 0x527e4.  Definition tfib_E_icpt_memset : Z := 0x52ad4.
Definition tfib_A_icpt_memcpy : Z := 0x52ad4.  Definition tfib_E_icpt_memcpy : Z := 0x530c4.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x530c4.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x530fc.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x530fc.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x53100.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x53100.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x53104.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x53104.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x53164.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x531b0.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x532ec.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x532ec.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x532f0.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x532f0.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x53458.
Definition tfib_A_free : Z := 0x53458.  Definition tfib_E_free : Z := 0x5345c.
Definition tfib_A_malloc : Z := 0x5345c.  Definition tfib_E_malloc : Z := 0x53460.
Definition tfib_A_icpt_free : Z := 0x53460.  Definition tfib_E_icpt_free : Z := 0x53630.
Definition tfib_A_icpt_malloc : Z := 0x53630.  Definition tfib_E_icpt_malloc : Z := 0x5378c.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x5378c.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x53858.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53858.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x5385c.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x5385c.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x5395c.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x53c84.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x53df0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x542d8.  Definition tfib_E_SetCanPoisonMemory : Z := 0x542e8.
Definition tfib_A_CanPoisonMemory : Z := 0x542e8.  Definition tfib_E_CanPoisonMemory : Z := 0x542fc.
Definition tfib_A_PoisonShadow : Z := 0x542fc.  Definition tfib_E_PoisonShadow : Z := 0x547f8.
Definition tfib_A_MemToShadow_checked : Z := 0x547f8.  Definition tfib_E_MemToShadow_checked : Z := 0x54934.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x54934.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x54ad4.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x54ad4.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x54c54.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54c84.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54fc8.
Definition tfib_A_AsanTSDInit : Z := 0x553e8.  Definition tfib_E_AsanTSDInit : Z := 0x55464.
Definition tfib_A_AsanTSDGet : Z := 0x55464.  Definition tfib_E_AsanTSDGet : Z := 0x554a4.
Definition tfib_A_AsanTSDSet : Z := 0x554a4.  Definition tfib_E_AsanTSDSet : Z := 0x554e4.
Definition tfib_A_PlatformTSDDtor : Z := 0x554e4.  Definition tfib_E_PlatformTSDDtor : Z := 0x55568.
Definition tfib_A_InstallAtForkHandler : Z := 0x55568.  Definition tfib_E_InstallAtForkHandler : Z := 0x55584.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x555e4.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x55628.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x55d40.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x55f4c.
Definition tfib_A_ReportDoubleFree : Z := 0x56654.  Definition tfib_E_ReportDoubleFree : Z := 0x568e4.
Definition tfib_A_ReportGenericError : Z := 0x581c0.  Definition tfib_E_ReportGenericError : Z := 0x58a7c.
Definition tfib_A_AsanInited : Z := 0x59208.  Definition tfib_E_AsanInited : Z := 0x59220.
Definition tfib_A_asan_report_load1 : Z := 0x59220.  Definition tfib_E_asan_report_load1 : Z := 0x59270.
Definition tfib_A_asan_report_exp_load1 : Z := 0x59270.  Definition tfib_E_asan_report_exp_load1 : Z := 0x592c0.
Definition tfib_A_asan_report_load2 : Z := 0x592c0.  Definition tfib_E_asan_report_load2 : Z := 0x59310.
Definition tfib_A_asan_report_exp_load2 : Z := 0x59310.  Definition tfib_E_asan_report_exp_load2 : Z := 0x59360.
Definition tfib_A_asan_report_load4 : Z := 0x59360.  Definition tfib_E_asan_report_load4 : Z := 0x593b0.
Definition tfib_A_asan_report_exp_load4 : Z := 0x593b0.  Definition tfib_E_asan_report_exp_load4 : Z := 0x59400.
Definition tfib_A_asan_report_load8 : Z := 0x59400.  Definition tfib_E_asan_report_load8 : Z := 0x59450.
Definition tfib_A_asan_report_exp_load8 : Z := 0x59450.  Definition tfib_E_asan_report_exp_load8 : Z := 0x594a0.
Definition tfib_A_asan_report_load16 : Z := 0x594a0.  Definition tfib_E_asan_report_load16 : Z := 0x594f0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x594f0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x59540.
Definition tfib_A_asan_report_store1 : Z := 0x59540.  Definition tfib_E_asan_report_store1 : Z := 0x59590.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59590.  Definition tfib_E_asan_report_exp_store1 : Z := 0x595e0.
Definition tfib_A_asan_report_store2 : Z := 0x595e0.  Definition tfib_E_asan_report_store2 : Z := 0x59630.
Definition tfib_A_asan_report_exp_store2 : Z := 0x59630.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59680.
Definition tfib_A_asan_report_store4 : Z := 0x59680.  Definition tfib_E_asan_report_store4 : Z := 0x596d0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x596d0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x59720.
Definition tfib_A_asan_report_store8 : Z := 0x59720.  Definition tfib_E_asan_report_store8 : Z := 0x59770.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59770.  Definition tfib_E_asan_report_exp_store8 : Z := 0x597c0.
Definition tfib_A_asan_report_store16 : Z := 0x597c0.  Definition tfib_E_asan_report_store16 : Z := 0x59810.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59810.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59860.
Definition tfib_A_asan_report_load_n : Z := 0x59860.  Definition tfib_E_asan_report_load_n : Z := 0x598b0.
Definition tfib_A_asan_report_exp_load_n : Z := 0x598b0.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59900.
Definition tfib_A_asan_report_store_n : Z := 0x59900.  Definition tfib_E_asan_report_store_n : Z := 0x59950.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59950.  Definition tfib_E_asan_report_exp_store_n : Z := 0x599a0.
Definition tfib_A_InitializeHighMemEnd : Z := 0x599a0.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59a20.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59a20.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59dd4.
Definition tfib_A_AsanInitInternal : Z := 0x59e64.  Definition tfib_E_AsanInitInternal : Z := 0x5a118.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a118.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a1b8.
Definition tfib_A_thunk_59674 : Z := 0x5a380.  Definition tfib_E_thunk_59674 : Z := 0x5a384.
Definition tfib_A_asan_init : Z := 0x5a384.  Definition tfib_E_asan_init : Z := 0x5a418.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a418.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a41c.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a41c.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a480.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5a5f4.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5a5fc.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a680.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a9a8.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a9a8.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5ab88.
Definition tfib_A_InitializeShadowMemory : Z := 0x5ab88.  Definition tfib_E_InitializeShadowMemory : Z := 0x5ae90.
Definition tfib_A_SetMallocContextSize : Z := 0x5ae90.  Definition tfib_E_SetMallocContextSize : Z := 0x5aea0.
Definition tfib_A_GetMallocContextSize : Z := 0x5aea0.  Definition tfib_E_GetMallocContextSize : Z := 0x5aeb0.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5aeb0.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b000.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5b3e0.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5b680.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5bae4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5bb1c.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5bdc4.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5bdd0.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5bdd0.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5be5c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5be5c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5bec4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5bec4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5bf3c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5bf3c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5bfa4.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5bfa4.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5c0f0.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5c37c.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5c388.
Definition tfib_A_AsanThread_Create : Z := 0x5c508.  Definition tfib_E_AsanThread_Create : Z := 0x5c6a4.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c700.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c918.
Definition tfib_A_GetCurrentThread : Z := 0x5c918.  Definition tfib_E_GetCurrentThread : Z := 0x5c938.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c938.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5cadc.
Definition tfib_A_AsanThread_stack_top : Z := 0x5cadc.  Definition tfib_E_AsanThread_stack_top : Z := 0x5cb34.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5cb34.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5cb8c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5cb8c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5cdbc.
Definition tfib_A_AsanThread_Init : Z := 0x5cdbc.  Definition tfib_E_AsanThread_Init : Z := 0x5d1b0.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d1b0.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d2bc.
Definition tfib_A_CreateMainThread : Z := 0x5d2f0.  Definition tfib_E_CreateMainThread : Z := 0x5d400.
Definition tfib_A_SetCurrentThread : Z := 0x5d400.  Definition tfib_E_SetCurrentThread : Z := 0x5d4e0.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d6e4.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5d820.
Definition tfib_A_weak_default_hook_ret : Z := 0x5e4f4.  Definition tfib_E_weak_default_hook_ret : Z := 0x5e4f8.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5e500.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5e740.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e994.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5eaec.
Definition tfib_A_internal_allocator_getter : Z := 0x5ecd8.  Definition tfib_E_internal_allocator_getter : Z := 0x5ece4.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ece4.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ee30.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ee30.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5ee7c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5ee7c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5ee88.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5eeb8.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5eec4.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5eec4.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5eed0.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5eed0.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5eee0.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5eeec.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f1b8.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f1b8.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f578.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x604d4.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x604e0.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x604e0.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x605b8.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x605b8.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x60654.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60b78.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60bbc.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60bbc.  Definition tfib_E_IncreaseTotalMmap : Z := 0x60be0.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60e34.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60f48.
Definition tfib_A_RunMallocHooks : Z := 0x610ec.  Definition tfib_E_RunMallocHooks : Z := 0x611a4.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x611a4.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x611a8.
Definition tfib_A_RunFreeHooks : Z := 0x611a8.  Definition tfib_E_RunFreeHooks : Z := 0x61254.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x61254.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x6125c.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x6125c.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x61260.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x61288.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x612d4.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61598.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x617d8.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61dd4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61dec.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x61dec.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x61f30.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61f30.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61f38.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x62280.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x63524.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x63524.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x63548.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x639fc.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63d0c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63d0c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63e50.
Definition tfib_A_FlagParser_ParseString : Z := 0x63e50.  Definition tfib_E_FlagParser_ParseString : Z := 0x63f44.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x640d8.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64138.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x64138.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x64178.
Definition tfib_A_internal_atoll : Z := 0x64178.  Definition tfib_E_internal_atoll : Z := 0x64264.
Definition tfib_A_internal_simple_strtoll : Z := 0x64264.  Definition tfib_E_internal_simple_strtoll : Z := 0x643c0.
Definition tfib_A_internal_memchr : Z := 0x643c0.  Definition tfib_E_internal_memchr : Z := 0x643e0.
Definition tfib_A_internal_memcmp : Z := 0x643e0.  Definition tfib_E_internal_memcmp : Z := 0x64418.
Definition tfib_A_internal_memcpy : Z := 0x64418.  Definition tfib_E_internal_memcpy : Z := 0x6443c.
Definition tfib_A_internal_memmove : Z := 0x6443c.  Definition tfib_E_internal_memmove : Z := 0x64494.
Definition tfib_A_internal_memset : Z := 0x64494.  Definition tfib_E_internal_memset : Z := 0x644f4.
Definition tfib_A_internal_strcspn : Z := 0x644f4.  Definition tfib_E_internal_strcspn : Z := 0x64548.
Definition tfib_A_internal_strcmp : Z := 0x64548.  Definition tfib_E_internal_strcmp : Z := 0x6457c.
Definition tfib_A_internal_strdup : Z := 0x6457c.  Definition tfib_E_internal_strdup : Z := 0x645e8.
Definition tfib_A_internal_strlen : Z := 0x645e8.  Definition tfib_E_internal_strlen : Z := 0x64604.
Definition tfib_A_internal_strncmp : Z := 0x64604.  Definition tfib_E_internal_strncmp : Z := 0x64648.
Definition tfib_A_internal_strchr : Z := 0x64648.  Definition tfib_E_internal_strchr : Z := 0x64694.
Definition tfib_A_internal_strchrnul : Z := 0x64694.  Definition tfib_E_internal_strchrnul : Z := 0x646dc.
Definition tfib_A_internal_strrchr : Z := 0x646dc.  Definition tfib_E_internal_strrchr : Z := 0x6471c.
Definition tfib_A_internal_strnlen : Z := 0x6484c.  Definition tfib_E_internal_strnlen : Z := 0x6487c.
Definition tfib_A_internal_strncpy : Z := 0x648c0.  Definition tfib_E_internal_strncpy : Z := 0x64930.
Definition tfib_A_internal_strstr : Z := 0x64930.  Definition tfib_E_internal_strstr : Z := 0x649c4.
Definition tfib_A_mem_is_zero : Z := 0x649c4.  Definition tfib_E_mem_is_zero : Z := 0x64a78.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64a78.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64a88.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64a88.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64c68.
Definition tfib_A_internal_iserror : Z := 0x64c74.  Definition tfib_E_internal_iserror : Z := 0x64c94.
Definition tfib_A_internal_mmap : Z := 0x64c94.  Definition tfib_E_internal_mmap : Z := 0x64ca0.
Definition tfib_A_internal_munmap : Z := 0x64ca0.  Definition tfib_E_internal_munmap : Z := 0x64cac.
Definition tfib_A_internal_mprotect : Z := 0x64cac.  Definition tfib_E_internal_mprotect : Z := 0x64cbc.
Definition tfib_A_internal_madvise : Z := 0x64cbc.  Definition tfib_E_internal_madvise : Z := 0x64ce8.
Definition tfib_A_internal_close : Z := 0x64ce8.  Definition tfib_E_internal_close : Z := 0x64cf4.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64cf4.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64d18.
Definition tfib_A_internal_read : Z := 0x64d18.  Definition tfib_E_internal_read : Z := 0x64d50.
Definition tfib_A_internal_write : Z := 0x64d50.  Definition tfib_E_internal_write : Z := 0x64d88.
Definition tfib_A_internal_ftruncate : Z := 0x64d88.  Definition tfib_E_internal_ftruncate : Z := 0x64dc0.
Definition tfib_A_internal_dup : Z := 0x64dc0.  Definition tfib_E_internal_dup : Z := 0x64dcc.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64dcc.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64ddc.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64ddc.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64df4.
Definition tfib_A_internal_sched_yield : Z := 0x64df4.  Definition tfib_E_internal_sched_yield : Z := 0x64e00.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64e00.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64e4c.
Definition tfib_A_internal_execve : Z := 0x64e4c.  Definition tfib_E_internal_execve : Z := 0x64e58.
Definition tfib_A_internal_exit_exit_group : Z := 0x64e58.  Definition tfib_E_internal_exit_exit_group : Z := 0x64e6c.
Definition tfib_A_FileExists_newfstatat : Z := 0x64e6c.  Definition tfib_E_FileExists_newfstatat : Z := 0x64eec.
Definition tfib_A_DirExists_newfstatat : Z := 0x64eec.  Definition tfib_E_DirExists_newfstatat : Z := 0x64f50.
Definition tfib_A_GetTid_gettid : Z := 0x64f50.  Definition tfib_E_GetTid_gettid : Z := 0x64f5c.
Definition tfib_A_GetEnv : Z := 0x64f5c.  Definition tfib_E_GetEnv : Z := 0x6508c.
Definition tfib_A_FutexWait : Z := 0x65190.  Definition tfib_E_FutexWait : Z := 0x651b4.
Definition tfib_A_FutexWake : Z := 0x651b4.  Definition tfib_E_FutexWake : Z := 0x651d8.
Definition tfib_A_internal_ptrace : Z := 0x651d8.  Definition tfib_E_internal_ptrace : Z := 0x651e4.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x651e4.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x651f4.
Definition tfib_A_internal_getpid : Z := 0x651f4.  Definition tfib_E_internal_getpid : Z := 0x65200.
Definition tfib_A_internal_getppid : Z := 0x65200.  Definition tfib_E_internal_getppid : Z := 0x6520c.
Definition tfib_A_internal_prctl : Z := 0x6520c.  Definition tfib_E_internal_prctl : Z := 0x65218.
Definition tfib_A_internal_sigaltstack : Z := 0x65218.  Definition tfib_E_internal_sigaltstack : Z := 0x65224.
Definition tfib_A_internal_fork_clone : Z := 0x65224.  Definition tfib_E_internal_fork_clone : Z := 0x6523c.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6523c.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x65368.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x65540.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6593c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65aa8.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65bc0.
Definition tfib_A_GetPageSizeCached : Z := 0x65bc0.  Definition tfib_E_GetPageSizeCached : Z := 0x65bc8.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65bc8.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65c74.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65c74.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65d94.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65e5c.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65edc.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x65edc.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x65f38.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65f38.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x66004.
Definition tfib_A_thunk_653ec : Z := 0x66100.  Definition tfib_E_thunk_653ec : Z := 0x66104.
Definition tfib_A_CheckASLR : Z := 0x66104.  Definition tfib_E_CheckASLR : Z := 0x66108.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x66354.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x66358.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x66358.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x66364.
Definition tfib_A_MmapOrDie : Z := 0x66364.  Definition tfib_E_MmapOrDie : Z := 0x66470.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x66470.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x664e4.
Definition tfib_A_UnmapOrDie : Z := 0x664e4.  Definition tfib_E_UnmapOrDie : Z := 0x66560.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x66560.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66670.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6689c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x669a0.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x669a0.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x669ac.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x669ac.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66b24.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66b24.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66b30.
Definition tfib_A_thunk_66008 : Z := 0x66d1c.  Definition tfib_E_thunk_66008 : Z := 0x66d20.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x67040.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6724c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67804.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67810.
Definition tfib_A_Printf : Z := 0x67814.  Definition tfib_E_Printf : Z := 0x67860.
Definition tfib_A_SharedPrintfCode : Z := 0x67860.  Definition tfib_E_SharedPrintfCode : Z := 0x678bc.
Definition tfib_A_Report : Z := 0x678bc.  Definition tfib_E_Report : Z := 0x67908.
Definition tfib_A_SuppressionContext_ctor : Z := 0x69400.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6945c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6945c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x69698.
Definition tfib_A_SuppressionContext_Parse : Z := 0x69698.  Definition tfib_E_SuppressionContext_Parse : Z := 0x699bc.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69f5c.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6a02c.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a02c.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a37c.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6a37c.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6a38c.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6a5c8.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6a60c.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6a60c.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6a66c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a66c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6aae4.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b3a4.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b6c8.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b6d0.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b7d4.
Definition tfib_A_AddDieCallback : Z := 0x6bf84.  Definition tfib_E_AddDieCallback : Z := 0x6c00c.
Definition tfib_A_Die : Z := 0x6c0d0.  Definition tfib_E_Die : Z := 0x6c190.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c190.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c19c.
Definition tfib_A_CheckFailed : Z := 0x6c19c.  Definition tfib_E_CheckFailed : Z := 0x6c254.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c8ac.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c9a4.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c9a4.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6cad0.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6ccf8.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6cd74.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6cda8.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6d090.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6d090.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6d094.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6d094.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6d484.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6d484.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6d554.
Definition tfib_A_AndroidLogInit : Z := 0x6d938.  Definition tfib_E_AndroidLogInit : Z := 0x6d93c.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d96c.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d9b4.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d9b4.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dc00.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6dc00.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6dc04.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6dc04.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6dd10.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dd10.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6de14.
Definition tfib_A_thunk_6d37c : Z := 0x6e090.  Definition tfib_E_thunk_6d37c : Z := 0x6e094.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e138.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e158.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e158.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e1f8.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6e244.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6e248.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e284.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e348.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e348.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e3d0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e3d0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e448.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e448.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e52c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e5e8.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e71c.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e954.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6ea84.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6ea84.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6eae4.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6eae4.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ebb0.
Definition tfib_A_MprotectNoAccess : Z := 0x6ebc4.  Definition tfib_E_MprotectNoAccess : Z := 0x6ebe4.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6ebe4.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6ed30.
Definition tfib_A_MmapFixedOrDie : Z := 0x6ed30.  Definition tfib_E_MmapFixedOrDie : Z := 0x6ed40.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x70538.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x7057c.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x7057c.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x705ac.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x709e0.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70b04.
Definition tfib_A_StackStore_Alloc : Z := 0x70b04.  Definition tfib_E_StackStore_Alloc : Z := 0x70c38.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x714ec.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x715a0.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72cf4.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72d50.
Definition tfib_A_StackDepotPut : Z := 0x72fdc.  Definition tfib_E_StackDepotPut : Z := 0x72ffc.
Definition tfib_A_StackDepotBase_Put : Z := 0x72ffc.  Definition tfib_E_StackDepotBase_Put : Z := 0x73280.
Definition tfib_A_StackDepotBase_Get : Z := 0x73280.  Definition tfib_E_StackDepotBase_Get : Z := 0x73390.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x73770.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x73800.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x73800.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x73900.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73960.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73968.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73968.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73ac8.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73ac8.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73b3c.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73fc4.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x740dc.
Definition tfib_A_thunk_762d8 : Z := 0x77128.  Definition tfib_E_thunk_762d8 : Z := 0x7712c.
Definition tfib_A_thunk_77ab0 : Z := 0x78900.  Definition tfib_E_thunk_77ab0 : Z := 0x78904.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a32c.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a3e8.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a3e8.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a4c0.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7a4c0.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7a734.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7aa60.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7aaa4.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7aaa4.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ae74.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b144.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b1fc.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c554.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c558.
Definition tfib_A_lsan_register_root_region : Z := 0x7d160.  Definition tfib_E_lsan_register_root_region : Z := 0x7d490.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d490.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d918.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7d918.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7d924.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x804dc.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x804f4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80878.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x808f4.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x808f4.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x809a4.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x809a4.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x809bc.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x809bc.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80b04.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80b04.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80b10.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80b10.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80b1c.
Definition tfib_A_main : Z := 0x80b1c.  Definition tfib_E_main : Z := 0x80de0.
Definition tfib_A_target_alloc_init : Z := 0x80de0.  Definition tfib_E_target_alloc_init : Z := 0x80de4.
Definition tfib_A_target_alloc_count : Z := 0x80de4.  Definition tfib_E_target_alloc_count : Z := 0x80dec.
Definition tfib_A_target_run : Z := 0x80dec.  Definition tfib_E_target_run : Z := 0x80f74.
Definition tfib_A_emit_printf : Z := 0x80f74.  Definition tfib_E_emit_printf : Z := 0x80fbc.
Definition tfib_A_asan_module_ctor : Z := 0x84614.  Definition tfib_E_asan_module_ctor : Z := 0x8464c.
Definition tfib_A_asan_module_dtor : Z := 0x8464c.  Definition tfib_E_asan_module_dtor : Z := 0x8467c.
Definition tfib_A_extenddftf2 : Z := 0x898d0.  Definition tfib_E_extenddftf2 : Z := 0x89a60.
Definition tfib_A_sysconf : Z := 0x8f6b0.  Definition tfib_E_sysconf : Z := 0x8f8d8.
Definition tfib_A_init : Z := 0x8f8d8.  Definition tfib_E_init : Z := 0x8f8dc.
Definition tfib_A_init_libc : Z := 0x8f8dc.  Definition tfib_E_init_libc : Z := 0x8fb08.
Definition tfib_A_libc_start_init : Z := 0x8fb08.  Definition tfib_E_libc_start_init : Z := 0x8fb54.
Definition tfib_A_libc_start_main : Z := 0x8fb54.  Definition tfib_E_libc_start_main : Z := 0x8fbb4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8fbb4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8fbfc.
Definition tfib_A_init_tls : Z := 0x8fcd4.  Definition tfib_E_init_tls : Z := 0x8ff84.
Definition tfib_A_init_ssp : Z := 0x8ff84.  Definition tfib_E_init_ssp : Z := 0x8ffe4.
Definition tfib_A_stack_chk_fail : Z := 0x8ffe4.  Definition tfib_E_stack_chk_fail : Z := 0x8ffec.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x90034.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x900c8.
Definition tfib_A_Exit : Z := 0x900c8.  Definition tfib_E_Exit : Z := 0x900e4.
Definition tfib_A_funcs_on_exit : Z := 0x90114.  Definition tfib_E_funcs_on_exit : Z := 0x901dc.
Definition tfib_A_fini_stub_ret : Z := 0x901dc.  Definition tfib_E_fini_stub_ret : Z := 0x901e0.
Definition tfib_A_cxa_atexit_atexit : Z := 0x901e0.  Definition tfib_E_cxa_atexit_atexit : Z := 0x902a4.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x902a4.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x902a8.
Definition tfib_A_musl_exit_helper_stub : Z := 0x902a8.  Definition tfib_E_musl_exit_helper_stub : Z := 0x902ac.
Definition tfib_A_libc_exit_fini : Z := 0x902ac.  Definition tfib_E_libc_exit_fini : Z := 0x902f8.
Definition tfib_A_exit : Z := 0x902f8.  Definition tfib_E_exit : Z := 0x9036c.
Definition tfib_A_open : Z := 0x9056c.  Definition tfib_E_open : Z := 0x90650.
Definition tfib_A_syscall_ret : Z := 0x90650.  Definition tfib_E_syscall_ret : Z := 0x90688.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x90688.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x90830.
Definition tfib_A_calloc : Z := 0x90df4.  Definition tfib_E_calloc : Z := 0x90f2c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x90f2c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x90f30.
Definition tfib_A_libc_free : Z := 0x90f30.  Definition tfib_E_libc_free : Z := 0x910fc.
Definition tfib_A_get_meta : Z := 0x910fc.  Definition tfib_E_get_meta : Z := 0x9120c.
Definition tfib_A_alloc_meta : Z := 0x915e4.  Definition tfib_E_alloc_meta : Z := 0x918bc.
Definition tfib_A_libc_malloc_impl : Z := 0x918bc.  Definition tfib_E_libc_malloc_impl : Z := 0x91c2c.
Definition tfib_A_alloc_slot : Z := 0x91c2c.  Definition tfib_E_alloc_slot : Z := 0x924d0.
Definition tfib_A_enframe : Z := 0x924d0.  Definition tfib_E_enframe : Z := 0x92620.
Definition tfib_A_malloc_allzerop : Z := 0x92620.  Definition tfib_E_malloc_allzerop : Z := 0x92798.
Definition tfib_A_getrlimit : Z := 0x94448.  Definition tfib_E_getrlimit : Z := 0x94540.
Definition tfib_A_getrusage : Z := 0x94540.  Definition tfib_E_getrusage : Z := 0x94568.
Definition tfib_A_setrlimit : Z := 0x94568.  Definition tfib_E_setrlimit : Z := 0x94630.
Definition tfib_A_mmap : Z := 0x94a58.  Definition tfib_E_mmap : Z := 0x94b44.
Definition tfib_A_mprotect : Z := 0x94b44.  Definition tfib_E_mprotect : Z := 0x94b8c.
Definition tfib_A_munmap : Z := 0x94c60.  Definition tfib_E_munmap : Z := 0x94ca8.
Definition tfib_A_sched_yield : Z := 0x94f6c.  Definition tfib_E_sched_yield : Z := 0x94f90.
Definition tfib_A_raise_tkill_path : Z := 0x94fec.  Definition tfib_E_raise_tkill_path : Z := 0x95064.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x95064.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x95238.
Definition tfib_A_musl_sigaltstack : Z := 0x95330.  Definition tfib_E_musl_sigaltstack : Z := 0x953bc.
Definition tfib_A_fprintf : Z := 0x95998.  Definition tfib_E_fprintf : Z := 0x959fc.
Definition tfib_A_lockfile : Z := 0x959fc.  Definition tfib_E_lockfile : Z := 0x95af8.
Definition tfib_A_unlockfile : Z := 0x95af8.  Definition tfib_E_unlockfile : Z := 0x95b58.
Definition tfib_A_stdio_read : Z := 0x956e8.  Definition tfib_E_stdio_read : Z := 0x95800.
Definition tfib_A_stdio_write : Z := 0x95808.  Definition tfib_E_stdio_write : Z := 0x95998.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x956b8.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x956bc.
Definition tfib_A_stdio_close : Z := 0x956bc.  Definition tfib_E_stdio_close : Z := 0x956e8.
Definition tfib_A_fwritex : Z := 0x95f8c.  Definition tfib_E_fwritex : Z := 0x960c4.
Definition tfib_A_musl_fwrite : Z := 0x960c4.  Definition tfib_E_musl_fwrite : Z := 0x9617c.
Definition tfib_A_towrite : Z := 0x9617c.  Definition tfib_E_towrite : Z := 0x961d0.
Definition tfib_A_stdio_exit : Z := 0x95de8.  Definition tfib_E_stdio_exit : Z := 0x95f8c.
Definition tfib_A_ofl_lock : Z := 0x961d0.  Definition tfib_E_ofl_lock : Z := 0x96200.
Definition tfib_A_musl_vfprintf : Z := 0x9634c.  Definition tfib_E_musl_vfprintf : Z := 0x964fc.
Definition tfib_A_printf_core : Z := 0x964fc.  Definition tfib_E_printf_core : Z := 0x9732c.
Definition tfib_A_pop_arg : Z := 0x9732c.  Definition tfib_E_pop_arg : Z := 0x97460.
Definition tfib_A_pad : Z := 0x97460.  Definition tfib_E_pad : Z := 0x97534.
Definition tfib_A_fmt_fp : Z := 0x97534.  Definition tfib_E_fmt_fp : Z := 0x98bfc.
Definition tfib_A_thunk_931e0 : Z := 0x90a48.  Definition tfib_E_thunk_931e0 : Z := 0x90a4c.
Definition tfib_A_musl_wctomb : Z := 0x94dd4.  Definition tfib_E_musl_wctomb : Z := 0x94df8.
Definition tfib_A_musl_wcrtomb : Z := 0x94ca8.  Definition tfib_E_musl_wcrtomb : Z := 0x94dd4.
Definition tfib_A_fpclassifyl : Z := 0x93038.  Definition tfib_E_fpclassifyl : Z := 0x9307c.
Definition tfib_A_letf2 : Z := 0x92870.  Definition tfib_E_letf2 : Z := 0x92938.
Definition tfib_A_multf3 : Z := 0x92938.  Definition tfib_E_multf3 : Z := 0x93038.
Definition tfib_A_floatsitf : Z := 0x93894.  Definition tfib_E_floatsitf : Z := 0x9399c.
Definition tfib_A_scalbn : Z := 0x942a0.  Definition tfib_E_scalbn : Z := 0x94338.
Definition tfib_A_subtf3 : Z := 0x93884.  Definition tfib_E_subtf3 : Z := 0x93894.
Definition tfib_A_addtf3 : Z := 0x9307c.  Definition tfib_E_addtf3 : Z := 0x93848.
Definition tfib_A_fe_getround : Z := 0x93848.  Definition tfib_E_fe_getround : Z := 0x93878.
Definition tfib_A_fixunstfsi : Z := 0x98c04.  Definition tfib_E_fixunstfsi : Z := 0x98c98.
Definition tfib_A_floatunsitf : Z := 0x98c98.  Definition tfib_E_floatunsitf : Z := 0x98d84.
Definition tfib_A_fixtfsi : Z := 0x94338.  Definition tfib_E_fixtfsi : Z := 0x943e0.
Definition tfib_A_divtf3 : Z := 0x9399c.  Definition tfib_E_divtf3 : Z := 0x942a0.
Definition tfib_A_musl_vprintf : Z := 0x9945c.  Definition tfib_E_musl_vprintf : Z := 0x99478.
Definition tfib_A_stdout_write : Z := 0x9620c.  Definition tfib_E_stdout_write : Z := 0x962ac.
Definition tfib_A_thunk_95368 : Z := 0x99a10.  Definition tfib_E_thunk_95368 : Z := 0x99a14.
Definition tfib_A_musl_memcmp : Z := 0x99ae0.  Definition tfib_E_musl_memcmp : Z := 0x99b10.
Definition tfib_A_musl_memcpy : Z := 0x99b10.  Definition tfib_E_musl_memcpy : Z := 0x99f14.
Definition tfib_A_musl_memset : Z := 0x99f14.  Definition tfib_E_musl_memset : Z := 0x9a00c.
Definition tfib_A_musl_strchr : Z := 0x9a00c.  Definition tfib_E_musl_strchr : Z := 0x9a048.
Definition tfib_A_strchrnul : Z := 0x9a048.  Definition tfib_E_strchrnul : Z := 0x9a128.
Definition tfib_A_musl_strlen : Z := 0x9a160.  Definition tfib_E_musl_strlen : Z := 0x9a1f0.
Definition tfib_A_musl_strnlen : Z := 0x9a39c.  Definition tfib_E_musl_strnlen : Z := 0x9a3e0.
Definition tfib_A_musl_memchr : Z := 0x99a14.  Definition tfib_E_musl_memchr : Z := 0x99ae0.
Definition tfib_A_lock : Z := 0x9a3e0.  Definition tfib_E_lock : Z := 0x9a668.
Definition tfib_A_unlock : Z := 0x9a668.  Definition tfib_E_unlock : Z := 0x9a6dc.
Definition tfib_A_syscall_cp_c : Z := 0x9a6dc.  Definition tfib_E_syscall_cp_c : Z := 0x9a700.
Definition tfib_A_syscall_cp_sccp : Z := 0x9a700.  Definition tfib_E_syscall_cp_sccp : Z := 0x9a704.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9a704.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9a728.
Definition tfib_A_pthread_atfork : Z := 0x9a740.  Definition tfib_E_pthread_atfork : Z := 0x9a7e4.
Definition tfib_A_mremap : Z := 0x94b8c.  Definition tfib_E_mremap : Z := 0x94c60.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9b7b8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9b7d4.
Definition tfib_A_pthread_key_create : Z := 0x9bb60.  Definition tfib_E_pthread_key_create : Z := 0x9bc34.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9bed8.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x9bf7c.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x9bf7c.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x9c098.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9c098.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9c0c4.
Definition tfib_A_pthread_setspecific : Z := 0x9c0fc.  Definition tfib_E_pthread_setspecific : Z := 0x9c130.
Definition tfib_A_thunk_96f9c : Z := 0x9c130.  Definition tfib_E_thunk_96f9c : Z := 0x9c138.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9ca64.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9cb1c.
Definition tfib_A_close : Z := 0x9f134.  Definition tfib_E_close : Z := 0x9f188.
Definition tfib_A_musl_read : Z := 0x9f214.  Definition tfib_E_musl_read : Z := 0x9f248.
Definition tfib_A_set_thread_area : Z := 0x9c138.  Definition tfib_E_set_thread_area : Z := 0x9c144.
Definition tfib_A_vm_wait : Z := 0x9c774.  Definition tfib_E_vm_wait : Z := 0x9c7c4.
Definition tfib_D_str_sealed : Z := 0x11835.
Definition tfib_D_init_array_0_3 : Z := 0xa0248.
Definition tfib_D_fini_array_0_1 : Z := 0xa0268.
Definition tfib_D_GOT_common_flags : Z := 0xa08a0.
Definition tfib_D_GOT_flags : Z := 0xa08a8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa08b0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa08b8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa08c0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa08c8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa1418.
Definition tfib_D_environ_musl : Z := 0xa1540.
Definition tfib_D_REAL_read : Z := 0xa25e8.
Definition tfib_D_REAL_memcpy : Z := 0xa2710.
Definition tfib_D_REAL_memset : Z := 0xa2718.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa5e18.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa6c78.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa9478.
Definition tfib_D_asan_inited : Z := 0xaa158.
Definition tfib_D_replace_intrin_cached : Z := 0xaa159.
Definition tfib_D_kHighMemEnd : Z := 0xaa160.
Definition tfib_D_kMidMemBeg : Z := 0xaa168.
Definition tfib_D_kMidMemEnd : Z := 0xaa170.
Definition tfib_D_malloc_context_size : Z := 0xaa17c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13afa8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5fc6a0.
Definition tfib_at_img_lo : Z := YImgTop.IMG_LO.
Definition tfib_at_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30f24.
Definition tfib_at_rw_lo : Z := 0xa2000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x64494.
Definition tfib_at_x_imemcpy : Z := 0x64418.
Definition tfib_at_x_memset : Z := 0x99f14.
Definition tfib_at_x_memcpy : Z := 0x99b10.
Definition tfib_at_x_memiszero : Z := 0x649c4.
Definition tfib_at_x_istrncpy : Z := 0x648c0.
Definition tfib_at_x_sealed : Z := 0x11835.
Definition tfib_at_x_popfree : Z := 0x37310.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8f914.
Definition tfib_at_x_envscan_k : Z := 0x8f920.
Definition tfib_at_x_pnscan : Z := 0x8f9d8.
Definition tfib_at_x_pnscan_k : Z := 0x8f9e4.
Definition tfib_at_stops_more : list Z := (0x34f84 :: 0x365a8 :: 0x547a0 :: 0x5ab58 :: 0x5ab6c :: 0x5ab80 :: 0x60510 :: 0x605e0 :: 0x6db0c :: 0x6ea18 :: 0x6eba8 :: 0x78900 :: nil)%list.
