(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build; its section bounds, function bounds and fake-stack entries are read from libreac/fuzz_disco's ASan image (gen_symtab.py), and the donor's own program functions and the libc functions fuzz_disco does not link have no entry. *)
From OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22fac.
Definition tfib_text_lo : Z := 0x30eac.  Definition tfib_text_hi : Z := 0x9eea8.
Definition tfib_init_array_lo : Z := 0x9fea8.  Definition tfib_init_array_hi : Z := 0x9fec8.
Definition tfib_fini_array_lo : Z := 0x9fec8.  Definition tfib_fini_array_hi : Z := 0x9fed8.
Definition tfib_preinit_array_lo : Z := 0x9fed8.  Definition tfib_preinit_array_hi : Z := 0x9fee0.
Definition tfib_data_rel_ro_lo : Z := 0x9fee0.  Definition tfib_data_rel_ro_hi : Z := 0xa04b0.
Definition tfib_got_lo : Z := 0xa04b0.  Definition tfib_got_hi : Z := 0xa1208.
Definition tfib_data_lo : Z := 0xa2208.  Definition tfib_data_hi : Z := 0xa4dc0.
Definition tfib_asan_globals_lo : Z := 0xa4dc0.  Definition tfib_asan_globals_hi : Z := 0xa5a00.
Definition tfib_bss_lo : Z := 0xa5a00.  Definition tfib_bss_hi : Z := 0x5fd930.
Definition tfib_tbss_lo : Z := 0x9eea8.  Definition tfib_tbss_hi : Z := 0x9eebc.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_entry : Z := 0x30eac.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30eac.  Definition tfib_E_start : Z := 0x30ef4.
Definition tfib_A_do_init : Z := 0x30ef4.  Definition tfib_E_do_init : Z := 0x30f68.
Definition tfib_A_do_fini : Z := 0x30f68.  Definition tfib_E_do_fini : Z := 0x30ff8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30ff8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x31034.
Definition tfib_A_InitializeAllocator : Z := 0x311a4.  Definition tfib_E_InitializeAllocator : Z := 0x311bc.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x311bc.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x31328.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31884.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x319e0.
Definition tfib_A_asan_free : Z := 0x31db4.  Definition tfib_E_asan_free : Z := 0x31ddc.
Definition tfib_A_Allocator_Deallocate : Z := 0x31ddc.  Definition tfib_E_Allocator_Deallocate : Z := 0x32094.
Definition tfib_A_asan_malloc : Z := 0x32094.  Definition tfib_E_asan_malloc : Z := 0x320f0.
Definition tfib_A_Allocator_Allocate : Z := 0x320f0.  Definition tfib_E_Allocator_Allocate : Z := 0x32a78.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x331b0.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x332f4.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x333e0.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x3343c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x3343c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3368c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3368c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33780.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x33780.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33868.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x33c9c.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x33e80.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x33e80.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x34004.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x3413c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x343c0.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x343c0.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34540.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34540.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34708.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34708.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x348d4.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x348d4.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34974.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34974.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34a78.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34da0.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34ee8.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34ee8.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34f20.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x356b8.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x359a0.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x36078.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x361f0.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x361f0.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x363a0.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x363a0.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x36584.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x36584.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x3685c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x3685c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36cd4.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36cd4.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36dd4.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36dd4.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x370dc.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x370dc.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x3744c.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x3744c.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x37564.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x3786c.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37968.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37968.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37a50.
Definition tfib_A_AsanActivate : Z := 0x37a50.  Definition tfib_E_AsanActivate : Z := 0x37b2c.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x38008.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x380f0.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3cba8.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3cc80.
Definition tfib_A_FakeStack_Create : Z := 0x3cc80.  Definition tfib_E_FakeStack_Create : Z := 0x3cd6c.
Definition tfib_A_FakeStack_Allocate : Z := 0x3d028.  Definition tfib_E_FakeStack_Allocate : Z := 0x3d310.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d444.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d474.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3c8a4.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3ca34.
Definition tfib_A_asan_stack_malloc_B : Z := 0x3ca34.  Definition tfib_E_asan_stack_malloc_B : Z := 0x3cbd0.
Definition tfib_A_FakeStack_SetShadow : Z := 0x3dca4.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3dde0.
Definition tfib_A_asan_InitializeFlags : Z := 0x3dde0.  Definition tfib_E_asan_InitializeFlags : Z := 0x3ee0c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f518.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40334.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x40334.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40900.
Definition tfib_A_asan_register_globals : Z := 0x40900.  Definition tfib_E_asan_register_globals : Z := 0x4096c.
Definition tfib_A_asan_unregister_globals : Z := 0x4096c.  Definition tfib_E_asan_unregister_globals : Z := 0x409d4.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x41054.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x412c4.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x412c4.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x415cc.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41d40.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41e90.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x428ac.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x429c4.
Definition tfib_A_strlen : Z := 0x429c4.  Definition tfib_E_strlen : Z := 0x429c8.
Definition tfib_A_strnlen : Z := 0x429c8.  Definition tfib_E_strnlen : Z := 0x429cc.
Definition tfib_A_strcmp : Z := 0x429cc.  Definition tfib_E_strcmp : Z := 0x429d0.
Definition tfib_A_strchr : Z := 0x429d0.  Definition tfib_E_strchr : Z := 0x429d4.
Definition tfib_A_memcmp : Z := 0x429d4.  Definition tfib_E_memcmp : Z := 0x429d8.
Definition tfib_A_memcmp_2 : Z := 0x429d8.  Definition tfib_E_memcmp_2 : Z := 0x429dc.
Definition tfib_A_memchr : Z := 0x429dc.  Definition tfib_E_memchr : Z := 0x429e0.
Definition tfib_A_frexpl : Z := 0x429e0.  Definition tfib_E_frexpl : Z := 0x429e4.
Definition tfib_A_read : Z := 0x429e4.  Definition tfib_E_read : Z := 0x429e8.
Definition tfib_A_fwrite : Z := 0x429e8.  Definition tfib_E_fwrite : Z := 0x429ec.
Definition tfib_A_time : Z := 0x429ec.  Definition tfib_E_time : Z := 0x429f0.
Definition tfib_A_gmtime_r : Z := 0x429f0.  Definition tfib_E_gmtime_r : Z := 0x429f4.
Definition tfib_A_vprintf : Z := 0x429f4.  Definition tfib_E_vprintf : Z := 0x429f8.
Definition tfib_A_vfprintf : Z := 0x429f8.  Definition tfib_E_vfprintf : Z := 0x429fc.
Definition tfib_A_vsnprintf : Z := 0x429fc.  Definition tfib_E_vsnprintf : Z := 0x42a00.
Definition tfib_A_vfprintf_2 : Z := 0x42a00.  Definition tfib_E_vfprintf_2 : Z := 0x42a04.
Definition tfib_A_thunk_417bc : Z := 0x42a04.  Definition tfib_E_thunk_417bc : Z := 0x42a08.
Definition tfib_A_clock_gettime : Z := 0x42a08.  Definition tfib_E_clock_gettime : Z := 0x42a0c.
Definition tfib_A_wcrtomb : Z := 0x42a0c.  Definition tfib_E_wcrtomb : Z := 0x42a10.
Definition tfib_A_wctomb : Z := 0x42a10.  Definition tfib_E_wctomb : Z := 0x42a14.
Definition tfib_A_thunk_417cc : Z := 0x42a14.  Definition tfib_E_thunk_417cc : Z := 0x42a1c.
Definition tfib_A_pthread_attr_getstack : Z := 0x42a1c.  Definition tfib_E_pthread_attr_getstack : Z := 0x42a20.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42a20.  Definition tfib_E_tls_get_addr_thunk : Z := 0x42a24.
Definition tfib_A_thunk_417dc : Z := 0x42a24.  Definition tfib_E_thunk_417dc : Z := 0x42a28.
Definition tfib_A_thunk_417e4 : Z := 0x42a28.  Definition tfib_E_thunk_417e4 : Z := 0x42a2c.
Definition tfib_A_thunk_417e8 : Z := 0x42a2c.  Definition tfib_E_thunk_417e8 : Z := 0x42a30.
Definition tfib_A_thunk_417ec : Z := 0x42a30.  Definition tfib_E_thunk_417ec : Z := 0x42a34.
Definition tfib_A_thunk_417f0 : Z := 0x42a34.  Definition tfib_E_thunk_417f0 : Z := 0x42a38.
Definition tfib_A_sem_timedwait : Z := 0x42a38.  Definition tfib_E_sem_timedwait : Z := 0x42a3c.
Definition tfib_A_thunk_417f8 : Z := 0x42a3c.  Definition tfib_E_thunk_417f8 : Z := 0x42a40.
Definition tfib_A_pthread_setcancelstate : Z := 0x42a40.  Definition tfib_E_pthread_setcancelstate : Z := 0x42a44.
Definition tfib_A_send : Z := 0x42a44.  Definition tfib_E_send : Z := 0x42a48.
Definition tfib_A_sendto : Z := 0x42a48.  Definition tfib_E_sendto : Z := 0x42a4c.
Definition tfib_A_sigaltstack : Z := 0x42a4c.  Definition tfib_E_sigaltstack : Z := 0x42a50.
Definition tfib_A_thunk_4180c : Z := 0x42a50.  Definition tfib_E_thunk_4180c : Z := 0x42a54.
Definition tfib_A_icpt_strlen : Z := 0x42a54.  Definition tfib_E_icpt_strlen : Z := 0x42ce8.
Definition tfib_A_icpt_strnlen : Z := 0x42ce8.  Definition tfib_E_icpt_strnlen : Z := 0x42f7c.
Definition tfib_A_icpt_strcmp : Z := 0x42f80.  Definition tfib_E_icpt_strcmp : Z := 0x434b0.
Definition tfib_A_icpt_strchr : Z := 0x434b0.  Definition tfib_E_icpt_strchr : Z := 0x43790.
Definition tfib_A_icpt_memcmp : Z := 0x44028.  Definition tfib_E_icpt_memcmp : Z := 0x440e4.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x440e4.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x441a0.
Definition tfib_A_icpt_memchr : Z := 0x441a0.  Definition tfib_E_icpt_memchr : Z := 0x44470.
Definition tfib_A_icpt_frexpl : Z := 0x44470.  Definition tfib_E_icpt_frexpl : Z := 0x446e8.
Definition tfib_A_icpt_read : Z := 0x446e8.  Definition tfib_E_icpt_read : Z := 0x44958.
Definition tfib_A_icpt_fwrite : Z := 0x44958.  Definition tfib_E_icpt_fwrite : Z := 0x44bcc.
Definition tfib_A_icpt_time : Z := 0x44bcc.  Definition tfib_E_icpt_time : Z := 0x44e68.
Definition tfib_A_icpt_gmtime_r : Z := 0x45070.  Definition tfib_E_icpt_gmtime_r : Z := 0x452b0.
Definition tfib_A_icpt_vprintf : Z := 0x452b0.  Definition tfib_E_icpt_vprintf : Z := 0x4534c.
Definition tfib_A_printf_common_format_interceptor : Z := 0x4534c.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45e14.
Definition tfib_A_icpt_vfprintf : Z := 0x45e14.  Definition tfib_E_icpt_vfprintf : Z := 0x45ec8.
Definition tfib_A_icpt_vsnprintf : Z := 0x45ec8.  Definition tfib_E_icpt_vsnprintf : Z := 0x461e0.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x461e0.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x462b8.
Definition tfib_A_icpt_clock_gettime : Z := 0x4635c.  Definition tfib_E_icpt_clock_gettime : Z := 0x465b4.
Definition tfib_A_icpt_wcrtomb : Z := 0x465b4.  Definition tfib_E_icpt_wcrtomb : Z := 0x46b24.
Definition tfib_A_icpt_wctomb : Z := 0x46b24.  Definition tfib_E_icpt_wctomb : Z := 0x46e80.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46f4c.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x47334.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x47340.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x473bc.
Definition tfib_A_icpt_sem_timedwait : Z := 0x475c8.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47860.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47890.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47ab8.
Definition tfib_A_icpt_send : Z := 0x47ab8.  Definition tfib_E_icpt_send : Z := 0x47d6c.
Definition tfib_A_icpt_sendto : Z := 0x47d6c.  Definition tfib_E_icpt_sendto : Z := 0x48030.
Definition tfib_A_icpt_sigaltstack : Z := 0x48030.  Definition tfib_E_icpt_sigaltstack : Z := 0x4828c.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x48360.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x48510.
Definition tfib_A_icpt_diouxXn : Z := 0x48510.  Definition tfib_E_icpt_diouxXn : Z := 0x486a8.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x49254.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x51f2c.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51f2c.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x52088.
Definition tfib_A_memset : Z := 0x52088.  Definition tfib_E_memset : Z := 0x5208c.
Definition tfib_A_memcpy : Z := 0x5208c.  Definition tfib_E_memcpy : Z := 0x52090.
Definition tfib_A_asan_memcpy : Z := 0x52090.  Definition tfib_E_asan_memcpy : Z := 0x5252c.
Definition tfib_A_asan_memset : Z := 0x5252c.  Definition tfib_E_asan_memset : Z := 0x5276c.
Definition tfib_A_icpt_memset : Z := 0x5276c.  Definition tfib_E_icpt_memset : Z := 0x52a5c.
Definition tfib_A_icpt_memcpy : Z := 0x52a5c.  Definition tfib_E_icpt_memcpy : Z := 0x5304c.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5304c.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x53084.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x53084.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x53088.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x53088.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x5308c.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5308c.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x530ec.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53138.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53274.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x53274.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x53278.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x53278.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x533e0.
Definition tfib_A_free : Z := 0x533e0.  Definition tfib_E_free : Z := 0x533e4.
Definition tfib_A_malloc : Z := 0x533e4.  Definition tfib_E_malloc : Z := 0x533e8.
Definition tfib_A_icpt_free : Z := 0x533e8.  Definition tfib_E_icpt_free : Z := 0x535b8.
Definition tfib_A_icpt_malloc : Z := 0x535b8.  Definition tfib_E_icpt_malloc : Z := 0x53714.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x53714.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x537e0.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x537e0.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x537e4.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x537e4.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x538e4.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x53c0c.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x53d78.
Definition tfib_A_SetCanPoisonMemory : Z := 0x54260.  Definition tfib_E_SetCanPoisonMemory : Z := 0x54270.
Definition tfib_A_CanPoisonMemory : Z := 0x54270.  Definition tfib_E_CanPoisonMemory : Z := 0x54284.
Definition tfib_A_PoisonShadow : Z := 0x54284.  Definition tfib_E_PoisonShadow : Z := 0x54780.
Definition tfib_A_MemToShadow_checked : Z := 0x54780.  Definition tfib_E_MemToShadow_checked : Z := 0x548bc.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x548bc.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x54a5c.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x54a5c.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x54bdc.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54c0c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54f50.
Definition tfib_A_AsanTSDInit : Z := 0x55370.  Definition tfib_E_AsanTSDInit : Z := 0x553ec.
Definition tfib_A_AsanTSDGet : Z := 0x553ec.  Definition tfib_E_AsanTSDGet : Z := 0x5542c.
Definition tfib_A_AsanTSDSet : Z := 0x5542c.  Definition tfib_E_AsanTSDSet : Z := 0x5546c.
Definition tfib_A_PlatformTSDDtor : Z := 0x5546c.  Definition tfib_E_PlatformTSDDtor : Z := 0x554f0.
Definition tfib_A_InstallAtForkHandler : Z := 0x554f0.  Definition tfib_E_InstallAtForkHandler : Z := 0x5550c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x5556c.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x555b0.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x55cc8.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x55ed4.
Definition tfib_A_ReportDoubleFree : Z := 0x565dc.  Definition tfib_E_ReportDoubleFree : Z := 0x5686c.
Definition tfib_A_ReportGenericError : Z := 0x58148.  Definition tfib_E_ReportGenericError : Z := 0x58a04.
Definition tfib_A_AsanInited : Z := 0x59190.  Definition tfib_E_AsanInited : Z := 0x591a8.
Definition tfib_A_asan_report_load1 : Z := 0x591a8.  Definition tfib_E_asan_report_load1 : Z := 0x591f8.
Definition tfib_A_asan_report_exp_load1 : Z := 0x591f8.  Definition tfib_E_asan_report_exp_load1 : Z := 0x59248.
Definition tfib_A_asan_report_load2 : Z := 0x59248.  Definition tfib_E_asan_report_load2 : Z := 0x59298.
Definition tfib_A_asan_report_exp_load2 : Z := 0x59298.  Definition tfib_E_asan_report_exp_load2 : Z := 0x592e8.
Definition tfib_A_asan_report_load4 : Z := 0x592e8.  Definition tfib_E_asan_report_load4 : Z := 0x59338.
Definition tfib_A_asan_report_exp_load4 : Z := 0x59338.  Definition tfib_E_asan_report_exp_load4 : Z := 0x59388.
Definition tfib_A_asan_report_load8 : Z := 0x59388.  Definition tfib_E_asan_report_load8 : Z := 0x593d8.
Definition tfib_A_asan_report_exp_load8 : Z := 0x593d8.  Definition tfib_E_asan_report_exp_load8 : Z := 0x59428.
Definition tfib_A_asan_report_load16 : Z := 0x59428.  Definition tfib_E_asan_report_load16 : Z := 0x59478.
Definition tfib_A_asan_report_exp_load16 : Z := 0x59478.  Definition tfib_E_asan_report_exp_load16 : Z := 0x594c8.
Definition tfib_A_asan_report_store1 : Z := 0x594c8.  Definition tfib_E_asan_report_store1 : Z := 0x59518.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59518.  Definition tfib_E_asan_report_exp_store1 : Z := 0x59568.
Definition tfib_A_asan_report_store2 : Z := 0x59568.  Definition tfib_E_asan_report_store2 : Z := 0x595b8.
Definition tfib_A_asan_report_exp_store2 : Z := 0x595b8.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59608.
Definition tfib_A_asan_report_store4 : Z := 0x59608.  Definition tfib_E_asan_report_store4 : Z := 0x59658.
Definition tfib_A_asan_report_exp_store4 : Z := 0x59658.  Definition tfib_E_asan_report_exp_store4 : Z := 0x596a8.
Definition tfib_A_asan_report_store8 : Z := 0x596a8.  Definition tfib_E_asan_report_store8 : Z := 0x596f8.
Definition tfib_A_asan_report_exp_store8 : Z := 0x596f8.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59748.
Definition tfib_A_asan_report_store16 : Z := 0x59748.  Definition tfib_E_asan_report_store16 : Z := 0x59798.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59798.  Definition tfib_E_asan_report_exp_store16 : Z := 0x597e8.
Definition tfib_A_asan_report_load_n : Z := 0x597e8.  Definition tfib_E_asan_report_load_n : Z := 0x59838.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59838.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59888.
Definition tfib_A_asan_report_store_n : Z := 0x59888.  Definition tfib_E_asan_report_store_n : Z := 0x598d8.
Definition tfib_A_asan_report_exp_store_n : Z := 0x598d8.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59928.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59928.  Definition tfib_E_InitializeHighMemEnd : Z := 0x599a8.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x599a8.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59d5c.
Definition tfib_A_AsanInitInternal : Z := 0x59dec.  Definition tfib_E_AsanInitInternal : Z := 0x5a0a0.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a0a0.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5a140.
Definition tfib_A_thunk_59674 : Z := 0x5a308.  Definition tfib_E_thunk_59674 : Z := 0x5a30c.
Definition tfib_A_asan_init : Z := 0x5a30c.  Definition tfib_E_asan_init : Z := 0x5a3a0.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a3a0.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a3a4.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a3a4.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a408.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5a57c.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5a584.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a608.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a930.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a930.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5ab10.
Definition tfib_A_InitializeShadowMemory : Z := 0x5ab10.  Definition tfib_E_InitializeShadowMemory : Z := 0x5ae18.
Definition tfib_A_SetMallocContextSize : Z := 0x5ae18.  Definition tfib_E_SetMallocContextSize : Z := 0x5ae28.
Definition tfib_A_GetMallocContextSize : Z := 0x5ae28.  Definition tfib_E_GetMallocContextSize : Z := 0x5ae38.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ae38.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5af88.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5b368.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5b608.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5ba6c.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5baa4.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5bd4c.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5bd58.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5bd58.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5bde4.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5bde4.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5be4c.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5be4c.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5bec4.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5bec4.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5bf2c.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5bf2c.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5c078.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5c304.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5c310.
Definition tfib_A_AsanThread_Create : Z := 0x5c490.  Definition tfib_E_AsanThread_Create : Z := 0x5c62c.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c688.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c8a0.
Definition tfib_A_GetCurrentThread : Z := 0x5c8a0.  Definition tfib_E_GetCurrentThread : Z := 0x5c8c0.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c8c0.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5ca64.
Definition tfib_A_AsanThread_stack_top : Z := 0x5ca64.  Definition tfib_E_AsanThread_stack_top : Z := 0x5cabc.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5cabc.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5cb14.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5cb14.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5cd44.
Definition tfib_A_AsanThread_Init : Z := 0x5cd44.  Definition tfib_E_AsanThread_Init : Z := 0x5d138.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d138.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5d244.
Definition tfib_A_CreateMainThread : Z := 0x5d278.  Definition tfib_E_CreateMainThread : Z := 0x5d388.
Definition tfib_A_SetCurrentThread : Z := 0x5d388.  Definition tfib_E_SetCurrentThread : Z := 0x5d468.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d66c.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5d7a8.
Definition tfib_A_weak_default_hook_ret : Z := 0x5e47c.  Definition tfib_E_weak_default_hook_ret : Z := 0x5e480.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5e488.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5e6c8.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e91c.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5ea74.
Definition tfib_A_internal_allocator_getter : Z := 0x5ec60.  Definition tfib_E_internal_allocator_getter : Z := 0x5ec6c.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ec6c.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5edb8.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5edb8.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5ee04.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5ee04.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5ee10.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5ee40.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5ee4c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5ee4c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5ee58.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5ee58.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5ee68.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5ee74.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f140.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f140.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f500.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x6045c.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x60468.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x60468.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x60540.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x60540.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x605dc.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60b00.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60b44.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60b44.  Definition tfib_E_IncreaseTotalMmap : Z := 0x60b68.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60dbc.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60ed0.
Definition tfib_A_RunMallocHooks : Z := 0x61074.  Definition tfib_E_RunMallocHooks : Z := 0x6112c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x6112c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x61130.
Definition tfib_A_RunFreeHooks : Z := 0x61130.  Definition tfib_E_RunFreeHooks : Z := 0x611dc.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x611dc.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x611e4.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x611e4.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x611e8.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x61210.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x6125c.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61520.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61760.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61d5c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61d74.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x61d74.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x61eb8.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61eb8.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61ec0.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x62208.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x634ac.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x634ac.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x634d0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63984.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63c94.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63c94.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63dd8.
Definition tfib_A_FlagParser_ParseString : Z := 0x63dd8.  Definition tfib_E_FlagParser_ParseString : Z := 0x63ecc.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64060.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x640c0.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x640c0.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x64100.
Definition tfib_A_internal_atoll : Z := 0x64100.  Definition tfib_E_internal_atoll : Z := 0x641ec.
Definition tfib_A_internal_simple_strtoll : Z := 0x641ec.  Definition tfib_E_internal_simple_strtoll : Z := 0x64348.
Definition tfib_A_internal_memchr : Z := 0x64348.  Definition tfib_E_internal_memchr : Z := 0x64368.
Definition tfib_A_internal_memcmp : Z := 0x64368.  Definition tfib_E_internal_memcmp : Z := 0x643a0.
Definition tfib_A_internal_memcpy : Z := 0x643a0.  Definition tfib_E_internal_memcpy : Z := 0x643c4.
Definition tfib_A_internal_memmove : Z := 0x643c4.  Definition tfib_E_internal_memmove : Z := 0x6441c.
Definition tfib_A_internal_memset : Z := 0x6441c.  Definition tfib_E_internal_memset : Z := 0x6447c.
Definition tfib_A_internal_strcspn : Z := 0x6447c.  Definition tfib_E_internal_strcspn : Z := 0x644d0.
Definition tfib_A_internal_strcmp : Z := 0x644d0.  Definition tfib_E_internal_strcmp : Z := 0x64504.
Definition tfib_A_internal_strdup : Z := 0x64504.  Definition tfib_E_internal_strdup : Z := 0x64570.
Definition tfib_A_internal_strlen : Z := 0x64570.  Definition tfib_E_internal_strlen : Z := 0x6458c.
Definition tfib_A_internal_strncmp : Z := 0x6458c.  Definition tfib_E_internal_strncmp : Z := 0x645d0.
Definition tfib_A_internal_strchr : Z := 0x645d0.  Definition tfib_E_internal_strchr : Z := 0x6461c.
Definition tfib_A_internal_strchrnul : Z := 0x6461c.  Definition tfib_E_internal_strchrnul : Z := 0x64664.
Definition tfib_A_internal_strrchr : Z := 0x64664.  Definition tfib_E_internal_strrchr : Z := 0x646a4.
Definition tfib_A_internal_strnlen : Z := 0x647d4.  Definition tfib_E_internal_strnlen : Z := 0x64804.
Definition tfib_A_internal_strncpy : Z := 0x64848.  Definition tfib_E_internal_strncpy : Z := 0x648b8.
Definition tfib_A_internal_strstr : Z := 0x648b8.  Definition tfib_E_internal_strstr : Z := 0x6494c.
Definition tfib_A_mem_is_zero : Z := 0x6494c.  Definition tfib_E_mem_is_zero : Z := 0x64a00.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64a00.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64a10.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64a10.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64bf0.
Definition tfib_A_internal_iserror : Z := 0x64bfc.  Definition tfib_E_internal_iserror : Z := 0x64c1c.
Definition tfib_A_internal_mmap : Z := 0x64c1c.  Definition tfib_E_internal_mmap : Z := 0x64c28.
Definition tfib_A_internal_munmap : Z := 0x64c28.  Definition tfib_E_internal_munmap : Z := 0x64c34.
Definition tfib_A_internal_mprotect : Z := 0x64c34.  Definition tfib_E_internal_mprotect : Z := 0x64c44.
Definition tfib_A_internal_madvise : Z := 0x64c44.  Definition tfib_E_internal_madvise : Z := 0x64c70.
Definition tfib_A_internal_close : Z := 0x64c70.  Definition tfib_E_internal_close : Z := 0x64c7c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64c7c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64ca0.
Definition tfib_A_internal_read : Z := 0x64ca0.  Definition tfib_E_internal_read : Z := 0x64cd8.
Definition tfib_A_internal_write : Z := 0x64cd8.  Definition tfib_E_internal_write : Z := 0x64d10.
Definition tfib_A_internal_ftruncate : Z := 0x64d10.  Definition tfib_E_internal_ftruncate : Z := 0x64d48.
Definition tfib_A_internal_dup : Z := 0x64d48.  Definition tfib_E_internal_dup : Z := 0x64d54.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64d54.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64d64.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64d64.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64d7c.
Definition tfib_A_internal_sched_yield : Z := 0x64d7c.  Definition tfib_E_internal_sched_yield : Z := 0x64d88.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64d88.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64dd4.
Definition tfib_A_internal_execve : Z := 0x64dd4.  Definition tfib_E_internal_execve : Z := 0x64de0.
Definition tfib_A_internal_exit_exit_group : Z := 0x64de0.  Definition tfib_E_internal_exit_exit_group : Z := 0x64df4.
Definition tfib_A_FileExists_newfstatat : Z := 0x64df4.  Definition tfib_E_FileExists_newfstatat : Z := 0x64e74.
Definition tfib_A_DirExists_newfstatat : Z := 0x64e74.  Definition tfib_E_DirExists_newfstatat : Z := 0x64ed8.
Definition tfib_A_GetTid_gettid : Z := 0x64ed8.  Definition tfib_E_GetTid_gettid : Z := 0x64ee4.
Definition tfib_A_GetEnv : Z := 0x64ee4.  Definition tfib_E_GetEnv : Z := 0x65014.
Definition tfib_A_FutexWait : Z := 0x65118.  Definition tfib_E_FutexWait : Z := 0x6513c.
Definition tfib_A_FutexWake : Z := 0x6513c.  Definition tfib_E_FutexWake : Z := 0x65160.
Definition tfib_A_internal_ptrace : Z := 0x65160.  Definition tfib_E_internal_ptrace : Z := 0x6516c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6516c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6517c.
Definition tfib_A_internal_getpid : Z := 0x6517c.  Definition tfib_E_internal_getpid : Z := 0x65188.
Definition tfib_A_internal_getppid : Z := 0x65188.  Definition tfib_E_internal_getppid : Z := 0x65194.
Definition tfib_A_internal_prctl : Z := 0x65194.  Definition tfib_E_internal_prctl : Z := 0x651a0.
Definition tfib_A_internal_sigaltstack : Z := 0x651a0.  Definition tfib_E_internal_sigaltstack : Z := 0x651ac.
Definition tfib_A_internal_fork_clone : Z := 0x651ac.  Definition tfib_E_internal_fork_clone : Z := 0x651c4.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x651c4.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x652f0.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x654c8.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x658c4.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65a30.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65b48.
Definition tfib_A_GetPageSizeCached : Z := 0x65b48.  Definition tfib_E_GetPageSizeCached : Z := 0x65b50.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65b50.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65bfc.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65bfc.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65d1c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65de4.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65e64.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x65e64.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x65ec0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65ec0.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65f8c.
Definition tfib_A_thunk_653ec : Z := 0x66088.  Definition tfib_E_thunk_653ec : Z := 0x6608c.
Definition tfib_A_CheckASLR : Z := 0x6608c.  Definition tfib_E_CheckASLR : Z := 0x66090.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x662dc.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x662e0.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x662e0.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x662ec.
Definition tfib_A_MmapOrDie : Z := 0x662ec.  Definition tfib_E_MmapOrDie : Z := 0x663f8.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x663f8.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6646c.
Definition tfib_A_UnmapOrDie : Z := 0x6646c.  Definition tfib_E_UnmapOrDie : Z := 0x664e8.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x664e8.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x665f8.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x66824.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66928.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x66928.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x66934.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66934.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66aac.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66aac.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66ab8.
Definition tfib_A_thunk_66008 : Z := 0x66ca4.  Definition tfib_E_thunk_66008 : Z := 0x66ca8.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66fc8.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x671d4.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x6778c.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67798.
Definition tfib_A_Printf : Z := 0x6779c.  Definition tfib_E_Printf : Z := 0x677e8.
Definition tfib_A_SharedPrintfCode : Z := 0x677e8.  Definition tfib_E_SharedPrintfCode : Z := 0x67844.
Definition tfib_A_Report : Z := 0x67844.  Definition tfib_E_Report : Z := 0x67890.
Definition tfib_A_SuppressionContext_ctor : Z := 0x69388.  Definition tfib_E_SuppressionContext_ctor : Z := 0x693e4.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x693e4.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x69620.
Definition tfib_A_SuppressionContext_Parse : Z := 0x69620.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69944.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69ee4.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69fb4.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69fb4.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6a304.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6a304.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6a314.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6a550.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6a594.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6a594.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6a5f4.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a5f4.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6aa6c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b32c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b650.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b658.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b75c.
Definition tfib_A_AddDieCallback : Z := 0x6bf0c.  Definition tfib_E_AddDieCallback : Z := 0x6bf94.
Definition tfib_A_Die : Z := 0x6c058.  Definition tfib_E_Die : Z := 0x6c118.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c118.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c124.
Definition tfib_A_CheckFailed : Z := 0x6c124.  Definition tfib_E_CheckFailed : Z := 0x6c1dc.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c834.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c92c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c92c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6ca58.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6cc80.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6ccfc.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6cd30.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6d018.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6d018.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6d01c.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6d01c.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6d40c.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6d40c.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6d4dc.
Definition tfib_A_AndroidLogInit : Z := 0x6d8c0.  Definition tfib_E_AndroidLogInit : Z := 0x6d8c4.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d8f4.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d93c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d93c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6db88.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6db88.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6db8c.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6db8c.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6dc98.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dc98.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6dd9c.
Definition tfib_A_thunk_6d37c : Z := 0x6e018.  Definition tfib_E_thunk_6d37c : Z := 0x6e01c.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e0c0.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e0e0.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e0e0.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e180.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6e1cc.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6e1d0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e20c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e2d0.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e2d0.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e358.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e358.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e3d0.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e3d0.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e4b4.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e570.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e6a4.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e8dc.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6ea0c.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6ea0c.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6ea6c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ea6c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6eb38.
Definition tfib_A_MprotectNoAccess : Z := 0x6eb4c.  Definition tfib_E_MprotectNoAccess : Z := 0x6eb6c.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6eb6c.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6ecb8.
Definition tfib_A_MmapFixedOrDie : Z := 0x6ecb8.  Definition tfib_E_MmapFixedOrDie : Z := 0x6ecc8.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x704c0.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x70504.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x70504.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x70534.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70968.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70a8c.
Definition tfib_A_StackStore_Alloc : Z := 0x70a8c.  Definition tfib_E_StackStore_Alloc : Z := 0x70bc0.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x71474.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x71528.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72c7c.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72cd8.
Definition tfib_A_StackDepotPut : Z := 0x72f64.  Definition tfib_E_StackDepotPut : Z := 0x72f84.
Definition tfib_A_StackDepotBase_Put : Z := 0x72f84.  Definition tfib_E_StackDepotBase_Put : Z := 0x73208.
Definition tfib_A_StackDepotBase_Get : Z := 0x73208.  Definition tfib_E_StackDepotBase_Get : Z := 0x73318.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x736f8.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x73788.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x73788.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x73888.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x738e8.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x738f0.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x738f0.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73a50.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73a50.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73ac4.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73f4c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x74064.
Definition tfib_A_thunk_762d8 : Z := 0x770b0.  Definition tfib_E_thunk_762d8 : Z := 0x770b4.
Definition tfib_A_thunk_77ab0 : Z := 0x78888.  Definition tfib_E_thunk_77ab0 : Z := 0x7888c.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a2b4.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a370.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a370.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a448.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7a448.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7a6bc.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7a9e8.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7aa2c.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7aa2c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7adfc.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b0cc.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b184.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c4dc.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c4e0.
Definition tfib_A_lsan_register_root_region : Z := 0x7d0e8.  Definition tfib_E_lsan_register_root_region : Z := 0x7d418.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d418.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d8a0.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7d8a0.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7d8ac.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x80464.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x8047c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80800.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x8087c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x8087c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x8092c.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x8092c.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80944.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80944.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80a8c.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80a8c.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80a98.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80a98.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80aa4.
Definition tfib_A_main : Z := 0x80aa4.  Definition tfib_E_main : Z := 0x80d68.
Definition tfib_A_target_alloc_init : Z := 0x80d68.  Definition tfib_E_target_alloc_init : Z := 0x80d6c.
Definition tfib_A_target_alloc_count : Z := 0x80d6c.  Definition tfib_E_target_alloc_count : Z := 0x80d74.
Definition tfib_A_target_run : Z := 0x80d74.  Definition tfib_E_target_run : Z := 0x80efc.
Definition tfib_A_emit_printf : Z := 0x80efc.  Definition tfib_E_emit_printf : Z := 0x80f44.
Definition tfib_A_asan_module_ctor : Z := 0x845b0.  Definition tfib_E_asan_module_ctor : Z := 0x845e8.
Definition tfib_A_asan_module_dtor : Z := 0x845e8.  Definition tfib_E_asan_module_dtor : Z := 0x84618.
Definition tfib_A_extenddftf2 : Z := 0x89530.  Definition tfib_E_extenddftf2 : Z := 0x896c0.
Definition tfib_A_sysconf : Z := 0x8f310.  Definition tfib_E_sysconf : Z := 0x8f538.
Definition tfib_A_init : Z := 0x8f538.  Definition tfib_E_init : Z := 0x8f53c.
Definition tfib_A_init_libc : Z := 0x8f53c.  Definition tfib_E_init_libc : Z := 0x8f768.
Definition tfib_A_libc_start_init : Z := 0x8f768.  Definition tfib_E_libc_start_init : Z := 0x8f7b4.
Definition tfib_A_libc_start_main : Z := 0x8f7b4.  Definition tfib_E_libc_start_main : Z := 0x8f814.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8f814.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8f85c.
Definition tfib_A_init_tls : Z := 0x8f934.  Definition tfib_E_init_tls : Z := 0x8fbe4.
Definition tfib_A_init_ssp : Z := 0x8fbe4.  Definition tfib_E_init_ssp : Z := 0x8fc44.
Definition tfib_A_stack_chk_fail : Z := 0x8fc44.  Definition tfib_E_stack_chk_fail : Z := 0x8fc4c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8fc94.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8fd28.
Definition tfib_A_Exit : Z := 0x8fd28.  Definition tfib_E_Exit : Z := 0x8fd44.
Definition tfib_A_funcs_on_exit : Z := 0x8fd74.  Definition tfib_E_funcs_on_exit : Z := 0x8fe3c.
Definition tfib_A_fini_stub_ret : Z := 0x8fe3c.  Definition tfib_E_fini_stub_ret : Z := 0x8fe40.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8fe40.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8ff04.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x8ff04.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x8ff08.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8ff08.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8ff0c.
Definition tfib_A_libc_exit_fini : Z := 0x8ff0c.  Definition tfib_E_libc_exit_fini : Z := 0x8ff58.
Definition tfib_A_exit : Z := 0x8ff58.  Definition tfib_E_exit : Z := 0x8ffcc.
Definition tfib_A_open : Z := 0x901cc.  Definition tfib_E_open : Z := 0x902b0.
Definition tfib_A_syscall_ret : Z := 0x902b0.  Definition tfib_E_syscall_ret : Z := 0x902e8.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x902e8.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x90490.
Definition tfib_A_calloc : Z := 0x90a54.  Definition tfib_E_calloc : Z := 0x90b8c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x90b8c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x90b90.
Definition tfib_A_libc_free : Z := 0x90b90.  Definition tfib_E_libc_free : Z := 0x90d5c.
Definition tfib_A_get_meta : Z := 0x90d5c.  Definition tfib_E_get_meta : Z := 0x90e6c.
Definition tfib_A_alloc_meta : Z := 0x91244.  Definition tfib_E_alloc_meta : Z := 0x9151c.
Definition tfib_A_libc_malloc_impl : Z := 0x9151c.  Definition tfib_E_libc_malloc_impl : Z := 0x9188c.
Definition tfib_A_alloc_slot : Z := 0x9188c.  Definition tfib_E_alloc_slot : Z := 0x92130.
Definition tfib_A_enframe : Z := 0x92130.  Definition tfib_E_enframe : Z := 0x92280.
Definition tfib_A_malloc_allzerop : Z := 0x92280.  Definition tfib_E_malloc_allzerop : Z := 0x923f8.
Definition tfib_A_getrlimit : Z := 0x940a8.  Definition tfib_E_getrlimit : Z := 0x941a0.
Definition tfib_A_getrusage : Z := 0x941a0.  Definition tfib_E_getrusage : Z := 0x941c8.
Definition tfib_A_setrlimit : Z := 0x941c8.  Definition tfib_E_setrlimit : Z := 0x94290.
Definition tfib_A_mmap : Z := 0x946b8.  Definition tfib_E_mmap : Z := 0x947a4.
Definition tfib_A_mprotect : Z := 0x947a4.  Definition tfib_E_mprotect : Z := 0x947ec.
Definition tfib_A_munmap : Z := 0x948c0.  Definition tfib_E_munmap : Z := 0x94908.
Definition tfib_A_sched_yield : Z := 0x94bcc.  Definition tfib_E_sched_yield : Z := 0x94bf0.
Definition tfib_A_raise_tkill_path : Z := 0x94c4c.  Definition tfib_E_raise_tkill_path : Z := 0x94cc4.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x94cc4.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x94e98.
Definition tfib_A_musl_sigaltstack : Z := 0x94f90.  Definition tfib_E_musl_sigaltstack : Z := 0x9501c.
Definition tfib_A_fprintf : Z := 0x955f8.  Definition tfib_E_fprintf : Z := 0x9565c.
Definition tfib_A_lockfile : Z := 0x9565c.  Definition tfib_E_lockfile : Z := 0x95758.
Definition tfib_A_unlockfile : Z := 0x95758.  Definition tfib_E_unlockfile : Z := 0x957b8.
Definition tfib_A_stdio_read : Z := 0x95348.  Definition tfib_E_stdio_read : Z := 0x95460.
Definition tfib_A_stdio_write : Z := 0x95468.  Definition tfib_E_stdio_write : Z := 0x955f8.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x95318.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9531c.
Definition tfib_A_stdio_close : Z := 0x9531c.  Definition tfib_E_stdio_close : Z := 0x95348.
Definition tfib_A_fwritex : Z := 0x95bec.  Definition tfib_E_fwritex : Z := 0x95d24.
Definition tfib_A_musl_fwrite : Z := 0x95d24.  Definition tfib_E_musl_fwrite : Z := 0x95ddc.
Definition tfib_A_towrite : Z := 0x95ddc.  Definition tfib_E_towrite : Z := 0x95e30.
Definition tfib_A_stdio_exit : Z := 0x95a48.  Definition tfib_E_stdio_exit : Z := 0x95bec.
Definition tfib_A_ofl_lock : Z := 0x95e30.  Definition tfib_E_ofl_lock : Z := 0x95e60.
Definition tfib_A_musl_vfprintf : Z := 0x95fac.  Definition tfib_E_musl_vfprintf : Z := 0x9615c.
Definition tfib_A_printf_core : Z := 0x9615c.  Definition tfib_E_printf_core : Z := 0x96f8c.
Definition tfib_A_pop_arg : Z := 0x96f8c.  Definition tfib_E_pop_arg : Z := 0x970c0.
Definition tfib_A_pad : Z := 0x970c0.  Definition tfib_E_pad : Z := 0x97194.
Definition tfib_A_fmt_fp : Z := 0x97194.  Definition tfib_E_fmt_fp : Z := 0x9885c.
Definition tfib_A_thunk_931e0 : Z := 0x906a8.  Definition tfib_E_thunk_931e0 : Z := 0x906ac.
Definition tfib_A_musl_wctomb : Z := 0x94a34.  Definition tfib_E_musl_wctomb : Z := 0x94a58.
Definition tfib_A_musl_wcrtomb : Z := 0x94908.  Definition tfib_E_musl_wcrtomb : Z := 0x94a34.
Definition tfib_A_fpclassifyl : Z := 0x92c98.  Definition tfib_E_fpclassifyl : Z := 0x92cdc.
Definition tfib_A_letf2 : Z := 0x924d0.  Definition tfib_E_letf2 : Z := 0x92598.
Definition tfib_A_multf3 : Z := 0x92598.  Definition tfib_E_multf3 : Z := 0x92c98.
Definition tfib_A_floatsitf : Z := 0x934f4.  Definition tfib_E_floatsitf : Z := 0x935fc.
Definition tfib_A_scalbn : Z := 0x93f00.  Definition tfib_E_scalbn : Z := 0x93f98.
Definition tfib_A_subtf3 : Z := 0x934e4.  Definition tfib_E_subtf3 : Z := 0x934f4.
Definition tfib_A_addtf3 : Z := 0x92cdc.  Definition tfib_E_addtf3 : Z := 0x934a8.
Definition tfib_A_fe_getround : Z := 0x934a8.  Definition tfib_E_fe_getround : Z := 0x934d8.
Definition tfib_A_fixunstfsi : Z := 0x98864.  Definition tfib_E_fixunstfsi : Z := 0x988f8.
Definition tfib_A_floatunsitf : Z := 0x988f8.  Definition tfib_E_floatunsitf : Z := 0x989e4.
Definition tfib_A_fixtfsi : Z := 0x93f98.  Definition tfib_E_fixtfsi : Z := 0x94040.
Definition tfib_A_divtf3 : Z := 0x935fc.  Definition tfib_E_divtf3 : Z := 0x93f00.
Definition tfib_A_musl_vprintf : Z := 0x990bc.  Definition tfib_E_musl_vprintf : Z := 0x990d8.
Definition tfib_A_stdout_write : Z := 0x95e6c.  Definition tfib_E_stdout_write : Z := 0x95f0c.
Definition tfib_A_thunk_95368 : Z := 0x99670.  Definition tfib_E_thunk_95368 : Z := 0x99674.
Definition tfib_A_musl_memcmp : Z := 0x99740.  Definition tfib_E_musl_memcmp : Z := 0x99770.
Definition tfib_A_musl_memcpy : Z := 0x99770.  Definition tfib_E_musl_memcpy : Z := 0x99b74.
Definition tfib_A_musl_memset : Z := 0x99b74.  Definition tfib_E_musl_memset : Z := 0x99c6c.
Definition tfib_A_musl_strchr : Z := 0x99c6c.  Definition tfib_E_musl_strchr : Z := 0x99ca8.
Definition tfib_A_strchrnul : Z := 0x99ca8.  Definition tfib_E_strchrnul : Z := 0x99d88.
Definition tfib_A_musl_strlen : Z := 0x99dc0.  Definition tfib_E_musl_strlen : Z := 0x99e50.
Definition tfib_A_musl_strnlen : Z := 0x99ffc.  Definition tfib_E_musl_strnlen : Z := 0x9a040.
Definition tfib_A_musl_memchr : Z := 0x99674.  Definition tfib_E_musl_memchr : Z := 0x99740.
Definition tfib_A_lock : Z := 0x9a040.  Definition tfib_E_lock : Z := 0x9a2c8.
Definition tfib_A_unlock : Z := 0x9a2c8.  Definition tfib_E_unlock : Z := 0x9a33c.
Definition tfib_A_syscall_cp_c : Z := 0x9a33c.  Definition tfib_E_syscall_cp_c : Z := 0x9a360.
Definition tfib_A_syscall_cp_sccp : Z := 0x9a360.  Definition tfib_E_syscall_cp_sccp : Z := 0x9a364.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9a364.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9a388.
Definition tfib_A_pthread_atfork : Z := 0x9a3a0.  Definition tfib_E_pthread_atfork : Z := 0x9a444.
Definition tfib_A_mremap : Z := 0x947ec.  Definition tfib_E_mremap : Z := 0x948c0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9b418.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9b434.
Definition tfib_A_pthread_key_create : Z := 0x9b7c0.  Definition tfib_E_pthread_key_create : Z := 0x9b894.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9bb38.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x9bbdc.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x9bbdc.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x9bcf8.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9bcf8.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9bd24.
Definition tfib_A_pthread_setspecific : Z := 0x9bd5c.  Definition tfib_E_pthread_setspecific : Z := 0x9bd90.
Definition tfib_A_thunk_96f9c : Z := 0x9bd90.  Definition tfib_E_thunk_96f9c : Z := 0x9bd98.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9c6c4.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9c77c.
Definition tfib_A_close : Z := 0x9ed94.  Definition tfib_E_close : Z := 0x9ede8.
Definition tfib_A_musl_read : Z := 0x9ee74.  Definition tfib_E_musl_read : Z := 0x9eea8.
Definition tfib_A_set_thread_area : Z := 0x9bd98.  Definition tfib_E_set_thread_area : Z := 0x9bda4.
Definition tfib_A_vm_wait : Z := 0x9c3d4.  Definition tfib_E_vm_wait : Z := 0x9c424.
Definition tfib_D_str_sealed : Z := 0x11835.
Definition tfib_D_init_array_0_3 : Z := 0x9fea8.
Definition tfib_D_fini_array_0_1 : Z := 0x9fec8.
Definition tfib_D_GOT_common_flags : Z := 0xa0500.
Definition tfib_D_GOT_flags : Z := 0xa0508.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa0510.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa0518.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa0520.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa0528.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa1078.
Definition tfib_D_environ_musl : Z := 0xa11a0.
Definition tfib_D_REAL_read : Z := 0xa2248.
Definition tfib_D_REAL_memcpy : Z := 0xa2370.
Definition tfib_D_REAL_memset : Z := 0xa2378.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa5a58.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa68b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa90b8.
Definition tfib_D_asan_inited : Z := 0xa9d98.
Definition tfib_D_replace_intrin_cached : Z := 0xa9d99.
Definition tfib_D_kHighMemEnd : Z := 0xa9da0.
Definition tfib_D_kMidMemBeg : Z := 0xa9da8.
Definition tfib_D_kMidMemEnd : Z := 0xa9db0.
Definition tfib_D_malloc_context_size : Z := 0xa9dbc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13abe8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5fc2e0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30eac.
Definition tfib_at_rw_lo : Z := 0xa2000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x6441c.
Definition tfib_at_x_imemcpy : Z := 0x643a0.
Definition tfib_at_x_memset : Z := 0x99b74.
Definition tfib_at_x_memcpy : Z := 0x99770.
Definition tfib_at_x_memiszero : Z := 0x6494c.
Definition tfib_at_x_istrncpy : Z := 0x64848.
Definition tfib_at_x_sealed : Z := 0x11835.
Definition tfib_at_x_popfree : Z := 0x37298.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8f574.
Definition tfib_at_x_envscan_k : Z := 0x8f580.
Definition tfib_at_x_pnscan : Z := 0x8f638.
Definition tfib_at_x_pnscan_k : Z := 0x8f644.
Definition tfib_at_stops_more : list Z := (0x34f0c :: 0x36530 :: 0x54728 :: 0x5aae0 :: 0x5aaf4 :: 0x5ab08 :: 0x60498 :: 0x60568 :: 0x6da94 :: 0x6e9a0 :: 0x6eb30 :: 0x78888 :: nil)%list.
