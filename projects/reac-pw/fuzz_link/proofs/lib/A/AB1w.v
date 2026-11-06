(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to reac-pw/fuzz_link's ASan build. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22fac.
Definition tfib_text_lo : Z := 0x3126c.
Definition tfib_init_array_lo : Z := 0xa1340.  Definition tfib_init_array_hi : Z := 0xa1360.
Definition tfib_fini_array_lo : Z := 0xa1360.  Definition tfib_fini_array_hi : Z := 0xa1370.
Definition tfib_preinit_array_lo : Z := 0xa1370.
Definition tfib_data_rel_ro_lo : Z := 0xa1380.  Definition tfib_data_rel_ro_hi : Z := 0xa1970.
Definition tfib_got_lo : Z := 0xa1970.  Definition tfib_got_hi : Z := 0xa26c8.
Definition tfib_data_lo : Z := 0xa36c8.
Definition tfib_asan_globals_lo : Z := 0xa62a0.  Definition tfib_asan_globals_hi : Z := 0xa6d60.
Definition tfib_bss_lo : Z := 0xa6d80.  Definition tfib_bss_hi : Z := 0x6534f0.
Definition tfib_tbss_lo : Z := 0xa0340.  Definition tfib_tbss_hi : Z := 0xa0354.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := pcap_img_end.
Definition tfib_entry : Z := 0x3126c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x3126c.  Definition tfib_E_start : Z := 0x312b4.
Definition tfib_A_do_init : Z := 0x312b4.  Definition tfib_E_do_init : Z := 0x31328.
Definition tfib_A_do_fini : Z := 0x31328.  Definition tfib_E_do_fini : Z := 0x313b8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x313b8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x313f4.
Definition tfib_A_InitializeAllocator : Z := 0x31564.  Definition tfib_E_InitializeAllocator : Z := 0x3157c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3157c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x316e8.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31c44.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31da0.
Definition tfib_A_asan_free : Z := 0x32174.  Definition tfib_E_asan_free : Z := 0x3219c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3219c.  Definition tfib_E_Allocator_Deallocate : Z := 0x32454.
Definition tfib_A_asan_malloc : Z := 0x32454.  Definition tfib_E_asan_malloc : Z := 0x324b0.
Definition tfib_A_Allocator_Allocate : Z := 0x324b0.  Definition tfib_E_Allocator_Allocate : Z := 0x32e38.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x33650.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x33794.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x33880.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x338dc.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x338dc.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33b2c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33b2c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33c20.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x33c20.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33d08.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x3413c.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x34320.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x34320.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x344a4.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x345dc.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34860.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34860.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x349e0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x349e0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34ba8.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34ba8.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34d74.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34d74.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34e14.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34e14.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34f18.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35240.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35388.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x35388.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x353c0.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35b58.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35e40.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x36518.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36690.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36690.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36840.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36840.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x36a24.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x36a24.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36cfc.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36cfc.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x37174.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x37174.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x37274.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x37274.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x3757c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x3757c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x378ec.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x378ec.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x37a04.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37d0c.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37e08.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37e08.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37ef0.
Definition tfib_A_AsanActivate : Z := 0x37ef0.  Definition tfib_E_AsanActivate : Z := 0x37fcc.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x384a8.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x38590.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3d048.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3d120.
Definition tfib_A_FakeStack_Create : Z := 0x3d120.  Definition tfib_E_FakeStack_Create : Z := 0x3d20c.
Definition tfib_A_FakeStack_Allocate : Z := 0x3d4c8.  Definition tfib_E_FakeStack_Allocate : Z := 0x3d7b0.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d8e4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d914.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3da88.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3dc18.
Definition tfib_A_FakeStack_SetShadow : Z := 0x3e324.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3e460.
Definition tfib_A_asan_InitializeFlags : Z := 0x3e460.  Definition tfib_E_asan_InitializeFlags : Z := 0x3f48c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fb98.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x409b4.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x409b4.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40f80.
Definition tfib_A_asan_register_globals : Z := 0x40f80.  Definition tfib_E_asan_register_globals : Z := 0x40fec.
Definition tfib_A_asan_unregister_globals : Z := 0x40fec.  Definition tfib_E_asan_unregister_globals : Z := 0x41054.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x416d4.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x41944.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x41944.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x41c4c.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x423c0.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x42510.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x42f2c.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x43044.
Definition tfib_A_strlen : Z := 0x43044.  Definition tfib_E_strlen : Z := 0x43048.
Definition tfib_A_strnlen : Z := 0x43048.  Definition tfib_E_strnlen : Z := 0x4304c.
Definition tfib_A_strcmp : Z := 0x4304c.  Definition tfib_E_strcmp : Z := 0x43050.
Definition tfib_A_strchr : Z := 0x43054.  Definition tfib_E_strchr : Z := 0x43058.
Definition tfib_A_memcmp : Z := 0x43058.  Definition tfib_E_memcmp : Z := 0x4305c.
Definition tfib_A_memcmp_2 : Z := 0x4305c.  Definition tfib_E_memcmp_2 : Z := 0x43060.
Definition tfib_A_memchr : Z := 0x43060.  Definition tfib_E_memchr : Z := 0x43064.
Definition tfib_A_frexpl : Z := 0x43064.  Definition tfib_E_frexpl : Z := 0x43068.
Definition tfib_A_read : Z := 0x43068.  Definition tfib_E_read : Z := 0x4306c.
Definition tfib_A_fwrite : Z := 0x4306c.  Definition tfib_E_fwrite : Z := 0x43070.
Definition tfib_A_time : Z := 0x43070.  Definition tfib_E_time : Z := 0x43074.
Definition tfib_A_gmtime_r : Z := 0x43074.  Definition tfib_E_gmtime_r : Z := 0x43078.
Definition tfib_A_vprintf : Z := 0x43078.  Definition tfib_E_vprintf : Z := 0x4307c.
Definition tfib_A_vfprintf : Z := 0x4307c.  Definition tfib_E_vfprintf : Z := 0x43080.
Definition tfib_A_vsnprintf : Z := 0x43080.  Definition tfib_E_vsnprintf : Z := 0x43084.
Definition tfib_A_vfprintf_2 : Z := 0x43084.  Definition tfib_E_vfprintf_2 : Z := 0x43088.
Definition tfib_A_thunk_417bc : Z := 0x43088.  Definition tfib_E_thunk_417bc : Z := 0x4308c.
Definition tfib_A_clock_gettime : Z := 0x4308c.  Definition tfib_E_clock_gettime : Z := 0x43090.
Definition tfib_A_wcrtomb : Z := 0x43090.  Definition tfib_E_wcrtomb : Z := 0x43094.
Definition tfib_A_wctomb : Z := 0x43094.  Definition tfib_E_wctomb : Z := 0x43098.
Definition tfib_A_thunk_417cc : Z := 0x43098.  Definition tfib_E_thunk_417cc : Z := 0x430a0.
Definition tfib_A_pthread_attr_getstack : Z := 0x430a0.  Definition tfib_E_pthread_attr_getstack : Z := 0x430a4.
Definition tfib_A_tls_get_addr_thunk : Z := 0x430a4.  Definition tfib_E_tls_get_addr_thunk : Z := 0x430a8.
Definition tfib_A_thunk_417dc : Z := 0x430ac.  Definition tfib_E_thunk_417dc : Z := 0x430b0.
Definition tfib_A_thunk_417e4 : Z := 0x430b0.  Definition tfib_E_thunk_417e4 : Z := 0x430b4.
Definition tfib_A_thunk_417e8 : Z := 0x430b4.  Definition tfib_E_thunk_417e8 : Z := 0x430b8.
Definition tfib_A_thunk_417ec : Z := 0x430b8.  Definition tfib_E_thunk_417ec : Z := 0x430bc.
Definition tfib_A_thunk_417f0 : Z := 0x430bc.  Definition tfib_E_thunk_417f0 : Z := 0x430c0.
Definition tfib_A_sem_timedwait : Z := 0x430c0.  Definition tfib_E_sem_timedwait : Z := 0x430c4.
Definition tfib_A_thunk_417f8 : Z := 0x430c4.  Definition tfib_E_thunk_417f8 : Z := 0x430c8.
Definition tfib_A_pthread_setcancelstate : Z := 0x430c8.  Definition tfib_E_pthread_setcancelstate : Z := 0x430cc.
Definition tfib_A_send : Z := 0x430cc.  Definition tfib_E_send : Z := 0x430d0.
Definition tfib_A_sendto : Z := 0x430d0.  Definition tfib_E_sendto : Z := 0x430d4.
Definition tfib_A_sigaltstack : Z := 0x430d8.  Definition tfib_E_sigaltstack : Z := 0x430dc.
Definition tfib_A_thunk_4180c : Z := 0x430dc.  Definition tfib_E_thunk_4180c : Z := 0x430e0.
Definition tfib_A_icpt_strlen : Z := 0x430e0.  Definition tfib_E_icpt_strlen : Z := 0x43374.
Definition tfib_A_icpt_strnlen : Z := 0x43374.  Definition tfib_E_icpt_strnlen : Z := 0x43608.
Definition tfib_A_icpt_strcmp : Z := 0x4360c.  Definition tfib_E_icpt_strcmp : Z := 0x43b3c.
Definition tfib_A_icpt_strchr : Z := 0x44118.  Definition tfib_E_icpt_strchr : Z := 0x443f8.
Definition tfib_A_icpt_memcmp : Z := 0x44c90.  Definition tfib_E_icpt_memcmp : Z := 0x44d4c.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x44d4c.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x44e08.
Definition tfib_A_icpt_memchr : Z := 0x44e08.  Definition tfib_E_icpt_memchr : Z := 0x450d8.
Definition tfib_A_icpt_frexpl : Z := 0x450d8.  Definition tfib_E_icpt_frexpl : Z := 0x45350.
Definition tfib_A_icpt_read : Z := 0x45350.  Definition tfib_E_icpt_read : Z := 0x455c0.
Definition tfib_A_icpt_fwrite : Z := 0x455c0.  Definition tfib_E_icpt_fwrite : Z := 0x45834.
Definition tfib_A_icpt_time : Z := 0x45834.  Definition tfib_E_icpt_time : Z := 0x45ad0.
Definition tfib_A_icpt_gmtime_r : Z := 0x45cd8.  Definition tfib_E_icpt_gmtime_r : Z := 0x45f18.
Definition tfib_A_icpt_vprintf : Z := 0x45f18.  Definition tfib_E_icpt_vprintf : Z := 0x45fb4.
Definition tfib_A_printf_common_format_interceptor : Z := 0x45fb4.  Definition tfib_E_printf_common_format_interceptor : Z := 0x46a7c.
Definition tfib_A_icpt_vfprintf : Z := 0x46a7c.  Definition tfib_E_icpt_vfprintf : Z := 0x46b30.
Definition tfib_A_icpt_vsnprintf : Z := 0x46b30.  Definition tfib_E_icpt_vsnprintf : Z := 0x46e48.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x46e48.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x46f20.
Definition tfib_A_icpt_clock_gettime : Z := 0x46fc4.  Definition tfib_E_icpt_clock_gettime : Z := 0x4721c.
Definition tfib_A_icpt_wcrtomb : Z := 0x4721c.  Definition tfib_E_icpt_wcrtomb : Z := 0x4778c.
Definition tfib_A_icpt_wctomb : Z := 0x4778c.  Definition tfib_E_icpt_wctomb : Z := 0x47ae8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x47bb4.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x47f9c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x47fa8.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x48024.
Definition tfib_A_icpt_sem_timedwait : Z := 0x48280.  Definition tfib_E_icpt_sem_timedwait : Z := 0x48518.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x48548.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x48770.
Definition tfib_A_icpt_send : Z := 0x48770.  Definition tfib_E_icpt_send : Z := 0x48a24.
Definition tfib_A_icpt_sendto : Z := 0x48a24.  Definition tfib_E_icpt_sendto : Z := 0x48ce8.
Definition tfib_A_icpt_sigaltstack : Z := 0x48d18.  Definition tfib_E_icpt_sigaltstack : Z := 0x48f74.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x49048.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x491f8.
Definition tfib_A_icpt_diouxXn : Z := 0x491f8.  Definition tfib_E_icpt_diouxXn : Z := 0x49390.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x49f3c.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x52c14.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x52c14.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x52d70.
Definition tfib_A_memset : Z := 0x52d70.  Definition tfib_E_memset : Z := 0x52d74.
Definition tfib_A_memcpy : Z := 0x52d74.  Definition tfib_E_memcpy : Z := 0x52d78.
Definition tfib_A_asan_memcpy : Z := 0x52d78.  Definition tfib_E_asan_memcpy : Z := 0x53214.
Definition tfib_A_asan_memset : Z := 0x53214.  Definition tfib_E_asan_memset : Z := 0x53454.
Definition tfib_A_icpt_memset : Z := 0x53454.  Definition tfib_E_icpt_memset : Z := 0x53744.
Definition tfib_A_icpt_memcpy : Z := 0x53744.  Definition tfib_E_icpt_memcpy : Z := 0x53d34.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x53d34.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x53d6c.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x53d6c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x53d70.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x53d70.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x53d74.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x53d74.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x53dd4.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53e20.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53f5c.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x53f5c.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x53f60.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x53f60.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x540c8.
Definition tfib_A_free : Z := 0x540c8.  Definition tfib_E_free : Z := 0x540cc.
Definition tfib_A_malloc : Z := 0x540cc.  Definition tfib_E_malloc : Z := 0x540d0.
Definition tfib_A_icpt_free : Z := 0x540d4.  Definition tfib_E_icpt_free : Z := 0x542a4.
Definition tfib_A_icpt_malloc : Z := 0x542a4.  Definition tfib_E_icpt_malloc : Z := 0x54400.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x54400.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x544cc.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x54704.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x54708.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x54708.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x54808.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x54b30.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x54c9c.
Definition tfib_A_SetCanPoisonMemory : Z := 0x55184.  Definition tfib_E_SetCanPoisonMemory : Z := 0x55194.
Definition tfib_A_CanPoisonMemory : Z := 0x55194.  Definition tfib_E_CanPoisonMemory : Z := 0x551a8.
Definition tfib_A_PoisonShadow : Z := 0x551a8.  Definition tfib_E_PoisonShadow : Z := 0x556a4.
Definition tfib_A_MemToShadow_checked : Z := 0x556a4.  Definition tfib_E_MemToShadow_checked : Z := 0x557e0.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x557e0.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x55980.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x55980.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x55b00.
Definition tfib_A_asan_region_is_poisoned : Z := 0x55b30.  Definition tfib_E_asan_region_is_poisoned : Z := 0x55e74.
Definition tfib_A_AsanTSDInit : Z := 0x56294.  Definition tfib_E_AsanTSDInit : Z := 0x56310.
Definition tfib_A_AsanTSDGet : Z := 0x56310.  Definition tfib_E_AsanTSDGet : Z := 0x56350.
Definition tfib_A_AsanTSDSet : Z := 0x56350.  Definition tfib_E_AsanTSDSet : Z := 0x56390.
Definition tfib_A_PlatformTSDDtor : Z := 0x56390.  Definition tfib_E_PlatformTSDDtor : Z := 0x56414.
Definition tfib_A_InstallAtForkHandler : Z := 0x56414.  Definition tfib_E_InstallAtForkHandler : Z := 0x56430.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x56490.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x564d4.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x56bec.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x56df8.
Definition tfib_A_ReportDoubleFree : Z := 0x57500.  Definition tfib_E_ReportDoubleFree : Z := 0x57790.
Definition tfib_A_ReportGenericError : Z := 0x592bc.  Definition tfib_E_ReportGenericError : Z := 0x59b78.
Definition tfib_A_AsanInited : Z := 0x5a304.  Definition tfib_E_AsanInited : Z := 0x5a31c.
Definition tfib_A_asan_report_load1 : Z := 0x5a31c.  Definition tfib_E_asan_report_load1 : Z := 0x5a36c.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5a36c.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5a3bc.
Definition tfib_A_asan_report_load2 : Z := 0x5a3bc.  Definition tfib_E_asan_report_load2 : Z := 0x5a40c.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5a40c.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5a45c.
Definition tfib_A_asan_report_load4 : Z := 0x5a45c.  Definition tfib_E_asan_report_load4 : Z := 0x5a4ac.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5a4ac.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5a4fc.
Definition tfib_A_asan_report_load8 : Z := 0x5a4fc.  Definition tfib_E_asan_report_load8 : Z := 0x5a54c.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5a54c.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5a59c.
Definition tfib_A_asan_report_load16 : Z := 0x5a59c.  Definition tfib_E_asan_report_load16 : Z := 0x5a5ec.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5a5ec.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5a63c.
Definition tfib_A_asan_report_store1 : Z := 0x5a63c.  Definition tfib_E_asan_report_store1 : Z := 0x5a68c.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5a68c.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5a6dc.
Definition tfib_A_asan_report_store2 : Z := 0x5a6dc.  Definition tfib_E_asan_report_store2 : Z := 0x5a72c.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5a72c.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5a77c.
Definition tfib_A_asan_report_store4 : Z := 0x5a77c.  Definition tfib_E_asan_report_store4 : Z := 0x5a7cc.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5a7cc.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5a81c.
Definition tfib_A_asan_report_store8 : Z := 0x5a81c.  Definition tfib_E_asan_report_store8 : Z := 0x5a86c.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5a86c.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5a8bc.
Definition tfib_A_asan_report_store16 : Z := 0x5a8bc.  Definition tfib_E_asan_report_store16 : Z := 0x5a90c.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5a90c.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5a95c.
Definition tfib_A_asan_report_load_n : Z := 0x5a95c.  Definition tfib_E_asan_report_load_n : Z := 0x5a9ac.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5a9ac.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5a9fc.
Definition tfib_A_asan_report_store_n : Z := 0x5a9fc.  Definition tfib_E_asan_report_store_n : Z := 0x5aa4c.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5aa4c.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5aa9c.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5aa9c.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5ab1c.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5ab1c.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5aed0.
Definition tfib_A_AsanInitInternal : Z := 0x5af60.  Definition tfib_E_AsanInitInternal : Z := 0x5b214.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5b214.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5b2b4.
Definition tfib_A_thunk_59674 : Z := 0x5b47c.  Definition tfib_E_thunk_59674 : Z := 0x5b480.
Definition tfib_A_asan_init : Z := 0x5b480.  Definition tfib_E_asan_init : Z := 0x5b514.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5b514.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5b518.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5b518.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5b57c.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5b6f0.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5b6f8.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5b77c.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5baa4.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5baa4.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5bc84.
Definition tfib_A_InitializeShadowMemory : Z := 0x5bc84.  Definition tfib_E_InitializeShadowMemory : Z := 0x5bf8c.
Definition tfib_A_SetMallocContextSize : Z := 0x5bf8c.  Definition tfib_E_SetMallocContextSize : Z := 0x5bf9c.
Definition tfib_A_GetMallocContextSize : Z := 0x5bf9c.  Definition tfib_E_GetMallocContextSize : Z := 0x5bfac.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5bfac.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5c0fc.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5c4dc.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5c77c.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5cbe0.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5cc18.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5cec0.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5cecc.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5cecc.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5cf58.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5cf58.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5cfc0.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5cfc0.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5d038.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5d038.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5d0a0.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5d0a0.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5d1ec.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5d478.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5d484.
Definition tfib_A_AsanThread_Create : Z := 0x5d604.  Definition tfib_E_AsanThread_Create : Z := 0x5d7a0.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5d7fc.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5da14.
Definition tfib_A_GetCurrentThread : Z := 0x5da14.  Definition tfib_E_GetCurrentThread : Z := 0x5da34.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5da34.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5dbd8.
Definition tfib_A_AsanThread_stack_top : Z := 0x5dbd8.  Definition tfib_E_AsanThread_stack_top : Z := 0x5dc30.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5dc30.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5dc88.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5dc88.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5deb8.
Definition tfib_A_AsanThread_Init : Z := 0x5deb8.  Definition tfib_E_AsanThread_Init : Z := 0x5e2ac.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5e2ac.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5e3b8.
Definition tfib_A_CreateMainThread : Z := 0x5e3ec.  Definition tfib_E_CreateMainThread : Z := 0x5e4fc.
Definition tfib_A_SetCurrentThread : Z := 0x5e4fc.  Definition tfib_E_SetCurrentThread : Z := 0x5e5dc.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5e7e0.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5e91c.
Definition tfib_A_weak_default_hook_ret : Z := 0x5f5f0.  Definition tfib_E_weak_default_hook_ret : Z := 0x5f5f4.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5f5fc.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5f83c.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5fa90.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5fbe8.
Definition tfib_A_internal_allocator_getter : Z := 0x5fee8.  Definition tfib_E_internal_allocator_getter : Z := 0x5fef4.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5fef4.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x60040.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x60040.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x6008c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x6008c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x60098.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x600c8.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x600d4.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x600d4.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x600e0.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x600e0.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x600f0.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x600fc.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x603c8.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x603c8.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x60788.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x616e4.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x616f0.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x616f0.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x617c8.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x617c8.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x61864.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x61d88.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x61dcc.
Definition tfib_A_IncreaseTotalMmap : Z := 0x61dcc.  Definition tfib_E_IncreaseTotalMmap : Z := 0x61df0.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x62044.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x62158.
Definition tfib_A_RunMallocHooks : Z := 0x622fc.  Definition tfib_E_RunMallocHooks : Z := 0x623b4.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x623b4.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x623b8.
Definition tfib_A_RunFreeHooks : Z := 0x623b8.  Definition tfib_E_RunFreeHooks : Z := 0x62464.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x62464.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x6246c.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x6246c.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x62470.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x62498.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x624e4.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x627a8.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x629e8.
Definition tfib_A_sanitizer_set_report_path : Z := 0x62fe4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x62ffc.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x62ffc.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x63140.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x63140.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x63148.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x63490.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x64734.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x64734.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x64758.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x64c0c.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x64f1c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x64f1c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x65060.
Definition tfib_A_FlagParser_ParseString : Z := 0x65060.  Definition tfib_E_FlagParser_ParseString : Z := 0x65154.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x652e8.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x65348.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x65348.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x65388.
Definition tfib_A_internal_atoll : Z := 0x65388.  Definition tfib_E_internal_atoll : Z := 0x65474.
Definition tfib_A_internal_simple_strtoll : Z := 0x65474.  Definition tfib_E_internal_simple_strtoll : Z := 0x655d0.
Definition tfib_A_internal_memchr : Z := 0x655d0.  Definition tfib_E_internal_memchr : Z := 0x655f0.
Definition tfib_A_internal_memcmp : Z := 0x655f0.  Definition tfib_E_internal_memcmp : Z := 0x65628.
Definition tfib_A_internal_memcpy : Z := 0x65628.  Definition tfib_E_internal_memcpy : Z := 0x6564c.
Definition tfib_A_internal_memmove : Z := 0x6564c.  Definition tfib_E_internal_memmove : Z := 0x656a4.
Definition tfib_A_internal_memset : Z := 0x656a4.  Definition tfib_E_internal_memset : Z := 0x65704.
Definition tfib_A_internal_strcspn : Z := 0x65704.  Definition tfib_E_internal_strcspn : Z := 0x65758.
Definition tfib_A_internal_strcmp : Z := 0x65758.  Definition tfib_E_internal_strcmp : Z := 0x6578c.
Definition tfib_A_internal_strdup : Z := 0x6578c.  Definition tfib_E_internal_strdup : Z := 0x657f8.
Definition tfib_A_internal_strlen : Z := 0x657f8.  Definition tfib_E_internal_strlen : Z := 0x65814.
Definition tfib_A_internal_strncmp : Z := 0x65814.  Definition tfib_E_internal_strncmp : Z := 0x65858.
Definition tfib_A_internal_strchr : Z := 0x65858.  Definition tfib_E_internal_strchr : Z := 0x658a4.
Definition tfib_A_internal_strchrnul : Z := 0x658a4.  Definition tfib_E_internal_strchrnul : Z := 0x658ec.
Definition tfib_A_internal_strrchr : Z := 0x658ec.  Definition tfib_E_internal_strrchr : Z := 0x6592c.
Definition tfib_A_internal_strnlen : Z := 0x65a5c.  Definition tfib_E_internal_strnlen : Z := 0x65a8c.
Definition tfib_A_internal_strncpy : Z := 0x65ad0.  Definition tfib_E_internal_strncpy : Z := 0x65b40.
Definition tfib_A_internal_strstr : Z := 0x65b40.  Definition tfib_E_internal_strstr : Z := 0x65bd4.
Definition tfib_A_mem_is_zero : Z := 0x65bd4.  Definition tfib_E_mem_is_zero : Z := 0x65c88.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x65c88.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x65c98.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x65c98.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x65e78.
Definition tfib_A_internal_iserror : Z := 0x65e84.  Definition tfib_E_internal_iserror : Z := 0x65ea4.
Definition tfib_A_internal_mmap : Z := 0x65ea4.  Definition tfib_E_internal_mmap : Z := 0x65eb0.
Definition tfib_A_internal_munmap : Z := 0x65eb0.  Definition tfib_E_internal_munmap : Z := 0x65ebc.
Definition tfib_A_internal_mprotect : Z := 0x65ebc.  Definition tfib_E_internal_mprotect : Z := 0x65ecc.
Definition tfib_A_internal_madvise : Z := 0x65ecc.  Definition tfib_E_internal_madvise : Z := 0x65ef8.
Definition tfib_A_internal_close : Z := 0x65ef8.  Definition tfib_E_internal_close : Z := 0x65f04.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x65f04.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x65f28.
Definition tfib_A_internal_read : Z := 0x65f28.  Definition tfib_E_internal_read : Z := 0x65f60.
Definition tfib_A_internal_write : Z := 0x65f60.  Definition tfib_E_internal_write : Z := 0x65f98.
Definition tfib_A_internal_ftruncate : Z := 0x65f98.  Definition tfib_E_internal_ftruncate : Z := 0x65fd0.
Definition tfib_A_internal_dup : Z := 0x65fd0.  Definition tfib_E_internal_dup : Z := 0x65fdc.
Definition tfib_A_internal_dup2_dup3 : Z := 0x65fdc.  Definition tfib_E_internal_dup2_dup3 : Z := 0x65fec.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x65fec.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x66004.
Definition tfib_A_internal_sched_yield : Z := 0x66004.  Definition tfib_E_internal_sched_yield : Z := 0x66010.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x66010.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x6605c.
Definition tfib_A_internal_execve : Z := 0x6605c.  Definition tfib_E_internal_execve : Z := 0x66068.
Definition tfib_A_internal_exit_exit_group : Z := 0x66068.  Definition tfib_E_internal_exit_exit_group : Z := 0x6607c.
Definition tfib_A_FileExists_newfstatat : Z := 0x6607c.  Definition tfib_E_FileExists_newfstatat : Z := 0x660fc.
Definition tfib_A_DirExists_newfstatat : Z := 0x660fc.  Definition tfib_E_DirExists_newfstatat : Z := 0x66160.
Definition tfib_A_GetTid_gettid : Z := 0x66160.  Definition tfib_E_GetTid_gettid : Z := 0x6616c.
Definition tfib_A_GetEnv : Z := 0x6616c.  Definition tfib_E_GetEnv : Z := 0x6629c.
Definition tfib_A_FutexWait : Z := 0x663a0.  Definition tfib_E_FutexWait : Z := 0x663c4.
Definition tfib_A_FutexWake : Z := 0x663c4.  Definition tfib_E_FutexWake : Z := 0x663e8.
Definition tfib_A_internal_ptrace : Z := 0x663e8.  Definition tfib_E_internal_ptrace : Z := 0x663f4.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x663f4.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x66404.
Definition tfib_A_internal_getpid : Z := 0x66404.  Definition tfib_E_internal_getpid : Z := 0x66410.
Definition tfib_A_internal_getppid : Z := 0x66410.  Definition tfib_E_internal_getppid : Z := 0x6641c.
Definition tfib_A_internal_prctl : Z := 0x6641c.  Definition tfib_E_internal_prctl : Z := 0x66428.
Definition tfib_A_internal_sigaltstack : Z := 0x66428.  Definition tfib_E_internal_sigaltstack : Z := 0x66434.
Definition tfib_A_internal_fork_clone : Z := 0x66434.  Definition tfib_E_internal_fork_clone : Z := 0x6644c.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6644c.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x66578.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x66750.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x66b4c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x66cb8.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x66dd0.
Definition tfib_A_GetPageSizeCached : Z := 0x66dd0.  Definition tfib_E_GetPageSizeCached : Z := 0x66dd8.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x66dd8.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x66e84.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x66e84.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x66fa4.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x6706c.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x670ec.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x670ec.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x67148.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x67148.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x67214.
Definition tfib_A_thunk_653ec : Z := 0x67310.  Definition tfib_E_thunk_653ec : Z := 0x67314.
Definition tfib_A_CheckASLR : Z := 0x67314.  Definition tfib_E_CheckASLR : Z := 0x67318.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x67564.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x67568.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x67568.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x67574.
Definition tfib_A_MmapOrDie : Z := 0x67574.  Definition tfib_E_MmapOrDie : Z := 0x67680.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x67680.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x676f4.
Definition tfib_A_UnmapOrDie : Z := 0x676f4.  Definition tfib_E_UnmapOrDie : Z := 0x67770.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x67770.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x67880.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x67aac.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x67bb0.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x67bb0.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x67bbc.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x67bbc.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x67d34.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x67d34.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x67d40.
Definition tfib_A_thunk_66008 : Z := 0x67f2c.  Definition tfib_E_thunk_66008 : Z := 0x67f30.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x68250.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6845c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x68a14.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x68a20.
Definition tfib_A_Printf : Z := 0x68a24.  Definition tfib_E_Printf : Z := 0x68a70.
Definition tfib_A_SharedPrintfCode : Z := 0x68a70.  Definition tfib_E_SharedPrintfCode : Z := 0x68acc.
Definition tfib_A_Report : Z := 0x68acc.  Definition tfib_E_Report : Z := 0x68b18.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6a610.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6a66c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6a66c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6a8a8.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6a8a8.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6abcc.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b16c.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6b23c.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6b23c.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6b58c.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6b58c.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6b59c.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6b7d8.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6b81c.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6b81c.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6b87c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6b87c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6bcf4.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6c5b4.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6c8d8.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6c8e0.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6c9e4.
Definition tfib_A_AddDieCallback : Z := 0x6d194.  Definition tfib_E_AddDieCallback : Z := 0x6d21c.
Definition tfib_A_Die : Z := 0x6d2e0.  Definition tfib_E_Die : Z := 0x6d3a0.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6d3a0.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6d3ac.
Definition tfib_A_CheckFailed : Z := 0x6d3ac.  Definition tfib_E_CheckFailed : Z := 0x6d464.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6dabc.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6dbb4.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6dbb4.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6dce0.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6df08.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6df84.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6dfb8.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6e2a0.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6e2a0.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6e2a4.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6e2a4.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6e694.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6e694.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6e764.
Definition tfib_A_AndroidLogInit : Z := 0x6eb48.  Definition tfib_E_AndroidLogInit : Z := 0x6eb4c.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6eb7c.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6ebc4.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ebc4.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ee10.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6ee10.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6ee14.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6ee14.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6ef20.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6ef20.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6f024.
Definition tfib_A_thunk_6d37c : Z := 0x6f2a0.  Definition tfib_E_thunk_6d37c : Z := 0x6f2a4.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6f348.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6f368.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6f368.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6f408.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6f454.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6f458.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6f494.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6f558.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6f558.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6f5e0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6f5e0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6f658.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6f658.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6f73c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6f7f8.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6f92c.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6fb64.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6fc94.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6fc94.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6fcf4.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6fcf4.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6fdc0.
Definition tfib_A_MprotectNoAccess : Z := 0x6fdd4.  Definition tfib_E_MprotectNoAccess : Z := 0x6fdf4.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6fdf4.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6ff40.
Definition tfib_A_MmapFixedOrDie : Z := 0x6ff40.  Definition tfib_E_MmapFixedOrDie : Z := 0x6ff50.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x71748.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x7178c.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x7178c.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x717bc.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x71bf0.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x71d14.
Definition tfib_A_StackStore_Alloc : Z := 0x71d14.  Definition tfib_E_StackStore_Alloc : Z := 0x71e48.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x726fc.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x727b0.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x73f04.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x73f60.
Definition tfib_A_StackDepotPut : Z := 0x741ec.  Definition tfib_E_StackDepotPut : Z := 0x7420c.
Definition tfib_A_StackDepotBase_Put : Z := 0x7420c.  Definition tfib_E_StackDepotBase_Put : Z := 0x74490.
Definition tfib_A_StackDepotBase_Get : Z := 0x74490.  Definition tfib_E_StackDepotBase_Get : Z := 0x745a0.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x74980.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x74a10.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x74a10.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x74b10.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x74b70.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x74b78.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x74b78.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x74cd8.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x74cd8.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x74d4c.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x751d4.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x752ec.
Definition tfib_A_thunk_762d8 : Z := 0x78338.  Definition tfib_E_thunk_762d8 : Z := 0x7833c.
Definition tfib_A_thunk_77ab0 : Z := 0x79b10.  Definition tfib_E_thunk_77ab0 : Z := 0x79b14.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7b53c.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7b5f8.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7b5f8.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7b6d0.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7b6d0.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7b944.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7bc70.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7bcb4.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7bcb4.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7c084.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7c354.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7c40c.
Definition tfib_A_thunk_7b6f8 : Z := 0x7d764.  Definition tfib_E_thunk_7b6f8 : Z := 0x7d768.
Definition tfib_A_lsan_register_root_region : Z := 0x7e370.  Definition tfib_E_lsan_register_root_region : Z := 0x7e6a0.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7e6a0.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7eb28.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7eb28.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7eb34.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x816ec.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x81704.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x81a88.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x81b04.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x81b04.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x81bb4.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x81bb4.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x81bcc.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x81bcc.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x81d14.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x81d14.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x81d20.
Definition tfib_A_asan_default_options_cli_c : Z := 0x81d20.  Definition tfib_E_asan_default_options_cli_c : Z := 0x81d2c.
Definition tfib_A_main : Z := 0x81d2c.  Definition tfib_E_main : Z := 0x81ff0.
Definition tfib_A_target_alloc_init : Z := 0x81ff0.  Definition tfib_E_target_alloc_init : Z := 0x81ff4.
Definition tfib_A_target_alloc_count : Z := 0x81ff4.  Definition tfib_E_target_alloc_count : Z := 0x81ffc.
Definition tfib_A_target_run : Z := 0x81ffc.  Definition tfib_E_target_run : Z := 0x82184.
Definition tfib_A_emit_printf : Z := 0x82184.  Definition tfib_E_emit_printf : Z := 0x821cc.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x827d4.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83d30.
Definition tfib_A_asan_module_ctor : Z := 0x88614.  Definition tfib_E_asan_module_ctor : Z := 0x8864c.
Definition tfib_A_asan_module_dtor : Z := 0x8864c.  Definition tfib_E_asan_module_dtor : Z := 0x8867c.
Definition tfib_A_extenddftf2 : Z := 0x8a360.  Definition tfib_E_extenddftf2 : Z := 0x8a4f0.
Definition tfib_A_sysconf : Z := 0x90140.  Definition tfib_E_sysconf : Z := 0x90368.
Definition tfib_A_init : Z := 0x90368.  Definition tfib_E_init : Z := 0x9036c.
Definition tfib_A_init_libc : Z := 0x9036c.  Definition tfib_E_init_libc : Z := 0x90598.
Definition tfib_A_libc_start_init : Z := 0x90598.  Definition tfib_E_libc_start_init : Z := 0x905e4.
Definition tfib_A_libc_start_main : Z := 0x905e4.  Definition tfib_E_libc_start_main : Z := 0x90644.
Definition tfib_A_libc_start_main_stage2 : Z := 0x90644.  Definition tfib_E_libc_start_main_stage2 : Z := 0x9068c.
Definition tfib_A_init_tls : Z := 0x90764.  Definition tfib_E_init_tls : Z := 0x90a14.
Definition tfib_A_init_ssp : Z := 0x90a14.  Definition tfib_E_init_ssp : Z := 0x90a74.
Definition tfib_A_stack_chk_fail : Z := 0x90a74.  Definition tfib_E_stack_chk_fail : Z := 0x90a7c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x90ac4.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x90b58.
Definition tfib_A_Exit : Z := 0x90b58.  Definition tfib_E_Exit : Z := 0x90b74.
Definition tfib_A_funcs_on_exit : Z := 0x90ba4.  Definition tfib_E_funcs_on_exit : Z := 0x90c6c.
Definition tfib_A_fini_stub_ret : Z := 0x90c6c.  Definition tfib_E_fini_stub_ret : Z := 0x90c70.
Definition tfib_A_cxa_atexit_atexit : Z := 0x90c70.  Definition tfib_E_cxa_atexit_atexit : Z := 0x90d34.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x90d34.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x90d38.
Definition tfib_A_musl_exit_helper_stub : Z := 0x90d38.  Definition tfib_E_musl_exit_helper_stub : Z := 0x90d3c.
Definition tfib_A_libc_exit_fini : Z := 0x90d3c.  Definition tfib_E_libc_exit_fini : Z := 0x90d88.
Definition tfib_A_exit : Z := 0x90d88.  Definition tfib_E_exit : Z := 0x90dfc.
Definition tfib_A_open : Z := 0x90ffc.  Definition tfib_E_open : Z := 0x910e0.
Definition tfib_A_syscall_ret : Z := 0x910e0.  Definition tfib_E_syscall_ret : Z := 0x91118.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x91118.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x912c0.
Definition tfib_A_calloc : Z := 0x91884.  Definition tfib_E_calloc : Z := 0x919bc.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x919bc.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x919c0.
Definition tfib_A_libc_free : Z := 0x919c0.  Definition tfib_E_libc_free : Z := 0x91b8c.
Definition tfib_A_get_meta : Z := 0x91b8c.  Definition tfib_E_get_meta : Z := 0x91c9c.
Definition tfib_A_alloc_meta : Z := 0x92074.  Definition tfib_E_alloc_meta : Z := 0x9234c.
Definition tfib_A_libc_malloc_impl : Z := 0x9234c.  Definition tfib_E_libc_malloc_impl : Z := 0x926bc.
Definition tfib_A_alloc_slot : Z := 0x926bc.  Definition tfib_E_alloc_slot : Z := 0x92f60.
Definition tfib_A_enframe : Z := 0x92f60.  Definition tfib_E_enframe : Z := 0x930b0.
Definition tfib_A_malloc_allzerop : Z := 0x930b0.  Definition tfib_E_malloc_allzerop : Z := 0x93228.
Definition tfib_A_getrlimit : Z := 0x94ed8.  Definition tfib_E_getrlimit : Z := 0x94fd0.
Definition tfib_A_getrusage : Z := 0x94fd0.  Definition tfib_E_getrusage : Z := 0x94ff8.
Definition tfib_A_setrlimit : Z := 0x94ff8.  Definition tfib_E_setrlimit : Z := 0x950c0.
Definition tfib_A_mmap : Z := 0x954e8.  Definition tfib_E_mmap : Z := 0x955d4.
Definition tfib_A_mprotect : Z := 0x955d4.  Definition tfib_E_mprotect : Z := 0x9561c.
Definition tfib_A_munmap : Z := 0x956f0.  Definition tfib_E_munmap : Z := 0x95738.
Definition tfib_A_sched_yield : Z := 0x959fc.  Definition tfib_E_sched_yield : Z := 0x95a20.
Definition tfib_A_raise_tkill_path : Z := 0x95a7c.  Definition tfib_E_raise_tkill_path : Z := 0x95af4.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x95af4.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x95cc8.
Definition tfib_A_musl_sigaltstack : Z := 0x95dc0.  Definition tfib_E_musl_sigaltstack : Z := 0x95e4c.
Definition tfib_A_fprintf : Z := 0x96428.  Definition tfib_E_fprintf : Z := 0x9648c.
Definition tfib_A_lockfile : Z := 0x9648c.  Definition tfib_E_lockfile : Z := 0x96588.
Definition tfib_A_unlockfile : Z := 0x96588.  Definition tfib_E_unlockfile : Z := 0x965e8.
Definition tfib_A_stdio_read : Z := 0x96178.  Definition tfib_E_stdio_read : Z := 0x96290.
Definition tfib_A_stdio_write : Z := 0x96298.  Definition tfib_E_stdio_write : Z := 0x96428.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x96148.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9614c.
Definition tfib_A_stdio_close : Z := 0x9614c.  Definition tfib_E_stdio_close : Z := 0x96178.
Definition tfib_A_fwritex : Z := 0x96f50.  Definition tfib_E_fwritex : Z := 0x97088.
Definition tfib_A_musl_fwrite : Z := 0x97088.  Definition tfib_E_musl_fwrite : Z := 0x97140.
Definition tfib_A_towrite : Z := 0x97140.  Definition tfib_E_towrite : Z := 0x97194.
Definition tfib_A_stdio_exit : Z := 0x96878.  Definition tfib_E_stdio_exit : Z := 0x96a1c.
Definition tfib_A_ofl_lock : Z := 0x97194.  Definition tfib_E_ofl_lock : Z := 0x971c4.
Definition tfib_A_ofl_add : Z := 0x971d0.  Definition tfib_E_ofl_add : Z := 0x97210.
Definition tfib_A_musl_vfprintf : Z := 0x973e0.  Definition tfib_E_musl_vfprintf : Z := 0x97590.
Definition tfib_A_printf_core : Z := 0x97590.  Definition tfib_E_printf_core : Z := 0x983c0.
Definition tfib_A_pop_arg : Z := 0x983c0.  Definition tfib_E_pop_arg : Z := 0x984f4.
Definition tfib_A_pad : Z := 0x984f4.  Definition tfib_E_pad : Z := 0x985c8.
Definition tfib_A_fmt_fp : Z := 0x985c8.  Definition tfib_E_fmt_fp : Z := 0x99c90.
Definition tfib_A_thunk_931e0 : Z := 0x914d8.  Definition tfib_E_thunk_931e0 : Z := 0x914dc.
Definition tfib_A_musl_wctomb : Z := 0x95864.  Definition tfib_E_musl_wctomb : Z := 0x95888.
Definition tfib_A_musl_wcrtomb : Z := 0x95738.  Definition tfib_E_musl_wcrtomb : Z := 0x95864.
Definition tfib_A_fpclassifyl : Z := 0x93ac8.  Definition tfib_E_fpclassifyl : Z := 0x93b0c.
Definition tfib_A_letf2 : Z := 0x93300.  Definition tfib_E_letf2 : Z := 0x933c8.
Definition tfib_A_multf3 : Z := 0x933c8.  Definition tfib_E_multf3 : Z := 0x93ac8.
Definition tfib_A_floatsitf : Z := 0x94324.  Definition tfib_E_floatsitf : Z := 0x9442c.
Definition tfib_A_scalbn : Z := 0x94d30.  Definition tfib_E_scalbn : Z := 0x94dc8.
Definition tfib_A_subtf3 : Z := 0x94314.  Definition tfib_E_subtf3 : Z := 0x94324.
Definition tfib_A_addtf3 : Z := 0x93b0c.  Definition tfib_E_addtf3 : Z := 0x942d8.
Definition tfib_A_fe_getround : Z := 0x942d8.  Definition tfib_E_fe_getround : Z := 0x94308.
Definition tfib_A_fixunstfsi : Z := 0x99c98.  Definition tfib_E_fixunstfsi : Z := 0x99d2c.
Definition tfib_A_floatunsitf : Z := 0x99d2c.  Definition tfib_E_floatunsitf : Z := 0x99e18.
Definition tfib_A_fixtfsi : Z := 0x94dc8.  Definition tfib_E_fixtfsi : Z := 0x94e70.
Definition tfib_A_divtf3 : Z := 0x9442c.  Definition tfib_E_divtf3 : Z := 0x94d30.
Definition tfib_A_musl_vprintf : Z := 0x9a4f0.  Definition tfib_E_musl_vprintf : Z := 0x9a50c.
Definition tfib_A_stdout_write : Z := 0x972a0.  Definition tfib_E_stdout_write : Z := 0x97340.
Definition tfib_A_thunk_95368 : Z := 0x9aaa4.  Definition tfib_E_thunk_95368 : Z := 0x9aaa8.
Definition tfib_A_musl_memcmp : Z := 0x9ab74.  Definition tfib_E_musl_memcmp : Z := 0x9aba4.
Definition tfib_A_musl_memcpy : Z := 0x9aba4.  Definition tfib_E_musl_memcpy : Z := 0x9afa8.
Definition tfib_A_musl_memset : Z := 0x9afa8.  Definition tfib_E_musl_memset : Z := 0x9b0a0.
Definition tfib_A_musl_strchr : Z := 0x9b0a0.  Definition tfib_E_musl_strchr : Z := 0x9b0dc.
Definition tfib_A_strchrnul : Z := 0x9b0dc.  Definition tfib_E_strchrnul : Z := 0x9b1bc.
Definition tfib_A_musl_strlen : Z := 0x9b1f4.  Definition tfib_E_musl_strlen : Z := 0x9b284.
Definition tfib_A_musl_strnlen : Z := 0x9b490.  Definition tfib_E_musl_strnlen : Z := 0x9b4d4.
Definition tfib_A_musl_memchr : Z := 0x9aaa8.  Definition tfib_E_musl_memchr : Z := 0x9ab74.
Definition tfib_A_lock : Z := 0x9b4d4.  Definition tfib_E_lock : Z := 0x9b75c.
Definition tfib_A_unlock : Z := 0x9b75c.  Definition tfib_E_unlock : Z := 0x9b7d0.
Definition tfib_A_syscall_cp_c : Z := 0x9b7d0.  Definition tfib_E_syscall_cp_c : Z := 0x9b7f4.
Definition tfib_A_syscall_cp_sccp : Z := 0x9b7f4.  Definition tfib_E_syscall_cp_sccp : Z := 0x9b7f8.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9b7f8.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9b81c.
Definition tfib_A_pthread_atfork : Z := 0x9b834.  Definition tfib_E_pthread_atfork : Z := 0x9b8d8.
Definition tfib_A_mremap : Z := 0x9561c.  Definition tfib_E_mremap : Z := 0x956f0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9c8ac.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9c8c8.
Definition tfib_A_pthread_key_create : Z := 0x9cc54.  Definition tfib_E_pthread_key_create : Z := 0x9cd28.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9cfcc.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x9d070.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x9d070.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x9d18c.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9d18c.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9d1b8.
Definition tfib_A_pthread_setspecific : Z := 0x9d1f0.  Definition tfib_E_pthread_setspecific : Z := 0x9d224.
Definition tfib_A_set_thread_area : Z := 0x9d22c.  Definition tfib_E_set_thread_area : Z := 0x9d238.
Definition tfib_A_thunk_96f9c : Z := 0x9d224.  Definition tfib_E_thunk_96f9c : Z := 0x9d22c.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9db58.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9dc10.
Definition tfib_A_close : Z := 0xa0228.  Definition tfib_E_close : Z := 0xa027c.
Definition tfib_A_musl_read : Z := 0xa0308.  Definition tfib_E_musl_read : Z := 0xa033c.
Definition tfib_A_vm_wait : Z := 0x9d868.  Definition tfib_E_vm_wait : Z := 0x9d8b8.
Definition tfib_D_str_sealed : Z := 0x11836.
Definition tfib_D_init_array_0_3 : Z := 0xa1340.
Definition tfib_D_fini_array_0_1 : Z := 0xa1360.
Definition tfib_D_GOT_common_flags : Z := 0xa19c0.
Definition tfib_D_GOT_flags : Z := 0xa19c8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa19d0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa19d8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa19e0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa19e8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa2538.
Definition tfib_D_environ_musl : Z := 0xa2660.
Definition tfib_D_REAL_read : Z := 0xa3710.
Definition tfib_D_REAL_memcpy : Z := 0xa3848.
Definition tfib_D_REAL_memset : Z := 0xa3850.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa6dd8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa7c38.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xaa438.
Definition tfib_D_asan_inited : Z := 0xab118.
Definition tfib_D_replace_intrin_cached : Z := 0xab119.
Definition tfib_D_kHighMemEnd : Z := 0xab120.
Definition tfib_D_kMidMemBeg : Z := 0xab128.
Definition tfib_D_kMidMemEnd : Z := 0xab130.
Definition tfib_D_malloc_context_size : Z := 0xab13c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13bf68.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x651ea0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := pcap_img_end.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x3126c.
Definition tfib_at_rw_lo : Z := 0xa3000.
Definition tfib_at_rw_len : Z := 0x5b1000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x656a4.
Definition tfib_at_x_imemcpy : Z := 0x65628.
Definition tfib_at_x_memset : Z := 0x9afa8.
Definition tfib_at_x_memcpy : Z := 0x9aba4.
Definition tfib_at_x_memiszero : Z := 0x65bd4.
Definition tfib_at_x_istrncpy : Z := 0x65ad0.
Definition tfib_at_x_sealed : Z := 0x11836.
Definition tfib_at_x_popfree : Z := 0x37738.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x903a4.
Definition tfib_at_x_envscan_k : Z := 0x903b0.
Definition tfib_at_x_pnscan : Z := 0x90468.
Definition tfib_at_x_pnscan_k : Z := 0x90474.
Definition tfib_at_stops_more : list Z := (0x353ac :: 0x369d0 :: 0x5564c :: 0x5bc54 :: 0x5bc68 :: 0x5bc7c :: 0x61720 :: 0x617f0 :: 0x6ed1c :: 0x6fc28 :: 0x6fdb8 :: 0x6ff28 :: 0x79b10 :: nil)%list.
