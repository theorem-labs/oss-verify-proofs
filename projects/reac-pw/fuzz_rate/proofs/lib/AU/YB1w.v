(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/AB1w.v at 4e3a0a9ad299, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's image-A values; the code below carries image B's values. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2304c.
Definition tfib_text_lo : Z := 0x30a0c.
Definition tfib_init_array_lo : Z := 0x9b998.  Definition tfib_init_array_hi : Z := 0x9b9b8.
Definition tfib_fini_array_lo : Z := 0x9b9b8.  Definition tfib_fini_array_hi : Z := 0x9b9c8.
Definition tfib_preinit_array_lo : Z := 0x9b9c8.  Definition tfib_preinit_array_hi : Z := 0x9b9d0.
Definition tfib_data_rel_ro_lo : Z := 0x9b9e0.  Definition tfib_data_rel_ro_hi : Z := 0x9c110.
Definition tfib_got_lo : Z := 0x9c110.  Definition tfib_got_hi : Z := 0x9ce68.
Definition tfib_data_lo : Z := 0x9de68.  Definition tfib_data_hi : Z := 0xa0a20.
Definition tfib_asan_globals_lo : Z := 0xa0a20.  Definition tfib_asan_globals_hi : Z := 0xa1860.
Definition tfib_bss_lo : Z := 0xa1880.  Definition tfib_bss_hi : Z := 0x5f97b0.
Definition tfib_tbss_lo : Z := 0x9a998.  Definition tfib_tbss_hi : Z := 0x9a9ac.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x30a0c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30a0c.
Definition tfib_A_do_init : Z := 0x30a54.  Definition tfib_E_do_init : Z := 0x30ac8.
Definition tfib_A_do_fini : Z := 0x30ac8.  Definition tfib_E_do_fini : Z := 0x30b58.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30b58.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30b94.
Definition tfib_A_InitializeAllocator : Z := 0x30d04.  Definition tfib_E_InitializeAllocator : Z := 0x30d1c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30d1c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30e88.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x313e4.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31540.
Definition tfib_A_asan_free : Z := 0x31914.  Definition tfib_E_asan_free : Z := 0x3193c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3193c.  Definition tfib_E_Allocator_Deallocate : Z := 0x31bf4.
Definition tfib_A_asan_malloc : Z := 0x31bf4.  Definition tfib_E_asan_malloc : Z := 0x31c50.
Definition tfib_A_Allocator_Allocate : Z := 0x31c50.  Definition tfib_E_Allocator_Allocate : Z := 0x325d8.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32d10.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32e54.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f40.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f9c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32f9c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x331ec.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x331ec.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x332e0.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x332e0.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x333c8.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x337fc.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x339e0.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x339e0.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x33b64.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33c9c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33f20.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33f20.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x340a0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x340a0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34268.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34268.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34434.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34434.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x344d4.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x344d4.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x345d8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34900.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34a48.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34a48.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34a80.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35218.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35500.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35bd8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35d50.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35d50.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35f00.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35f00.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x360e4.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x360e4.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x363bc.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x363bc.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36834.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36834.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36934.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36934.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36c3c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36c3c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36fac.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36fac.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x370c4.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x373cc.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x374c8.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x374c8.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x375b0.
Definition tfib_A_AsanActivate : Z := 0x375b0.  Definition tfib_E_AsanActivate : Z := 0x3768c.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37b68.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x37c50.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c708.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c7e0.
Definition tfib_A_FakeStack_Create : Z := 0x3c7e0.  Definition tfib_E_FakeStack_Create : Z := 0x3c8cc.
Definition tfib_A_FakeStack_Allocate : Z := 0x3cb88.  Definition tfib_E_FakeStack_Allocate : Z := 0x3ce70.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cfa4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cfd4.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3cfd4.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d164.  Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d164.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3d300.  Definition tfib_A_asan_stack_malloc_4 : Z := 0x3d300.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3d4cc.

Definition tfib_A_FakeStack_SetShadow : Z := 0x3d4cc.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3d608.
Definition tfib_A_asan_InitializeFlags : Z := 0x3d608.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e634.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ed40.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fb5c.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3fb5c.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40128.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x4087c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40aec.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40aec.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40df4.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41568.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x416b8.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x420d4.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x421ec.
Definition tfib_A_memcmp_2 : Z := 0x42200.  Definition tfib_E_memcmp_2 : Z := 0x42204.
Definition tfib_A_vfprintf_2 : Z := 0x42228.  Definition tfib_E_vfprintf_2 : Z := 0x4222c.
Definition tfib_A_thunk_417bc : Z := 0x4222c.  Definition tfib_E_thunk_417bc : Z := 0x42230.
Definition tfib_A_thunk_417cc : Z := 0x4223c.  Definition tfib_E_thunk_417cc : Z := 0x42244.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42248.  Definition tfib_E_tls_get_addr_thunk : Z := 0x4224c.
Definition tfib_A_check_absent : Z := 0x83558.  Definition tfib_E_check_absent : Z := 0x83588.  Definition tfib_A_check_rate : Z := 0x83588.  Definition tfib_E_check_rate : Z := 0x835b4.  Definition tfib_A_check_malformed : Z := 0x835b4.  Definition tfib_E_check_malformed : Z := 0x835e8.  Definition tfib_A_check_decide : Z := 0x835e8.  Definition tfib_E_check_decide : Z := 0x8360c.  Definition tfib_A_check_code : Z := 0x8360c.  Definition tfib_E_check_code : Z := 0x83684.  Definition tfib_A_check_list : Z := 0x83684.  Definition tfib_E_check_list : Z := 0x837c0.  Definition tfib_A_check_csv : Z := 0x837c0.  Definition tfib_E_check_csv : Z := 0x83cc4.  Definition tfib_A_pod_write_ent : Z := 0x83cc4.  Definition tfib_E_pod_write_ent : Z := 0x83fcc.  Definition tfib_A_pod_nearest : Z := 0x83fcc.  Definition tfib_E_pod_nearest : Z := 0x8414c.  Definition tfib_A_reac_rate_refuse_code : Z := 0x841b4.  Definition tfib_E_reac_rate_refuse_code : Z := 0x84220.  Definition tfib_A_reac_rate_is_closed : Z := 0x84220.  Definition tfib_E_reac_rate_is_closed : Z := 0x84254.  Definition tfib_A_reac_rate_bit : Z := 0x84254.  Definition tfib_E_reac_rate_bit : Z := 0x84298.  Definition tfib_A_reac_rate_best_drivable : Z := 0x84298.  Definition tfib_E_reac_rate_best_drivable : Z := 0x842d8.  Definition tfib_A_reac_rate_drivable_csv : Z := 0x842d8.  Definition tfib_E_reac_rate_drivable_csv : Z := 0x846f8.  Definition tfib_A_reac_rate_cfg_decide : Z := 0x846f8.  Definition tfib_E_reac_rate_cfg_decide : Z := 0x8474c.  Definition tfib_A_reac_rate_prop_parse : Z := 0x8474c.  Definition tfib_E_reac_rate_prop_parse : Z := 0x84cd0.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x8076c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83558.
Definition tfib_A_thunk_417dc : Z := 0x4224c.  Definition tfib_E_thunk_417dc : Z := 0x42250.

Definition tfib_A_thunk_417e4 : Z := 0x42250.  Definition tfib_E_thunk_417e4 : Z := 0x42254.
Definition tfib_A_thunk_417e8 : Z := 0x42254.  Definition tfib_E_thunk_417e8 : Z := 0x42258.
Definition tfib_A_thunk_417ec : Z := 0x42258.  Definition tfib_E_thunk_417ec : Z := 0x4225c.
Definition tfib_A_thunk_417f0 : Z := 0x4225c.  Definition tfib_E_thunk_417f0 : Z := 0x42260.
Definition tfib_A_thunk_417f8 : Z := 0x42264.  Definition tfib_E_thunk_417f8 : Z := 0x42268.
Definition tfib_A_thunk_4180c : Z := 0x42278.  Definition tfib_E_thunk_4180c : Z := 0x4227c.
Definition tfib_A_icpt_strlen : Z := 0x4227c.  Definition tfib_E_icpt_strlen : Z := 0x42510.
Definition tfib_A_icpt_strnlen : Z := 0x42510.  Definition tfib_E_icpt_strnlen : Z := 0x427a4.
Definition tfib_A_icpt_strcmp : Z := 0x427a8.  Definition tfib_E_icpt_strcmp : Z := 0x42cd8.
Definition tfib_A_icpt_strchr : Z := 0x42cd8.  Definition tfib_E_icpt_strchr : Z := 0x42fb8.
Definition tfib_A_icpt_memcmp : Z := 0x43850.  Definition tfib_E_icpt_memcmp : Z := 0x4390c.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x4390c.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x439c8.
Definition tfib_A_icpt_memchr : Z := 0x439c8.  Definition tfib_E_icpt_memchr : Z := 0x43c98.
Definition tfib_A_icpt_frexpl : Z := 0x43c98.  Definition tfib_E_icpt_frexpl : Z := 0x43f10.
Definition tfib_A_icpt_read : Z := 0x43f10.  Definition tfib_E_icpt_read : Z := 0x44180.
Definition tfib_A_icpt_fwrite : Z := 0x44180.  Definition tfib_E_icpt_fwrite : Z := 0x443f4.
Definition tfib_A_icpt_time : Z := 0x443f4.  Definition tfib_E_icpt_time : Z := 0x44690.
Definition tfib_A_icpt_gmtime_r : Z := 0x44898.  Definition tfib_E_icpt_gmtime_r : Z := 0x44ad8.
Definition tfib_A_icpt_vprintf : Z := 0x44ad8.  Definition tfib_E_icpt_vprintf : Z := 0x44b74.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44b74.  Definition tfib_E_printf_common_format_interceptor : Z := 0x4563c.
Definition tfib_A_icpt_vfprintf : Z := 0x4563c.  Definition tfib_E_icpt_vfprintf : Z := 0x456f0.
Definition tfib_A_icpt_vsnprintf : Z := 0x456f0.  Definition tfib_E_icpt_vsnprintf : Z := 0x45a08.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x45a08.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x45ae0.
Definition tfib_A_icpt_clock_gettime : Z := 0x45b84.  Definition tfib_E_icpt_clock_gettime : Z := 0x45ddc.
Definition tfib_A_icpt_wcrtomb : Z := 0x45ddc.  Definition tfib_E_icpt_wcrtomb : Z := 0x4634c.
Definition tfib_A_icpt_wctomb : Z := 0x4634c.  Definition tfib_E_icpt_wctomb : Z := 0x466a8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46774.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46b5c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b68.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46be4.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46df0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47088.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x470b8.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x472e0.
Definition tfib_A_icpt_send : Z := 0x472e0.  Definition tfib_E_icpt_send : Z := 0x47594.
Definition tfib_A_icpt_sendto : Z := 0x47594.  Definition tfib_E_icpt_sendto : Z := 0x47858.
Definition tfib_A_icpt_sigaltstack : Z := 0x47858.  Definition tfib_E_icpt_sigaltstack : Z := 0x47ab4.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b88.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47d38.
Definition tfib_A_icpt_diouxXn : Z := 0x47d38.  Definition tfib_E_icpt_diouxXn : Z := 0x47ed0.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48a7c.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x51754.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51754.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x518b0.
Definition tfib_A_asan_memcpy : Z := 0x518b8.  Definition tfib_E_asan_memcpy : Z := 0x51d54.
Definition tfib_A_asan_memset : Z := 0x51d54.  Definition tfib_E_asan_memset : Z := 0x51f94.
Definition tfib_A_icpt_memset : Z := 0x51f94.  Definition tfib_E_icpt_memset : Z := 0x52284.
Definition tfib_A_icpt_memcpy : Z := 0x52284.  Definition tfib_E_icpt_memcpy : Z := 0x52874.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52874.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x528ac.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x528ac.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x528b0.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x528b0.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x528b4.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x528b4.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52914.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52960.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52a9c.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52a9c.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52aa0.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x52aa0.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52c08.
Definition tfib_A_free : Z := 0x52c08.  Definition tfib_E_free : Z := 0x52c0c.
Definition tfib_A_malloc : Z := 0x52c0c.  Definition tfib_E_malloc : Z := 0x52c10.
Definition tfib_A_icpt_free : Z := 0x52c10.  Definition tfib_E_icpt_free : Z := 0x52de0.
Definition tfib_A_icpt_malloc : Z := 0x52de0.  Definition tfib_E_icpt_malloc : Z := 0x52f3c.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x52f3c.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x53008.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53008.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x5300c.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x5300c.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x5310c.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x53434.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x535a0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53a88.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53a98.
Definition tfib_A_CanPoisonMemory : Z := 0x53a98.  Definition tfib_E_CanPoisonMemory : Z := 0x53aac.
Definition tfib_A_PoisonShadow : Z := 0x53aac.  Definition tfib_E_PoisonShadow : Z := 0x53fa8.
Definition tfib_A_MemToShadow_checked : Z := 0x53fa8.  Definition tfib_E_MemToShadow_checked : Z := 0x540e4.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x540e4.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x54284.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54434.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54778.
Definition tfib_A_AsanTSDInit : Z := 0x54b98.  Definition tfib_E_AsanTSDInit : Z := 0x54c14.
Definition tfib_A_AsanTSDGet : Z := 0x54c14.  Definition tfib_E_AsanTSDGet : Z := 0x54c54.
Definition tfib_A_AsanTSDSet : Z := 0x54c54.  Definition tfib_E_AsanTSDSet : Z := 0x54c94.
Definition tfib_A_PlatformTSDDtor : Z := 0x54c94.  Definition tfib_E_PlatformTSDDtor : Z := 0x54d18.
Definition tfib_A_InstallAtForkHandler : Z := 0x54d18.  Definition tfib_E_InstallAtForkHandler : Z := 0x54d34.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54d94.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54dd8.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x554f0.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x556fc.
Definition tfib_A_ReportDoubleFree : Z := 0x55e04.  Definition tfib_E_ReportDoubleFree : Z := 0x56094.
Definition tfib_A_ReportGenericError : Z := 0x57970.  Definition tfib_E_ReportGenericError : Z := 0x5822c.
Definition tfib_A_AsanInited : Z := 0x589b8.  Definition tfib_E_AsanInited : Z := 0x589d0.
Definition tfib_A_asan_report_load1 : Z := 0x589d0.  Definition tfib_E_asan_report_load1 : Z := 0x58a20.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58a20.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58a70.
Definition tfib_A_asan_report_load2 : Z := 0x58a70.  Definition tfib_E_asan_report_load2 : Z := 0x58ac0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58ac0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58b10.
Definition tfib_A_asan_report_load4 : Z := 0x58b10.  Definition tfib_E_asan_report_load4 : Z := 0x58b60.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58b60.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58bb0.
Definition tfib_A_asan_report_load8 : Z := 0x58bb0.  Definition tfib_E_asan_report_load8 : Z := 0x58c00.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58c00.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58c50.
Definition tfib_A_asan_report_load16 : Z := 0x58c50.  Definition tfib_E_asan_report_load16 : Z := 0x58ca0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58ca0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58cf0.
Definition tfib_A_asan_report_store1 : Z := 0x58cf0.  Definition tfib_E_asan_report_store1 : Z := 0x58d40.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58d40.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58d90.
Definition tfib_A_asan_report_store2 : Z := 0x58d90.  Definition tfib_E_asan_report_store2 : Z := 0x58de0.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58de0.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58e30.
Definition tfib_A_asan_report_store4 : Z := 0x58e30.  Definition tfib_E_asan_report_store4 : Z := 0x58e80.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58e80.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58ed0.
Definition tfib_A_asan_report_store8 : Z := 0x58ed0.  Definition tfib_E_asan_report_store8 : Z := 0x58f20.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58f20.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58f70.
Definition tfib_A_asan_report_store16 : Z := 0x58f70.  Definition tfib_E_asan_report_store16 : Z := 0x58fc0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58fc0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59010.
Definition tfib_A_asan_report_load_n : Z := 0x59010.  Definition tfib_E_asan_report_load_n : Z := 0x59060.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59060.  Definition tfib_E_asan_report_exp_load_n : Z := 0x590b0.
Definition tfib_A_asan_report_store_n : Z := 0x590b0.  Definition tfib_E_asan_report_store_n : Z := 0x59100.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59100.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59150.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59150.  Definition tfib_E_InitializeHighMemEnd : Z := 0x591d0.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x591d0.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59584.
Definition tfib_A_AsanInitInternal : Z := 0x59614.  Definition tfib_E_AsanInitInternal : Z := 0x598c8.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x598c8.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59968.
Definition tfib_A_thunk_59674 : Z := 0x59b30.  Definition tfib_E_thunk_59674 : Z := 0x59b34.
Definition tfib_A_asan_init : Z := 0x59b34.  Definition tfib_E_asan_init : Z := 0x59bc8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59bc8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59bcc.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x59bcc.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x59c30.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59da4.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59dac.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59e30.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a158.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a158.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a338.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a338.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a640.
Definition tfib_A_SetMallocContextSize : Z := 0x5a640.  Definition tfib_E_SetMallocContextSize : Z := 0x5a650.
Definition tfib_A_GetMallocContextSize : Z := 0x5a650.  Definition tfib_E_GetMallocContextSize : Z := 0x5a660.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a660.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a7b0.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5ab90.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5ae30.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b294.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b2cc.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5b574.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5b580.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b580.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b60c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b60c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b674.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b674.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b6ec.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b6ec.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b754.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5b754.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5b8a0.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5bb2c.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5bb38.
Definition tfib_A_AsanThread_Create : Z := 0x5bcb8.  Definition tfib_E_AsanThread_Create : Z := 0x5be54.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5beb0.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c0c8.
Definition tfib_A_GetCurrentThread : Z := 0x5c0c8.  Definition tfib_E_GetCurrentThread : Z := 0x5c0e8.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c0e8.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5c28c.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c28c.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c2e4.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c2e4.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c33c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c33c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c56c.
Definition tfib_A_AsanThread_Init : Z := 0x5c56c.  Definition tfib_E_AsanThread_Init : Z := 0x5c960.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c960.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5ca6c.
Definition tfib_A_CreateMainThread : Z := 0x5caa0.  Definition tfib_E_CreateMainThread : Z := 0x5cbb0.
Definition tfib_A_SetCurrentThread : Z := 0x5cbb0.  Definition tfib_E_SetCurrentThread : Z := 0x5cc90.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5ce94.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5cfd0.
Definition tfib_A_weak_default_hook_ret : Z := 0x5dca4.  Definition tfib_E_weak_default_hook_ret : Z := 0x5dca8.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5dcb0.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5def0.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e144.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e29c.
Definition tfib_A_internal_allocator_getter : Z := 0x5e488.  Definition tfib_E_internal_allocator_getter : Z := 0x5e494.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5e494.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5e5e0.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e5e0.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e62c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e62c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e638.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e668.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e674.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e674.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e680.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5e680.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5e690.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e69c.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e968.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e968.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ed28.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5fc84.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5fc90.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fc90.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fd68.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fd68.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fe04.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60328.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6036c.
Definition tfib_A_IncreaseTotalMmap : Z := 0x6036c.  Definition tfib_E_IncreaseTotalMmap : Z := 0x60390.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x605e4.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x606f8.
Definition tfib_A_RunMallocHooks : Z := 0x6089c.  Definition tfib_E_RunMallocHooks : Z := 0x60954.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60954.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60958.
Definition tfib_A_RunFreeHooks : Z := 0x60958.  Definition tfib_E_RunFreeHooks : Z := 0x60a04.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x60a04.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x60a0c.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x60a0c.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x60a10.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60a38.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60a84.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60d48.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60f88.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61584.  Definition tfib_E_sanitizer_set_report_path : Z := 0x6159c.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x6159c.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x616e0.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x616e0.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x616e8.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x61a30.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x62cd4.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62cd4.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62cf8.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x631ac.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x634bc.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x634bc.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63600.
Definition tfib_A_FlagParser_ParseString : Z := 0x63600.  Definition tfib_E_FlagParser_ParseString : Z := 0x636f4.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63888.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x638e8.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x638e8.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63928.
Definition tfib_A_internal_atoll : Z := 0x63928.  Definition tfib_E_internal_atoll : Z := 0x63a14.
Definition tfib_A_internal_simple_strtoll : Z := 0x63a14.  Definition tfib_E_internal_simple_strtoll : Z := 0x63b70.
Definition tfib_A_internal_memchr : Z := 0x63b70.  Definition tfib_E_internal_memchr : Z := 0x63b90.
Definition tfib_A_internal_memcmp : Z := 0x63b90.  Definition tfib_E_internal_memcmp : Z := 0x63bc8.
Definition tfib_A_internal_memcpy : Z := 0x63bc8.  Definition tfib_E_internal_memcpy : Z := 0x63bec.
Definition tfib_A_internal_memmove : Z := 0x63bec.  Definition tfib_E_internal_memmove : Z := 0x63c44.
Definition tfib_A_internal_memset : Z := 0x63c44.  Definition tfib_E_internal_memset : Z := 0x63ca4.
Definition tfib_A_internal_strcspn : Z := 0x63ca4.  Definition tfib_E_internal_strcspn : Z := 0x63cf8.
Definition tfib_A_internal_strcmp : Z := 0x63cf8.  Definition tfib_E_internal_strcmp : Z := 0x63d2c.
Definition tfib_A_internal_strdup : Z := 0x63d2c.  Definition tfib_E_internal_strdup : Z := 0x63d98.
Definition tfib_A_internal_strlen : Z := 0x63d98.  Definition tfib_E_internal_strlen : Z := 0x63db4.
Definition tfib_A_internal_strncmp : Z := 0x63db4.  Definition tfib_E_internal_strncmp : Z := 0x63df8.
Definition tfib_A_internal_strchr : Z := 0x63df8.  Definition tfib_E_internal_strchr : Z := 0x63e44.
Definition tfib_A_internal_strchrnul : Z := 0x63e44.  Definition tfib_E_internal_strchrnul : Z := 0x63e8c.
Definition tfib_A_internal_strrchr : Z := 0x63e8c.  Definition tfib_E_internal_strrchr : Z := 0x63ecc.
Definition tfib_A_internal_strnlen : Z := 0x63ffc.  Definition tfib_E_internal_strnlen : Z := 0x6402c.
Definition tfib_A_internal_strncpy : Z := 0x64070.  Definition tfib_E_internal_strncpy : Z := 0x640e0.
Definition tfib_A_internal_strstr : Z := 0x640e0.  Definition tfib_E_internal_strstr : Z := 0x64174.
Definition tfib_A_mem_is_zero : Z := 0x64174.  Definition tfib_E_mem_is_zero : Z := 0x64228.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64228.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64238.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64238.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64418.
Definition tfib_A_internal_iserror : Z := 0x64424.  Definition tfib_E_internal_iserror : Z := 0x64444.
Definition tfib_A_internal_mmap : Z := 0x64444.  Definition tfib_E_internal_mmap : Z := 0x64450.
Definition tfib_A_internal_munmap : Z := 0x64450.  Definition tfib_E_internal_munmap : Z := 0x6445c.
Definition tfib_A_internal_mprotect : Z := 0x6445c.  Definition tfib_E_internal_mprotect : Z := 0x6446c.
Definition tfib_A_internal_madvise : Z := 0x6446c.  Definition tfib_E_internal_madvise : Z := 0x64498.
Definition tfib_A_internal_close : Z := 0x64498.  Definition tfib_E_internal_close : Z := 0x644a4.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x644a4.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x644c8.
Definition tfib_A_internal_read : Z := 0x644c8.  Definition tfib_E_internal_read : Z := 0x64500.
Definition tfib_A_internal_write : Z := 0x64500.  Definition tfib_E_internal_write : Z := 0x64538.
Definition tfib_A_internal_ftruncate : Z := 0x64538.  Definition tfib_E_internal_ftruncate : Z := 0x64570.
Definition tfib_A_internal_dup : Z := 0x64570.  Definition tfib_E_internal_dup : Z := 0x6457c.
Definition tfib_A_internal_dup2_dup3 : Z := 0x6457c.  Definition tfib_E_internal_dup2_dup3 : Z := 0x6458c.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x6458c.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x645a4.
Definition tfib_A_internal_sched_yield : Z := 0x645a4.  Definition tfib_E_internal_sched_yield : Z := 0x645b0.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x645b0.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x645fc.
Definition tfib_A_internal_execve : Z := 0x645fc.  Definition tfib_E_internal_execve : Z := 0x64608.
Definition tfib_A_internal_exit_exit_group : Z := 0x64608.  Definition tfib_E_internal_exit_exit_group : Z := 0x6461c.
Definition tfib_A_FileExists_newfstatat : Z := 0x6461c.  Definition tfib_E_FileExists_newfstatat : Z := 0x6469c.
Definition tfib_A_DirExists_newfstatat : Z := 0x6469c.  Definition tfib_E_DirExists_newfstatat : Z := 0x64700.
Definition tfib_A_GetTid_gettid : Z := 0x64700.  Definition tfib_E_GetTid_gettid : Z := 0x6470c.
Definition tfib_A_GetEnv : Z := 0x6470c.  Definition tfib_E_GetEnv : Z := 0x6483c.
Definition tfib_A_FutexWait : Z := 0x64940.  Definition tfib_E_FutexWait : Z := 0x64964.
Definition tfib_A_FutexWake : Z := 0x64964.  Definition tfib_E_FutexWake : Z := 0x64988.
Definition tfib_A_internal_ptrace : Z := 0x64988.  Definition tfib_E_internal_ptrace : Z := 0x64994.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64994.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x649a4.
Definition tfib_A_internal_getpid : Z := 0x649a4.  Definition tfib_E_internal_getpid : Z := 0x649b0.
Definition tfib_A_internal_getppid : Z := 0x649b0.  Definition tfib_E_internal_getppid : Z := 0x649bc.
Definition tfib_A_internal_prctl : Z := 0x649bc.  Definition tfib_E_internal_prctl : Z := 0x649c8.
Definition tfib_A_internal_sigaltstack : Z := 0x649c8.  Definition tfib_E_internal_sigaltstack : Z := 0x649d4.
Definition tfib_A_internal_fork_clone : Z := 0x649d4.  Definition tfib_E_internal_fork_clone : Z := 0x649ec.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x649ec.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64b18.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x64cf0.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x650ec.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65258.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65370.
Definition tfib_A_GetPageSizeCached : Z := 0x65370.  Definition tfib_E_GetPageSizeCached : Z := 0x65378.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65378.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65424.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65424.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65544.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x6560c.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x6568c.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x6568c.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x656e8.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x656e8.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x657b4.
Definition tfib_A_thunk_653ec : Z := 0x658b0.  Definition tfib_E_thunk_653ec : Z := 0x658b4.
Definition tfib_A_CheckASLR : Z := 0x658b4.  Definition tfib_E_CheckASLR : Z := 0x658b8.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65b04.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65b08.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x65b08.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x65b14.
Definition tfib_A_MmapOrDie : Z := 0x65b14.  Definition tfib_E_MmapOrDie : Z := 0x65c20.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65c20.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65c94.
Definition tfib_A_UnmapOrDie : Z := 0x65c94.  Definition tfib_E_UnmapOrDie : Z := 0x65d10.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65d10.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65e20.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6604c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66150.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x66150.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x6615c.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6615c.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x662d4.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x662d4.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x662e0.
Definition tfib_A_thunk_66008 : Z := 0x664cc.  Definition tfib_E_thunk_66008 : Z := 0x664d0.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x667f0.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x669fc.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66fb4.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66fc0.
Definition tfib_A_Printf : Z := 0x66fc4.  Definition tfib_E_Printf : Z := 0x67010.
Definition tfib_A_SharedPrintfCode : Z := 0x67010.  Definition tfib_E_SharedPrintfCode : Z := 0x6706c.
Definition tfib_A_Report : Z := 0x6706c.  Definition tfib_E_Report : Z := 0x670b8.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68bb0.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68c0c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68c0c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68e48.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68e48.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6916c.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6970c.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x697dc.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x697dc.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69b2c.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69b2c.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69b3c.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69d78.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69dbc.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69dbc.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69e1c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69e1c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a294.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6ab54.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6ae78.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6ae80.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6af84.
Definition tfib_A_AddDieCallback : Z := 0x6b734.  Definition tfib_E_AddDieCallback : Z := 0x6b7bc.
Definition tfib_A_Die : Z := 0x6b880.  Definition tfib_E_Die : Z := 0x6b940.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b940.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b94c.
Definition tfib_A_CheckFailed : Z := 0x6b94c.  Definition tfib_E_CheckFailed : Z := 0x6ba04.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c05c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c154.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c154.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c280.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c4a8.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c524.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c558.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c840.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6c840.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6c844.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c844.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6cc34.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cc34.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cd04.
Definition tfib_A_AndroidLogInit : Z := 0x6d0e8.  Definition tfib_E_AndroidLogInit : Z := 0x6d0ec.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d11c.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d164.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d164.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d3b0.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6d3b0.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6d3b4.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6d3b4.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6d4c0.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d4c0.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d5c4.
Definition tfib_A_thunk_6d37c : Z := 0x6d840.  Definition tfib_E_thunk_6d37c : Z := 0x6d844.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d8e8.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d908.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d908.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d9a8.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6d9f4.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6d9f8.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6da34.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6daf8.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6daf8.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6db80.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6db80.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6dbf8.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6dbf8.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dcdc.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dd98.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6decc.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e104.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e234.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6e234.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6e294.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e294.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e360.
Definition tfib_A_MprotectNoAccess : Z := 0x6e374.  Definition tfib_E_MprotectNoAccess : Z := 0x6e394.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e394.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e4e0.
Definition tfib_A_MmapFixedOrDie : Z := 0x6e4e0.  Definition tfib_E_MmapFixedOrDie : Z := 0x6e4f0.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x6fce8.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x6fd2c.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6fd2c.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6fd5c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70190.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x702b4.
Definition tfib_A_StackStore_Alloc : Z := 0x702b4.  Definition tfib_E_StackStore_Alloc : Z := 0x703e8.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70c9c.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70d50.

Definition tfib_A_StackDepotPut : Z := 0x7278c.  Definition tfib_E_StackDepotPut : Z := 0x727ac.
Definition tfib_A_StackDepotBase_Put : Z := 0x727ac.  Definition tfib_E_StackDepotBase_Put : Z := 0x72a30.
Definition tfib_A_StackDepotBase_Get : Z := 0x72a30.  Definition tfib_E_StackDepotBase_Get : Z := 0x72b40.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x72f20.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x72fb0.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x72fb0.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x730b0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73110.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73118.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73118.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73278.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73278.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x732ec.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73774.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7388c.
Definition tfib_A_thunk_762d8 : Z := 0x768d8.  Definition tfib_E_thunk_762d8 : Z := 0x768dc.
Definition tfib_A_thunk_77ab0 : Z := 0x780b0.  Definition tfib_E_thunk_77ab0 : Z := 0x780b4.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79adc.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79b98.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79b98.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79c70.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x79c70.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x79ee4.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7a210.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7a254.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a254.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a624.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a8f4.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a9ac.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bd04.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bd08.
Definition tfib_A_lsan_register_root_region : Z := 0x7c910.  Definition tfib_E_lsan_register_root_region : Z := 0x7cc40.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cc40.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d0c8.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7d0c8.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7d0d4.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7fc8c.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7fca4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80028.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x800a4.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x800a4.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80154.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80154.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x8016c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8016c.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x802b4.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x802b4.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x802c0.
Definition tfib_A_asan_default_options_cli_c : Z := 0x802c0.  Definition tfib_E_asan_default_options_cli_c : Z := 0x802cc.
Definition tfib_A_main : Z := 0x802cc.  Definition tfib_E_main : Z := 0x80590.
Definition tfib_A_target_alloc_init : Z := 0x80590.  Definition tfib_E_target_alloc_init : Z := 0x80594.
Definition tfib_A_target_alloc_count : Z := 0x80594.  Definition tfib_E_target_alloc_count : Z := 0x8059c.
Definition tfib_A_target_run : Z := 0x8059c.
Definition tfib_A_emit_printf : Z := 0x80724.  Definition tfib_E_emit_printf : Z := 0x8076c.


Definition tfib_A_asan_module_ctor : Z := 0x8414c.  Definition tfib_E_asan_module_ctor : Z := 0x84184.








Definition tfib_A_asan_module_dtor : Z := 0x84184.  Definition tfib_E_asan_module_dtor : Z := 0x841b4.






Definition tfib_A_extenddftf2 : Z := 0x84e64.  Definition tfib_E_extenddftf2 : Z := 0x84ff4.
Definition tfib_A_sysconf : Z := 0x8b6dc.  Definition tfib_E_sysconf : Z := 0x8b904.
Definition tfib_A_init : Z := 0x8b904.  Definition tfib_E_init : Z := 0x8b908.
Definition tfib_A_init_libc : Z := 0x8b908.  Definition tfib_E_init_libc : Z := 0x8bb34.
Definition tfib_A_libc_start_init : Z := 0x8bb34.  Definition tfib_E_libc_start_init : Z := 0x8bb80.
Definition tfib_A_libc_start_main : Z := 0x8bb80.  Definition tfib_E_libc_start_main : Z := 0x8bbe0.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8bbe0.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8bc28.
Definition tfib_A_init_tls : Z := 0x8bd00.  Definition tfib_E_init_tls : Z := 0x8bfb0.
Definition tfib_A_init_ssp : Z := 0x8bfb0.  Definition tfib_E_init_ssp : Z := 0x8c010.
Definition tfib_A_stack_chk_fail : Z := 0x8c010.  Definition tfib_E_stack_chk_fail : Z := 0x8c018.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c060.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c0f4.
Definition tfib_A_Exit : Z := 0x8c0f4.  Definition tfib_E_Exit : Z := 0x8c110.
Definition tfib_A_funcs_on_exit : Z := 0x8c140.  Definition tfib_E_funcs_on_exit : Z := 0x8c208.
Definition tfib_A_fini_stub_ret : Z := 0x8c208.  Definition tfib_E_fini_stub_ret : Z := 0x8c20c.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8c20c.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8c2d0.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x8c2d0.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x8c2d4.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8c2d4.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8c2d8.
Definition tfib_A_libc_exit_fini : Z := 0x8c2d8.  Definition tfib_E_libc_exit_fini : Z := 0x8c324.
Definition tfib_A_exit : Z := 0x8c324.  Definition tfib_E_exit : Z := 0x8c398.
Definition tfib_A_open : Z := 0x8c598.  Definition tfib_E_open : Z := 0x8c67c.
Definition tfib_A_syscall_ret : Z := 0x8c67c.  Definition tfib_E_syscall_ret : Z := 0x8c6b4.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8c6b4.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8c85c.
Definition tfib_A_calloc : Z := 0x8ce20.  Definition tfib_E_calloc : Z := 0x8cf58.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8cf58.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8cf5c.
Definition tfib_A_libc_free : Z := 0x8cf5c.  Definition tfib_E_libc_free : Z := 0x8d128.
Definition tfib_A_get_meta : Z := 0x8d128.  Definition tfib_E_get_meta : Z := 0x8d238.
Definition tfib_A_alloc_meta : Z := 0x8d610.  Definition tfib_E_alloc_meta : Z := 0x8d8e8.
Definition tfib_A_libc_malloc_impl : Z := 0x8d8e8.  Definition tfib_E_libc_malloc_impl : Z := 0x8dc58.
Definition tfib_A_alloc_slot : Z := 0x8dc58.  Definition tfib_E_alloc_slot : Z := 0x8e4fc.
Definition tfib_A_enframe : Z := 0x8e4fc.  Definition tfib_E_enframe : Z := 0x8e64c.
Definition tfib_A_malloc_allzerop : Z := 0x8e64c.  Definition tfib_E_malloc_allzerop : Z := 0x8e7c4.
Definition tfib_A_getrlimit : Z := 0x8fb94.  Definition tfib_E_getrlimit : Z := 0x8fc8c.
Definition tfib_A_getrusage : Z := 0x8fc8c.  Definition tfib_E_getrusage : Z := 0x8fcb4.
Definition tfib_A_setrlimit : Z := 0x8fcb4.  Definition tfib_E_setrlimit : Z := 0x8fd7c.
Definition tfib_A_mmap : Z := 0x901a4.  Definition tfib_E_mmap : Z := 0x90290.
Definition tfib_A_mprotect : Z := 0x90290.  Definition tfib_E_mprotect : Z := 0x902d8.
Definition tfib_A_munmap : Z := 0x903ac.  Definition tfib_E_munmap : Z := 0x903f4.
Definition tfib_A_sched_yield : Z := 0x906b8.  Definition tfib_E_sched_yield : Z := 0x906dc.
Definition tfib_A_raise_tkill_path : Z := 0x90738.  Definition tfib_E_raise_tkill_path : Z := 0x907b0.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x907b0.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x90984.
Definition tfib_A_musl_sigaltstack : Z := 0x90a7c.  Definition tfib_E_musl_sigaltstack : Z := 0x90b08.
Definition tfib_A_fprintf : Z := 0x910e4.  Definition tfib_E_fprintf : Z := 0x91148.

Definition tfib_A_lockfile : Z := 0x91148.  Definition tfib_E_lockfile : Z := 0x91244.
Definition tfib_A_unlockfile : Z := 0x91244.  Definition tfib_E_unlockfile : Z := 0x912a4.



Definition tfib_A_stdio_read : Z := 0x90e34.  Definition tfib_E_stdio_read : Z := 0x90f4c.
Definition tfib_A_stdio_write : Z := 0x90f54.  Definition tfib_E_stdio_write : Z := 0x910e4.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x90e04.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x90e08.
Definition tfib_A_stdio_close : Z := 0x90e08.  Definition tfib_E_stdio_close : Z := 0x90e34.
Definition tfib_A_fwritex : Z := 0x916d8.  Definition tfib_E_fwritex : Z := 0x91810.
Definition tfib_A_musl_fwrite : Z := 0x91810.  Definition tfib_E_musl_fwrite : Z := 0x918c8.
Definition tfib_A_towrite : Z := 0x918c8.  Definition tfib_E_towrite : Z := 0x9191c.
Definition tfib_A_stdio_exit : Z := 0x91534.  Definition tfib_E_stdio_exit : Z := 0x916d8.
Definition tfib_A_ofl_lock : Z := 0x9191c.  Definition tfib_E_ofl_lock : Z := 0x9194c.

Definition tfib_A_musl_vfprintf : Z := 0x91a98.  Definition tfib_E_musl_vfprintf : Z := 0x91c48.
Definition tfib_A_printf_core : Z := 0x91c48.  Definition tfib_E_printf_core : Z := 0x92a78.
Definition tfib_A_pop_arg : Z := 0x92a78.  Definition tfib_E_pop_arg : Z := 0x92bac.
Definition tfib_A_pad : Z := 0x92bac.  Definition tfib_E_pad : Z := 0x92c80.
Definition tfib_A_fmt_fp : Z := 0x92c80.  Definition tfib_E_fmt_fp : Z := 0x94348.
Definition tfib_A_thunk_931e0 : Z := 0x8ca74.  Definition tfib_E_thunk_931e0 : Z := 0x8ca78.
Definition tfib_A_musl_wctomb : Z := 0x90520.  Definition tfib_E_musl_wctomb : Z := 0x90544.
Definition tfib_A_musl_wcrtomb : Z := 0x903f4.  Definition tfib_E_musl_wcrtomb : Z := 0x90520.
Definition tfib_A_fpclassifyl : Z := 0x8ef9c.  Definition tfib_E_fpclassifyl : Z := 0x8efe0.
Definition tfib_A_letf2 : Z := 0x84ce0.  Definition tfib_E_letf2 : Z := 0x84da8.
Definition tfib_A_multf3 : Z := 0x8e89c.  Definition tfib_E_multf3 : Z := 0x8ef9c.
Definition tfib_A_floatsitf : Z := 0x8efe0.  Definition tfib_E_floatsitf : Z := 0x8f0e8.
Definition tfib_A_scalbn : Z := 0x8f9ec.  Definition tfib_E_scalbn : Z := 0x8fa84.
Definition tfib_A_subtf3 : Z := 0x85274.  Definition tfib_E_subtf3 : Z := 0x85284.
Definition tfib_A_addtf3 : Z := 0x85284.  Definition tfib_E_addtf3 : Z := 0x85a50.
Definition tfib_A_fe_getround : Z := 0x85a50.  Definition tfib_E_fe_getround : Z := 0x85a80.
Definition tfib_A_fixunstfsi : Z := 0x94350.  Definition tfib_E_fixunstfsi : Z := 0x943e4.
Definition tfib_A_floatunsitf : Z := 0x943e4.  Definition tfib_E_floatunsitf : Z := 0x944d0.
Definition tfib_A_fixtfsi : Z := 0x8fa84.  Definition tfib_E_fixtfsi : Z := 0x8fb2c.
Definition tfib_A_divtf3 : Z := 0x8f0e8.  Definition tfib_E_divtf3 : Z := 0x8f9ec.
Definition tfib_A_musl_vprintf : Z := 0x94ba8.  Definition tfib_E_musl_vprintf : Z := 0x94bc4.
Definition tfib_A_stdout_write : Z := 0x91958.  Definition tfib_E_stdout_write : Z := 0x919f8.
Definition tfib_A_thunk_95368 : Z := 0x9515c.  Definition tfib_E_thunk_95368 : Z := 0x95160.
Definition tfib_A_musl_memcmp : Z := 0x9522c.  Definition tfib_E_musl_memcmp : Z := 0x9525c.
Definition tfib_A_musl_memcpy : Z := 0x9525c.  Definition tfib_E_musl_memcpy : Z := 0x95660.
Definition tfib_A_musl_memset : Z := 0x95660.  Definition tfib_E_musl_memset : Z := 0x95758.
Definition tfib_A_musl_strchr : Z := 0x95758.  Definition tfib_E_musl_strchr : Z := 0x95794.
Definition tfib_A_strchrnul : Z := 0x95794.  Definition tfib_E_strchrnul : Z := 0x95874.
Definition tfib_A_musl_strlen : Z := 0x958ac.  Definition tfib_E_musl_strlen : Z := 0x9593c.
Definition tfib_A_musl_strnlen : Z := 0x95ae8.  Definition tfib_E_musl_strnlen : Z := 0x95b2c.
Definition tfib_A_musl_memchr : Z := 0x95160.  Definition tfib_E_musl_memchr : Z := 0x9522c.
Definition tfib_A_lock : Z := 0x95b2c.  Definition tfib_E_lock : Z := 0x95db4.
Definition tfib_A_unlock : Z := 0x95db4.  Definition tfib_E_unlock : Z := 0x95e28.
Definition tfib_A_syscall_cp_c : Z := 0x95e28.  Definition tfib_E_syscall_cp_c : Z := 0x95e4c.
Definition tfib_A_syscall_cp_sccp : Z := 0x95e4c.  Definition tfib_E_syscall_cp_sccp : Z := 0x95e50.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x95e50.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x95e74.
Definition tfib_A_pthread_atfork : Z := 0x95e8c.  Definition tfib_E_pthread_atfork : Z := 0x95f30.
Definition tfib_A_mremap : Z := 0x902d8.  Definition tfib_E_mremap : Z := 0x903ac.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x96f04.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x96f20.
Definition tfib_A_pthread_key_create : Z := 0x972ac.  Definition tfib_E_pthread_key_create : Z := 0x97380.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x97624.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x976c8.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x976c8.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x977e4.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x977e4.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x97810.
Definition tfib_A_pthread_setspecific : Z := 0x97848.  Definition tfib_E_pthread_setspecific : Z := 0x9787c.
Definition tfib_A_set_thread_area : Z := 0x97884.  Definition tfib_E_set_thread_area : Z := 0x97890.
Definition tfib_A_thunk_96f9c : Z := 0x9787c.  Definition tfib_E_thunk_96f9c : Z := 0x97884.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x981b0.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98268.
Definition tfib_A_close : Z := 0x9a880.  Definition tfib_E_close : Z := 0x9a8d4.
Definition tfib_A_musl_read : Z := 0x9a960.  Definition tfib_E_musl_read : Z := 0x9a994.
Definition tfib_A_vm_wait : Z := 0x97ec0.  Definition tfib_E_vm_wait : Z := 0x97f10.
Definition tfib_D_str_sealed : Z := 0x118dd.
Definition tfib_D_init_array_0_3 : Z := 0x9b998.
Definition tfib_D_fini_array_0_1 : Z := 0x9b9b8.
Definition tfib_D_GOT_common_flags : Z := 0x9c160.
Definition tfib_D_GOT_flags : Z := 0x9c168.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c170.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c178.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c180.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c188.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9ccd8.
Definition tfib_D_REAL_read : Z := 0x9dea8.
Definition tfib_D_REAL_memcpy : Z := 0x9dfd0.
Definition tfib_D_REAL_memset : Z := 0x9dfd8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa18d8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa2738.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa4f38.
Definition tfib_D_asan_inited : Z := 0xa5c18.
Definition tfib_D_replace_intrin_cached : Z := 0xa5c19.
Definition tfib_D_kHighMemEnd : Z := 0xa5c20.
Definition tfib_D_kMidMemBeg : Z := 0xa5c28.
Definition tfib_D_kMidMemEnd : Z := 0xa5c30.
Definition tfib_D_malloc_context_size : Z := 0xa5c3c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136a68.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f8160.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30a0c.
Definition tfib_at_rw_lo : Z := 0x9d000.
Definition tfib_at_rw_len : Z := 0x55d000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63c44.
Definition tfib_at_x_imemcpy : Z := 0x63bc8.
Definition tfib_at_x_memset : Z := 0x95660.
Definition tfib_at_x_memcpy : Z := 0x9525c.
Definition tfib_at_x_memiszero : Z := 0x64174.
Definition tfib_at_x_istrncpy : Z := 0x64070.
Definition tfib_at_x_sealed : Z := 0x118dd.
Definition tfib_at_x_popfree : Z := 0x36df8.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8b940.
Definition tfib_at_x_envscan_k : Z := 0x8b94c.
Definition tfib_at_x_pnscan : Z := 0x8ba04.
Definition tfib_at_x_pnscan_k : Z := 0x8ba10.
Definition tfib_at_stops_more : list Z := (0x34a6c :: 0x36090 :: 0x53f50 :: 0x5a308 :: 0x5a31c :: 0x5a330 :: 0x5fcc0 :: 0x5fd90 :: 0x6d2bc :: 0x6e1c8 :: 0x6e358 :: 0x780b0 :: nil)%list.
