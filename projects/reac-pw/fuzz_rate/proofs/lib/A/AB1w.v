(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2304c.
Definition tfib_text_lo : Z := 0x309d4.
Definition tfib_init_array_lo : Z := 0x9b690.  Definition tfib_init_array_hi : Z := 0x9b6b0.
Definition tfib_fini_array_lo : Z := 0x9b6b0.  Definition tfib_fini_array_hi : Z := 0x9b6c0.
Definition tfib_preinit_array_lo : Z := 0x9b6c0.  Definition tfib_preinit_array_hi : Z := 0x9b6c8.
Definition tfib_data_rel_ro_lo : Z := 0x9b6e0.  Definition tfib_data_rel_ro_hi : Z := 0x9be10.
Definition tfib_got_lo : Z := 0x9be10.  Definition tfib_got_hi : Z := 0x9cb68.
Definition tfib_data_lo : Z := 0x9db68.  Definition tfib_data_hi : Z := 0xa0720.
Definition tfib_asan_globals_lo : Z := 0xa0720.  Definition tfib_asan_globals_hi : Z := 0xa1560.
Definition tfib_bss_lo : Z := 0xa1580.  Definition tfib_bss_hi : Z := 0x5f94b0.
Definition tfib_tbss_lo : Z := 0x9a690.  Definition tfib_tbss_hi : Z := 0x9a6a4.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x309d4.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x309d4.
Definition tfib_A_do_init : Z := 0x30a1c.  Definition tfib_E_do_init : Z := 0x30a90.
Definition tfib_A_do_fini : Z := 0x30a90.  Definition tfib_E_do_fini : Z := 0x30b20.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30b20.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30b5c.
Definition tfib_A_InitializeAllocator : Z := 0x30ccc.  Definition tfib_E_InitializeAllocator : Z := 0x30ce4.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30ce4.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30e50.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x313ac.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31508.
Definition tfib_A_asan_free : Z := 0x318dc.  Definition tfib_E_asan_free : Z := 0x31904.
Definition tfib_A_Allocator_Deallocate : Z := 0x31904.  Definition tfib_E_Allocator_Deallocate : Z := 0x31bbc.
Definition tfib_A_asan_malloc : Z := 0x31bbc.  Definition tfib_E_asan_malloc : Z := 0x31c18.
Definition tfib_A_Allocator_Allocate : Z := 0x31c18.  Definition tfib_E_Allocator_Allocate : Z := 0x325a0.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32cd8.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32e1c.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f08.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f64.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32f64.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x331b4.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x331b4.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x332a8.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x332a8.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33390.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x337c4.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x339a8.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x339a8.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x33b2c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33c64.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33ee8.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33ee8.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34068.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34068.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34230.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34230.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x343fc.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x343fc.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x3449c.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x3449c.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x345a0.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x348c8.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34a10.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34a10.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34a48.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x351e0.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x354c8.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35ba0.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35d18.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35d18.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35ec8.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35ec8.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x360ac.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x360ac.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36384.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36384.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x367fc.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x367fc.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x368fc.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x368fc.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36c04.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36c04.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36f74.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36f74.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x3708c.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37394.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37490.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37490.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37578.
Definition tfib_A_AsanActivate : Z := 0x37578.  Definition tfib_E_AsanActivate : Z := 0x37654.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37b30.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x37c18.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c6d0.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c7a8.
Definition tfib_A_FakeStack_Create : Z := 0x3c7a8.  Definition tfib_E_FakeStack_Create : Z := 0x3c894.
Definition tfib_A_FakeStack_Allocate : Z := 0x3cb50.  Definition tfib_E_FakeStack_Allocate : Z := 0x3ce38.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cf6c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cf9c.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3cf9c.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d12c.  Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d12c.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3d2c8.  Definition tfib_A_asan_stack_malloc_3 : Z := 0x3d2c8.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3d474.

Definition tfib_A_FakeStack_SetShadow : Z := 0x3d474.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3d5b0.
Definition tfib_A_asan_InitializeFlags : Z := 0x3d5b0.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e5dc.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ece8.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fb04.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3fb04.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x400d0.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x40824.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40a94.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40a94.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40d9c.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41510.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x41660.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x4207c.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x42194.
Definition tfib_A_memcmp_2 : Z := 0x421a8.  Definition tfib_E_memcmp_2 : Z := 0x421ac.
Definition tfib_A_vfprintf_2 : Z := 0x421d0.  Definition tfib_E_vfprintf_2 : Z := 0x421d4.
Definition tfib_A_thunk_417bc : Z := 0x421d4.  Definition tfib_E_thunk_417bc : Z := 0x421d8.
Definition tfib_A_thunk_417cc : Z := 0x421e4.  Definition tfib_E_thunk_417cc : Z := 0x421ec.
Definition tfib_A_tls_get_addr_thunk : Z := 0x421f0.  Definition tfib_E_tls_get_addr_thunk : Z := 0x421f4.
Definition tfib_A_check_absent : Z := 0x83690.  Definition tfib_E_check_absent : Z := 0x836bc.  Definition tfib_A_check_rate : Z := 0x836bc.  Definition tfib_E_check_rate : Z := 0x836e4.  Definition tfib_A_check_malformed : Z := 0x836e4.  Definition tfib_E_check_malformed : Z := 0x83714.  Definition tfib_A_check_decide : Z := 0x83714.  Definition tfib_E_check_decide : Z := 0x83734.  Definition tfib_A_check_code : Z := 0x83734.  Definition tfib_E_check_code : Z := 0x837a8.  Definition tfib_A_check_list : Z := 0x837a8.  Definition tfib_E_check_list : Z := 0x838e0.  Definition tfib_A_check_csv : Z := 0x838e0.  Definition tfib_E_check_csv : Z := 0x83dc0.  Definition tfib_A_pod_nearest : Z := 0x83dc0.  Definition tfib_E_pod_nearest : Z := 0x83ef8.  Definition tfib_A_reac_rate_refuse_code : Z := 0x83f60.  Definition tfib_E_reac_rate_refuse_code : Z := 0x83fbc.  Definition tfib_A_reac_rate_is_closed : Z := 0x83fbc.  Definition tfib_E_reac_rate_is_closed : Z := 0x83ff0.  Definition tfib_A_reac_rate_bit : Z := 0x83ff0.  Definition tfib_E_reac_rate_bit : Z := 0x84034.  Definition tfib_A_reac_rate_best_drivable : Z := 0x84034.  Definition tfib_E_reac_rate_best_drivable : Z := 0x84074.  Definition tfib_A_reac_rate_drivable_csv : Z := 0x84074.  Definition tfib_E_reac_rate_drivable_csv : Z := 0x84448.  Definition tfib_A_reac_rate_cfg_decide : Z := 0x84448.  Definition tfib_E_reac_rate_cfg_decide : Z := 0x8449c.  Definition tfib_A_reac_rate_prop_parse : Z := 0x8449c.  Definition tfib_E_reac_rate_prop_parse : Z := 0x849c8.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80714.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83690.
Definition tfib_A_thunk_417dc : Z := 0x421f4.  Definition tfib_E_thunk_417dc : Z := 0x421f8.

Definition tfib_A_thunk_417e4 : Z := 0x421f8.  Definition tfib_E_thunk_417e4 : Z := 0x421fc.
Definition tfib_A_thunk_417e8 : Z := 0x421fc.  Definition tfib_E_thunk_417e8 : Z := 0x42200.
Definition tfib_A_thunk_417ec : Z := 0x42200.  Definition tfib_E_thunk_417ec : Z := 0x42204.
Definition tfib_A_thunk_417f0 : Z := 0x42204.  Definition tfib_E_thunk_417f0 : Z := 0x42208.
Definition tfib_A_thunk_417f8 : Z := 0x4220c.  Definition tfib_E_thunk_417f8 : Z := 0x42210.
Definition tfib_A_thunk_4180c : Z := 0x42220.  Definition tfib_E_thunk_4180c : Z := 0x42224.
Definition tfib_A_icpt_strlen : Z := 0x42224.  Definition tfib_E_icpt_strlen : Z := 0x424b8.
Definition tfib_A_icpt_strnlen : Z := 0x424b8.  Definition tfib_E_icpt_strnlen : Z := 0x4274c.
Definition tfib_A_icpt_strcmp : Z := 0x42750.  Definition tfib_E_icpt_strcmp : Z := 0x42c80.
Definition tfib_A_icpt_strchr : Z := 0x42c80.  Definition tfib_E_icpt_strchr : Z := 0x42f60.
Definition tfib_A_icpt_memcmp : Z := 0x437f8.  Definition tfib_E_icpt_memcmp : Z := 0x438b4.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x438b4.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x43970.
Definition tfib_A_icpt_memchr : Z := 0x43970.  Definition tfib_E_icpt_memchr : Z := 0x43c40.
Definition tfib_A_icpt_frexpl : Z := 0x43c40.  Definition tfib_E_icpt_frexpl : Z := 0x43eb8.
Definition tfib_A_icpt_read : Z := 0x43eb8.  Definition tfib_E_icpt_read : Z := 0x44128.
Definition tfib_A_icpt_fwrite : Z := 0x44128.  Definition tfib_E_icpt_fwrite : Z := 0x4439c.
Definition tfib_A_icpt_time : Z := 0x4439c.  Definition tfib_E_icpt_time : Z := 0x44638.
Definition tfib_A_icpt_gmtime_r : Z := 0x44840.  Definition tfib_E_icpt_gmtime_r : Z := 0x44a80.
Definition tfib_A_icpt_vprintf : Z := 0x44a80.  Definition tfib_E_icpt_vprintf : Z := 0x44b1c.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44b1c.  Definition tfib_E_printf_common_format_interceptor : Z := 0x455e4.
Definition tfib_A_icpt_vfprintf : Z := 0x455e4.  Definition tfib_E_icpt_vfprintf : Z := 0x45698.
Definition tfib_A_icpt_vsnprintf : Z := 0x45698.  Definition tfib_E_icpt_vsnprintf : Z := 0x459b0.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x459b0.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x45a88.
Definition tfib_A_icpt_clock_gettime : Z := 0x45b2c.  Definition tfib_E_icpt_clock_gettime : Z := 0x45d84.
Definition tfib_A_icpt_wcrtomb : Z := 0x45d84.  Definition tfib_E_icpt_wcrtomb : Z := 0x462f4.
Definition tfib_A_icpt_wctomb : Z := 0x462f4.  Definition tfib_E_icpt_wctomb : Z := 0x46650.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x4671c.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46b04.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b10.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b8c.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46d98.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47030.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47060.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47288.
Definition tfib_A_icpt_send : Z := 0x47288.  Definition tfib_E_icpt_send : Z := 0x4753c.
Definition tfib_A_icpt_sendto : Z := 0x4753c.  Definition tfib_E_icpt_sendto : Z := 0x47800.
Definition tfib_A_icpt_sigaltstack : Z := 0x47800.  Definition tfib_E_icpt_sigaltstack : Z := 0x47a5c.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b30.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47ce0.
Definition tfib_A_icpt_diouxXn : Z := 0x47ce0.  Definition tfib_E_icpt_diouxXn : Z := 0x47e78.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48a24.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x516fc.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x516fc.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51858.
Definition tfib_A_asan_memcpy : Z := 0x51860.  Definition tfib_E_asan_memcpy : Z := 0x51cfc.
Definition tfib_A_asan_memset : Z := 0x51cfc.  Definition tfib_E_asan_memset : Z := 0x51f3c.
Definition tfib_A_icpt_memset : Z := 0x51f3c.  Definition tfib_E_icpt_memset : Z := 0x5222c.
Definition tfib_A_icpt_memcpy : Z := 0x5222c.  Definition tfib_E_icpt_memcpy : Z := 0x5281c.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5281c.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52854.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52854.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52858.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52858.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x5285c.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5285c.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x528bc.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52908.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52a44.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52a44.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52a48.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x52a48.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52bb0.
Definition tfib_A_free : Z := 0x52bb0.  Definition tfib_E_free : Z := 0x52bb4.
Definition tfib_A_malloc : Z := 0x52bb4.  Definition tfib_E_malloc : Z := 0x52bb8.
Definition tfib_A_icpt_free : Z := 0x52bb8.  Definition tfib_E_icpt_free : Z := 0x52d88.
Definition tfib_A_icpt_malloc : Z := 0x52d88.  Definition tfib_E_icpt_malloc : Z := 0x52ee4.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x52ee4.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x52fb0.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52fb0.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52fb4.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x52fb4.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x530b4.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x533dc.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x53548.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53a30.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53a40.
Definition tfib_A_CanPoisonMemory : Z := 0x53a40.  Definition tfib_E_CanPoisonMemory : Z := 0x53a54.
Definition tfib_A_PoisonShadow : Z := 0x53a54.  Definition tfib_E_PoisonShadow : Z := 0x53f50.
Definition tfib_A_MemToShadow_checked : Z := 0x53f50.  Definition tfib_E_MemToShadow_checked : Z := 0x5408c.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x5408c.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x5422c.
Definition tfib_A_asan_region_is_poisoned : Z := 0x543dc.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54720.
Definition tfib_A_AsanTSDInit : Z := 0x54b40.  Definition tfib_E_AsanTSDInit : Z := 0x54bbc.
Definition tfib_A_AsanTSDGet : Z := 0x54bbc.  Definition tfib_E_AsanTSDGet : Z := 0x54bfc.
Definition tfib_A_AsanTSDSet : Z := 0x54bfc.  Definition tfib_E_AsanTSDSet : Z := 0x54c3c.
Definition tfib_A_PlatformTSDDtor : Z := 0x54c3c.  Definition tfib_E_PlatformTSDDtor : Z := 0x54cc0.
Definition tfib_A_InstallAtForkHandler : Z := 0x54cc0.  Definition tfib_E_InstallAtForkHandler : Z := 0x54cdc.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54d3c.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54d80.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x55498.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x556a4.
Definition tfib_A_ReportDoubleFree : Z := 0x55dac.  Definition tfib_E_ReportDoubleFree : Z := 0x5603c.
Definition tfib_A_ReportGenericError : Z := 0x57918.  Definition tfib_E_ReportGenericError : Z := 0x581d4.
Definition tfib_A_AsanInited : Z := 0x58960.  Definition tfib_E_AsanInited : Z := 0x58978.
Definition tfib_A_asan_report_load1 : Z := 0x58978.  Definition tfib_E_asan_report_load1 : Z := 0x589c8.
Definition tfib_A_asan_report_exp_load1 : Z := 0x589c8.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58a18.
Definition tfib_A_asan_report_load2 : Z := 0x58a18.  Definition tfib_E_asan_report_load2 : Z := 0x58a68.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58a68.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58ab8.
Definition tfib_A_asan_report_load4 : Z := 0x58ab8.  Definition tfib_E_asan_report_load4 : Z := 0x58b08.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58b08.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58b58.
Definition tfib_A_asan_report_load8 : Z := 0x58b58.  Definition tfib_E_asan_report_load8 : Z := 0x58ba8.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58ba8.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58bf8.
Definition tfib_A_asan_report_load16 : Z := 0x58bf8.  Definition tfib_E_asan_report_load16 : Z := 0x58c48.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58c48.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58c98.
Definition tfib_A_asan_report_store1 : Z := 0x58c98.  Definition tfib_E_asan_report_store1 : Z := 0x58ce8.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58ce8.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58d38.
Definition tfib_A_asan_report_store2 : Z := 0x58d38.  Definition tfib_E_asan_report_store2 : Z := 0x58d88.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58d88.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58dd8.
Definition tfib_A_asan_report_store4 : Z := 0x58dd8.  Definition tfib_E_asan_report_store4 : Z := 0x58e28.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58e28.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58e78.
Definition tfib_A_asan_report_store8 : Z := 0x58e78.  Definition tfib_E_asan_report_store8 : Z := 0x58ec8.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58ec8.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58f18.
Definition tfib_A_asan_report_store16 : Z := 0x58f18.  Definition tfib_E_asan_report_store16 : Z := 0x58f68.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58f68.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58fb8.
Definition tfib_A_asan_report_load_n : Z := 0x58fb8.  Definition tfib_E_asan_report_load_n : Z := 0x59008.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59008.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59058.
Definition tfib_A_asan_report_store_n : Z := 0x59058.  Definition tfib_E_asan_report_store_n : Z := 0x590a8.
Definition tfib_A_asan_report_exp_store_n : Z := 0x590a8.  Definition tfib_E_asan_report_exp_store_n : Z := 0x590f8.
Definition tfib_A_InitializeHighMemEnd : Z := 0x590f8.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59178.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59178.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5952c.
Definition tfib_A_AsanInitInternal : Z := 0x595bc.  Definition tfib_E_AsanInitInternal : Z := 0x59870.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59870.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59910.
Definition tfib_A_thunk_59674 : Z := 0x59ad8.  Definition tfib_E_thunk_59674 : Z := 0x59adc.
Definition tfib_A_asan_init : Z := 0x59adc.  Definition tfib_E_asan_init : Z := 0x59b70.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59b70.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59b74.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x59b74.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x59bd8.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59d4c.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59d54.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59dd8.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a100.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a100.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a2e0.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a2e0.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a5e8.
Definition tfib_A_SetMallocContextSize : Z := 0x5a5e8.  Definition tfib_E_SetMallocContextSize : Z := 0x5a5f8.
Definition tfib_A_GetMallocContextSize : Z := 0x5a5f8.  Definition tfib_E_GetMallocContextSize : Z := 0x5a608.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a608.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a758.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5ab38.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5add8.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b23c.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b274.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5b51c.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5b528.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b528.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b5b4.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b5b4.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b61c.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b61c.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b694.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b694.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b6fc.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5b6fc.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5b848.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5bad4.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5bae0.
Definition tfib_A_AsanThread_Create : Z := 0x5bc60.  Definition tfib_E_AsanThread_Create : Z := 0x5bdfc.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5be58.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c070.
Definition tfib_A_GetCurrentThread : Z := 0x5c070.  Definition tfib_E_GetCurrentThread : Z := 0x5c090.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c090.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5c234.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c234.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c28c.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c28c.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c2e4.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c2e4.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c514.
Definition tfib_A_AsanThread_Init : Z := 0x5c514.  Definition tfib_E_AsanThread_Init : Z := 0x5c908.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c908.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5ca14.
Definition tfib_A_CreateMainThread : Z := 0x5ca48.  Definition tfib_E_CreateMainThread : Z := 0x5cb58.
Definition tfib_A_SetCurrentThread : Z := 0x5cb58.  Definition tfib_E_SetCurrentThread : Z := 0x5cc38.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5ce3c.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5cf78.
Definition tfib_A_weak_default_hook_ret : Z := 0x5dc4c.  Definition tfib_E_weak_default_hook_ret : Z := 0x5dc50.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5dc58.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5de98.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e0ec.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e244.
Definition tfib_A_internal_allocator_getter : Z := 0x5e430.  Definition tfib_E_internal_allocator_getter : Z := 0x5e43c.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5e43c.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5e588.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e588.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e5d4.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e5d4.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e5e0.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e610.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e61c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e61c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e628.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5e628.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5e638.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e644.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e910.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e910.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ecd0.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5fc2c.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5fc38.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fc38.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fd10.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fd10.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fdac.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x602d0.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60314.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60314.  Definition tfib_E_IncreaseTotalMmap : Z := 0x60338.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x6058c.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x606a0.
Definition tfib_A_RunMallocHooks : Z := 0x60844.  Definition tfib_E_RunMallocHooks : Z := 0x608fc.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x608fc.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60900.
Definition tfib_A_RunFreeHooks : Z := 0x60900.  Definition tfib_E_RunFreeHooks : Z := 0x609ac.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x609ac.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x609b4.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x609b4.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x609b8.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x609e0.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60a2c.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60cf0.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60f30.
Definition tfib_A_sanitizer_set_report_path : Z := 0x6152c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61544.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x61544.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x61688.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61688.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61690.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x619d8.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x62c7c.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62c7c.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62ca0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63154.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63464.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63464.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x635a8.
Definition tfib_A_FlagParser_ParseString : Z := 0x635a8.  Definition tfib_E_FlagParser_ParseString : Z := 0x6369c.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63830.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63890.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63890.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x638d0.
Definition tfib_A_internal_atoll : Z := 0x638d0.  Definition tfib_E_internal_atoll : Z := 0x639bc.
Definition tfib_A_internal_simple_strtoll : Z := 0x639bc.  Definition tfib_E_internal_simple_strtoll : Z := 0x63b18.
Definition tfib_A_internal_memchr : Z := 0x63b18.  Definition tfib_E_internal_memchr : Z := 0x63b38.
Definition tfib_A_internal_memcmp : Z := 0x63b38.  Definition tfib_E_internal_memcmp : Z := 0x63b70.
Definition tfib_A_internal_memcpy : Z := 0x63b70.  Definition tfib_E_internal_memcpy : Z := 0x63b94.
Definition tfib_A_internal_memmove : Z := 0x63b94.  Definition tfib_E_internal_memmove : Z := 0x63bec.
Definition tfib_A_internal_memset : Z := 0x63bec.  Definition tfib_E_internal_memset : Z := 0x63c4c.
Definition tfib_A_internal_strcspn : Z := 0x63c4c.  Definition tfib_E_internal_strcspn : Z := 0x63ca0.
Definition tfib_A_internal_strcmp : Z := 0x63ca0.  Definition tfib_E_internal_strcmp : Z := 0x63cd4.
Definition tfib_A_internal_strdup : Z := 0x63cd4.  Definition tfib_E_internal_strdup : Z := 0x63d40.
Definition tfib_A_internal_strlen : Z := 0x63d40.  Definition tfib_E_internal_strlen : Z := 0x63d5c.
Definition tfib_A_internal_strncmp : Z := 0x63d5c.  Definition tfib_E_internal_strncmp : Z := 0x63da0.
Definition tfib_A_internal_strchr : Z := 0x63da0.  Definition tfib_E_internal_strchr : Z := 0x63dec.
Definition tfib_A_internal_strchrnul : Z := 0x63dec.  Definition tfib_E_internal_strchrnul : Z := 0x63e34.
Definition tfib_A_internal_strrchr : Z := 0x63e34.  Definition tfib_E_internal_strrchr : Z := 0x63e74.
Definition tfib_A_internal_strnlen : Z := 0x63fa4.  Definition tfib_E_internal_strnlen : Z := 0x63fd4.
Definition tfib_A_internal_strncpy : Z := 0x64018.  Definition tfib_E_internal_strncpy : Z := 0x64088.
Definition tfib_A_internal_strstr : Z := 0x64088.  Definition tfib_E_internal_strstr : Z := 0x6411c.
Definition tfib_A_mem_is_zero : Z := 0x6411c.  Definition tfib_E_mem_is_zero : Z := 0x641d0.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x641d0.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x641e0.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x641e0.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x643c0.
Definition tfib_A_internal_iserror : Z := 0x643cc.  Definition tfib_E_internal_iserror : Z := 0x643ec.
Definition tfib_A_internal_mmap : Z := 0x643ec.  Definition tfib_E_internal_mmap : Z := 0x643f8.
Definition tfib_A_internal_munmap : Z := 0x643f8.  Definition tfib_E_internal_munmap : Z := 0x64404.
Definition tfib_A_internal_mprotect : Z := 0x64404.  Definition tfib_E_internal_mprotect : Z := 0x64414.
Definition tfib_A_internal_madvise : Z := 0x64414.  Definition tfib_E_internal_madvise : Z := 0x64440.
Definition tfib_A_internal_close : Z := 0x64440.  Definition tfib_E_internal_close : Z := 0x6444c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x6444c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64470.
Definition tfib_A_internal_read : Z := 0x64470.  Definition tfib_E_internal_read : Z := 0x644a8.
Definition tfib_A_internal_write : Z := 0x644a8.  Definition tfib_E_internal_write : Z := 0x644e0.
Definition tfib_A_internal_ftruncate : Z := 0x644e0.  Definition tfib_E_internal_ftruncate : Z := 0x64518.
Definition tfib_A_internal_dup : Z := 0x64518.  Definition tfib_E_internal_dup : Z := 0x64524.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64524.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64534.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64534.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x6454c.
Definition tfib_A_internal_sched_yield : Z := 0x6454c.  Definition tfib_E_internal_sched_yield : Z := 0x64558.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64558.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x645a4.
Definition tfib_A_internal_execve : Z := 0x645a4.  Definition tfib_E_internal_execve : Z := 0x645b0.
Definition tfib_A_internal_exit_exit_group : Z := 0x645b0.  Definition tfib_E_internal_exit_exit_group : Z := 0x645c4.
Definition tfib_A_FileExists_newfstatat : Z := 0x645c4.  Definition tfib_E_FileExists_newfstatat : Z := 0x64644.
Definition tfib_A_DirExists_newfstatat : Z := 0x64644.  Definition tfib_E_DirExists_newfstatat : Z := 0x646a8.
Definition tfib_A_GetTid_gettid : Z := 0x646a8.  Definition tfib_E_GetTid_gettid : Z := 0x646b4.
Definition tfib_A_GetEnv : Z := 0x646b4.  Definition tfib_E_GetEnv : Z := 0x647e4.
Definition tfib_A_FutexWait : Z := 0x648e8.  Definition tfib_E_FutexWait : Z := 0x6490c.
Definition tfib_A_FutexWake : Z := 0x6490c.  Definition tfib_E_FutexWake : Z := 0x64930.
Definition tfib_A_internal_ptrace : Z := 0x64930.  Definition tfib_E_internal_ptrace : Z := 0x6493c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6493c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6494c.
Definition tfib_A_internal_getpid : Z := 0x6494c.  Definition tfib_E_internal_getpid : Z := 0x64958.
Definition tfib_A_internal_getppid : Z := 0x64958.  Definition tfib_E_internal_getppid : Z := 0x64964.
Definition tfib_A_internal_prctl : Z := 0x64964.  Definition tfib_E_internal_prctl : Z := 0x64970.
Definition tfib_A_internal_sigaltstack : Z := 0x64970.  Definition tfib_E_internal_sigaltstack : Z := 0x6497c.
Definition tfib_A_internal_fork_clone : Z := 0x6497c.  Definition tfib_E_internal_fork_clone : Z := 0x64994.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64994.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64ac0.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x64c98.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x65094.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65200.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65318.
Definition tfib_A_GetPageSizeCached : Z := 0x65318.  Definition tfib_E_GetPageSizeCached : Z := 0x65320.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65320.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x653cc.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x653cc.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x654ec.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x655b4.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65634.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x65634.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x65690.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65690.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6575c.
Definition tfib_A_thunk_653ec : Z := 0x65858.  Definition tfib_E_thunk_653ec : Z := 0x6585c.
Definition tfib_A_CheckASLR : Z := 0x6585c.  Definition tfib_E_CheckASLR : Z := 0x65860.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65aac.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65ab0.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x65ab0.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x65abc.
Definition tfib_A_MmapOrDie : Z := 0x65abc.  Definition tfib_E_MmapOrDie : Z := 0x65bc8.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65bc8.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65c3c.
Definition tfib_A_UnmapOrDie : Z := 0x65c3c.  Definition tfib_E_UnmapOrDie : Z := 0x65cb8.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65cb8.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65dc8.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65ff4.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x660f8.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x660f8.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x66104.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66104.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6627c.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6627c.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x66288.
Definition tfib_A_thunk_66008 : Z := 0x66474.  Definition tfib_E_thunk_66008 : Z := 0x66478.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66798.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x669a4.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66f5c.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66f68.
Definition tfib_A_Printf : Z := 0x66f6c.  Definition tfib_E_Printf : Z := 0x66fb8.
Definition tfib_A_SharedPrintfCode : Z := 0x66fb8.  Definition tfib_E_SharedPrintfCode : Z := 0x67014.
Definition tfib_A_Report : Z := 0x67014.  Definition tfib_E_Report : Z := 0x67060.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68b58.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68bb4.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68bb4.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68df0.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68df0.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69114.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x696b4.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69784.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69784.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69ad4.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69ad4.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69ae4.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69d20.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69d64.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69d64.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69dc4.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69dc4.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a23c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6aafc.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6ae20.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6ae28.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6af2c.
Definition tfib_A_AddDieCallback : Z := 0x6b6dc.  Definition tfib_E_AddDieCallback : Z := 0x6b764.
Definition tfib_A_Die : Z := 0x6b828.  Definition tfib_E_Die : Z := 0x6b8e8.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b8e8.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b8f4.
Definition tfib_A_CheckFailed : Z := 0x6b8f4.  Definition tfib_E_CheckFailed : Z := 0x6b9ac.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c004.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c0fc.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c0fc.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c228.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c450.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c4cc.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c500.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c7e8.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6c7e8.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6c7ec.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c7ec.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6cbdc.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cbdc.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6ccac.
Definition tfib_A_AndroidLogInit : Z := 0x6d090.  Definition tfib_E_AndroidLogInit : Z := 0x6d094.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d0c4.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d10c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d10c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d358.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6d358.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6d35c.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6d35c.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6d468.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d468.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d56c.
Definition tfib_A_thunk_6d37c : Z := 0x6d7e8.  Definition tfib_E_thunk_6d37c : Z := 0x6d7ec.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d890.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d8b0.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d8b0.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d950.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6d99c.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6d9a0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d9dc.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6daa0.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6daa0.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6db28.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6db28.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6dba0.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6dba0.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dc84.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dd40.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6de74.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e0ac.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e1dc.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6e1dc.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6e23c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e23c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e308.
Definition tfib_A_MprotectNoAccess : Z := 0x6e31c.  Definition tfib_E_MprotectNoAccess : Z := 0x6e33c.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e33c.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e488.
Definition tfib_A_MmapFixedOrDie : Z := 0x6e488.  Definition tfib_E_MmapFixedOrDie : Z := 0x6e498.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x6fc90.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x6fcd4.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6fcd4.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6fd04.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70138.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x7025c.
Definition tfib_A_StackStore_Alloc : Z := 0x7025c.  Definition tfib_E_StackStore_Alloc : Z := 0x70390.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70c44.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70cf8.

Definition tfib_A_StackDepotPut : Z := 0x72734.  Definition tfib_E_StackDepotPut : Z := 0x72754.
Definition tfib_A_StackDepotBase_Put : Z := 0x72754.  Definition tfib_E_StackDepotBase_Put : Z := 0x729d8.
Definition tfib_A_StackDepotBase_Get : Z := 0x729d8.  Definition tfib_E_StackDepotBase_Get : Z := 0x72ae8.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x72ec8.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x72f58.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x72f58.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x73058.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x730b8.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x730c0.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x730c0.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73220.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73220.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73294.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7371c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73834.
Definition tfib_A_thunk_762d8 : Z := 0x76880.  Definition tfib_E_thunk_762d8 : Z := 0x76884.
Definition tfib_A_thunk_77ab0 : Z := 0x78058.  Definition tfib_E_thunk_77ab0 : Z := 0x7805c.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79a84.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79b40.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79b40.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79c18.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x79c18.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x79e8c.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7a1b8.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7a1fc.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a1fc.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a5cc.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a89c.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a954.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bcac.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bcb0.
Definition tfib_A_lsan_register_root_region : Z := 0x7c8b8.  Definition tfib_E_lsan_register_root_region : Z := 0x7cbe8.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cbe8.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d070.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7d070.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7d07c.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7fc34.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7fc4c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7ffd0.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x8004c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x8004c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x800fc.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x800fc.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80114.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80114.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8025c.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x8025c.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80268.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80268.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80274.
Definition tfib_A_main : Z := 0x80274.  Definition tfib_E_main : Z := 0x80538.
Definition tfib_A_target_alloc_init : Z := 0x80538.  Definition tfib_E_target_alloc_init : Z := 0x8053c.
Definition tfib_A_target_alloc_count : Z := 0x8053c.  Definition tfib_E_target_alloc_count : Z := 0x80544.
Definition tfib_A_target_run : Z := 0x80544.
Definition tfib_A_emit_printf : Z := 0x806cc.  Definition tfib_E_emit_printf : Z := 0x80714.


Definition tfib_A_asan_module_ctor : Z := 0x83ef8.  Definition tfib_E_asan_module_ctor : Z := 0x83f30.








Definition tfib_A_asan_module_dtor : Z := 0x83f30.  Definition tfib_E_asan_module_dtor : Z := 0x83f60.






Definition tfib_A_extenddftf2 : Z := 0x84b5c.  Definition tfib_E_extenddftf2 : Z := 0x84cec.
Definition tfib_A_sysconf : Z := 0x8b3d4.  Definition tfib_E_sysconf : Z := 0x8b5fc.
Definition tfib_A_init : Z := 0x8b5fc.  Definition tfib_E_init : Z := 0x8b600.
Definition tfib_A_init_libc : Z := 0x8b600.  Definition tfib_E_init_libc : Z := 0x8b82c.
Definition tfib_A_libc_start_init : Z := 0x8b82c.  Definition tfib_E_libc_start_init : Z := 0x8b878.
Definition tfib_A_libc_start_main : Z := 0x8b878.  Definition tfib_E_libc_start_main : Z := 0x8b8d8.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8b8d8.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8b920.
Definition tfib_A_init_tls : Z := 0x8b9f8.  Definition tfib_E_init_tls : Z := 0x8bca8.
Definition tfib_A_init_ssp : Z := 0x8bca8.  Definition tfib_E_init_ssp : Z := 0x8bd08.
Definition tfib_A_stack_chk_fail : Z := 0x8bd08.  Definition tfib_E_stack_chk_fail : Z := 0x8bd10.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8bd58.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8bdec.
Definition tfib_A_Exit : Z := 0x8bdec.  Definition tfib_E_Exit : Z := 0x8be08.
Definition tfib_A_funcs_on_exit : Z := 0x8be38.  Definition tfib_E_funcs_on_exit : Z := 0x8bf00.
Definition tfib_A_fini_stub_ret : Z := 0x8bf00.  Definition tfib_E_fini_stub_ret : Z := 0x8bf04.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8bf04.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8bfc8.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x8bfc8.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x8bfcc.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8bfcc.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8bfd0.
Definition tfib_A_libc_exit_fini : Z := 0x8bfd0.  Definition tfib_E_libc_exit_fini : Z := 0x8c01c.
Definition tfib_A_exit : Z := 0x8c01c.  Definition tfib_E_exit : Z := 0x8c090.
Definition tfib_A_open : Z := 0x8c290.  Definition tfib_E_open : Z := 0x8c374.
Definition tfib_A_syscall_ret : Z := 0x8c374.  Definition tfib_E_syscall_ret : Z := 0x8c3ac.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8c3ac.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8c554.
Definition tfib_A_calloc : Z := 0x8cb18.  Definition tfib_E_calloc : Z := 0x8cc50.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8cc50.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8cc54.
Definition tfib_A_libc_free : Z := 0x8cc54.  Definition tfib_E_libc_free : Z := 0x8ce20.
Definition tfib_A_get_meta : Z := 0x8ce20.  Definition tfib_E_get_meta : Z := 0x8cf30.
Definition tfib_A_alloc_meta : Z := 0x8d308.  Definition tfib_E_alloc_meta : Z := 0x8d5e0.
Definition tfib_A_libc_malloc_impl : Z := 0x8d5e0.  Definition tfib_E_libc_malloc_impl : Z := 0x8d950.
Definition tfib_A_alloc_slot : Z := 0x8d950.  Definition tfib_E_alloc_slot : Z := 0x8e1f4.
Definition tfib_A_enframe : Z := 0x8e1f4.  Definition tfib_E_enframe : Z := 0x8e344.
Definition tfib_A_malloc_allzerop : Z := 0x8e344.  Definition tfib_E_malloc_allzerop : Z := 0x8e4bc.
Definition tfib_A_getrlimit : Z := 0x8f88c.  Definition tfib_E_getrlimit : Z := 0x8f984.
Definition tfib_A_getrusage : Z := 0x8f984.  Definition tfib_E_getrusage : Z := 0x8f9ac.
Definition tfib_A_setrlimit : Z := 0x8f9ac.  Definition tfib_E_setrlimit : Z := 0x8fa74.
Definition tfib_A_mmap : Z := 0x8fe9c.  Definition tfib_E_mmap : Z := 0x8ff88.
Definition tfib_A_mprotect : Z := 0x8ff88.  Definition tfib_E_mprotect : Z := 0x8ffd0.
Definition tfib_A_munmap : Z := 0x900a4.  Definition tfib_E_munmap : Z := 0x900ec.
Definition tfib_A_sched_yield : Z := 0x903b0.  Definition tfib_E_sched_yield : Z := 0x903d4.
Definition tfib_A_raise_tkill_path : Z := 0x90430.  Definition tfib_E_raise_tkill_path : Z := 0x904a8.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x904a8.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x9067c.
Definition tfib_A_musl_sigaltstack : Z := 0x90774.  Definition tfib_E_musl_sigaltstack : Z := 0x90800.
Definition tfib_A_fprintf : Z := 0x90ddc.  Definition tfib_E_fprintf : Z := 0x90e40.

Definition tfib_A_lockfile : Z := 0x90e40.  Definition tfib_E_lockfile : Z := 0x90f3c.
Definition tfib_A_unlockfile : Z := 0x90f3c.  Definition tfib_E_unlockfile : Z := 0x90f9c.



Definition tfib_A_stdio_read : Z := 0x90b2c.  Definition tfib_E_stdio_read : Z := 0x90c44.
Definition tfib_A_stdio_write : Z := 0x90c4c.  Definition tfib_E_stdio_write : Z := 0x90ddc.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x90afc.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x90b00.
Definition tfib_A_stdio_close : Z := 0x90b00.  Definition tfib_E_stdio_close : Z := 0x90b2c.
Definition tfib_A_fwritex : Z := 0x913d0.  Definition tfib_E_fwritex : Z := 0x91508.
Definition tfib_A_musl_fwrite : Z := 0x91508.  Definition tfib_E_musl_fwrite : Z := 0x915c0.
Definition tfib_A_towrite : Z := 0x915c0.  Definition tfib_E_towrite : Z := 0x91614.
Definition tfib_A_stdio_exit : Z := 0x9122c.  Definition tfib_E_stdio_exit : Z := 0x913d0.
Definition tfib_A_ofl_lock : Z := 0x91614.  Definition tfib_E_ofl_lock : Z := 0x91644.

Definition tfib_A_musl_vfprintf : Z := 0x91790.  Definition tfib_E_musl_vfprintf : Z := 0x91940.
Definition tfib_A_printf_core : Z := 0x91940.  Definition tfib_E_printf_core : Z := 0x92770.
Definition tfib_A_pop_arg : Z := 0x92770.  Definition tfib_E_pop_arg : Z := 0x928a4.
Definition tfib_A_pad : Z := 0x928a4.  Definition tfib_E_pad : Z := 0x92978.
Definition tfib_A_fmt_fp : Z := 0x92978.  Definition tfib_E_fmt_fp : Z := 0x94040.
Definition tfib_A_thunk_931e0 : Z := 0x8c76c.  Definition tfib_E_thunk_931e0 : Z := 0x8c770.
Definition tfib_A_musl_wctomb : Z := 0x90218.  Definition tfib_E_musl_wctomb : Z := 0x9023c.
Definition tfib_A_musl_wcrtomb : Z := 0x900ec.  Definition tfib_E_musl_wcrtomb : Z := 0x90218.
Definition tfib_A_fpclassifyl : Z := 0x8ec94.  Definition tfib_E_fpclassifyl : Z := 0x8ecd8.
Definition tfib_A_letf2 : Z := 0x849d8.  Definition tfib_E_letf2 : Z := 0x84aa0.
Definition tfib_A_multf3 : Z := 0x8e594.  Definition tfib_E_multf3 : Z := 0x8ec94.
Definition tfib_A_floatsitf : Z := 0x8ecd8.  Definition tfib_E_floatsitf : Z := 0x8ede0.
Definition tfib_A_scalbn : Z := 0x8f6e4.  Definition tfib_E_scalbn : Z := 0x8f77c.
Definition tfib_A_subtf3 : Z := 0x84f6c.  Definition tfib_E_subtf3 : Z := 0x84f7c.
Definition tfib_A_addtf3 : Z := 0x84f7c.  Definition tfib_E_addtf3 : Z := 0x85748.
Definition tfib_A_fe_getround : Z := 0x85748.  Definition tfib_E_fe_getround : Z := 0x85778.
Definition tfib_A_fixunstfsi : Z := 0x94048.  Definition tfib_E_fixunstfsi : Z := 0x940dc.
Definition tfib_A_floatunsitf : Z := 0x940dc.  Definition tfib_E_floatunsitf : Z := 0x941c8.
Definition tfib_A_fixtfsi : Z := 0x8f77c.  Definition tfib_E_fixtfsi : Z := 0x8f824.
Definition tfib_A_divtf3 : Z := 0x8ede0.  Definition tfib_E_divtf3 : Z := 0x8f6e4.
Definition tfib_A_musl_vprintf : Z := 0x948a0.  Definition tfib_E_musl_vprintf : Z := 0x948bc.
Definition tfib_A_stdout_write : Z := 0x91650.  Definition tfib_E_stdout_write : Z := 0x916f0.
Definition tfib_A_thunk_95368 : Z := 0x94e54.  Definition tfib_E_thunk_95368 : Z := 0x94e58.
Definition tfib_A_musl_memcmp : Z := 0x94f24.  Definition tfib_E_musl_memcmp : Z := 0x94f54.
Definition tfib_A_musl_memcpy : Z := 0x94f54.  Definition tfib_E_musl_memcpy : Z := 0x95358.
Definition tfib_A_musl_memset : Z := 0x95358.  Definition tfib_E_musl_memset : Z := 0x95450.
Definition tfib_A_musl_strchr : Z := 0x95450.  Definition tfib_E_musl_strchr : Z := 0x9548c.
Definition tfib_A_strchrnul : Z := 0x9548c.  Definition tfib_E_strchrnul : Z := 0x9556c.
Definition tfib_A_musl_strlen : Z := 0x955a4.  Definition tfib_E_musl_strlen : Z := 0x95634.
Definition tfib_A_musl_strnlen : Z := 0x957e0.  Definition tfib_E_musl_strnlen : Z := 0x95824.
Definition tfib_A_musl_memchr : Z := 0x94e58.  Definition tfib_E_musl_memchr : Z := 0x94f24.
Definition tfib_A_lock : Z := 0x95824.  Definition tfib_E_lock : Z := 0x95aac.
Definition tfib_A_unlock : Z := 0x95aac.  Definition tfib_E_unlock : Z := 0x95b20.
Definition tfib_A_syscall_cp_c : Z := 0x95b20.  Definition tfib_E_syscall_cp_c : Z := 0x95b44.
Definition tfib_A_syscall_cp_sccp : Z := 0x95b44.  Definition tfib_E_syscall_cp_sccp : Z := 0x95b48.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x95b48.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x95b6c.
Definition tfib_A_pthread_atfork : Z := 0x95b84.  Definition tfib_E_pthread_atfork : Z := 0x95c28.
Definition tfib_A_mremap : Z := 0x8ffd0.  Definition tfib_E_mremap : Z := 0x900a4.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x96bfc.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x96c18.
Definition tfib_A_pthread_key_create : Z := 0x96fa4.  Definition tfib_E_pthread_key_create : Z := 0x97078.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9731c.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x973c0.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x973c0.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x974dc.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x974dc.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x97508.
Definition tfib_A_pthread_setspecific : Z := 0x97540.  Definition tfib_E_pthread_setspecific : Z := 0x97574.
Definition tfib_A_set_thread_area : Z := 0x9757c.  Definition tfib_E_set_thread_area : Z := 0x97588.
Definition tfib_A_thunk_96f9c : Z := 0x97574.  Definition tfib_E_thunk_96f9c : Z := 0x9757c.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97ea8.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97f60.
Definition tfib_A_close : Z := 0x9a578.  Definition tfib_E_close : Z := 0x9a5cc.
Definition tfib_A_musl_read : Z := 0x9a658.  Definition tfib_E_musl_read : Z := 0x9a68c.
Definition tfib_A_vm_wait : Z := 0x97bb8.  Definition tfib_E_vm_wait : Z := 0x97c08.
Definition tfib_D_str_sealed : Z := 0x11855.
Definition tfib_D_init_array_0_3 : Z := 0x9b690.
Definition tfib_D_fini_array_0_1 : Z := 0x9b6b0.
Definition tfib_D_GOT_common_flags : Z := 0x9be60.
Definition tfib_D_GOT_flags : Z := 0x9be68.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9be70.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9be78.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9be80.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9be88.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9c9d8.
Definition tfib_D_REAL_read : Z := 0x9dba8.
Definition tfib_D_REAL_memcpy : Z := 0x9dcd0.
Definition tfib_D_REAL_memset : Z := 0x9dcd8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa15d8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa2438.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa4c38.
Definition tfib_D_asan_inited : Z := 0xa5918.
Definition tfib_D_replace_intrin_cached : Z := 0xa5919.
Definition tfib_D_kHighMemEnd : Z := 0xa5920.
Definition tfib_D_kMidMemBeg : Z := 0xa5928.
Definition tfib_D_kMidMemEnd : Z := 0xa5930.
Definition tfib_D_malloc_context_size : Z := 0xa593c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136768.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f7e60.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x309d4.
Definition tfib_at_rw_lo : Z := 0x9d000.
Definition tfib_at_rw_len : Z := 0x55d000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63bec.
Definition tfib_at_x_imemcpy : Z := 0x63b70.
Definition tfib_at_x_memset : Z := 0x95358.
Definition tfib_at_x_memcpy : Z := 0x94f54.
Definition tfib_at_x_memiszero : Z := 0x6411c.
Definition tfib_at_x_istrncpy : Z := 0x64018.
Definition tfib_at_x_sealed : Z := 0x11855.
Definition tfib_at_x_popfree : Z := 0x36dc0.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8b638.
Definition tfib_at_x_envscan_k : Z := 0x8b644.
Definition tfib_at_x_pnscan : Z := 0x8b6fc.
Definition tfib_at_x_pnscan_k : Z := 0x8b708.
Definition tfib_at_stops_more : list Z := (0x34a34 :: 0x36058 :: 0x53ef8 :: 0x5a2b0 :: 0x5a2c4 :: 0x5a2d8 :: 0x5fc68 :: 0x5fd38 :: 0x6d264 :: 0x6e170 :: 0x6e300 :: 0x78058 :: nil)%list.
