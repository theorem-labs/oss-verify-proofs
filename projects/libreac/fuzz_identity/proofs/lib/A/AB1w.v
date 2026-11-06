(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1w.v (donor image sha256 7093581aab04), with its addresses changed; 7 of its 519 lines of code are new or changed and 100 lines of the source are left out. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2306c.
Definition tfib_text_lo : Z := 0x309b8.
Definition tfib_init_array_lo : Z := 0x9ad50.  Definition tfib_init_array_hi : Z := 0x9ad70.
Definition tfib_fini_array_lo : Z := 0x9ad70.  Definition tfib_fini_array_hi : Z := 0x9ad80.
Definition tfib_preinit_array_lo : Z := 0x9ad80.  Definition tfib_preinit_array_hi : Z := 0x9ad88.
Definition tfib_data_rel_ro_lo : Z := 0x9ada0.  Definition tfib_data_rel_ro_hi : Z := 0x9c350.
Definition tfib_got_lo : Z := 0x9c350.  Definition tfib_got_hi : Z := 0x9d0a8.
Definition tfib_data_lo : Z := 0x9e0a8.  Definition tfib_data_hi : Z := 0xa0c60.
Definition tfib_asan_globals_lo : Z := 0xa0c60.  Definition tfib_asan_globals_hi : Z := 0xa18e0.
Definition tfib_bss_lo : Z := 0xa1900.  Definition tfib_bss_hi : Z := 0x5f9830.
Definition tfib_tbss_lo : Z := 0x99d50.  Definition tfib_tbss_hi : Z := 0x99d64.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x309b8.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x309b8.  Definition tfib_E_start : Z := 0x30a00.
Definition tfib_A_do_init : Z := 0x30a00.  Definition tfib_E_do_init : Z := 0x30a74.
Definition tfib_A_do_fini : Z := 0x30a74.  Definition tfib_E_do_fini : Z := 0x30b04.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30b04.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30b40.
Definition tfib_A_InitializeAllocator : Z := 0x30cb0.  Definition tfib_E_InitializeAllocator : Z := 0x30cc8.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30cc8.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30e34.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31390.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x314ec.
Definition tfib_A_asan_free : Z := 0x318c0.  Definition tfib_E_asan_free : Z := 0x318e8.
Definition tfib_A_Allocator_Deallocate : Z := 0x318e8.  Definition tfib_E_Allocator_Deallocate : Z := 0x31ba0.
Definition tfib_A_asan_malloc : Z := 0x31ba0.  Definition tfib_E_asan_malloc : Z := 0x31bfc.
Definition tfib_A_Allocator_Allocate : Z := 0x31bfc.  Definition tfib_E_Allocator_Allocate : Z := 0x32584.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32cbc.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32e00.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32eec.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f48.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32f48.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33198.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33198.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3328c.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x3328c.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33374.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x337a8.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x3398c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33c48.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33ecc.
(* Theorem Labs, 2026-10-29: six rows added for six functions of identity's own .symtab that the table
   lacked, each checked against that .symtab (E = st_value + st_size). A second derivation found them missing and
   corrected its own entry end from 0x82874 to 0x8251c; I re-derived every value here. *)
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x8070c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x8251c.  (* LLVMFuzzerTestOneInput: LLVMFuzzerTestOneInput, size 0x1e10 *)
Definition tfib_A_stack_malloc_0 : Z := 0x3cf80.  Definition tfib_E_stack_malloc_0 : Z := 0x3d0f4.  (* __asan_stack_malloc_0: __asan_stack_malloc_0 *)
Definition tfib_A_stack_malloc_3 : Z := 0x3d0f4.  Definition tfib_E_stack_malloc_3 : Z := 0x3d2a0.  (* __asan_stack_malloc_3: __asan_stack_malloc_3 *)
Definition tfib_A_stack_malloc_4 : Z := 0x3d2a0.  Definition tfib_E_stack_malloc_4 : Z := 0x3d46c.  (* __asan_stack_malloc_4: __asan_stack_malloc_4 *)
Definition tfib_A_MemToShadow_2 : Z := 0x3d46c.  Definition tfib_E_MemToShadow_2 : Z := 0x3d5a8.  (* _ZN6__asanL11MemToShadowEm: _ZN6__asanL11MemToShadowEm, size 0x13c (copy 2 of 5) *)
Definition tfib_A_StackDepotNode_store : Z := 0x72444.  Definition tfib_E_StackDepotNode_store : Z := 0x724a0.  (* _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy: _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy, size 0x5c *)
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33ecc.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x3404c.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3404c.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34214.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34214.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x343e0.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x343e0.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34480.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34480.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34584.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x348ac.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x349f4.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x349f4.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34a2c.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x351c4.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x354ac.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35b84.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35cfc.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35cfc.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35eac.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35eac.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x36090.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x36090.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36368.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36368.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x367e0.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x367e0.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x368e0.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x368e0.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36be8.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36be8.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36f58.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36f58.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x37070.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37474.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x3755c.
Definition tfib_A_AsanActivate : Z := 0x3755c.  Definition tfib_E_AsanActivate : Z := 0x37638.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37b14.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x37bfc.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c6b4.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c78c.
Definition tfib_A_FakeStack_Create : Z := 0x3c78c.  Definition tfib_E_FakeStack_Create : Z := 0x3c878.
Definition tfib_A_FakeStack_Allocate : Z := 0x3cb34.  Definition tfib_E_FakeStack_Allocate : Z := 0x3ce1c.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cf50.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cf80.



Definition tfib_A_asan_InitializeFlags : Z := 0x3d5a8.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e5d4.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ece0.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fafc.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3fafc.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x400c8.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x4081c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40a8c.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40a8c.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40d94.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x42074.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x4218c.
Definition tfib_A_strlen : Z := 0x4218c.  Definition tfib_E_strlen : Z := 0x42190.
Definition tfib_A_strnlen : Z := 0x42190.  Definition tfib_E_strnlen : Z := 0x42194.
Definition tfib_A_strcmp : Z := 0x42194.  Definition tfib_E_strcmp : Z := 0x42198.
Definition tfib_A_strchr : Z := 0x42198.  Definition tfib_E_strchr : Z := 0x4219c.
Definition tfib_A_memcmp : Z := 0x4219c.  Definition tfib_E_memcmp : Z := 0x421a0.
Definition tfib_A_memchr : Z := 0x421a4.  Definition tfib_E_memchr : Z := 0x421a8.
Definition tfib_A_frexpl : Z := 0x421a8.  Definition tfib_E_frexpl : Z := 0x421ac.
Definition tfib_A_read : Z := 0x421ac.  Definition tfib_E_read : Z := 0x421b0.
Definition tfib_A_fwrite : Z := 0x421b0.  Definition tfib_E_fwrite : Z := 0x421b4.
Definition tfib_A_time : Z := 0x421b4.  Definition tfib_E_time : Z := 0x421b8.
Definition tfib_A_gmtime_r : Z := 0x421b8.  Definition tfib_E_gmtime_r : Z := 0x421bc.
Definition tfib_A_vprintf : Z := 0x421bc.  Definition tfib_E_vprintf : Z := 0x421c0.
Definition tfib_A_vfprintf : Z := 0x421c0.  Definition tfib_E_vfprintf : Z := 0x421c4.
Definition tfib_A_vsnprintf : Z := 0x421c4.  Definition tfib_E_vsnprintf : Z := 0x421c8.
Definition tfib_A_thunk_417bc : Z := 0x421cc.  Definition tfib_E_thunk_417bc : Z := 0x421d0.
Definition tfib_A_clock_gettime : Z := 0x421d0.  Definition tfib_E_clock_gettime : Z := 0x421d4.
Definition tfib_A_wcrtomb : Z := 0x421d4.  Definition tfib_E_wcrtomb : Z := 0x421d8.
Definition tfib_A_wctomb : Z := 0x421d8.  Definition tfib_E_wctomb : Z := 0x421dc.
Definition tfib_A_thunk_417cc : Z := 0x421dc.  Definition tfib_E_thunk_417cc : Z := 0x421e4.
Definition tfib_A_pthread_attr_getstack : Z := 0x421e4.  Definition tfib_E_pthread_attr_getstack : Z := 0x421e8.
Definition tfib_A_tls_get_addr_thunk : Z := 0x421e8.  Definition tfib_E_tls_get_addr_thunk : Z := 0x421ec.

Definition tfib_A_thunk_417dc : Z := 0x421ec.  Definition tfib_E_thunk_417dc : Z := 0x421f0.

Definition tfib_A_thunk_417e4 : Z := 0x421f0.  Definition tfib_E_thunk_417e4 : Z := 0x421f4.
Definition tfib_A_thunk_417e8 : Z := 0x421f4.  Definition tfib_E_thunk_417e8 : Z := 0x421f8.
Definition tfib_A_thunk_417ec : Z := 0x421f8.  Definition tfib_E_thunk_417ec : Z := 0x421fc.
Definition tfib_A_thunk_417f0 : Z := 0x421fc.  Definition tfib_E_thunk_417f0 : Z := 0x42200.
Definition tfib_A_sem_timedwait : Z := 0x42200.  Definition tfib_E_sem_timedwait : Z := 0x42204.
Definition tfib_A_thunk_417f8 : Z := 0x42204.  Definition tfib_E_thunk_417f8 : Z := 0x42208.
Definition tfib_A_pthread_setcancelstate : Z := 0x42208.  Definition tfib_E_pthread_setcancelstate : Z := 0x4220c.
Definition tfib_A_send : Z := 0x4220c.  Definition tfib_E_send : Z := 0x42210.
Definition tfib_A_sendto : Z := 0x42210.  Definition tfib_E_sendto : Z := 0x42214.
Definition tfib_A_sigaltstack : Z := 0x42214.  Definition tfib_E_sigaltstack : Z := 0x42218.
Definition tfib_A_thunk_4180c : Z := 0x42218.  Definition tfib_E_thunk_4180c : Z := 0x4221c.
Definition tfib_A_icpt_strlen : Z := 0x4221c.  Definition tfib_E_icpt_strlen : Z := 0x424b0.
Definition tfib_A_icpt_strnlen : Z := 0x424b0.  Definition tfib_E_icpt_strnlen : Z := 0x42744.
Definition tfib_A_icpt_strcmp : Z := 0x42748.  Definition tfib_E_icpt_strcmp : Z := 0x42c78.
Definition tfib_A_icpt_strchr : Z := 0x42c78.  Definition tfib_E_icpt_strchr : Z := 0x42f58.
Definition tfib_A_icpt_memcmp : Z := 0x437f0.  Definition tfib_E_icpt_memcmp : Z := 0x438ac.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x438ac.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x43968.
Definition tfib_A_icpt_memchr : Z := 0x43968.  Definition tfib_E_icpt_memchr : Z := 0x43c38.
Definition tfib_A_icpt_frexpl : Z := 0x43c38.  Definition tfib_E_icpt_frexpl : Z := 0x43eb0.
Definition tfib_A_icpt_read : Z := 0x43eb0.  Definition tfib_E_icpt_read : Z := 0x44120.
Definition tfib_A_icpt_fwrite : Z := 0x44120.  Definition tfib_E_icpt_fwrite : Z := 0x44394.
Definition tfib_A_icpt_time : Z := 0x44394.  Definition tfib_E_icpt_time : Z := 0x44630.
Definition tfib_A_icpt_gmtime_r : Z := 0x44838.  Definition tfib_E_icpt_gmtime_r : Z := 0x44a78.
Definition tfib_A_icpt_vprintf : Z := 0x44a78.  Definition tfib_E_icpt_vprintf : Z := 0x44b14.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44b14.  Definition tfib_E_printf_common_format_interceptor : Z := 0x455dc.
Definition tfib_A_icpt_vfprintf : Z := 0x455dc.  Definition tfib_E_icpt_vfprintf : Z := 0x45690.
Definition tfib_A_icpt_vsnprintf : Z := 0x45690.  Definition tfib_E_icpt_vsnprintf : Z := 0x459a8.
Definition tfib_A_icpt_clock_gettime : Z := 0x45b24.  Definition tfib_E_icpt_clock_gettime : Z := 0x45d7c.
Definition tfib_A_icpt_wcrtomb : Z := 0x45d7c.  Definition tfib_E_icpt_wcrtomb : Z := 0x462ec.
Definition tfib_A_icpt_wctomb : Z := 0x462ec.  Definition tfib_E_icpt_wctomb : Z := 0x46648.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46714.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46afc.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b08.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b84.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46d90.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47028.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47058.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47280.
Definition tfib_A_icpt_send : Z := 0x47280.  Definition tfib_E_icpt_send : Z := 0x47534.
Definition tfib_A_icpt_sendto : Z := 0x47534.  Definition tfib_E_icpt_sendto : Z := 0x477f8.
Definition tfib_A_icpt_sigaltstack : Z := 0x477f8.  Definition tfib_E_icpt_sigaltstack : Z := 0x47a54.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b28.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47cd8.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48a1c.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x516f4.
Definition tfib_A_memset : Z := 0x51850.  Definition tfib_E_memset : Z := 0x51854.
Definition tfib_A_memcpy : Z := 0x51854.  Definition tfib_E_memcpy : Z := 0x51858.
Definition tfib_A_asan_memcpy : Z := 0x51858.  Definition tfib_E_asan_memcpy : Z := 0x51cf4.
Definition tfib_A_asan_memset : Z := 0x51cf4.  Definition tfib_E_asan_memset : Z := 0x51f34.
Definition tfib_A_icpt_memset : Z := 0x51f34.  Definition tfib_E_icpt_memset : Z := 0x52224.
Definition tfib_A_icpt_memcpy : Z := 0x52224.  Definition tfib_E_icpt_memcpy : Z := 0x52814.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52814.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5284c.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x5284c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52850.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52850.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52854.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52854.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x528b4.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52900.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52a3c.
Definition tfib_A_free : Z := 0x52ba8.  Definition tfib_E_free : Z := 0x52bac.
Definition tfib_A_malloc : Z := 0x52bac.  Definition tfib_E_malloc : Z := 0x52bb0.
Definition tfib_A_icpt_free : Z := 0x52bb0.  Definition tfib_E_icpt_free : Z := 0x52d80.
Definition tfib_A_icpt_malloc : Z := 0x52d80.  Definition tfib_E_icpt_malloc : Z := 0x52edc.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52fa8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52fac.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x52fac.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x530ac.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53a28.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53a38.
Definition tfib_A_CanPoisonMemory : Z := 0x53a38.  Definition tfib_E_CanPoisonMemory : Z := 0x53a4c.
Definition tfib_A_PoisonShadow : Z := 0x53a4c.  Definition tfib_E_PoisonShadow : Z := 0x53f48.
Definition tfib_A_MemToShadow_checked : Z := 0x53f48.  Definition tfib_E_MemToShadow_checked : Z := 0x54084.
Definition tfib_A_asan_region_is_poisoned : Z := 0x543d4.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54718.
Definition tfib_A_AsanTSDInit : Z := 0x54b38.  Definition tfib_E_AsanTSDInit : Z := 0x54bb4.
Definition tfib_A_AsanTSDGet : Z := 0x54bb4.  Definition tfib_E_AsanTSDGet : Z := 0x54bf4.
Definition tfib_A_AsanTSDSet : Z := 0x54bf4.  Definition tfib_E_AsanTSDSet : Z := 0x54c34.
Definition tfib_A_PlatformTSDDtor : Z := 0x54c34.  Definition tfib_E_PlatformTSDDtor : Z := 0x54cb8.
Definition tfib_A_InstallAtForkHandler : Z := 0x54cb8.  Definition tfib_E_InstallAtForkHandler : Z := 0x54cd4.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54d34.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54d78.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x55490.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x5569c.
Definition tfib_A_ReportDoubleFree : Z := 0x55da4.  Definition tfib_E_ReportDoubleFree : Z := 0x56034.
Definition tfib_A_ReportGenericError : Z := 0x57910.  Definition tfib_E_ReportGenericError : Z := 0x581cc.
Definition tfib_A_AsanInited : Z := 0x58958.  Definition tfib_E_AsanInited : Z := 0x58970.
Definition tfib_A_asan_report_load1 : Z := 0x58970.  Definition tfib_E_asan_report_load1 : Z := 0x589c0.
Definition tfib_A_asan_report_exp_load1 : Z := 0x589c0.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58a10.
Definition tfib_A_asan_report_load2 : Z := 0x58a10.  Definition tfib_E_asan_report_load2 : Z := 0x58a60.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58a60.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58ab0.
Definition tfib_A_asan_report_load4 : Z := 0x58ab0.  Definition tfib_E_asan_report_load4 : Z := 0x58b00.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58b00.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58b50.
Definition tfib_A_asan_report_load8 : Z := 0x58b50.  Definition tfib_E_asan_report_load8 : Z := 0x58ba0.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58ba0.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58bf0.
Definition tfib_A_asan_report_load16 : Z := 0x58bf0.  Definition tfib_E_asan_report_load16 : Z := 0x58c40.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58c40.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58c90.
Definition tfib_A_asan_report_store1 : Z := 0x58c90.  Definition tfib_E_asan_report_store1 : Z := 0x58ce0.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58ce0.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58d30.
Definition tfib_A_asan_report_store2 : Z := 0x58d30.  Definition tfib_E_asan_report_store2 : Z := 0x58d80.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58d80.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58dd0.
Definition tfib_A_asan_report_store4 : Z := 0x58dd0.  Definition tfib_E_asan_report_store4 : Z := 0x58e20.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58e20.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58e70.
Definition tfib_A_asan_report_store8 : Z := 0x58e70.  Definition tfib_E_asan_report_store8 : Z := 0x58ec0.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58ec0.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58f10.
Definition tfib_A_asan_report_store16 : Z := 0x58f10.  Definition tfib_E_asan_report_store16 : Z := 0x58f60.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58f60.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58fb0.
Definition tfib_A_asan_report_load_n : Z := 0x58fb0.  Definition tfib_E_asan_report_load_n : Z := 0x59000.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59000.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59050.
Definition tfib_A_asan_report_store_n : Z := 0x59050.  Definition tfib_E_asan_report_store_n : Z := 0x590a0.
Definition tfib_A_asan_report_exp_store_n : Z := 0x590a0.  Definition tfib_E_asan_report_exp_store_n : Z := 0x590f0.
Definition tfib_A_InitializeHighMemEnd : Z := 0x590f0.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59170.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59170.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59524.
Definition tfib_A_AsanInitInternal : Z := 0x595b4.  Definition tfib_E_AsanInitInternal : Z := 0x59868.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59868.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59908.
Definition tfib_A_thunk_59674 : Z := 0x59ad0.  Definition tfib_E_thunk_59674 : Z := 0x59ad4.
Definition tfib_A_asan_init : Z := 0x59ad4.  Definition tfib_E_asan_init : Z := 0x59b68.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59b68.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59b6c.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59dd0.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a0f8.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a0f8.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a2d8.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a2d8.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a5e0.
Definition tfib_A_SetMallocContextSize : Z := 0x5a5e0.  Definition tfib_E_SetMallocContextSize : Z := 0x5a5f0.
Definition tfib_A_GetMallocContextSize : Z := 0x5a5f0.  Definition tfib_E_GetMallocContextSize : Z := 0x5a600.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a600.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a750.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5ab30.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5add0.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b234.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b26c.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5b514.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5b520.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b520.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b5ac.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b5ac.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b614.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b614.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b68c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b68c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b6f4.
Definition tfib_A_AsanThread_Create : Z := 0x5bc58.  Definition tfib_E_AsanThread_Create : Z := 0x5bdf4.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5be50.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c068.
Definition tfib_A_GetCurrentThread : Z := 0x5c068.  Definition tfib_E_GetCurrentThread : Z := 0x5c088.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c22c.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c284.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c284.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c2dc.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c2dc.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c50c.
Definition tfib_A_AsanThread_Init : Z := 0x5c50c.  Definition tfib_E_AsanThread_Init : Z := 0x5c900.
Definition tfib_A_CreateMainThread : Z := 0x5ca40.  Definition tfib_E_CreateMainThread : Z := 0x5cb50.
Definition tfib_A_SetCurrentThread : Z := 0x5cb50.  Definition tfib_E_SetCurrentThread : Z := 0x5cc30.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5ce34.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5cf70.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e0e4.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e23c.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e580.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e5cc.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e5cc.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e5d8.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e608.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e614.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e614.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e620.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e63c.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e908.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e908.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ecc8.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5fc24.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5fc30.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fc30.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fd08.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fd08.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fda4.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x602c8.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6030c.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60584.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60698.
Definition tfib_A_RunMallocHooks : Z := 0x6083c.  Definition tfib_E_RunMallocHooks : Z := 0x608f4.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x608f4.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x608f8.
Definition tfib_A_RunFreeHooks : Z := 0x608f8.  Definition tfib_E_RunFreeHooks : Z := 0x609a4.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x609d8.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60a24.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60ce8.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60f28.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61524.  Definition tfib_E_sanitizer_set_report_path : Z := 0x6153c.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61680.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x61688.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x6314c.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x6345c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x6345c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x635a0.
Definition tfib_A_FlagParser_ParseString : Z := 0x635a0.  Definition tfib_E_FlagParser_ParseString : Z := 0x63694.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63828.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63888.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63888.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x638c8.
Definition tfib_A_internal_atoll : Z := 0x638c8.  Definition tfib_E_internal_atoll : Z := 0x639b4.
Definition tfib_A_internal_simple_strtoll : Z := 0x639b4.  Definition tfib_E_internal_simple_strtoll : Z := 0x63b10.
Definition tfib_A_internal_memchr : Z := 0x63b10.  Definition tfib_E_internal_memchr : Z := 0x63b30.
Definition tfib_A_internal_memcmp : Z := 0x63b30.  Definition tfib_E_internal_memcmp : Z := 0x63b68.
Definition tfib_A_internal_memcpy : Z := 0x63b68.  Definition tfib_E_internal_memcpy : Z := 0x63b8c.
Definition tfib_A_internal_memmove : Z := 0x63b8c.  Definition tfib_E_internal_memmove : Z := 0x63be4.
Definition tfib_A_internal_memset : Z := 0x63be4.  Definition tfib_E_internal_memset : Z := 0x63c44.
Definition tfib_A_internal_strcspn : Z := 0x63c44.  Definition tfib_E_internal_strcspn : Z := 0x63c98.
Definition tfib_A_internal_strdup : Z := 0x63ccc.  Definition tfib_E_internal_strdup : Z := 0x63d38.
Definition tfib_A_internal_strlen : Z := 0x63d38.  Definition tfib_E_internal_strlen : Z := 0x63d54.
Definition tfib_A_internal_strchrnul : Z := 0x63de4.  Definition tfib_E_internal_strchrnul : Z := 0x63e2c.
Definition tfib_A_internal_strrchr : Z := 0x63e2c.  Definition tfib_E_internal_strrchr : Z := 0x63e6c.
Definition tfib_A_internal_strnlen : Z := 0x63f9c.  Definition tfib_E_internal_strnlen : Z := 0x63fcc.
Definition tfib_A_internal_strncpy : Z := 0x64010.  Definition tfib_E_internal_strncpy : Z := 0x64080.
Definition tfib_A_internal_strstr : Z := 0x64080.  Definition tfib_E_internal_strstr : Z := 0x64114.
Definition tfib_A_mem_is_zero : Z := 0x64114.  Definition tfib_E_mem_is_zero : Z := 0x641c8.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x641c8.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x641d8.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x641d8.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x643b8.
Definition tfib_A_internal_iserror : Z := 0x643c4.  Definition tfib_E_internal_iserror : Z := 0x643e4.
Definition tfib_A_internal_mmap : Z := 0x643e4.  Definition tfib_E_internal_mmap : Z := 0x643f0.
Definition tfib_A_internal_munmap : Z := 0x643f0.  Definition tfib_E_internal_munmap : Z := 0x643fc.
Definition tfib_A_internal_mprotect : Z := 0x643fc.  Definition tfib_E_internal_mprotect : Z := 0x6440c.
Definition tfib_A_internal_madvise : Z := 0x6440c.  Definition tfib_E_internal_madvise : Z := 0x64438.
Definition tfib_A_internal_close : Z := 0x64438.  Definition tfib_E_internal_close : Z := 0x64444.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64444.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64468.
Definition tfib_A_internal_read : Z := 0x64468.  Definition tfib_E_internal_read : Z := 0x644a0.
Definition tfib_A_internal_write : Z := 0x644a0.  Definition tfib_E_internal_write : Z := 0x644d8.
Definition tfib_A_internal_ftruncate : Z := 0x644d8.  Definition tfib_E_internal_ftruncate : Z := 0x64510.
Definition tfib_A_internal_dup : Z := 0x64510.  Definition tfib_E_internal_dup : Z := 0x6451c.
Definition tfib_A_internal_dup2_dup3 : Z := 0x6451c.  Definition tfib_E_internal_dup2_dup3 : Z := 0x6452c.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x6452c.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64544.
Definition tfib_A_internal_sched_yield : Z := 0x64544.  Definition tfib_E_internal_sched_yield : Z := 0x64550.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64550.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x6459c.
Definition tfib_A_internal_execve : Z := 0x6459c.  Definition tfib_E_internal_execve : Z := 0x645a8.
Definition tfib_A_internal_exit_exit_group : Z := 0x645a8.  Definition tfib_E_internal_exit_exit_group : Z := 0x645bc.
Definition tfib_A_FileExists_newfstatat : Z := 0x645bc.  Definition tfib_E_FileExists_newfstatat : Z := 0x6463c.
Definition tfib_A_DirExists_newfstatat : Z := 0x6463c.  Definition tfib_E_DirExists_newfstatat : Z := 0x646a0.
Definition tfib_A_GetTid_gettid : Z := 0x646a0.  Definition tfib_E_GetTid_gettid : Z := 0x646ac.
Definition tfib_A_GetEnv : Z := 0x646ac.  Definition tfib_E_GetEnv : Z := 0x647dc.
Definition tfib_A_FutexWait : Z := 0x648e0.  Definition tfib_E_FutexWait : Z := 0x64904.
Definition tfib_A_FutexWake : Z := 0x64904.  Definition tfib_E_FutexWake : Z := 0x64928.
Definition tfib_A_internal_ptrace : Z := 0x64928.  Definition tfib_E_internal_ptrace : Z := 0x64934.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64934.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64944.
Definition tfib_A_internal_getpid : Z := 0x64944.  Definition tfib_E_internal_getpid : Z := 0x64950.
Definition tfib_A_internal_getppid : Z := 0x64950.  Definition tfib_E_internal_getppid : Z := 0x6495c.
Definition tfib_A_internal_prctl : Z := 0x6495c.  Definition tfib_E_internal_prctl : Z := 0x64968.
Definition tfib_A_internal_sigaltstack : Z := 0x64968.  Definition tfib_E_internal_sigaltstack : Z := 0x64974.
Definition tfib_A_internal_fork_clone : Z := 0x64974.  Definition tfib_E_internal_fork_clone : Z := 0x6498c.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6498c.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64ab8.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x651f8.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65310.
Definition tfib_A_GetPageSizeCached : Z := 0x65310.  Definition tfib_E_GetPageSizeCached : Z := 0x65318.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65318.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x653c4.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x653c4.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x654e4.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x655ac.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x6562c.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65688.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65754.
Definition tfib_A_thunk_653ec : Z := 0x65850.  Definition tfib_E_thunk_653ec : Z := 0x65854.
Definition tfib_A_CheckASLR : Z := 0x65854.  Definition tfib_E_CheckASLR : Z := 0x65858.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65aa4.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65aa8.
Definition tfib_A_MmapOrDie : Z := 0x65ab4.  Definition tfib_E_MmapOrDie : Z := 0x65bc0.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65bc0.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65c34.
Definition tfib_A_UnmapOrDie : Z := 0x65c34.  Definition tfib_E_UnmapOrDie : Z := 0x65cb0.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65cb0.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65dc0.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65fec.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x660f0.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x660fc.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66274.
Definition tfib_A_thunk_66008 : Z := 0x6646c.  Definition tfib_E_thunk_66008 : Z := 0x66470.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66790.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6699c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66f54.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66f60.
Definition tfib_A_Printf : Z := 0x66f64.  Definition tfib_E_Printf : Z := 0x66fb0.
Definition tfib_A_SharedPrintfCode : Z := 0x66fb0.  Definition tfib_E_SharedPrintfCode : Z := 0x6700c.
Definition tfib_A_Report : Z := 0x6700c.  Definition tfib_E_Report : Z := 0x67058.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68b50.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68bac.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68bac.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68de8.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68de8.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6910c.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x696ac.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6977c.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6977c.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69acc.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69dbc.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a234.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6aaf4.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6ae18.
Definition tfib_A_AddDieCallback : Z := 0x6b6d4.  Definition tfib_E_AddDieCallback : Z := 0x6b75c.
Definition tfib_A_Die : Z := 0x6b820.  Definition tfib_E_Die : Z := 0x6b8e0.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b8e0.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b8ec.
Definition tfib_A_CheckFailed : Z := 0x6b8ec.  Definition tfib_E_CheckFailed : Z := 0x6b9a4.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6bffc.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c0f4.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c0f4.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c220.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c448.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c4c4.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c4f8.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c7e0.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cbd4.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cca4.
Definition tfib_A_AndroidLogInit : Z := 0x6d088.  Definition tfib_E_AndroidLogInit : Z := 0x6d08c.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d0bc.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d104.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d104.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d350.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6d354.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6d460.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d460.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d564.
Definition tfib_A_thunk_6d37c : Z := 0x6d7e0.  Definition tfib_E_thunk_6d37c : Z := 0x6d7e4.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d8a8.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d948.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d9d4.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6da98.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6da98.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6db20.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6db20.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6db98.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6db98.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dc7c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dd38.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6de6c.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e0a4.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e1d4.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e234.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e300.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e334.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e480.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70130.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70254.
Definition tfib_A_StackStore_Alloc : Z := 0x70254.  Definition tfib_E_StackStore_Alloc : Z := 0x70388.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70c3c.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70cf0.

Definition tfib_A_StackDepotPut : Z := 0x7272c.  Definition tfib_E_StackDepotPut : Z := 0x7274c.
Definition tfib_A_StackDepotBase_Put : Z := 0x7274c.  Definition tfib_E_StackDepotBase_Put : Z := 0x729d0.
Definition tfib_A_StackDepotBase_Get : Z := 0x729d0.  Definition tfib_E_StackDepotBase_Get : Z := 0x72ae0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x730b0.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x730b8.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x730b8.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73218.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73218.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x7328c.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73714.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7382c.
Definition tfib_A_thunk_762d8 : Z := 0x76878.  Definition tfib_E_thunk_762d8 : Z := 0x7687c.
Definition tfib_A_thunk_77ab0 : Z := 0x78050.  Definition tfib_E_thunk_77ab0 : Z := 0x78054.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79a7c.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79b38.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79b38.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79c10.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a1f4.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a5c4.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a894.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a94c.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bca4.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bca8.
Definition tfib_A_lsan_register_root_region : Z := 0x7c8b0.  Definition tfib_E_lsan_register_root_region : Z := 0x7cbe0.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cbe0.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d068.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7ffc8.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80044.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80044.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x800f4.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x800f4.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x8010c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8010c.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80254.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80254.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80260.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80260.  Definition tfib_E_asan_default_options_cli_c : Z := 0x8026c.
Definition tfib_A_main : Z := 0x8026c.  Definition tfib_E_main : Z := 0x80530.
Definition tfib_A_target_alloc_init : Z := 0x80530.  Definition tfib_E_target_alloc_init : Z := 0x80534.
Definition tfib_A_target_alloc_count : Z := 0x80534.  Definition tfib_E_target_alloc_count : Z := 0x8053c.
(* tfib_E_target_run is target_run THROUGH oft_exit_guard - the exit walk's region, not target_run's own
   end: this image's .symtab has target_run 0x8053c..0x80694 and oft_exit_guard 0x80694..0x806c4, and the
   0x30 bytes between them are the guard's code. The B core states the same region against its own image
   (lib/ReusableB/YB1w.v: 0x805a4..0x8072c), so each copy is derived from the image it describes. *)
Definition tfib_A_target_run : Z := 0x8053c.  Definition tfib_E_target_run : Z := 0x806c4.
Definition tfib_A_emit_printf : Z := 0x806c4.  Definition tfib_E_emit_printf : Z := 0x8070c.


Definition tfib_A_asan_module_ctor : Z := 0x82874.  Definition tfib_E_asan_module_ctor : Z := 0x828ac.








Definition tfib_A_asan_module_dtor : Z := 0x828ac.  Definition tfib_E_asan_module_dtor : Z := 0x828dc.






Definition tfib_A_extenddftf2 : Z := 0x843d4.  Definition tfib_E_extenddftf2 : Z := 0x84564.
Definition tfib_A_sysconf : Z := 0x8a1b4.  Definition tfib_E_sysconf : Z := 0x8a3dc.
Definition tfib_A_init : Z := 0x8a3dc.  Definition tfib_E_init : Z := 0x8a3e0.
Definition tfib_A_init_libc : Z := 0x8a3e0.  Definition tfib_E_init_libc : Z := 0x8a60c.
Definition tfib_A_libc_start_init : Z := 0x8a60c.  Definition tfib_E_libc_start_init : Z := 0x8a658.
Definition tfib_A_libc_start_main : Z := 0x8a658.  Definition tfib_E_libc_start_main : Z := 0x8a6b8.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8a6b8.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8a700.
Definition tfib_A_init_tls : Z := 0x8a7d8.  Definition tfib_E_init_tls : Z := 0x8aa88.
Definition tfib_A_init_ssp : Z := 0x8aa88.  Definition tfib_E_init_ssp : Z := 0x8aae8.
Definition tfib_A_stack_chk_fail : Z := 0x8aae8.  Definition tfib_E_stack_chk_fail : Z := 0x8aaf0.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8ab38.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8abcc.
Definition tfib_A_Exit : Z := 0x8abcc.  Definition tfib_E_Exit : Z := 0x8abe8.
Definition tfib_A_funcs_on_exit : Z := 0x8ac18.  Definition tfib_E_funcs_on_exit : Z := 0x8ace0.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8ace4.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8ada8.
Definition tfib_A_libc_exit_fini : Z := 0x8adb0.  Definition tfib_E_libc_exit_fini : Z := 0x8adfc.
Definition tfib_A_exit : Z := 0x8adfc.  Definition tfib_E_exit : Z := 0x8ae70.
Definition tfib_A_open : Z := 0x8b070.  Definition tfib_E_open : Z := 0x8b154.
Definition tfib_A_syscall_ret : Z := 0x8b154.  Definition tfib_E_syscall_ret : Z := 0x8b18c.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8b18c.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8b334.
Definition tfib_A_calloc : Z := 0x8b8f8.  Definition tfib_E_calloc : Z := 0x8ba30.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8ba30.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8ba34.
Definition tfib_A_libc_free : Z := 0x8ba34.  Definition tfib_E_libc_free : Z := 0x8bc00.
Definition tfib_A_get_meta : Z := 0x8bc00.  Definition tfib_E_get_meta : Z := 0x8bd10.
Definition tfib_A_alloc_meta : Z := 0x8c0e8.  Definition tfib_E_alloc_meta : Z := 0x8c3c0.
Definition tfib_A_libc_malloc_impl : Z := 0x8c3c0.  Definition tfib_E_libc_malloc_impl : Z := 0x8c730.
Definition tfib_A_alloc_slot : Z := 0x8c730.  Definition tfib_E_alloc_slot : Z := 0x8cfd4.
Definition tfib_A_enframe : Z := 0x8cfd4.  Definition tfib_E_enframe : Z := 0x8d124.
Definition tfib_A_malloc_allzerop : Z := 0x8d124.  Definition tfib_E_malloc_allzerop : Z := 0x8d29c.
Definition tfib_A_getrlimit : Z := 0x8ef4c.  Definition tfib_E_getrlimit : Z := 0x8f044.
Definition tfib_A_getrusage : Z := 0x8f044.  Definition tfib_E_getrusage : Z := 0x8f06c.
Definition tfib_A_setrlimit : Z := 0x8f06c.  Definition tfib_E_setrlimit : Z := 0x8f134.
Definition tfib_A_mmap : Z := 0x8f55c.  Definition tfib_E_mmap : Z := 0x8f648.
Definition tfib_A_mprotect : Z := 0x8f648.  Definition tfib_E_mprotect : Z := 0x8f690.
Definition tfib_A_munmap : Z := 0x8f764.  Definition tfib_E_munmap : Z := 0x8f7ac.
Definition tfib_A_sched_yield : Z := 0x8fa70.  Definition tfib_E_sched_yield : Z := 0x8fa94.
Definition tfib_A_raise_tkill_path : Z := 0x8faf0.  Definition tfib_E_raise_tkill_path : Z := 0x8fb68.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8fb68.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8fd3c.
Definition tfib_A_musl_sigaltstack : Z := 0x8fe34.  Definition tfib_E_musl_sigaltstack : Z := 0x8fec0.

Definition tfib_A_lockfile : Z := 0x90500.  Definition tfib_E_lockfile : Z := 0x905fc.
Definition tfib_A_unlockfile : Z := 0x905fc.  Definition tfib_E_unlockfile : Z := 0x9065c.



Definition tfib_A_stdio_read : Z := 0x901ec.  Definition tfib_E_stdio_read : Z := 0x90304.
Definition tfib_A_stdio_write : Z := 0x9030c.  Definition tfib_E_stdio_write : Z := 0x9049c.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x901bc.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x901c0.
Definition tfib_A_stdio_close : Z := 0x901c0.  Definition tfib_E_stdio_close : Z := 0x901ec.
Definition tfib_A_fwritex : Z := 0x90a90.  Definition tfib_E_fwritex : Z := 0x90bc8.
Definition tfib_A_musl_fwrite : Z := 0x90bc8.  Definition tfib_E_musl_fwrite : Z := 0x90c80.
Definition tfib_A_towrite : Z := 0x90c80.  Definition tfib_E_towrite : Z := 0x90cd4.
Definition tfib_A_stdio_exit : Z := 0x908ec.  Definition tfib_E_stdio_exit : Z := 0x90a90.
Definition tfib_A_ofl_lock : Z := 0x90cd4.  Definition tfib_E_ofl_lock : Z := 0x90d04.

Definition tfib_A_musl_vfprintf : Z := 0x90e50.  Definition tfib_E_musl_vfprintf : Z := 0x91000.
Definition tfib_A_printf_core : Z := 0x91000.  Definition tfib_E_printf_core : Z := 0x91e30.
Definition tfib_A_pop_arg : Z := 0x91e30.  Definition tfib_E_pop_arg : Z := 0x91f64.
Definition tfib_A_pad : Z := 0x91f64.  Definition tfib_E_pad : Z := 0x92038.
Definition tfib_A_fmt_fp : Z := 0x92038.  Definition tfib_E_fmt_fp : Z := 0x93700.
Definition tfib_A_thunk_931e0 : Z := 0x8b54c.  Definition tfib_E_thunk_931e0 : Z := 0x8b550.
Definition tfib_A_musl_wctomb : Z := 0x8f8d8.  Definition tfib_E_musl_wctomb : Z := 0x8f8fc.
Definition tfib_A_musl_wcrtomb : Z := 0x8f7ac.  Definition tfib_E_musl_wcrtomb : Z := 0x8f8d8.
Definition tfib_A_fpclassifyl : Z := 0x8db3c.  Definition tfib_E_fpclassifyl : Z := 0x8db80.
Definition tfib_A_letf2 : Z := 0x8d374.  Definition tfib_E_letf2 : Z := 0x8d43c.
Definition tfib_A_multf3 : Z := 0x8d43c.  Definition tfib_E_multf3 : Z := 0x8db3c.
Definition tfib_A_floatsitf : Z := 0x8e398.  Definition tfib_E_floatsitf : Z := 0x8e4a0.
Definition tfib_A_scalbn : Z := 0x8eda4.  Definition tfib_E_scalbn : Z := 0x8ee3c.
Definition tfib_A_subtf3 : Z := 0x8e388.  Definition tfib_E_subtf3 : Z := 0x8e398.
Definition tfib_A_addtf3 : Z := 0x8db80.  Definition tfib_E_addtf3 : Z := 0x8e34c.
Definition tfib_A_fe_getround : Z := 0x8e34c.  Definition tfib_E_fe_getround : Z := 0x8e37c.
Definition tfib_A_fixunstfsi : Z := 0x93708.  Definition tfib_E_fixunstfsi : Z := 0x9379c.
Definition tfib_A_floatunsitf : Z := 0x9379c.  Definition tfib_E_floatunsitf : Z := 0x93888.
Definition tfib_A_fixtfsi : Z := 0x8ee3c.  Definition tfib_E_fixtfsi : Z := 0x8eee4.
Definition tfib_A_divtf3 : Z := 0x8e4a0.  Definition tfib_E_divtf3 : Z := 0x8eda4.
Definition tfib_A_musl_vprintf : Z := 0x93f60.  Definition tfib_E_musl_vprintf : Z := 0x93f7c.
Definition tfib_A_stdout_write : Z := 0x90d10.  Definition tfib_E_stdout_write : Z := 0x90db0.
Definition tfib_A_thunk_95368 : Z := 0x94514.  Definition tfib_E_thunk_95368 : Z := 0x94518.
Definition tfib_A_musl_memcmp : Z := 0x945e4.  Definition tfib_E_musl_memcmp : Z := 0x94614.
Definition tfib_A_musl_memcpy : Z := 0x94614.  Definition tfib_E_musl_memcpy : Z := 0x94a18.
Definition tfib_A_musl_memset : Z := 0x94a18.  Definition tfib_E_musl_memset : Z := 0x94b10.
Definition tfib_A_musl_strchr : Z := 0x94b10.  Definition tfib_E_musl_strchr : Z := 0x94b4c.
Definition tfib_A_strchrnul : Z := 0x94b4c.  Definition tfib_E_strchrnul : Z := 0x94c2c.
Definition tfib_A_musl_strlen : Z := 0x94c64.  Definition tfib_E_musl_strlen : Z := 0x94cf4.
Definition tfib_A_musl_strnlen : Z := 0x94ea0.  Definition tfib_E_musl_strnlen : Z := 0x94ee4.
Definition tfib_A_musl_memchr : Z := 0x94518.  Definition tfib_E_musl_memchr : Z := 0x945e4.
Definition tfib_A_lock : Z := 0x94ee4.  Definition tfib_E_lock : Z := 0x9516c.
Definition tfib_A_unlock : Z := 0x9516c.  Definition tfib_E_unlock : Z := 0x951e0.
Definition tfib_A_syscall_cp_c : Z := 0x951e0.  Definition tfib_E_syscall_cp_c : Z := 0x95204.
Definition tfib_A_syscall_cp_sccp : Z := 0x95204.  Definition tfib_E_syscall_cp_sccp : Z := 0x95208.
Definition tfib_A_pthread_atfork : Z := 0x95244.  Definition tfib_E_pthread_atfork : Z := 0x952e8.
Definition tfib_A_mremap : Z := 0x8f690.  Definition tfib_E_mremap : Z := 0x8f764.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x962bc.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x962d8.
Definition tfib_A_pthread_key_create : Z := 0x96664.  Definition tfib_E_pthread_key_create : Z := 0x96738.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x96a80.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x96b9c.
Definition tfib_A_pthread_setspecific : Z := 0x96c00.  Definition tfib_E_pthread_setspecific : Z := 0x96c34.
Definition tfib_A_set_thread_area : Z := 0x96c3c.  Definition tfib_E_set_thread_area : Z := 0x96c48.
Definition tfib_A_thunk_96f9c : Z := 0x96c34.  Definition tfib_E_thunk_96f9c : Z := 0x96c3c.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97568.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97620.
Definition tfib_A_close : Z := 0x99c38.  Definition tfib_E_close : Z := 0x99c8c.
Definition tfib_A_musl_read : Z := 0x99d18.  Definition tfib_E_musl_read : Z := 0x99d4c.
Definition tfib_A_vm_wait : Z := 0x97278.  Definition tfib_E_vm_wait : Z := 0x972c8.
Definition tfib_D_str_sealed : Z := 0x11837.
Definition tfib_D_init_array_0_3 : Z := 0x9ad50.
Definition tfib_D_fini_array_0_1 : Z := 0x9ad70.
Definition tfib_D_GOT_common_flags : Z := 0x9c3a0.
Definition tfib_D_GOT_flags : Z := 0x9c3a8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c3b0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c3b8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c3c0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c3c8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9cf18.
Definition tfib_D_REAL_read : Z := 0x9e0e8.
Definition tfib_D_REAL_memcpy : Z := 0x9e210.
Definition tfib_D_REAL_memset : Z := 0x9e218.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa1958.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa27b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa4fb8.
Definition tfib_D_asan_inited : Z := 0xa5c98.
Definition tfib_D_replace_intrin_cached : Z := 0xa5c99.
Definition tfib_D_kHighMemEnd : Z := 0xa5ca0.
Definition tfib_D_kMidMemBeg : Z := 0xa5ca8.
Definition tfib_D_kMidMemEnd : Z := 0xa5cb0.
Definition tfib_D_malloc_context_size : Z := 0xa5cbc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136ae8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x309b8.
Definition tfib_at_rw_lo : Z := 0x9e000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63be4.
Definition tfib_at_x_imemcpy : Z := 0x63b68.
Definition tfib_at_x_memset : Z := 0x94a18.
Definition tfib_at_x_memcpy : Z := 0x94614.
Definition tfib_at_x_memiszero : Z := 0x64114.
Definition tfib_at_x_istrncpy : Z := 0x64010.
Definition tfib_at_x_sealed : Z := 0x11837.
Definition tfib_at_x_popfree : Z := 0x36da4.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8a418.
Definition tfib_at_x_envscan_k : Z := 0x8a424.
Definition tfib_at_x_pnscan : Z := 0x8a4dc.
Definition tfib_at_x_pnscan_k : Z := 0x8a4e8.
Definition tfib_at_stops_more : list Z := (0x34a18 :: 0x3603c :: 0x53ef0 :: 0x5a2a8 :: 0x5a2bc :: 0x5a2d0 :: 0x5fc60 :: 0x5fd30 :: 0x6d25c :: 0x6e168 :: 0x6e2f8 :: 0x78050 :: nil)%list.
