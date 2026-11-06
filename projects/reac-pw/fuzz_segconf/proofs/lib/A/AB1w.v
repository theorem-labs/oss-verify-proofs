(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its rows regenerated for plugin-hostd/fuzz_command's ASan build by the AB1w row regenerator: each start is the fuzz_command function paired by code with cgif's, each end the pair of cgif's last instruction plus its length; a row whose label is a FUNC symbol of fuzz_command's image takes that symbol's range (LLVMFuzzerTestOneInput); the side-stack class rows are fuzz_command's own __asan_stack_malloc_0, _1, _3, _4, _5 and _7 (symbol address and size; class 1 keeps cgif's row name asan_stack_malloc_A, the others are named by class); six rows are set from the image by hand (HaveStackTraceBasedSuppressions, set_thread_area, two jump stubs by their target, the self-loop stub, and the ends of __stdio_exit and musl memset, whose code differs); section bounds come from fuzz_command's section headers; the rows of cgif functions fuzz_command does not have (cgif's program and GIF library, fopen/fclose/fdopen/ofl_add/fmodeflags and their interceptors, stack_malloc_2) are dropped; thirteen rows whose cgif label names another function than the code of their range take the name of the image symbol at their start (internal_strchr / _strcmp / _strncmp, AsanCheckIncompatibleRT / AsanCheckDynamicRTPrereqs, IsAddrSuppressed, IsRssLimitExceeded, DecreaseTotalMmap, GetTls, MmapFixedSuperNoReserve, MmapNoAccess, ReservedAddressRange_MapOrDie, and MmapFixedOrDie for cgif's shim row). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1w.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x23a6c.
Definition tfib_text_lo : Z := 0x31ed4.  Definition tfib_text_hi : Z := 0xa0468.
Definition tfib_init_array_lo : Z := 0xa1468.  Definition tfib_init_array_hi : Z := 0xa1488.
Definition tfib_fini_array_lo : Z := 0xa1488.  Definition tfib_fini_array_hi : Z := 0xa1498.
Definition tfib_preinit_array_lo : Z := 0xa1498.  Definition tfib_preinit_array_hi : Z := 0xa14a0.
Definition tfib_data_rel_ro_lo : Z := 0xa14a0.  Definition tfib_data_rel_ro_hi : Z := 0xa29f0.
Definition tfib_got_lo : Z := 0xa29f0.  Definition tfib_got_hi : Z := 0xa3748.
Definition tfib_data_lo : Z := 0xa4748.  Definition tfib_data_hi : Z := 0xa7330.
Definition tfib_asan_globals_lo : Z := 0xa7330.  Definition tfib_asan_globals_hi : Z := 0xa8930.
Definition tfib_bss_lo : Z := 0xa8940.  Definition tfib_bss_hi : Z := 0x600918.
Definition tfib_tbss_lo : Z := 0xa0468.  Definition tfib_tbss_hi : Z := 0xa047c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x601000.
Definition tfib_entry : Z := 0x31ed4.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x31ed4.  Definition tfib_E_start : Z := 0x31f1c.
Definition tfib_A_do_init : Z := 0x31f1c.  Definition tfib_E_do_init : Z := 0x31f90.
Definition tfib_A_do_fini : Z := 0x31f90.  Definition tfib_E_do_fini : Z := 0x32020.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x32020.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x3205c.
Definition tfib_A_InitializeAllocator : Z := 0x321cc.  Definition tfib_E_InitializeAllocator : Z := 0x321e4.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x321e4.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x32350.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x328ac.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x32a08.
Definition tfib_A_asan_free : Z := 0x32ddc.  Definition tfib_E_asan_free : Z := 0x32e04.
Definition tfib_A_Allocator_Deallocate : Z := 0x32e04.  Definition tfib_E_Allocator_Deallocate : Z := 0x330bc.
Definition tfib_A_asan_malloc : Z := 0x330bc.  Definition tfib_E_asan_malloc : Z := 0x33118.
Definition tfib_A_Allocator_Allocate : Z := 0x33118.  Definition tfib_E_Allocator_Allocate : Z := 0x33aa0.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x342b8.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x343fc.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x344e8.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x34544.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x34544.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x34794.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x34794.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x34888.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x34888.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x34970.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x34da4.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x34f88.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x34f88.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x3510c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x35244.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x354c8.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x354c8.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x35648.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x35648.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x35810.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x35810.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x359dc.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x359dc.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x35a7c.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x35a7c.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x35b80.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35ea8.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35ff0.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x35ff0.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x36028.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x367c0.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x36aa8.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x37180.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x372f8.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x372f8.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x374a8.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x374a8.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3768c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x3768c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x37964.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x37964.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x37ddc.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x37ddc.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x37edc.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x37edc.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x381e4.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x381e4.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x38554.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x38554.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x3866c.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x38974.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x38a70.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x38a70.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x38b58.
Definition tfib_A_AsanActivate : Z := 0x38b58.  Definition tfib_E_AsanActivate : Z := 0x38c34.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x39110.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x391f8.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3dcb0.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3dd88.
Definition tfib_A_FakeStack_Create : Z := 0x3dd88.  Definition tfib_E_FakeStack_Create : Z := 0x3de74.
Definition tfib_A_FakeStack_Allocate : Z := 0x3e130.  Definition tfib_E_FakeStack_Allocate : Z := 0x3e418.
Definition tfib_A_SetTLSFakeStack : Z := 0x3e54c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3e57c.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3e6f0.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3e880.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3e57c.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3e6f0.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3e880.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3ea2c.

Definition tfib_A_asan_stack_malloc_5 : Z := 0x3ea2c.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x3ec38.

Definition tfib_A_FakeStack_SetShadow : Z := 0x3ecec.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3ee28.
Definition tfib_A_asan_InitializeFlags : Z := 0x3ee28.  Definition tfib_E_asan_InitializeFlags : Z := 0x3fe54.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40560.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x4137c.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x4137c.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x41948.
Definition tfib_A_asan_register_globals : Z := 0x41948.  Definition tfib_E_asan_register_globals : Z := 0x419b4.
Definition tfib_A_asan_unregister_globals : Z := 0x419b4.  Definition tfib_E_asan_unregister_globals : Z := 0x41a1c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x4209c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x4230c.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x4230c.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42614.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x42d88.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x42ed8.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x438f4.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x43a0c.
Definition tfib_A_strlen : Z := 0x43a0c.  Definition tfib_E_strlen : Z := 0x43a10.
Definition tfib_A_strnlen : Z := 0x43a10.  Definition tfib_E_strnlen : Z := 0x43a14.
Definition tfib_A_strcmp : Z := 0x43a14.  Definition tfib_E_strcmp : Z := 0x43a18.
Definition tfib_A_strchr : Z := 0x43a28.  Definition tfib_E_strchr : Z := 0x43a2c.
Definition tfib_A_memcmp : Z := 0x43a34.  Definition tfib_E_memcmp : Z := 0x43a38.
Definition tfib_A_memcmp_2 : Z := 0x43a38.  Definition tfib_E_memcmp_2 : Z := 0x43a3c.
Definition tfib_A_memchr : Z := 0x43a3c.  Definition tfib_E_memchr : Z := 0x43a40.
Definition tfib_A_frexpl : Z := 0x43a40.  Definition tfib_E_frexpl : Z := 0x43a44.
Definition tfib_A_read : Z := 0x43a44.  Definition tfib_E_read : Z := 0x43a48.
Definition tfib_A_fwrite : Z := 0x43a48.  Definition tfib_E_fwrite : Z := 0x43a4c.
Definition tfib_A_time : Z := 0x43a4c.  Definition tfib_E_time : Z := 0x43a50.
Definition tfib_A_gmtime_r : Z := 0x43a50.  Definition tfib_E_gmtime_r : Z := 0x43a54.
Definition tfib_A_vprintf : Z := 0x43a54.  Definition tfib_E_vprintf : Z := 0x43a58.
Definition tfib_A_vfprintf : Z := 0x43a58.  Definition tfib_E_vfprintf : Z := 0x43a5c.
Definition tfib_A_vsnprintf : Z := 0x43a5c.  Definition tfib_E_vsnprintf : Z := 0x43a60.
Definition tfib_A_vfprintf_2 : Z := 0x43a60.  Definition tfib_E_vfprintf_2 : Z := 0x43a64.
Definition tfib_A_thunk_417bc : Z := 0x43a64.  Definition tfib_E_thunk_417bc : Z := 0x43a68.
Definition tfib_A_clock_gettime : Z := 0x43a68.  Definition tfib_E_clock_gettime : Z := 0x43a6c.
Definition tfib_A_wcrtomb : Z := 0x43a6c.  Definition tfib_E_wcrtomb : Z := 0x43a70.
Definition tfib_A_wctomb : Z := 0x43a70.  Definition tfib_E_wctomb : Z := 0x43a74.
Definition tfib_A_thunk_417cc : Z := 0x43a74.  Definition tfib_E_thunk_417cc : Z := 0x43a7c.
Definition tfib_A_pthread_attr_getstack : Z := 0x43a7c.  Definition tfib_E_pthread_attr_getstack : Z := 0x43a80.
Definition tfib_A_tls_get_addr_thunk : Z := 0x43a80.  Definition tfib_E_tls_get_addr_thunk : Z := 0x43a84.
Definition tfib_A_thunk_417dc : Z := 0x43a84.  Definition tfib_E_thunk_417dc : Z := 0x43a88.
Definition tfib_A_thunk_417e4 : Z := 0x43a88.  Definition tfib_E_thunk_417e4 : Z := 0x43a8c.
Definition tfib_A_thunk_417e8 : Z := 0x43a8c.  Definition tfib_E_thunk_417e8 : Z := 0x43a90.
Definition tfib_A_thunk_417ec : Z := 0x43a90.  Definition tfib_E_thunk_417ec : Z := 0x43a94.
Definition tfib_A_thunk_417f0 : Z := 0x43a94.  Definition tfib_E_thunk_417f0 : Z := 0x43a98.
Definition tfib_A_sem_timedwait : Z := 0x43a98.  Definition tfib_E_sem_timedwait : Z := 0x43a9c.
Definition tfib_A_thunk_417f8 : Z := 0x43a9c.  Definition tfib_E_thunk_417f8 : Z := 0x43aa0.
Definition tfib_A_pthread_setcancelstate : Z := 0x43aa0.  Definition tfib_E_pthread_setcancelstate : Z := 0x43aa4.
Definition tfib_A_send : Z := 0x43aa4.  Definition tfib_E_send : Z := 0x43aa8.
Definition tfib_A_sendto : Z := 0x43aa8.  Definition tfib_E_sendto : Z := 0x43aac.
Definition tfib_A_sigaltstack : Z := 0x43aac.  Definition tfib_E_sigaltstack : Z := 0x43ab0.
Definition tfib_A_thunk_4180c : Z := 0x43ab0.  Definition tfib_E_thunk_4180c : Z := 0x43ab4.
Definition tfib_A_icpt_strlen : Z := 0x43abc.  Definition tfib_E_icpt_strlen : Z := 0x43d50.
Definition tfib_A_icpt_strnlen : Z := 0x43d50.  Definition tfib_E_icpt_strnlen : Z := 0x43fe4.
Definition tfib_A_icpt_strcmp : Z := 0x43fe8.  Definition tfib_E_icpt_strcmp : Z := 0x44518.
Definition tfib_A_icpt_strchr : Z := 0x45ae4.  Definition tfib_E_icpt_strchr : Z := 0x45dc4.
Definition tfib_A_icpt_memcmp : Z := 0x46dc4.  Definition tfib_E_icpt_memcmp : Z := 0x46e80.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x46e80.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x46f3c.
Definition tfib_A_icpt_memchr : Z := 0x46f3c.  Definition tfib_E_icpt_memchr : Z := 0x4720c.
Definition tfib_A_icpt_frexpl : Z := 0x4720c.  Definition tfib_E_icpt_frexpl : Z := 0x47484.
Definition tfib_A_icpt_read : Z := 0x47484.  Definition tfib_E_icpt_read : Z := 0x476f4.
Definition tfib_A_icpt_fwrite : Z := 0x476f4.  Definition tfib_E_icpt_fwrite : Z := 0x47968.
Definition tfib_A_icpt_time : Z := 0x47968.  Definition tfib_E_icpt_time : Z := 0x47c04.
Definition tfib_A_icpt_gmtime_r : Z := 0x47e0c.  Definition tfib_E_icpt_gmtime_r : Z := 0x4804c.
Definition tfib_A_icpt_vprintf : Z := 0x4804c.  Definition tfib_E_icpt_vprintf : Z := 0x480e8.
Definition tfib_A_printf_common_format_interceptor : Z := 0x480e8.  Definition tfib_E_printf_common_format_interceptor : Z := 0x48bb0.
Definition tfib_A_icpt_vfprintf : Z := 0x48bb0.  Definition tfib_E_icpt_vfprintf : Z := 0x48c64.
Definition tfib_A_icpt_vsnprintf : Z := 0x48c64.  Definition tfib_E_icpt_vsnprintf : Z := 0x48f7c.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x48f7c.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x49054.
Definition tfib_A_icpt_clock_gettime : Z := 0x490f8.  Definition tfib_E_icpt_clock_gettime : Z := 0x49350.
Definition tfib_A_icpt_wcrtomb : Z := 0x49350.  Definition tfib_E_icpt_wcrtomb : Z := 0x498c0.
Definition tfib_A_icpt_wctomb : Z := 0x498c0.  Definition tfib_E_icpt_wctomb : Z := 0x49c1c.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x49ce8.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4a0d0.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4a0dc.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4a158.

Definition tfib_A_icpt_sem_timedwait : Z := 0x4a364.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4a5fc.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4a62c.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4a854.
Definition tfib_A_icpt_send : Z := 0x4a854.  Definition tfib_E_icpt_send : Z := 0x4ab08.
Definition tfib_A_icpt_sendto : Z := 0x4ab08.  Definition tfib_E_icpt_sendto : Z := 0x4adcc.
Definition tfib_A_icpt_sigaltstack : Z := 0x4adcc.  Definition tfib_E_icpt_sigaltstack : Z := 0x4b028.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4b6f0.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4b8a0.
Definition tfib_A_icpt_diouxXn : Z := 0x4b8a0.  Definition tfib_E_icpt_diouxXn : Z := 0x4ba38.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x4c5e4.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x552bc.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x552bc.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x55418.
Definition tfib_A_memset : Z := 0x558d8.  Definition tfib_E_memset : Z := 0x558dc.
Definition tfib_A_memcpy : Z := 0x558dc.  Definition tfib_E_memcpy : Z := 0x558e0.
Definition tfib_A_asan_memcpy : Z := 0x558e0.  Definition tfib_E_asan_memcpy : Z := 0x55d7c.
Definition tfib_A_asan_memset : Z := 0x55d7c.  Definition tfib_E_asan_memset : Z := 0x55fbc.
Definition tfib_A_icpt_memset : Z := 0x55fbc.  Definition tfib_E_icpt_memset : Z := 0x562ac.
Definition tfib_A_icpt_memcpy : Z := 0x562ac.  Definition tfib_E_icpt_memcpy : Z := 0x5689c.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5689c.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x568d4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x568d4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x568d8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x568d8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x568dc.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x568dc.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5693c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x56988.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x56ac4.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x56ac4.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x56ac8.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x56ac8.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x56c30.
Definition tfib_A_free : Z := 0x56c30.  Definition tfib_E_free : Z := 0x56c34.
Definition tfib_A_malloc : Z := 0x56c34.  Definition tfib_E_malloc : Z := 0x56c38.
Definition tfib_A_icpt_free : Z := 0x56c3c.  Definition tfib_E_icpt_free : Z := 0x56e0c.
Definition tfib_A_icpt_malloc : Z := 0x56e0c.  Definition tfib_E_icpt_malloc : Z := 0x56f68.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x56f68.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x57034.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x5726c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x57270.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x57270.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x57370.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x57698.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x57804.
Definition tfib_A_SetCanPoisonMemory : Z := 0x57cec.  Definition tfib_E_SetCanPoisonMemory : Z := 0x57cfc.
Definition tfib_A_CanPoisonMemory : Z := 0x57cfc.  Definition tfib_E_CanPoisonMemory : Z := 0x57d10.
Definition tfib_A_PoisonShadow : Z := 0x57d10.  Definition tfib_E_PoisonShadow : Z := 0x5820c.
Definition tfib_A_MemToShadow_checked : Z := 0x5820c.  Definition tfib_E_MemToShadow_checked : Z := 0x58348.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x58348.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x584e8.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x584e8.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x58668.
Definition tfib_A_asan_region_is_poisoned : Z := 0x58698.  Definition tfib_E_asan_region_is_poisoned : Z := 0x589dc.
Definition tfib_A_AsanTSDInit : Z := 0x58dfc.  Definition tfib_E_AsanTSDInit : Z := 0x58e78.
Definition tfib_A_AsanTSDGet : Z := 0x58e78.  Definition tfib_E_AsanTSDGet : Z := 0x58eb8.
Definition tfib_A_AsanTSDSet : Z := 0x58eb8.  Definition tfib_E_AsanTSDSet : Z := 0x58ef8.
Definition tfib_A_PlatformTSDDtor : Z := 0x58ef8.  Definition tfib_E_PlatformTSDDtor : Z := 0x58f7c.
Definition tfib_A_InstallAtForkHandler : Z := 0x58f7c.  Definition tfib_E_InstallAtForkHandler : Z := 0x58f98.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x58ff8.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5903c.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x59754.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x59960.
Definition tfib_A_ReportDoubleFree : Z := 0x5a068.  Definition tfib_E_ReportDoubleFree : Z := 0x5a2f8.
Definition tfib_A_ReportGenericError : Z := 0x5be24.  Definition tfib_E_ReportGenericError : Z := 0x5c6e0.
Definition tfib_A_AsanInited : Z := 0x5ce6c.  Definition tfib_E_AsanInited : Z := 0x5ce84.
Definition tfib_A_asan_report_load1 : Z := 0x5ce84.  Definition tfib_E_asan_report_load1 : Z := 0x5ced4.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5ced4.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5cf24.
Definition tfib_A_asan_report_load2 : Z := 0x5cf24.  Definition tfib_E_asan_report_load2 : Z := 0x5cf74.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5cf74.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5cfc4.
Definition tfib_A_asan_report_load4 : Z := 0x5cfc4.  Definition tfib_E_asan_report_load4 : Z := 0x5d014.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5d014.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5d064.
Definition tfib_A_asan_report_load8 : Z := 0x5d064.  Definition tfib_E_asan_report_load8 : Z := 0x5d0b4.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5d0b4.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5d104.
Definition tfib_A_asan_report_load16 : Z := 0x5d104.  Definition tfib_E_asan_report_load16 : Z := 0x5d154.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5d154.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5d1a4.
Definition tfib_A_asan_report_store1 : Z := 0x5d1a4.  Definition tfib_E_asan_report_store1 : Z := 0x5d1f4.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5d1f4.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5d244.
Definition tfib_A_asan_report_store2 : Z := 0x5d244.  Definition tfib_E_asan_report_store2 : Z := 0x5d294.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5d294.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5d2e4.
Definition tfib_A_asan_report_store4 : Z := 0x5d2e4.  Definition tfib_E_asan_report_store4 : Z := 0x5d334.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5d334.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5d384.
Definition tfib_A_asan_report_store8 : Z := 0x5d384.  Definition tfib_E_asan_report_store8 : Z := 0x5d3d4.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5d3d4.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5d424.
Definition tfib_A_asan_report_store16 : Z := 0x5d424.  Definition tfib_E_asan_report_store16 : Z := 0x5d474.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5d474.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5d4c4.
Definition tfib_A_asan_report_load_n : Z := 0x5d4c4.  Definition tfib_E_asan_report_load_n : Z := 0x5d514.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5d514.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5d564.
Definition tfib_A_asan_report_store_n : Z := 0x5d564.  Definition tfib_E_asan_report_store_n : Z := 0x5d5b4.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5d5b4.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5d604.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5d604.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5d684.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5d684.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5da38.
Definition tfib_A_AsanInitInternal : Z := 0x5dac8.  Definition tfib_E_AsanInitInternal : Z := 0x5dd7c.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5dd7c.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5de1c.
Definition tfib_A_thunk_59674 : Z := 0x5dfe4.  Definition tfib_E_thunk_59674 : Z := 0x5dfe8.
Definition tfib_A_asan_init : Z := 0x5dfe8.  Definition tfib_E_asan_init : Z := 0x5e07c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5e07c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5e080.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5e080.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5e0e4.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5e258.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5e260.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5e2e4.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5e60c.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5e60c.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5e7ec.
Definition tfib_A_InitializeShadowMemory : Z := 0x5e7ec.  Definition tfib_E_InitializeShadowMemory : Z := 0x5eaf4.
Definition tfib_A_SetMallocContextSize : Z := 0x5eaf4.  Definition tfib_E_SetMallocContextSize : Z := 0x5eb04.
Definition tfib_A_GetMallocContextSize : Z := 0x5eb04.  Definition tfib_E_GetMallocContextSize : Z := 0x5eb14.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5eb14.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ec64.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5f044.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5f2e4.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5f748.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5f780.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5fa28.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5fa34.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5fa34.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5fac0.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5fac0.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5fb28.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5fb28.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5fba0.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5fba0.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5fc08.
Definition tfib_A_IsAddrSuppressed : Z := 0x5fc08.  Definition tfib_E_IsAddrSuppressed : Z := 0x5fd54.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5ffe0.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5ffec.
Definition tfib_A_AsanThread_Create : Z := 0x6016c.  Definition tfib_E_AsanThread_Create : Z := 0x60308.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x60364.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x6057c.
Definition tfib_A_GetCurrentThread : Z := 0x6057c.  Definition tfib_E_GetCurrentThread : Z := 0x6059c.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x6059c.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x60740.
Definition tfib_A_AsanThread_stack_top : Z := 0x60740.  Definition tfib_E_AsanThread_stack_top : Z := 0x60798.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x60798.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x607f0.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x607f0.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x60a20.
Definition tfib_A_AsanThread_Init : Z := 0x60a20.  Definition tfib_E_AsanThread_Init : Z := 0x60e14.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x60e14.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x60f20.
Definition tfib_A_CreateMainThread : Z := 0x60f54.  Definition tfib_E_CreateMainThread : Z := 0x61064.
Definition tfib_A_SetCurrentThread : Z := 0x61064.  Definition tfib_E_SetCurrentThread : Z := 0x61144.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x61348.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x61484.
Definition tfib_A_weak_default_hook_ret : Z := 0x62158.  Definition tfib_E_weak_default_hook_ret : Z := 0x6215c.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x62164.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x623a4.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x625f8.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x62750.
Definition tfib_A_internal_allocator_getter : Z := 0x62a50.  Definition tfib_E_internal_allocator_getter : Z := 0x62a5c.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x62a5c.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x62ba8.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x62ba8.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x62bf4.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x62bf4.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x62c00.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x62c30.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x62c3c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x62c3c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x62c48.
Definition tfib_A_IsRssLimitExceeded : Z := 0x62c48.  Definition tfib_E_IsRssLimitExceeded : Z := 0x62c58.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x62c64.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x62f30.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x62f30.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x632f0.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x6424c.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x64258.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x64258.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x64330.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x64330.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x643cc.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x648f0.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x64934.
Definition tfib_A_DecreaseTotalMmap : Z := 0x64934.  Definition tfib_E_DecreaseTotalMmap : Z := 0x64958.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x64bac.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x64cc0.
Definition tfib_A_RunMallocHooks : Z := 0x64e64.  Definition tfib_E_RunMallocHooks : Z := 0x64f1c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x64f1c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x64f20.
Definition tfib_A_RunFreeHooks : Z := 0x64f20.  Definition tfib_E_RunFreeHooks : Z := 0x64fcc.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x64fcc.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x64fd4.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x64fd4.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x64fd8.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x65000.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x6504c.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x65310.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x65550.
Definition tfib_A_sanitizer_set_report_path : Z := 0x65b4c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x65b64.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x65b64.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x65ca8.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x65ca8.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x65cb0.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x65ff8.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x6729c.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x6729c.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x672c0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x67774.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x67a84.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x67a84.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x67bc8.
Definition tfib_A_FlagParser_ParseString : Z := 0x67bc8.  Definition tfib_E_FlagParser_ParseString : Z := 0x67cbc.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x67e50.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x67eb0.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x67eb0.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x67ef0.
Definition tfib_A_internal_atoll : Z := 0x67ef0.  Definition tfib_E_internal_atoll : Z := 0x67fdc.
Definition tfib_A_internal_simple_strtoll : Z := 0x67fdc.  Definition tfib_E_internal_simple_strtoll : Z := 0x68138.
Definition tfib_A_internal_memchr : Z := 0x68138.  Definition tfib_E_internal_memchr : Z := 0x68158.
Definition tfib_A_internal_memcmp : Z := 0x68158.  Definition tfib_E_internal_memcmp : Z := 0x68190.
Definition tfib_A_internal_memcpy : Z := 0x68190.  Definition tfib_E_internal_memcpy : Z := 0x681b4.
Definition tfib_A_internal_memmove : Z := 0x681b4.  Definition tfib_E_internal_memmove : Z := 0x6820c.
Definition tfib_A_internal_memset : Z := 0x6820c.  Definition tfib_E_internal_memset : Z := 0x6826c.
Definition tfib_A_internal_strcspn : Z := 0x6826c.  Definition tfib_E_internal_strcspn : Z := 0x682c0.
Definition tfib_A_internal_strchr : Z := 0x682c0.  Definition tfib_E_internal_strchr : Z := 0x682f4.
Definition tfib_A_internal_strdup : Z := 0x682f4.  Definition tfib_E_internal_strdup : Z := 0x68360.
Definition tfib_A_internal_strlen : Z := 0x68360.  Definition tfib_E_internal_strlen : Z := 0x6837c.
Definition tfib_A_internal_strcmp : Z := 0x6837c.  Definition tfib_E_internal_strcmp : Z := 0x683c0.
Definition tfib_A_internal_strncmp : Z := 0x683c0.  Definition tfib_E_internal_strncmp : Z := 0x6840c.
Definition tfib_A_internal_strchrnul : Z := 0x6840c.  Definition tfib_E_internal_strchrnul : Z := 0x68454.
Definition tfib_A_internal_strrchr : Z := 0x68454.  Definition tfib_E_internal_strrchr : Z := 0x68494.
Definition tfib_A_internal_strnlen : Z := 0x685c4.  Definition tfib_E_internal_strnlen : Z := 0x685f4.
Definition tfib_A_internal_strncpy : Z := 0x68638.  Definition tfib_E_internal_strncpy : Z := 0x686a8.
Definition tfib_A_internal_strstr : Z := 0x686a8.  Definition tfib_E_internal_strstr : Z := 0x6873c.
Definition tfib_A_mem_is_zero : Z := 0x6873c.  Definition tfib_E_mem_is_zero : Z := 0x687f0.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x687f0.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x68800.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x68800.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x689e0.
Definition tfib_A_internal_iserror : Z := 0x689ec.  Definition tfib_E_internal_iserror : Z := 0x68a0c.
Definition tfib_A_internal_mmap : Z := 0x68a0c.  Definition tfib_E_internal_mmap : Z := 0x68a18.
Definition tfib_A_internal_munmap : Z := 0x68a18.  Definition tfib_E_internal_munmap : Z := 0x68a24.
Definition tfib_A_internal_mprotect : Z := 0x68a24.  Definition tfib_E_internal_mprotect : Z := 0x68a34.
Definition tfib_A_internal_madvise : Z := 0x68a34.  Definition tfib_E_internal_madvise : Z := 0x68a60.
Definition tfib_A_internal_close : Z := 0x68a60.  Definition tfib_E_internal_close : Z := 0x68a6c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x68a6c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x68a90.
Definition tfib_A_internal_read : Z := 0x68a90.  Definition tfib_E_internal_read : Z := 0x68ac8.
Definition tfib_A_internal_write : Z := 0x68ac8.  Definition tfib_E_internal_write : Z := 0x68b00.
Definition tfib_A_internal_ftruncate : Z := 0x68b00.  Definition tfib_E_internal_ftruncate : Z := 0x68b38.
Definition tfib_A_internal_dup : Z := 0x68b38.  Definition tfib_E_internal_dup : Z := 0x68b44.
Definition tfib_A_internal_dup2_dup3 : Z := 0x68b44.  Definition tfib_E_internal_dup2_dup3 : Z := 0x68b54.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x68b54.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x68b6c.
Definition tfib_A_internal_sched_yield : Z := 0x68b6c.  Definition tfib_E_internal_sched_yield : Z := 0x68b78.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x68b78.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x68bc4.
Definition tfib_A_internal_execve : Z := 0x68bc4.  Definition tfib_E_internal_execve : Z := 0x68bd0.
Definition tfib_A_internal_exit_exit_group : Z := 0x68bd0.  Definition tfib_E_internal_exit_exit_group : Z := 0x68be4.
Definition tfib_A_FileExists_newfstatat : Z := 0x68be4.  Definition tfib_E_FileExists_newfstatat : Z := 0x68c64.
Definition tfib_A_DirExists_newfstatat : Z := 0x68c64.  Definition tfib_E_DirExists_newfstatat : Z := 0x68cc8.
Definition tfib_A_GetTid_gettid : Z := 0x68cc8.  Definition tfib_E_GetTid_gettid : Z := 0x68cd4.
Definition tfib_A_GetEnv : Z := 0x68cd4.  Definition tfib_E_GetEnv : Z := 0x68e04.
Definition tfib_A_FutexWait : Z := 0x68f08.  Definition tfib_E_FutexWait : Z := 0x68f2c.
Definition tfib_A_FutexWake : Z := 0x68f2c.  Definition tfib_E_FutexWake : Z := 0x68f50.
Definition tfib_A_internal_ptrace : Z := 0x68f50.  Definition tfib_E_internal_ptrace : Z := 0x68f5c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x68f5c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x68f6c.
Definition tfib_A_internal_getpid : Z := 0x68f6c.  Definition tfib_E_internal_getpid : Z := 0x68f78.
Definition tfib_A_internal_getppid : Z := 0x68f78.  Definition tfib_E_internal_getppid : Z := 0x68f84.
Definition tfib_A_internal_prctl : Z := 0x68f84.  Definition tfib_E_internal_prctl : Z := 0x68f90.
Definition tfib_A_internal_sigaltstack : Z := 0x68f90.  Definition tfib_E_internal_sigaltstack : Z := 0x68f9c.
Definition tfib_A_internal_fork_clone : Z := 0x68f9c.  Definition tfib_E_internal_fork_clone : Z := 0x68fb4.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x68fb4.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x690e0.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x692b8.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x696b4.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x69820.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x69938.
Definition tfib_A_GetPageSizeCached : Z := 0x69938.  Definition tfib_E_GetPageSizeCached : Z := 0x69940.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x69940.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x699ec.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x699ec.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x69b0c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x69bd4.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x69c54.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x69c54.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x69cb0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x69cb0.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x69d7c.
Definition tfib_A_thunk_653ec : Z := 0x69e78.  Definition tfib_E_thunk_653ec : Z := 0x69e7c.
Definition tfib_A_CheckASLR : Z := 0x69e7c.  Definition tfib_E_CheckASLR : Z := 0x69e80.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x6a0cc.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6a0d0.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x6a0d0.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x6a0dc.
Definition tfib_A_MmapOrDie : Z := 0x6a0dc.  Definition tfib_E_MmapOrDie : Z := 0x6a1e8.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6a1e8.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6a25c.
Definition tfib_A_UnmapOrDie : Z := 0x6a25c.  Definition tfib_E_UnmapOrDie : Z := 0x6a2d8.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6a2d8.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6a3e8.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6a614.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6a718.
Definition tfib_A_MmapFixedOrDie : Z := 0x6a718.  Definition tfib_E_MmapFixedOrDie : Z := 0x6a724.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6a724.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6a89c.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6a89c.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6a8a8.
Definition tfib_A_thunk_66008 : Z := 0x6aa94.  Definition tfib_E_thunk_66008 : Z := 0x6aa98.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6adb8.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6afc4.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x6b57c.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6b588.
Definition tfib_A_Printf : Z := 0x6b58c.  Definition tfib_E_Printf : Z := 0x6b5d8.
Definition tfib_A_SharedPrintfCode : Z := 0x6b5d8.  Definition tfib_E_SharedPrintfCode : Z := 0x6b634.
Definition tfib_A_Report : Z := 0x6b634.  Definition tfib_E_Report : Z := 0x6b680.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6d178.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6d1d4.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6d1d4.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6d410.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6d410.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6d734.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6dcd4.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6dda4.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6dda4.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6e0f4.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6e0f4.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6e104.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6e340.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6e384.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6e384.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6e3e4.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6e3e4.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6e85c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6f11c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6f440.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6f448.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6f54c.
Definition tfib_A_AddDieCallback : Z := 0x6fcfc.  Definition tfib_E_AddDieCallback : Z := 0x6fd84.
Definition tfib_A_Die : Z := 0x6fe48.  Definition tfib_E_Die : Z := 0x6ff08.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6ff08.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6ff14.
Definition tfib_A_CheckFailed : Z := 0x6ff14.  Definition tfib_E_CheckFailed : Z := 0x6ffcc.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x70624.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x7071c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x7071c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x70848.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x70a70.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x70aec.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x70b20.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x70e08.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x70e08.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x70e0c.
Definition tfib_A_GetTls : Z := 0x70e0c.  Definition tfib_E_GetTls : Z := 0x711fc.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x711fc.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x712cc.
Definition tfib_A_AndroidLogInit : Z := 0x716b0.  Definition tfib_E_AndroidLogInit : Z := 0x716b4.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x716e4.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x7172c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x7172c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x71978.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x71978.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x7197c.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x7197c.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x71a88.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x71a88.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x71b8c.
Definition tfib_A_thunk_6d37c : Z := 0x71e08.  Definition tfib_E_thunk_6d37c : Z := 0x71e0c.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x71eb0.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x71ed0.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x71ed0.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x71f70.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x71fbc.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x71fc0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x71ffc.  Definition tfib_E_SetAlternateSignalStack : Z := 0x720c0.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x720c0.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x72148.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x72148.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x721c0.
Definition tfib_A_MaybeInstallSigaction : Z := 0x721c0.  Definition tfib_E_MaybeInstallSigaction : Z := 0x722a4.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x72360.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x72494.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x726cc.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x727fc.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x727fc.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x7285c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x7285c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x72928.
Definition tfib_A_MmapNoAccess : Z := 0x7293c.  Definition tfib_E_MmapNoAccess : Z := 0x7295c.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x7295c.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x72aa8.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x72aa8.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x72ab8.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x742b0.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x742f4.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x742f4.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x74324.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x74758.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x7487c.
Definition tfib_A_StackStore_Alloc : Z := 0x7487c.  Definition tfib_E_StackStore_Alloc : Z := 0x749b0.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x75264.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x75318.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x76a6c.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x76ac8.
Definition tfib_A_StackDepotPut : Z := 0x76d54.  Definition tfib_E_StackDepotPut : Z := 0x76d74.
Definition tfib_A_StackDepotBase_Put : Z := 0x76d74.  Definition tfib_E_StackDepotBase_Put : Z := 0x76ff8.
Definition tfib_A_StackDepotBase_Get : Z := 0x76ff8.  Definition tfib_E_StackDepotBase_Get : Z := 0x77108.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x774e8.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x77578.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x77578.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x77678.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x776d8.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x776e0.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x776e0.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x77840.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x77840.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x778b4.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x77d3c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x77e54.
Definition tfib_A_thunk_762d8 : Z := 0x7aea0.  Definition tfib_E_thunk_762d8 : Z := 0x7aea4.
Definition tfib_A_thunk_77ab0 : Z := 0x7c678.  Definition tfib_E_thunk_77ab0 : Z := 0x7c67c.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7e0a4.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7e160.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7e160.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7e238.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7e238.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7e4ac.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7e7d8.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7e81c.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7e81c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ebec.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7eebc.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7ef74.
Definition tfib_A_thunk_7b6f8 : Z := 0x802cc.  Definition tfib_E_thunk_7b6f8 : Z := 0x802d0.
Definition tfib_A_lsan_register_root_region : Z := 0x80ed8.  Definition tfib_E_lsan_register_root_region : Z := 0x81208.
Definition tfib_A_lsan_unregister_root_region : Z := 0x81208.  Definition tfib_E_lsan_unregister_root_region : Z := 0x81690.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x81690.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x8169c.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x84254.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x8426c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x845f0.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x8466c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x8466c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x8471c.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x8471c.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x84734.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x84734.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8487c.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x8487c.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x84888.
Definition tfib_A_asan_default_options_cli_c : Z := 0x84888.  Definition tfib_E_asan_default_options_cli_c : Z := 0x84894.
Definition tfib_A_main : Z := 0x84894.  Definition tfib_E_main : Z := 0x84b58.
Definition tfib_A_target_alloc_init : Z := 0x84b58.  Definition tfib_E_target_alloc_init : Z := 0x84b5c.
Definition tfib_A_target_alloc_count : Z := 0x84b5c.  Definition tfib_E_target_alloc_count : Z := 0x84b64.
Definition tfib_A_target_run : Z := 0x84b64.  Definition tfib_E_target_run : Z := 0x84cec.
Definition tfib_A_emit_printf : Z := 0x84cec.  Definition tfib_E_emit_printf : Z := 0x84d34.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x84d34.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x85ebc.  Definition tfib_A_m_file : Z := 0x85ebc.  Definition tfib_E_m_file : Z := 0x8704c.  Definition tfib_A_check_segments : Z := 0x8704c.  Definition tfib_E_check_segments : Z := 0x87188.  Definition tfib_A_check_role : Z := 0x87188.  Definition tfib_E_check_role : Z := 0x87210.  Definition tfib_A_check_model : Z := 0x87210.  Definition tfib_E_check_model : Z := 0x87288.  Definition tfib_A_check_ignore : Z := 0x87288.  Definition tfib_E_check_ignore : Z := 0x872e0.  Definition tfib_A_check_provenance : Z := 0x872e0.  Definition tfib_E_check_provenance : Z := 0x873c8.  Definition tfib_A_check_refusals : Z := 0x873c8.  Definition tfib_E_check_refusals : Z := 0x874b8.  Definition tfib_A_check_address : Z := 0x874b8.  Definition tfib_E_check_address : Z := 0x87508.  Definition tfib_A_check_knock_refused : Z := 0x87508.  Definition tfib_E_check_knock_refused : Z := 0x87538.  Definition tfib_A_m_find : Z := 0x87538.  Definition tfib_E_m_find : Z := 0x875e8.  Definition tfib_A_check_absent : Z := 0x875e8.  Definition tfib_E_check_absent : Z := 0x87658.  Definition tfib_A_check_declared : Z := 0x87658.  Definition tfib_E_check_declared : Z := 0x877d0.  Definition tfib_A_m_refuse : Z := 0x877d0.  Definition tfib_E_m_refuse : Z := 0x87904.  Definition tfib_A_ieq : Z := 0x87904.  Definition tfib_E_ieq : Z := 0x879ec.  Definition tfib_A_reac_segconf_init : Z := 0x87a54.  Definition tfib_E_reac_segconf_init : Z := 0x87a78.  Definition tfib_A_reac_segconf_parse_file : Z := 0x87a78.  Definition tfib_E_reac_segconf_parse_file : Z := 0x88da4.  Definition tfib_A_refuse : Z := 0x88da4.  Definition tfib_E_refuse : Z := 0x890a8.  Definition tfib_A_trim : Z := 0x890a8.  Definition tfib_E_trim : Z := 0x891d0.  Definition tfib_A_reac_segconf_parse : Z := 0x891d0.  Definition tfib_E_reac_segconf_parse : Z := 0x89218.  Definition tfib_A_cross_check : Z := 0x89218.  Definition tfib_E_cross_check : Z := 0x894ec.  Definition tfib_A_reac_segconf_find : Z := 0x894ec.  Definition tfib_E_reac_segconf_find : Z := 0x89594.  Definition tfib_A_reac_segconf_ignored : Z := 0x89594.  Definition tfib_E_reac_segconf_ignored : Z := 0x895f0.  Definition tfib_A_reac_segconf_role : Z := 0x895f0.  Definition tfib_E_reac_segconf_role : Z := 0x896b8.  Definition tfib_A_reac_segconf_role_file : Z := 0x896b8.  Definition tfib_E_reac_segconf_role_file : Z := 0x89750.  Definition tfib_A_reac_segconf_ignore_file : Z := 0x89750.  Definition tfib_E_reac_segconf_ignore_file : Z := 0x897e8.  Definition tfib_A_reac_segconf_model : Z := 0x897e8.  Definition tfib_E_reac_segconf_model : Z := 0x89854.  Definition tfib_A_reac_segconf_declared : Z := 0x89854.  Definition tfib_E_reac_segconf_declared : Z := 0x89b8c.  Definition tfib_A_reac_declared_vlan_split : Z := 0x89b8c.  Definition tfib_E_reac_declared_vlan_split : Z := 0x89d58.  Definition tfib_A_name_ok : Z := 0x89d58.  Definition tfib_E_name_ok : Z := 0x89e4c.  Definition tfib_A_reac_declared_vlan_add : Z := 0x89e4c.  Definition tfib_E_reac_declared_vlan_add : Z := 0x8a038.  Definition tfib_A_fuzz_catalogue_row : Z := 0x8a038.  Definition tfib_E_fuzz_catalogue_row : Z := 0x8a100.  Definition tfib_A_reac_box_catalogue : Z := 0x8a100.  Definition tfib_E_reac_box_catalogue : Z := 0x8a148.  Definition tfib_A_reac_box_catalogue_by_token : Z := 0x8a148.  Definition tfib_E_reac_box_catalogue_by_token : Z := 0x8a188.
Definition tfib_A_asan_module_ctor : Z := 0x879ec.  Definition tfib_E_asan_module_ctor : Z := 0x87a24.




Definition tfib_A_asan_module_dtor : Z := 0x87a24.  Definition tfib_E_asan_module_dtor : Z := 0x87a54.



Definition tfib_A_extenddftf2 : Z := 0x8a198.  Definition tfib_E_extenddftf2 : Z := 0x8a328.
Definition tfib_A_sysconf : Z := 0x8ff78.  Definition tfib_E_sysconf : Z := 0x901a0.
Definition tfib_A_init : Z := 0x901bc.  Definition tfib_E_init : Z := 0x901c0.
Definition tfib_A_init_libc : Z := 0x901c0.  Definition tfib_E_init_libc : Z := 0x903ec.
Definition tfib_A_libc_start_init : Z := 0x903ec.  Definition tfib_E_libc_start_init : Z := 0x90438.
Definition tfib_A_libc_start_main : Z := 0x90438.  Definition tfib_E_libc_start_main : Z := 0x90498.
Definition tfib_A_libc_start_main_stage2 : Z := 0x90498.  Definition tfib_E_libc_start_main_stage2 : Z := 0x904e0.
Definition tfib_A_init_tls : Z := 0x905b8.  Definition tfib_E_init_tls : Z := 0x90868.
Definition tfib_A_init_ssp : Z := 0x90868.  Definition tfib_E_init_ssp : Z := 0x908c8.
Definition tfib_A_stack_chk_fail : Z := 0x908c8.  Definition tfib_E_stack_chk_fail : Z := 0x908d0.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x90918.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x909ac.
Definition tfib_A_Exit : Z := 0x909ac.  Definition tfib_E_Exit : Z := 0x909c8.
Definition tfib_A_funcs_on_exit : Z := 0x909f8.  Definition tfib_E_funcs_on_exit : Z := 0x90ac0.
Definition tfib_A_fini_stub_ret : Z := 0x90ac0.  Definition tfib_E_fini_stub_ret : Z := 0x90ac4.
Definition tfib_A_cxa_atexit_atexit : Z := 0x90ac4.  Definition tfib_E_cxa_atexit_atexit : Z := 0x90b88.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x90b88.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x90b8c.
Definition tfib_A_musl_exit_helper_stub : Z := 0x90b8c.  Definition tfib_E_musl_exit_helper_stub : Z := 0x90b90.
Definition tfib_A_libc_exit_fini : Z := 0x90b90.  Definition tfib_E_libc_exit_fini : Z := 0x90bdc.
Definition tfib_A_exit : Z := 0x90bdc.  Definition tfib_E_exit : Z := 0x90c50.
Definition tfib_A_open : Z := 0x90e50.  Definition tfib_E_open : Z := 0x90f34.
Definition tfib_A_syscall_ret : Z := 0x90f34.  Definition tfib_E_syscall_ret : Z := 0x90f6c.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x90f6c.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x91114.
Definition tfib_A_calloc : Z := 0x916d8.  Definition tfib_E_calloc : Z := 0x91810.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x91810.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x91814.
Definition tfib_A_libc_free : Z := 0x91814.  Definition tfib_E_libc_free : Z := 0x919e0.
Definition tfib_A_get_meta : Z := 0x919e0.  Definition tfib_E_get_meta : Z := 0x91af0.
Definition tfib_A_alloc_meta : Z := 0x91ec8.  Definition tfib_E_alloc_meta : Z := 0x921a0.
Definition tfib_A_libc_malloc_impl : Z := 0x921a0.  Definition tfib_E_libc_malloc_impl : Z := 0x92510.
Definition tfib_A_alloc_slot : Z := 0x92510.  Definition tfib_E_alloc_slot : Z := 0x92db4.
Definition tfib_A_enframe : Z := 0x92db4.  Definition tfib_E_enframe : Z := 0x92f04.
Definition tfib_A_malloc_allzerop : Z := 0x92f04.  Definition tfib_E_malloc_allzerop : Z := 0x9307c.
Definition tfib_A_getrlimit : Z := 0x94d2c.  Definition tfib_E_getrlimit : Z := 0x94e24.
Definition tfib_A_getrusage : Z := 0x94e24.  Definition tfib_E_getrusage : Z := 0x94e4c.
Definition tfib_A_setrlimit : Z := 0x94e4c.  Definition tfib_E_setrlimit : Z := 0x94f14.
Definition tfib_A_mmap : Z := 0x9533c.  Definition tfib_E_mmap : Z := 0x95428.
Definition tfib_A_mprotect : Z := 0x95428.  Definition tfib_E_mprotect : Z := 0x95470.
Definition tfib_A_munmap : Z := 0x95544.  Definition tfib_E_munmap : Z := 0x9558c.
Definition tfib_A_sched_yield : Z := 0x95850.  Definition tfib_E_sched_yield : Z := 0x95874.
Definition tfib_A_raise_tkill_path : Z := 0x958d0.  Definition tfib_E_raise_tkill_path : Z := 0x95948.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x95948.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x95b1c.
Definition tfib_A_musl_sigaltstack : Z := 0x95c14.  Definition tfib_E_musl_sigaltstack : Z := 0x95ca0.
Definition tfib_A_fprintf : Z := 0x9627c.  Definition tfib_E_fprintf : Z := 0x962e0.
Definition tfib_A_lockfile : Z := 0x962e0.  Definition tfib_E_lockfile : Z := 0x963dc.
Definition tfib_A_unlockfile : Z := 0x963dc.  Definition tfib_E_unlockfile : Z := 0x9643c.

Definition tfib_A_stdio_read : Z := 0x95fcc.  Definition tfib_E_stdio_read : Z := 0x960e4.
Definition tfib_A_stdio_write : Z := 0x960ec.  Definition tfib_E_stdio_write : Z := 0x9627c.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x95f9c.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x95fa0.
Definition tfib_A_stdio_close : Z := 0x95fa0.  Definition tfib_E_stdio_close : Z := 0x95fcc.
Definition tfib_A_fwritex : Z := 0x96870.  Definition tfib_E_fwritex : Z := 0x969a8.
Definition tfib_A_musl_fwrite : Z := 0x969a8.  Definition tfib_E_musl_fwrite : Z := 0x96a60.
Definition tfib_A_towrite : Z := 0x96a60.  Definition tfib_E_towrite : Z := 0x96ab4.
Definition tfib_A_stdio_exit : Z := 0x966cc.  Definition tfib_E_stdio_exit : Z := 0x96870.
Definition tfib_A_ofl_lock : Z := 0x96ab4.  Definition tfib_E_ofl_lock : Z := 0x96ae4.
Definition tfib_A_musl_vfprintf : Z := 0x96c30.  Definition tfib_E_musl_vfprintf : Z := 0x96de0.
Definition tfib_A_printf_core : Z := 0x96de0.  Definition tfib_E_printf_core : Z := 0x97c10.
Definition tfib_A_pop_arg : Z := 0x97c10.  Definition tfib_E_pop_arg : Z := 0x97d44.
Definition tfib_A_pad : Z := 0x97d44.  Definition tfib_E_pad : Z := 0x97e18.
Definition tfib_A_fmt_fp : Z := 0x97e18.  Definition tfib_E_fmt_fp : Z := 0x994e0.
Definition tfib_A_thunk_931e0 : Z := 0x9132c.  Definition tfib_E_thunk_931e0 : Z := 0x91330.
Definition tfib_A_musl_wctomb : Z := 0x956b8.  Definition tfib_E_musl_wctomb : Z := 0x956dc.
Definition tfib_A_musl_wcrtomb : Z := 0x9558c.  Definition tfib_E_musl_wcrtomb : Z := 0x956b8.
Definition tfib_A_fpclassifyl : Z := 0x9391c.  Definition tfib_E_fpclassifyl : Z := 0x93960.
Definition tfib_A_letf2 : Z := 0x93154.  Definition tfib_E_letf2 : Z := 0x9321c.
Definition tfib_A_multf3 : Z := 0x9321c.  Definition tfib_E_multf3 : Z := 0x9391c.
Definition tfib_A_floatsitf : Z := 0x94178.  Definition tfib_E_floatsitf : Z := 0x94280.
Definition tfib_A_scalbn : Z := 0x94b84.  Definition tfib_E_scalbn : Z := 0x94c1c.
Definition tfib_A_subtf3 : Z := 0x94168.  Definition tfib_E_subtf3 : Z := 0x94178.
Definition tfib_A_addtf3 : Z := 0x93960.  Definition tfib_E_addtf3 : Z := 0x9412c.
Definition tfib_A_fe_getround : Z := 0x9412c.  Definition tfib_E_fe_getround : Z := 0x9415c.
Definition tfib_A_fixunstfsi : Z := 0x994e8.  Definition tfib_E_fixunstfsi : Z := 0x9957c.
Definition tfib_A_floatunsitf : Z := 0x9957c.  Definition tfib_E_floatunsitf : Z := 0x99668.
Definition tfib_A_fixtfsi : Z := 0x94c1c.  Definition tfib_E_fixtfsi : Z := 0x94cc4.
Definition tfib_A_divtf3 : Z := 0x94280.  Definition tfib_E_divtf3 : Z := 0x94b84.
Definition tfib_A_musl_vprintf : Z := 0x99d40.  Definition tfib_E_musl_vprintf : Z := 0x99d5c.
Definition tfib_A_stdout_write : Z := 0x96af0.  Definition tfib_E_stdout_write : Z := 0x96b90.
Definition tfib_A_thunk_95368 : Z := 0x9a2f4.  Definition tfib_E_thunk_95368 : Z := 0x9a2f8.
Definition tfib_A_musl_memcmp : Z := 0x9a3c4.  Definition tfib_E_musl_memcmp : Z := 0x9a3f4.
Definition tfib_A_musl_memcpy : Z := 0x9a3f4.  Definition tfib_E_musl_memcpy : Z := 0x9a7f8.
Definition tfib_A_musl_memset : Z := 0x9a828.  Definition tfib_E_musl_memset : Z := 0x9a920.
Definition tfib_A_musl_strchr : Z := 0x9a9d4.  Definition tfib_E_musl_strchr : Z := 0x9aa10.
Definition tfib_A_strchrnul : Z := 0x9aa10.  Definition tfib_E_strchrnul : Z := 0x9aaf0.
Definition tfib_A_musl_strlen : Z := 0x9ab28.  Definition tfib_E_musl_strlen : Z := 0x9abb8.
Definition tfib_A_musl_strnlen : Z := 0x9ae88.  Definition tfib_E_musl_strnlen : Z := 0x9aecc.
Definition tfib_A_musl_memchr : Z := 0x9a2f8.  Definition tfib_E_musl_memchr : Z := 0x9a3c4.
Definition tfib_A_lock : Z := 0x9b600.  Definition tfib_E_lock : Z := 0x9b888.
Definition tfib_A_unlock : Z := 0x9b888.  Definition tfib_E_unlock : Z := 0x9b8fc.
Definition tfib_A_syscall_cp_c : Z := 0x9b8fc.  Definition tfib_E_syscall_cp_c : Z := 0x9b920.
Definition tfib_A_syscall_cp_sccp : Z := 0x9b920.  Definition tfib_E_syscall_cp_sccp : Z := 0x9b924.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9b924.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9b948.
Definition tfib_A_pthread_atfork : Z := 0x9b960.  Definition tfib_E_pthread_atfork : Z := 0x9ba04.
Definition tfib_A_mremap : Z := 0x95470.  Definition tfib_E_mremap : Z := 0x95544.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9c9d8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9c9f4.
Definition tfib_A_pthread_key_create : Z := 0x9cd80.  Definition tfib_E_pthread_key_create : Z := 0x9ce54.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9d0f8.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x9d19c.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x9d19c.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x9d2b8.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9d2b8.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9d2e4.
Definition tfib_A_pthread_setspecific : Z := 0x9d31c.  Definition tfib_E_pthread_setspecific : Z := 0x9d350.
Definition tfib_A_set_thread_area : Z := 0x9d358.  Definition tfib_E_set_thread_area : Z := 0x9d364.
Definition tfib_A_thunk_96f9c : Z := 0x9d350.  Definition tfib_E_thunk_96f9c : Z := 0x9d358.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9dc84.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9dd3c.
Definition tfib_A_close : Z := 0xa0354.  Definition tfib_E_close : Z := 0xa03a8.
Definition tfib_A_musl_read : Z := 0xa0434.  Definition tfib_E_musl_read : Z := 0xa0468.
Definition tfib_A_vm_wait : Z := 0x9d994.  Definition tfib_E_vm_wait : Z := 0x9d9e4.
Definition tfib_D_str_sealed : Z := 0x11848.
Definition tfib_D_init_array_0_3 : Z := 0xa1468.
Definition tfib_D_fini_array_0_1 : Z := 0xa1488.
Definition tfib_D_GOT_common_flags : Z := 0xa2a40.
Definition tfib_D_GOT_flags : Z := 0xa2a48.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa2a50.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa2a58.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa2a60.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa2a68.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa35b8.
Definition tfib_D_environ_musl : Z := 0xa36e0.
Definition tfib_D_REAL_read : Z := 0xa47b8.
Definition tfib_D_REAL_memcpy : Z := 0xa48e0.
Definition tfib_D_REAL_memset : Z := 0xa48e8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa8998.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa97f8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xabff8.
Definition tfib_D_asan_inited : Z := 0xaccd8.
Definition tfib_D_replace_intrin_cached : Z := 0xaccd9.
Definition tfib_D_kHighMemEnd : Z := 0xacce0.
Definition tfib_D_kMidMemBeg : Z := 0xacce8.
Definition tfib_D_kMidMemEnd : Z := 0xaccf0.
Definition tfib_D_malloc_context_size : Z := 0xaccfc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13db28.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5ff2c8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x601000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x31ed4.
Definition tfib_at_rw_lo : Z := 0xa4000.
Definition tfib_at_rw_len : Z := 0x55d000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x6820c.
Definition tfib_at_x_imemcpy : Z := 0x68190.
Definition tfib_at_x_memset : Z := 0x9a828.
Definition tfib_at_x_memcpy : Z := 0x9a3f4.
Definition tfib_at_x_memiszero : Z := 0x6873c.
Definition tfib_at_x_istrncpy : Z := 0x68638.
Definition tfib_at_x_sealed : Z := 0x11848.
Definition tfib_at_x_popfree : Z := 0x383a0.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x901f8.
Definition tfib_at_x_envscan_k : Z := 0x90204.
Definition tfib_at_x_pnscan : Z := 0x902bc.
Definition tfib_at_x_pnscan_k : Z := 0x902c8.
Definition tfib_at_stops_more : list Z := (0x36014 :: 0x37638 :: 0x581b4 :: 0x5e7bc :: 0x5e7d0 :: 0x5e7e4 :: 0x64288 :: 0x64358 :: 0x71884 :: 0x72790 :: 0x72920 :: 0x7c678 :: nil)%list.
