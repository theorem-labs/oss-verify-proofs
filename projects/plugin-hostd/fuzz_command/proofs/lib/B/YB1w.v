(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its rows regenerated for plugin-hostd/fuzz_command's ASan build by the AB1w row regenerator: each start is the fuzz_command function paired by code with cgif's, each end the pair of cgif's last instruction plus its length; a row whose label is a FUNC symbol of fuzz_command's image takes that symbol's range (LLVMFuzzerTestOneInput); the side-stack class rows are fuzz_command's own __asan_stack_malloc_0, _1, _3, _4, _5 and _7 (symbol address and size; class 1 keeps cgif's row name asan_stack_malloc_A, the others are named by class); six rows are set from the image by hand (HaveStackTraceBasedSuppressions, set_thread_area, two jump stubs by their target, the self-loop stub, and the ends of __stdio_exit and musl memset, whose code differs); section bounds come from fuzz_command's section headers; the rows of cgif functions fuzz_command does not have (cgif's program and GIF library, fopen/fclose/fdopen/ofl_add/fmodeflags and their interceptors, stack_malloc_2) are dropped; twelve rows whose cgif label names another function than the code of their range take the name of the image symbol at their start (internal_strchr / _strcmp / _strncmp, AsanCheckIncompatibleRT / AsanCheckDynamicRTPrereqs, IsAddrSuppressed, IsRssLimitExceeded, DecreaseTotalMmap, GetTls, MmapFixedSuperNoReserve, MmapNoAccess, ReservedAddressRange_MapOrDie). *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AB1w.v (the twin of cgif_file_fuzzer's lib/YB1w.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x246e4.
Definition tfib_text_lo : Z := 0x3338c.  Definition tfib_text_hi : Z := 0xa4258.
Definition tfib_init_array_lo : Z := 0xa5258.  Definition tfib_init_array_hi : Z := 0xa5278.
Definition tfib_fini_array_lo : Z := 0xa5278.  Definition tfib_fini_array_hi : Z := 0xa5288.
Definition tfib_preinit_array_lo : Z := 0xa5288.  Definition tfib_preinit_array_hi : Z := 0xa5290.
Definition tfib_data_rel_ro_lo : Z := 0xa52a0.  Definition tfib_data_rel_ro_hi : Z := 0xa5ef0.
Definition tfib_got_lo : Z := 0xa5ef0.  Definition tfib_got_hi : Z := 0xa6c68.
Definition tfib_data_lo : Z := 0xa7c68.  Definition tfib_data_hi : Z := 0xaa858.
Definition tfib_asan_globals_lo : Z := 0xaa860.  Definition tfib_asan_globals_hi : Z := 0xad560.
Definition tfib_bss_lo : Z := 0xad580.  Definition tfib_bss_hi : Z := 0x6059f8.
Definition tfib_tbss_lo : Z := 0xa4258.  Definition tfib_tbss_hi : Z := 0xa426c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x606000.
Definition tfib_entry : Z := 0x3338c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x3338c.  Definition tfib_E_start : Z := 0x333d4.
Definition tfib_A_do_init : Z := 0x333d4.  Definition tfib_E_do_init : Z := 0x33448.
Definition tfib_A_do_fini : Z := 0x33448.  Definition tfib_E_do_fini : Z := 0x334d8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x334d8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x33514.
Definition tfib_A_InitializeAllocator : Z := 0x33684.  Definition tfib_E_InitializeAllocator : Z := 0x3369c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3369c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x33808.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x33d64.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x33ec0.
Definition tfib_A_asan_free : Z := 0x34294.  Definition tfib_E_asan_free : Z := 0x342bc.
Definition tfib_A_Allocator_Deallocate : Z := 0x342bc.  Definition tfib_E_Allocator_Deallocate : Z := 0x34574.
Definition tfib_A_asan_malloc : Z := 0x34574.  Definition tfib_E_asan_malloc : Z := 0x345d0.
Definition tfib_A_Allocator_Allocate : Z := 0x345d0.  Definition tfib_E_Allocator_Allocate : Z := 0x34f58.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x35690.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x357d4.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x358c0.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x3591c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x3591c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x35b6c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35b6c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x35c60.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x35c60.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x35d48.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x3617c.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x36360.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x36360.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x364e4.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x3661c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x368a0.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x368a0.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x36a20.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x36a20.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x36be8.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x36be8.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x36db4.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x36db4.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x36e54.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x36e54.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x36f58.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x37280.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x373c8.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x373c8.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x37400.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37b98.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x37e80.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x38558.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x386d0.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x386d0.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x38880.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x38880.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x38a64.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x38a64.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x38d3c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x38d3c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x391b4.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x391b4.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x392b4.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x392b4.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x395bc.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x395bc.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x3992c.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x3992c.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x39a44.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x39d4c.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x39e48.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x39e48.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x39f30.
Definition tfib_A_AsanActivate : Z := 0x39f30.  Definition tfib_E_AsanActivate : Z := 0x3a00c.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x3a4e8.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x3a5d0.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3f088.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3f160.
Definition tfib_A_FakeStack_Create : Z := 0x3f160.  Definition tfib_E_FakeStack_Create : Z := 0x3f24c.
Definition tfib_A_FakeStack_Allocate : Z := 0x3f508.  Definition tfib_E_FakeStack_Allocate : Z := 0x3f7f0.
Definition tfib_A_SetTLSFakeStack : Z := 0x3f924.  Definition tfib_E_SetTLSFakeStack : Z := 0x3f954.
Definition tfib_A_asan_stack_malloc_A : Z := 0x3fac8.  Definition tfib_E_asan_stack_malloc_A : Z := 0x3fc58.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3f954.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3fac8.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3fc58.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3fe04.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3fe04.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3ffd0.
Definition tfib_A_asan_stack_malloc_5 : Z := 0x3ffd0.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x401dc.
Definition tfib_A_asan_stack_malloc_7 : Z := 0x40290.  Definition tfib_E_asan_stack_malloc_7 : Z := 0x4040c.
Definition tfib_A_FakeStack_SetShadow : Z := 0x4045c.  Definition tfib_E_FakeStack_SetShadow : Z := 0x40598.
Definition tfib_A_asan_InitializeFlags : Z := 0x40598.  Definition tfib_E_asan_InitializeFlags : Z := 0x415c4.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x41cd0.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x42aec.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x42aec.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x430b8.
Definition tfib_A_asan_register_globals : Z := 0x430b8.  Definition tfib_E_asan_register_globals : Z := 0x43124.
Definition tfib_A_asan_unregister_globals : Z := 0x43124.  Definition tfib_E_asan_unregister_globals : Z := 0x4318c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x4380c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x43a7c.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x43a7c.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x43d84.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x444f8.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x44648.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x45064.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x4517c.
Definition tfib_A_strlen : Z := 0x4517c.  Definition tfib_E_strlen : Z := 0x45180.
Definition tfib_A_strnlen : Z := 0x45180.  Definition tfib_E_strnlen : Z := 0x45184.
Definition tfib_A_strcmp : Z := 0x45188.  Definition tfib_E_strcmp : Z := 0x4518c.
Definition tfib_A_strchr : Z := 0x45190.  Definition tfib_E_strchr : Z := 0x45194.
Definition tfib_A_memcmp : Z := 0x4519c.  Definition tfib_E_memcmp : Z := 0x451a0.
Definition tfib_A_memcmp_2 : Z := 0x451a0.  Definition tfib_E_memcmp_2 : Z := 0x451a4.
Definition tfib_A_memchr : Z := 0x451a4.  Definition tfib_E_memchr : Z := 0x451a8.
Definition tfib_A_frexpl : Z := 0x451a8.  Definition tfib_E_frexpl : Z := 0x451ac.
Definition tfib_A_read : Z := 0x451ac.  Definition tfib_E_read : Z := 0x451b0.
Definition tfib_A_fwrite : Z := 0x451b0.  Definition tfib_E_fwrite : Z := 0x451b4.
Definition tfib_A_time : Z := 0x451b4.  Definition tfib_E_time : Z := 0x451b8.
Definition tfib_A_gmtime_r : Z := 0x451b8.  Definition tfib_E_gmtime_r : Z := 0x451bc.
Definition tfib_A_vprintf : Z := 0x451bc.  Definition tfib_E_vprintf : Z := 0x451c0.
Definition tfib_A_vfprintf : Z := 0x451c0.  Definition tfib_E_vfprintf : Z := 0x451c4.
Definition tfib_A_vsnprintf : Z := 0x451c4.  Definition tfib_E_vsnprintf : Z := 0x451c8.
Definition tfib_A_vfprintf_2 : Z := 0x451c8.  Definition tfib_E_vfprintf_2 : Z := 0x451cc.
Definition tfib_A_thunk_417bc : Z := 0x451d0.  Definition tfib_E_thunk_417bc : Z := 0x451d4.
Definition tfib_A_clock_gettime : Z := 0x451d4.  Definition tfib_E_clock_gettime : Z := 0x451d8.
Definition tfib_A_wcrtomb : Z := 0x451d8.  Definition tfib_E_wcrtomb : Z := 0x451dc.
Definition tfib_A_wctomb : Z := 0x451dc.  Definition tfib_E_wctomb : Z := 0x451e0.
Definition tfib_A_thunk_417cc : Z := 0x451e0.  Definition tfib_E_thunk_417cc : Z := 0x451e8.
Definition tfib_A_pthread_attr_getstack : Z := 0x451e8.  Definition tfib_E_pthread_attr_getstack : Z := 0x451ec.
Definition tfib_A_tls_get_addr_thunk : Z := 0x451ec.  Definition tfib_E_tls_get_addr_thunk : Z := 0x451f0.
Definition tfib_A_thunk_417dc : Z := 0x451f0.  Definition tfib_E_thunk_417dc : Z := 0x451f4.
Definition tfib_A_thunk_417e4 : Z := 0x451f4.  Definition tfib_E_thunk_417e4 : Z := 0x451f8.
Definition tfib_A_thunk_417e8 : Z := 0x451f8.  Definition tfib_E_thunk_417e8 : Z := 0x451fc.
Definition tfib_A_thunk_417ec : Z := 0x451fc.  Definition tfib_E_thunk_417ec : Z := 0x45200.
Definition tfib_A_thunk_417f0 : Z := 0x45200.  Definition tfib_E_thunk_417f0 : Z := 0x45204.
Definition tfib_A_sem_timedwait : Z := 0x45204.  Definition tfib_E_sem_timedwait : Z := 0x45208.
Definition tfib_A_thunk_417f8 : Z := 0x45208.  Definition tfib_E_thunk_417f8 : Z := 0x4520c.
Definition tfib_A_pthread_setcancelstate : Z := 0x4520c.  Definition tfib_E_pthread_setcancelstate : Z := 0x45210.
Definition tfib_A_send : Z := 0x45210.  Definition tfib_E_send : Z := 0x45214.
Definition tfib_A_sendto : Z := 0x45214.  Definition tfib_E_sendto : Z := 0x45218.
Definition tfib_A_sigaltstack : Z := 0x45218.  Definition tfib_E_sigaltstack : Z := 0x4521c.
Definition tfib_A_thunk_4180c : Z := 0x4521c.  Definition tfib_E_thunk_4180c : Z := 0x45220.
Definition tfib_A_icpt_strlen : Z := 0x45234.  Definition tfib_E_icpt_strlen : Z := 0x454c8.
Definition tfib_A_icpt_strnlen : Z := 0x454c8.  Definition tfib_E_icpt_strnlen : Z := 0x4575c.
Definition tfib_A_icpt_strcmp : Z := 0x45a70.  Definition tfib_E_icpt_strcmp : Z := 0x45fa0.
Definition tfib_A_icpt_strchr : Z := 0x4657c.  Definition tfib_E_icpt_strchr : Z := 0x4685c.
Definition tfib_A_icpt_memcmp : Z := 0x47a04.  Definition tfib_E_icpt_memcmp : Z := 0x47ac0.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x47ac0.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x47b7c.
Definition tfib_A_icpt_memchr : Z := 0x47b7c.  Definition tfib_E_icpt_memchr : Z := 0x47e4c.
Definition tfib_A_icpt_frexpl : Z := 0x47e4c.  Definition tfib_E_icpt_frexpl : Z := 0x480c4.
Definition tfib_A_icpt_read : Z := 0x480c4.  Definition tfib_E_icpt_read : Z := 0x48334.
Definition tfib_A_icpt_fwrite : Z := 0x48334.  Definition tfib_E_icpt_fwrite : Z := 0x485a8.
Definition tfib_A_icpt_time : Z := 0x485a8.  Definition tfib_E_icpt_time : Z := 0x48844.
Definition tfib_A_icpt_gmtime_r : Z := 0x48a4c.  Definition tfib_E_icpt_gmtime_r : Z := 0x48c8c.
Definition tfib_A_icpt_vprintf : Z := 0x48c8c.  Definition tfib_E_icpt_vprintf : Z := 0x48d28.
Definition tfib_A_printf_common_format_interceptor : Z := 0x48d28.  Definition tfib_E_printf_common_format_interceptor : Z := 0x497f0.
Definition tfib_A_icpt_vfprintf : Z := 0x497f0.  Definition tfib_E_icpt_vfprintf : Z := 0x498a4.
Definition tfib_A_icpt_vsnprintf : Z := 0x498a4.  Definition tfib_E_icpt_vsnprintf : Z := 0x49bbc.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x49e9c.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x49f74.
Definition tfib_A_icpt_clock_gettime : Z := 0x4a0a8.  Definition tfib_E_icpt_clock_gettime : Z := 0x4a300.
Definition tfib_A_icpt_wcrtomb : Z := 0x4a300.  Definition tfib_E_icpt_wcrtomb : Z := 0x4a870.
Definition tfib_A_icpt_wctomb : Z := 0x4a870.  Definition tfib_E_icpt_wctomb : Z := 0x4abcc.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x4ac98.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4b080.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4b08c.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4b108.

Definition tfib_A_icpt_sem_timedwait : Z := 0x4b314.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4b5ac.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4b5dc.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4b804.
Definition tfib_A_icpt_send : Z := 0x4b804.  Definition tfib_E_icpt_send : Z := 0x4bab8.
Definition tfib_A_icpt_sendto : Z := 0x4bab8.  Definition tfib_E_icpt_sendto : Z := 0x4bd7c.
Definition tfib_A_icpt_sigaltstack : Z := 0x4bd7c.  Definition tfib_E_icpt_sigaltstack : Z := 0x4bfd8.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4d48c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4d63c.
Definition tfib_A_icpt_diouxXn : Z := 0x4d63c.  Definition tfib_E_icpt_diouxXn : Z := 0x4d7d4.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x4e380.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x57058.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x57058.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x571b4.
Definition tfib_A_memset : Z := 0x57674.  Definition tfib_E_memset : Z := 0x57678.
Definition tfib_A_memcpy : Z := 0x57678.  Definition tfib_E_memcpy : Z := 0x5767c.
Definition tfib_A_asan_memcpy : Z := 0x5767c.  Definition tfib_E_asan_memcpy : Z := 0x57b18.
Definition tfib_A_asan_memset : Z := 0x57b18.  Definition tfib_E_asan_memset : Z := 0x57d58.
Definition tfib_A_icpt_memset : Z := 0x57d58.  Definition tfib_E_icpt_memset : Z := 0x58048.
Definition tfib_A_icpt_memcpy : Z := 0x58048.  Definition tfib_E_icpt_memcpy : Z := 0x58638.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x58638.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x58670.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x58670.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x58674.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x58674.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x58678.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x58678.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x586d8.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x58724.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x58860.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x58860.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x58864.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x58864.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x589cc.
Definition tfib_A_free : Z := 0x589cc.  Definition tfib_E_free : Z := 0x589d0.
Definition tfib_A_malloc : Z := 0x589d0.  Definition tfib_E_malloc : Z := 0x589d4.
Definition tfib_A_icpt_free : Z := 0x589d4.  Definition tfib_E_icpt_free : Z := 0x58ba4.
Definition tfib_A_icpt_malloc : Z := 0x58ba4.  Definition tfib_E_icpt_malloc : Z := 0x58d00.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x58d00.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x58dcc.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x58dcc.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x58dd0.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x58dd0.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x58ed0.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x591f8.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x59364.
Definition tfib_A_SetCanPoisonMemory : Z := 0x5984c.  Definition tfib_E_SetCanPoisonMemory : Z := 0x5985c.
Definition tfib_A_CanPoisonMemory : Z := 0x5985c.  Definition tfib_E_CanPoisonMemory : Z := 0x59870.
Definition tfib_A_PoisonShadow : Z := 0x59870.  Definition tfib_E_PoisonShadow : Z := 0x59d6c.
Definition tfib_A_MemToShadow_checked : Z := 0x59d6c.  Definition tfib_E_MemToShadow_checked : Z := 0x59ea8.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x59ea8.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x5a048.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x5a048.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x5a1c8.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5a1f8.  Definition tfib_E_asan_region_is_poisoned : Z := 0x5a53c.
Definition tfib_A_AsanTSDInit : Z := 0x5a95c.  Definition tfib_E_AsanTSDInit : Z := 0x5a9d8.
Definition tfib_A_AsanTSDGet : Z := 0x5a9d8.  Definition tfib_E_AsanTSDGet : Z := 0x5aa18.
Definition tfib_A_AsanTSDSet : Z := 0x5aa18.  Definition tfib_E_AsanTSDSet : Z := 0x5aa58.
Definition tfib_A_PlatformTSDDtor : Z := 0x5aa58.  Definition tfib_E_PlatformTSDDtor : Z := 0x5aadc.
Definition tfib_A_InstallAtForkHandler : Z := 0x5aadc.  Definition tfib_E_InstallAtForkHandler : Z := 0x5aaf8.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x5ab58.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5ab9c.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x5b2b4.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x5b4c0.
Definition tfib_A_ReportDoubleFree : Z := 0x5bbc8.  Definition tfib_E_ReportDoubleFree : Z := 0x5be58.
Definition tfib_A_ReportGenericError : Z := 0x5d734.  Definition tfib_E_ReportGenericError : Z := 0x5dff0.
Definition tfib_A_AsanInited : Z := 0x5e77c.  Definition tfib_E_AsanInited : Z := 0x5e794.
Definition tfib_A_asan_report_load1 : Z := 0x5e794.  Definition tfib_E_asan_report_load1 : Z := 0x5e7e4.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5e7e4.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5e834.
Definition tfib_A_asan_report_load2 : Z := 0x5e834.  Definition tfib_E_asan_report_load2 : Z := 0x5e884.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5e884.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5e8d4.
Definition tfib_A_asan_report_load4 : Z := 0x5e8d4.  Definition tfib_E_asan_report_load4 : Z := 0x5e924.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5e924.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5e974.
Definition tfib_A_asan_report_load8 : Z := 0x5e974.  Definition tfib_E_asan_report_load8 : Z := 0x5e9c4.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5e9c4.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5ea14.
Definition tfib_A_asan_report_load16 : Z := 0x5ea14.  Definition tfib_E_asan_report_load16 : Z := 0x5ea64.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5ea64.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5eab4.
Definition tfib_A_asan_report_store1 : Z := 0x5eab4.  Definition tfib_E_asan_report_store1 : Z := 0x5eb04.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5eb04.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5eb54.
Definition tfib_A_asan_report_store2 : Z := 0x5eb54.  Definition tfib_E_asan_report_store2 : Z := 0x5eba4.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5eba4.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5ebf4.
Definition tfib_A_asan_report_store4 : Z := 0x5ebf4.  Definition tfib_E_asan_report_store4 : Z := 0x5ec44.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5ec44.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5ec94.
Definition tfib_A_asan_report_store8 : Z := 0x5ec94.  Definition tfib_E_asan_report_store8 : Z := 0x5ece4.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5ece4.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5ed34.
Definition tfib_A_asan_report_store16 : Z := 0x5ed34.  Definition tfib_E_asan_report_store16 : Z := 0x5ed84.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5ed84.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5edd4.
Definition tfib_A_asan_report_load_n : Z := 0x5edd4.  Definition tfib_E_asan_report_load_n : Z := 0x5ee24.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5ee24.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5ee74.
Definition tfib_A_asan_report_store_n : Z := 0x5ee74.  Definition tfib_E_asan_report_store_n : Z := 0x5eec4.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5eec4.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5ef14.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5ef14.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5ef94.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5ef94.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5f348.
Definition tfib_A_AsanInitInternal : Z := 0x5f3d8.  Definition tfib_E_AsanInitInternal : Z := 0x5f68c.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5f68c.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5f72c.
Definition tfib_A_thunk_59674 : Z := 0x5f8f4.  Definition tfib_E_thunk_59674 : Z := 0x5f8f8.
Definition tfib_A_asan_init : Z := 0x5f8f8.  Definition tfib_E_asan_init : Z := 0x5f98c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5f98c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5f990.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5f990.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5f9f4.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5fb68.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5fb70.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5fbf4.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5ff1c.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5ff1c.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x600fc.
Definition tfib_A_InitializeShadowMemory : Z := 0x600fc.  Definition tfib_E_InitializeShadowMemory : Z := 0x60404.
Definition tfib_A_SetMallocContextSize : Z := 0x60404.  Definition tfib_E_SetMallocContextSize : Z := 0x60414.
Definition tfib_A_GetMallocContextSize : Z := 0x60414.  Definition tfib_E_GetMallocContextSize : Z := 0x60424.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x60424.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x60574.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x60954.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x60bf4.
Definition tfib_A_GetCurrentThreadStats : Z := 0x61058.  Definition tfib_E_GetCurrentThreadStats : Z := 0x61090.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x61338.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x61344.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x61344.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x613d0.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x613d0.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x61438.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x61438.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x614b0.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x614b0.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x61518.
Definition tfib_A_IsAddrSuppressed : Z := 0x61518.  Definition tfib_E_IsAddrSuppressed : Z := 0x61664.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x618f0.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x618fc.
Definition tfib_A_AsanThread_Create : Z := 0x61a7c.  Definition tfib_E_AsanThread_Create : Z := 0x61c18.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x61c74.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x61e8c.
Definition tfib_A_GetCurrentThread : Z := 0x61e8c.  Definition tfib_E_GetCurrentThread : Z := 0x61eac.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x61eac.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x62050.
Definition tfib_A_AsanThread_stack_top : Z := 0x62050.  Definition tfib_E_AsanThread_stack_top : Z := 0x620a8.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x620a8.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x62100.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x62100.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x62330.
Definition tfib_A_AsanThread_Init : Z := 0x62330.  Definition tfib_E_AsanThread_Init : Z := 0x62724.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x62724.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x62830.
Definition tfib_A_CreateMainThread : Z := 0x62864.  Definition tfib_E_CreateMainThread : Z := 0x62974.
Definition tfib_A_SetCurrentThread : Z := 0x62974.  Definition tfib_E_SetCurrentThread : Z := 0x62a54.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x62c58.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x62d94.
Definition tfib_A_weak_default_hook_ret : Z := 0x63a68.  Definition tfib_E_weak_default_hook_ret : Z := 0x63a6c.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x63a74.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x63cb4.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x63f08.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x64060.
Definition tfib_A_internal_allocator_getter : Z := 0x6424c.  Definition tfib_E_internal_allocator_getter : Z := 0x64258.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x64258.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x643a4.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x643a4.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x643f0.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x643f0.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x643fc.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x6442c.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x64438.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x64438.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x64444.
Definition tfib_A_IsRssLimitExceeded : Z := 0x64444.  Definition tfib_E_IsRssLimitExceeded : Z := 0x64454.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x64460.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x6472c.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x6472c.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x64aec.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x65a48.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x65a54.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x65a54.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x65b2c.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x65b2c.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x65bc8.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x660ec.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x66130.
Definition tfib_A_DecreaseTotalMmap : Z := 0x66130.  Definition tfib_E_DecreaseTotalMmap : Z := 0x66154.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x663a8.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x664bc.
Definition tfib_A_RunMallocHooks : Z := 0x66660.  Definition tfib_E_RunMallocHooks : Z := 0x66718.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x66718.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x6671c.
Definition tfib_A_RunFreeHooks : Z := 0x6671c.  Definition tfib_E_RunFreeHooks : Z := 0x667c8.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x667c8.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x667d0.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x667d0.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x667d4.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x667fc.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x66848.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x66b0c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x66d4c.
Definition tfib_A_sanitizer_set_report_path : Z := 0x67348.  Definition tfib_E_sanitizer_set_report_path : Z := 0x67360.

Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x674a4.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x674ac.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x677f4.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x68a98.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x68a98.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x68abc.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x68f70.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x69280.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x69280.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x693c4.
Definition tfib_A_FlagParser_ParseString : Z := 0x693c4.  Definition tfib_E_FlagParser_ParseString : Z := 0x694b8.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x6964c.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x696ac.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x696ac.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x696ec.
Definition tfib_A_internal_atoll : Z := 0x696ec.  Definition tfib_E_internal_atoll : Z := 0x697d8.
Definition tfib_A_internal_simple_strtoll : Z := 0x697d8.  Definition tfib_E_internal_simple_strtoll : Z := 0x69934.
Definition tfib_A_internal_memchr : Z := 0x69934.  Definition tfib_E_internal_memchr : Z := 0x69954.
Definition tfib_A_internal_memcmp : Z := 0x69954.  Definition tfib_E_internal_memcmp : Z := 0x6998c.
Definition tfib_A_internal_memcpy : Z := 0x6998c.  Definition tfib_E_internal_memcpy : Z := 0x699b0.
Definition tfib_A_internal_memmove : Z := 0x699b0.  Definition tfib_E_internal_memmove : Z := 0x69a08.
Definition tfib_A_internal_memset : Z := 0x69a08.  Definition tfib_E_internal_memset : Z := 0x69a68.
Definition tfib_A_internal_strcspn : Z := 0x69a68.  Definition tfib_E_internal_strcspn : Z := 0x69abc.
Definition tfib_A_internal_strchr : Z := 0x69abc.  Definition tfib_E_internal_strchr : Z := 0x69af0.
Definition tfib_A_internal_strdup : Z := 0x69af0.  Definition tfib_E_internal_strdup : Z := 0x69b5c.
Definition tfib_A_internal_strlen : Z := 0x69b5c.  Definition tfib_E_internal_strlen : Z := 0x69b78.
Definition tfib_A_internal_strcmp : Z := 0x69b78.  Definition tfib_E_internal_strcmp : Z := 0x69bbc.
Definition tfib_A_internal_strncmp : Z := 0x69bbc.  Definition tfib_E_internal_strncmp : Z := 0x69c08.
Definition tfib_A_internal_strchrnul : Z := 0x69c08.  Definition tfib_E_internal_strchrnul : Z := 0x69c50.
Definition tfib_A_internal_strrchr : Z := 0x69c50.  Definition tfib_E_internal_strrchr : Z := 0x69c90.
Definition tfib_A_internal_strnlen : Z := 0x69dc0.  Definition tfib_E_internal_strnlen : Z := 0x69df0.
Definition tfib_A_internal_strncpy : Z := 0x69e34.  Definition tfib_E_internal_strncpy : Z := 0x69ea4.
Definition tfib_A_internal_strstr : Z := 0x69ea4.  Definition tfib_E_internal_strstr : Z := 0x69f38.
Definition tfib_A_mem_is_zero : Z := 0x69f38.  Definition tfib_E_mem_is_zero : Z := 0x69fec.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x69fec.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x69ffc.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x69ffc.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6a1dc.
Definition tfib_A_internal_iserror : Z := 0x6a1e8.  Definition tfib_E_internal_iserror : Z := 0x6a208.
Definition tfib_A_internal_mmap : Z := 0x6a208.  Definition tfib_E_internal_mmap : Z := 0x6a214.
Definition tfib_A_internal_munmap : Z := 0x6a214.  Definition tfib_E_internal_munmap : Z := 0x6a220.
Definition tfib_A_internal_mprotect : Z := 0x6a220.  Definition tfib_E_internal_mprotect : Z := 0x6a230.
Definition tfib_A_internal_madvise : Z := 0x6a230.  Definition tfib_E_internal_madvise : Z := 0x6a25c.
Definition tfib_A_internal_close : Z := 0x6a25c.  Definition tfib_E_internal_close : Z := 0x6a268.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x6a268.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x6a28c.
Definition tfib_A_internal_read : Z := 0x6a28c.  Definition tfib_E_internal_read : Z := 0x6a2c4.
Definition tfib_A_internal_write : Z := 0x6a2c4.  Definition tfib_E_internal_write : Z := 0x6a2fc.
Definition tfib_A_internal_ftruncate : Z := 0x6a2fc.  Definition tfib_E_internal_ftruncate : Z := 0x6a334.
Definition tfib_A_internal_dup : Z := 0x6a334.  Definition tfib_E_internal_dup : Z := 0x6a340.
Definition tfib_A_internal_dup2_dup3 : Z := 0x6a340.  Definition tfib_E_internal_dup2_dup3 : Z := 0x6a350.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x6a350.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x6a368.
Definition tfib_A_internal_sched_yield : Z := 0x6a368.  Definition tfib_E_internal_sched_yield : Z := 0x6a374.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x6a374.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x6a3c0.
Definition tfib_A_internal_execve : Z := 0x6a3c0.  Definition tfib_E_internal_execve : Z := 0x6a3cc.
Definition tfib_A_internal_exit_exit_group : Z := 0x6a3cc.  Definition tfib_E_internal_exit_exit_group : Z := 0x6a3e0.
Definition tfib_A_FileExists_newfstatat : Z := 0x6a3e0.  Definition tfib_E_FileExists_newfstatat : Z := 0x6a460.
Definition tfib_A_DirExists_newfstatat : Z := 0x6a460.  Definition tfib_E_DirExists_newfstatat : Z := 0x6a4c4.
Definition tfib_A_GetTid_gettid : Z := 0x6a4c4.  Definition tfib_E_GetTid_gettid : Z := 0x6a4d0.
Definition tfib_A_GetEnv : Z := 0x6a4d0.  Definition tfib_E_GetEnv : Z := 0x6a600.
Definition tfib_A_FutexWait : Z := 0x6a704.  Definition tfib_E_FutexWait : Z := 0x6a728.
Definition tfib_A_FutexWake : Z := 0x6a728.  Definition tfib_E_FutexWake : Z := 0x6a74c.
Definition tfib_A_internal_ptrace : Z := 0x6a74c.  Definition tfib_E_internal_ptrace : Z := 0x6a758.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6a758.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6a768.
Definition tfib_A_internal_getpid : Z := 0x6a768.  Definition tfib_E_internal_getpid : Z := 0x6a774.
Definition tfib_A_internal_getppid : Z := 0x6a774.  Definition tfib_E_internal_getppid : Z := 0x6a780.
Definition tfib_A_internal_prctl : Z := 0x6a780.  Definition tfib_E_internal_prctl : Z := 0x6a78c.
Definition tfib_A_internal_sigaltstack : Z := 0x6a78c.  Definition tfib_E_internal_sigaltstack : Z := 0x6a798.
Definition tfib_A_internal_fork_clone : Z := 0x6a798.  Definition tfib_E_internal_fork_clone : Z := 0x6a7b0.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6a7b0.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x6a8dc.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6aab4.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6aeb0.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6b01c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6b134.
Definition tfib_A_GetPageSizeCached : Z := 0x6b134.  Definition tfib_E_GetPageSizeCached : Z := 0x6b13c.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6b13c.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6b1e8.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x6b1e8.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x6b308.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x6b3d0.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x6b450.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x6b450.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x6b4ac.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6b4ac.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6b578.
Definition tfib_A_thunk_653ec : Z := 0x6b674.  Definition tfib_E_thunk_653ec : Z := 0x6b678.
Definition tfib_A_CheckASLR : Z := 0x6b678.  Definition tfib_E_CheckASLR : Z := 0x6b67c.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x6b8c8.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6b8cc.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x6b8cc.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x6b8d8.
Definition tfib_A_MmapOrDie : Z := 0x6b8d8.  Definition tfib_E_MmapOrDie : Z := 0x6b9e4.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6b9e4.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6ba58.
Definition tfib_A_UnmapOrDie : Z := 0x6ba58.  Definition tfib_E_UnmapOrDie : Z := 0x6bad4.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6bad4.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6bbe4.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6be10.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6bf14.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x6bf14.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x6bf20.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6bf20.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6c098.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6c098.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6c0a4.
Definition tfib_A_thunk_66008 : Z := 0x6c290.  Definition tfib_E_thunk_66008 : Z := 0x6c294.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6c5b4.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6c7c0.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x6cd78.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6cd84.
Definition tfib_A_Printf : Z := 0x6cd88.  Definition tfib_E_Printf : Z := 0x6cdd4.
Definition tfib_A_SharedPrintfCode : Z := 0x6cdd4.  Definition tfib_E_SharedPrintfCode : Z := 0x6ce30.
Definition tfib_A_Report : Z := 0x6ce30.  Definition tfib_E_Report : Z := 0x6ce7c.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6e974.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6e9d0.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6e9d0.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6ec0c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6ec0c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6ef30.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6f4d0.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6f5a0.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6f5a0.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6f8f0.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6f8f0.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6f900.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6fb3c.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6fb80.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6fb80.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6fbe0.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6fbe0.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x70058.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x70918.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x70c3c.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x70c44.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x70d48.
Definition tfib_A_AddDieCallback : Z := 0x714f8.  Definition tfib_E_AddDieCallback : Z := 0x71580.
Definition tfib_A_Die : Z := 0x71644.  Definition tfib_E_Die : Z := 0x71704.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x71704.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x71710.
Definition tfib_A_CheckFailed : Z := 0x71710.  Definition tfib_E_CheckFailed : Z := 0x717c8.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x71e20.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x71f18.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x71f18.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x72044.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x7226c.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x722e8.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x7231c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x72604.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x72604.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x72608.
Definition tfib_A_GetTls : Z := 0x72608.  Definition tfib_E_GetTls : Z := 0x729f8.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x729f8.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x72ac8.
Definition tfib_A_AndroidLogInit : Z := 0x72eac.  Definition tfib_E_AndroidLogInit : Z := 0x72eb0.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x72ee0.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x72f28.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x72f28.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x73174.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x73174.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x73178.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x73178.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x73284.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x73284.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x73388.
Definition tfib_A_thunk_6d37c : Z := 0x73604.  Definition tfib_E_thunk_6d37c : Z := 0x73608.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x736ac.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x736cc.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x736cc.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x7376c.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x737b8.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x737bc.
Definition tfib_A_SetAlternateSignalStack : Z := 0x737f8.  Definition tfib_E_SetAlternateSignalStack : Z := 0x738bc.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x738bc.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x73944.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x73944.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x739bc.
Definition tfib_A_MaybeInstallSigaction : Z := 0x739bc.  Definition tfib_E_MaybeInstallSigaction : Z := 0x73aa0.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x73b5c.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x73c90.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x73ec8.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x73ff8.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x73ff8.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x74058.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x74058.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x74124.
Definition tfib_A_MmapNoAccess : Z := 0x74138.  Definition tfib_E_MmapNoAccess : Z := 0x74158.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x74158.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x742a4.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x742a4.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x742b4.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x75aac.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x75af0.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x75af0.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x75b20.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x75f54.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x76078.
Definition tfib_A_StackStore_Alloc : Z := 0x76078.  Definition tfib_E_StackStore_Alloc : Z := 0x761ac.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x76a60.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x76b14.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x78268.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x782c4.
Definition tfib_A_StackDepotPut : Z := 0x78550.  Definition tfib_E_StackDepotPut : Z := 0x78570.
Definition tfib_A_StackDepotBase_Put : Z := 0x78570.  Definition tfib_E_StackDepotBase_Put : Z := 0x787f4.
Definition tfib_A_StackDepotBase_Get : Z := 0x787f4.  Definition tfib_E_StackDepotBase_Get : Z := 0x78904.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x78ce4.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x78d74.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x78d74.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x78e74.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x78ed4.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x78edc.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x78edc.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x7903c.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x7903c.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x790b0.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x79538.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x79650.
Definition tfib_A_thunk_762d8 : Z := 0x7c69c.  Definition tfib_E_thunk_762d8 : Z := 0x7c6a0.
Definition tfib_A_thunk_77ab0 : Z := 0x7de74.  Definition tfib_E_thunk_77ab0 : Z := 0x7de78.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7f8a0.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7f95c.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7f95c.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7fa34.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7fa34.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7fca8.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7ffd4.  Definition tfib_E_lsan_flags_init_helper : Z := 0x80018.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x80018.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x803e8.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x806b8.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x80770.
Definition tfib_A_thunk_7b6f8 : Z := 0x81ac8.  Definition tfib_E_thunk_7b6f8 : Z := 0x81acc.
Definition tfib_A_lsan_register_root_region : Z := 0x826d4.  Definition tfib_E_lsan_register_root_region : Z := 0x82a04.
Definition tfib_A_lsan_unregister_root_region : Z := 0x82a04.  Definition tfib_E_lsan_unregister_root_region : Z := 0x82e8c.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x82e8c.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x82e98.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x85a50.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x85a68.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x85dec.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x85e68.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x85e68.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x85f18.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x85f18.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x85f30.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x85f30.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x86078.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x86078.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x86084.
Definition tfib_A_asan_default_options_cli_c : Z := 0x86084.  Definition tfib_E_asan_default_options_cli_c : Z := 0x86090.
Definition tfib_A_main : Z := 0x86090.  Definition tfib_E_main : Z := 0x86354.
Definition tfib_A_target_alloc_init : Z := 0x86354.  Definition tfib_E_target_alloc_init : Z := 0x86358.
Definition tfib_A_target_alloc_count : Z := 0x86358.  Definition tfib_E_target_alloc_count : Z := 0x86360.
Definition tfib_A_target_run : Z := 0x86360.  Definition tfib_E_target_run : Z := 0x864e8.
Definition tfib_A_emit_printf : Z := 0x864e8.  Definition tfib_E_emit_printf : Z := 0x86530.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x86530.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x86bf8.
Definition tfib_A_asan_module_ctor : Z := 0x895f0.  Definition tfib_E_asan_module_ctor : Z := 0x89628.




Definition tfib_A_asan_module_dtor : Z := 0x89628.  Definition tfib_E_asan_module_dtor : Z := 0x89658.



Definition tfib_A_extenddftf2 : Z := 0x8e444.  Definition tfib_E_extenddftf2 : Z := 0x8e5d4.
Definition tfib_A_sysconf : Z := 0x94224.  Definition tfib_E_sysconf : Z := 0x9444c.
Definition tfib_A_init : Z := 0x9444c.  Definition tfib_E_init : Z := 0x94450.
Definition tfib_A_init_libc : Z := 0x94450.  Definition tfib_E_init_libc : Z := 0x9467c.
Definition tfib_A_libc_start_init : Z := 0x9467c.  Definition tfib_E_libc_start_init : Z := 0x946c8.
Definition tfib_A_libc_start_main : Z := 0x946c8.  Definition tfib_E_libc_start_main : Z := 0x94728.
Definition tfib_A_libc_start_main_stage2 : Z := 0x94728.  Definition tfib_E_libc_start_main_stage2 : Z := 0x94770.
Definition tfib_A_init_tls : Z := 0x94848.  Definition tfib_E_init_tls : Z := 0x94af8.
Definition tfib_A_init_ssp : Z := 0x94af8.  Definition tfib_E_init_ssp : Z := 0x94b58.
Definition tfib_A_stack_chk_fail : Z := 0x94b58.  Definition tfib_E_stack_chk_fail : Z := 0x94b60.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x94ba8.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x94c3c.
Definition tfib_A_Exit : Z := 0x94c3c.  Definition tfib_E_Exit : Z := 0x94c58.
Definition tfib_A_funcs_on_exit : Z := 0x94c88.  Definition tfib_E_funcs_on_exit : Z := 0x94d50.
Definition tfib_A_fini_stub_ret : Z := 0x94d50.  Definition tfib_E_fini_stub_ret : Z := 0x94d54.
Definition tfib_A_cxa_atexit_atexit : Z := 0x94d54.  Definition tfib_E_cxa_atexit_atexit : Z := 0x94e18.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x94e18.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x94e1c.
Definition tfib_A_musl_exit_helper_stub : Z := 0x94e1c.  Definition tfib_E_musl_exit_helper_stub : Z := 0x94e20.
Definition tfib_A_libc_exit_fini : Z := 0x94e20.  Definition tfib_E_libc_exit_fini : Z := 0x94e6c.
Definition tfib_A_exit : Z := 0x94e6c.  Definition tfib_E_exit : Z := 0x94ee0.
Definition tfib_A_open : Z := 0x950e0.  Definition tfib_E_open : Z := 0x951c4.
Definition tfib_A_syscall_ret : Z := 0x951c4.  Definition tfib_E_syscall_ret : Z := 0x951fc.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x951fc.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x953a4.
Definition tfib_A_calloc : Z := 0x95968.  Definition tfib_E_calloc : Z := 0x95aa0.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x95aa0.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x95aa4.
Definition tfib_A_libc_free : Z := 0x95aa4.  Definition tfib_E_libc_free : Z := 0x95c70.
Definition tfib_A_get_meta : Z := 0x95c70.  Definition tfib_E_get_meta : Z := 0x95d80.
Definition tfib_A_alloc_meta : Z := 0x96158.  Definition tfib_E_alloc_meta : Z := 0x96430.
Definition tfib_A_libc_malloc_impl : Z := 0x96430.  Definition tfib_E_libc_malloc_impl : Z := 0x967a0.
Definition tfib_A_alloc_slot : Z := 0x967a0.  Definition tfib_E_alloc_slot : Z := 0x97044.
Definition tfib_A_enframe : Z := 0x97044.  Definition tfib_E_enframe : Z := 0x97194.
Definition tfib_A_malloc_allzerop : Z := 0x97194.  Definition tfib_E_malloc_allzerop : Z := 0x9730c.
Definition tfib_A_getrlimit : Z := 0x98fbc.  Definition tfib_E_getrlimit : Z := 0x990b4.
Definition tfib_A_getrusage : Z := 0x990b4.  Definition tfib_E_getrusage : Z := 0x990dc.
Definition tfib_A_setrlimit : Z := 0x990dc.  Definition tfib_E_setrlimit : Z := 0x991a4.
Definition tfib_A_mmap : Z := 0x995cc.  Definition tfib_E_mmap : Z := 0x996b8.
Definition tfib_A_mprotect : Z := 0x996b8.  Definition tfib_E_mprotect : Z := 0x99700.
Definition tfib_A_munmap : Z := 0x997d4.  Definition tfib_E_munmap : Z := 0x9981c.
Definition tfib_A_sched_yield : Z := 0x99ae0.  Definition tfib_E_sched_yield : Z := 0x99b04.
Definition tfib_A_raise_tkill_path : Z := 0x99b60.  Definition tfib_E_raise_tkill_path : Z := 0x99bd8.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x99bd8.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x99dac.
Definition tfib_A_musl_sigaltstack : Z := 0x99ea4.  Definition tfib_E_musl_sigaltstack : Z := 0x99f30.
Definition tfib_A_fprintf : Z := 0x9a50c.  Definition tfib_E_fprintf : Z := 0x9a570.
Definition tfib_A_lockfile : Z := 0x9a570.  Definition tfib_E_lockfile : Z := 0x9a66c.
Definition tfib_A_unlockfile : Z := 0x9a66c.  Definition tfib_E_unlockfile : Z := 0x9a6cc.

Definition tfib_A_stdio_read : Z := 0x9a25c.  Definition tfib_E_stdio_read : Z := 0x9a374.
Definition tfib_A_stdio_write : Z := 0x9a37c.  Definition tfib_E_stdio_write : Z := 0x9a50c.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9a22c.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9a230.
Definition tfib_A_stdio_close : Z := 0x9a230.  Definition tfib_E_stdio_close : Z := 0x9a25c.
Definition tfib_A_fwritex : Z := 0x9ab00.  Definition tfib_E_fwritex : Z := 0x9ac38.
Definition tfib_A_musl_fwrite : Z := 0x9ac38.  Definition tfib_E_musl_fwrite : Z := 0x9acf0.
Definition tfib_A_towrite : Z := 0x9acf0.  Definition tfib_E_towrite : Z := 0x9ad44.
Definition tfib_A_stdio_exit : Z := 0x9a95c.  Definition tfib_E_stdio_exit : Z := 0x9ab00.
Definition tfib_A_ofl_lock : Z := 0x9ad44.  Definition tfib_E_ofl_lock : Z := 0x9ad74.
Definition tfib_A_musl_vfprintf : Z := 0x9aec0.  Definition tfib_E_musl_vfprintf : Z := 0x9b070.
Definition tfib_A_printf_core : Z := 0x9b070.  Definition tfib_E_printf_core : Z := 0x9bea0.
Definition tfib_A_pop_arg : Z := 0x9bea0.  Definition tfib_E_pop_arg : Z := 0x9bfd4.
Definition tfib_A_pad : Z := 0x9bfd4.  Definition tfib_E_pad : Z := 0x9c0a8.
Definition tfib_A_fmt_fp : Z := 0x9c0a8.  Definition tfib_E_fmt_fp : Z := 0x9d770.
Definition tfib_A_thunk_931e0 : Z := 0x955bc.  Definition tfib_E_thunk_931e0 : Z := 0x955c0.
Definition tfib_A_musl_wctomb : Z := 0x99948.  Definition tfib_E_musl_wctomb : Z := 0x9996c.
Definition tfib_A_musl_wcrtomb : Z := 0x9981c.  Definition tfib_E_musl_wcrtomb : Z := 0x99948.
Definition tfib_A_fpclassifyl : Z := 0x97bac.  Definition tfib_E_fpclassifyl : Z := 0x97bf0.
Definition tfib_A_letf2 : Z := 0x973e4.  Definition tfib_E_letf2 : Z := 0x974ac.
Definition tfib_A_multf3 : Z := 0x974ac.  Definition tfib_E_multf3 : Z := 0x97bac.
Definition tfib_A_floatsitf : Z := 0x98408.  Definition tfib_E_floatsitf : Z := 0x98510.
Definition tfib_A_scalbn : Z := 0x98e14.  Definition tfib_E_scalbn : Z := 0x98eac.
Definition tfib_A_subtf3 : Z := 0x983f8.  Definition tfib_E_subtf3 : Z := 0x98408.
Definition tfib_A_addtf3 : Z := 0x97bf0.  Definition tfib_E_addtf3 : Z := 0x983bc.
Definition tfib_A_fe_getround : Z := 0x983bc.  Definition tfib_E_fe_getround : Z := 0x983ec.
Definition tfib_A_fixunstfsi : Z := 0x9d778.  Definition tfib_E_fixunstfsi : Z := 0x9d80c.
Definition tfib_A_floatunsitf : Z := 0x9d80c.  Definition tfib_E_floatunsitf : Z := 0x9d8f8.
Definition tfib_A_fixtfsi : Z := 0x98eac.  Definition tfib_E_fixtfsi : Z := 0x98f54.
Definition tfib_A_divtf3 : Z := 0x98510.  Definition tfib_E_divtf3 : Z := 0x98e14.
Definition tfib_A_musl_vprintf : Z := 0x9dfd0.  Definition tfib_E_musl_vprintf : Z := 0x9dfec.
Definition tfib_A_stdout_write : Z := 0x9ad80.  Definition tfib_E_stdout_write : Z := 0x9ae20.
Definition tfib_A_thunk_95368 : Z := 0x9e598.  Definition tfib_E_thunk_95368 : Z := 0x9e59c.
Definition tfib_A_musl_memcmp : Z := 0x9e668.  Definition tfib_E_musl_memcmp : Z := 0x9e698.
Definition tfib_A_musl_memcpy : Z := 0x9e698.  Definition tfib_E_musl_memcpy : Z := 0x9ea9c.
Definition tfib_A_musl_memset : Z := 0x9ea9c.  Definition tfib_E_musl_memset : Z := 0x9eb94.
Definition tfib_A_musl_strchr : Z := 0x9ebd4.  Definition tfib_E_musl_strchr : Z := 0x9ec10.
Definition tfib_A_strchrnul : Z := 0x9ec10.  Definition tfib_E_strchrnul : Z := 0x9ecf0.
Definition tfib_A_musl_strlen : Z := 0x9ef28.  Definition tfib_E_musl_strlen : Z := 0x9efb8.
Definition tfib_A_musl_strnlen : Z := 0x9f224.  Definition tfib_E_musl_strnlen : Z := 0x9f268.
Definition tfib_A_musl_memchr : Z := 0x9e59c.  Definition tfib_E_musl_memchr : Z := 0x9e668.
Definition tfib_A_lock : Z := 0x9f3f0.  Definition tfib_E_lock : Z := 0x9f678.
Definition tfib_A_unlock : Z := 0x9f678.  Definition tfib_E_unlock : Z := 0x9f6ec.
Definition tfib_A_syscall_cp_c : Z := 0x9f6ec.  Definition tfib_E_syscall_cp_c : Z := 0x9f710.
Definition tfib_A_syscall_cp_sccp : Z := 0x9f710.  Definition tfib_E_syscall_cp_sccp : Z := 0x9f714.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9f714.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9f738.
Definition tfib_A_pthread_atfork : Z := 0x9f750.  Definition tfib_E_pthread_atfork : Z := 0x9f7f4.
Definition tfib_A_mremap : Z := 0x99700.  Definition tfib_E_mremap : Z := 0x997d4.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0xa07c8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0xa07e4.
Definition tfib_A_pthread_key_create : Z := 0xa0b70.  Definition tfib_E_pthread_key_create : Z := 0xa0c44.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0xa0ee8.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0xa0f8c.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0xa0f8c.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0xa10a8.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0xa10a8.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0xa10d4.
Definition tfib_A_pthread_setspecific : Z := 0xa110c.  Definition tfib_E_pthread_setspecific : Z := 0xa1140.
Definition tfib_A_set_thread_area : Z := 0xa1148.  Definition tfib_E_set_thread_area : Z := 0xa1154.
Definition tfib_A_thunk_96f9c : Z := 0xa1140.  Definition tfib_E_thunk_96f9c : Z := 0xa1148.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa1a74.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa1b2c.
Definition tfib_A_close : Z := 0xa4144.  Definition tfib_E_close : Z := 0xa4198.
Definition tfib_A_musl_read : Z := 0xa4224.  Definition tfib_E_musl_read : Z := 0xa4258.
Definition tfib_A_vm_wait : Z := 0xa1784.  Definition tfib_E_vm_wait : Z := 0xa17d4.
Definition tfib_D_str_sealed : Z := 0x11860.
Definition tfib_D_init_array_0_3 : Z := 0xa5258.
Definition tfib_D_fini_array_0_1 : Z := 0xa5278.
Definition tfib_D_GOT_common_flags : Z := 0xa5f40.
Definition tfib_D_GOT_flags : Z := 0xa5f48.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa5f50.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa5f58.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa5f60.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa5f68.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa6ab8.
Definition tfib_D_environ_musl : Z := 0xa6c00.
Definition tfib_D_REAL_read : Z := 0xa7cc8.
Definition tfib_D_REAL_memcpy : Z := 0xa7e08.
Definition tfib_D_REAL_memset : Z := 0xa7e10.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xad5d8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xae438.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xb0c38.
Definition tfib_D_asan_inited : Z := 0xb1918.
Definition tfib_D_replace_intrin_cached : Z := 0xb1919.
Definition tfib_D_kHighMemEnd : Z := 0xb1920.
Definition tfib_D_kMidMemBeg : Z := 0xb1928.
Definition tfib_D_kMidMemEnd : Z := 0xb1930.
Definition tfib_D_malloc_context_size : Z := 0xb193c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x142768.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x6043a8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x606000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x3338c.
Definition tfib_at_rw_lo : Z := 0xa7000.
Definition tfib_at_rw_len : Z := 0x55f000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x69a08.
Definition tfib_at_x_imemcpy : Z := 0x6998c.
Definition tfib_at_x_memset : Z := 0x9ea9c.
Definition tfib_at_x_memcpy : Z := 0x9e698.
Definition tfib_at_x_memiszero : Z := 0x69f38.
Definition tfib_at_x_istrncpy : Z := 0x69e34.
Definition tfib_at_x_sealed : Z := 0x11860.
Definition tfib_at_x_popfree : Z := 0x39778.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x94488.
Definition tfib_at_x_envscan_k : Z := 0x94494.
Definition tfib_at_x_pnscan : Z := 0x9454c.
Definition tfib_at_x_pnscan_k : Z := 0x94558.
Definition tfib_at_stops_more : list Z := (0x373ec :: 0x38a10 :: 0x59d14 :: 0x600cc :: 0x600e0 :: 0x600f4 :: 0x65a84 :: 0x65b54 :: 0x73080 :: 0x73f8c :: 0x7411c :: 0x7de74 :: nil)%list.
