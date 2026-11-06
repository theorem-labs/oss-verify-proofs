(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its rows regenerated for plugin-hostd/fuzz_command's ASan build by the AB1w row regenerator: each start is the fuzz_command function paired by code with cgif's, each end the pair of cgif's last instruction plus its length; a row whose label is a FUNC symbol of fuzz_command's image takes that symbol's range (LLVMFuzzerTestOneInput); the side-stack class rows are fuzz_command's own __asan_stack_malloc_0, _1, _3, _4, _5 and _7 (symbol address and size; class 1 keeps cgif's row name asan_stack_malloc_A, the others are named by class); six rows are set from the image by hand (HaveStackTraceBasedSuppressions, set_thread_area, two jump stubs by their target, the self-loop stub, and the ends of __stdio_exit and musl memset, whose code differs); section bounds come from fuzz_command's section headers; the rows of cgif functions fuzz_command does not have (cgif's program and GIF library, fopen/fclose/fdopen/ofl_add/fmodeflags and their interceptors, stack_malloc_2) are dropped; thirteen rows whose cgif label names another function than the code of their range take the name of the image symbol at their start (internal_strchr / _strcmp / _strncmp, AsanCheckIncompatibleRT / AsanCheckDynamicRTPrereqs, IsAddrSuppressed, IsRssLimitExceeded, DecreaseTotalMmap, GetTls, MmapFixedSuperNoReserve, MmapNoAccess, ReservedAddressRange_MapOrDie, and MmapFixedOrDie for cgif's shim row). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1w.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AB1w.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x23a6c.
Definition tfib_text_lo : Z := 0x31f60.  Definition tfib_text_hi : Z := 0xa0c14.
Definition tfib_init_array_lo : Z := 0xa1c18.  Definition tfib_init_array_hi : Z := 0xa1c38.
Definition tfib_fini_array_lo : Z := 0xa1c38.  Definition tfib_fini_array_hi : Z := 0xa1c48.
Definition tfib_preinit_array_lo : Z := 0xa1c48.  Definition tfib_preinit_array_hi : Z := 0xa1c50.
Definition tfib_data_rel_ro_lo : Z := 0xa1c60.  Definition tfib_data_rel_ro_hi : Z := 0xa31b0.
Definition tfib_got_lo : Z := 0xa31b0.  Definition tfib_got_hi : Z := 0xa3f08.
Definition tfib_data_lo : Z := 0xa4f08.  Definition tfib_data_hi : Z := 0xa7af0.
Definition tfib_asan_globals_lo : Z := 0xa7af0.  Definition tfib_asan_globals_hi : Z := 0xa90f0.
Definition tfib_bss_lo : Z := 0xa9100.  Definition tfib_bss_hi : Z := 0x6010d8.
Definition tfib_tbss_lo : Z := 0xa0c18.  Definition tfib_tbss_hi : Z := 0xa0c2c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x602000.
Definition tfib_entry : Z := 0x31f60.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x31f60.  Definition tfib_E_start : Z := 0x31fa8.
Definition tfib_A_do_init : Z := 0x31fa8.  Definition tfib_E_do_init : Z := 0x3201c.
Definition tfib_A_do_fini : Z := 0x3201c.  Definition tfib_E_do_fini : Z := 0x320ac.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x320ac.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x320e8.
Definition tfib_A_InitializeAllocator : Z := 0x32258.  Definition tfib_E_InitializeAllocator : Z := 0x32270.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x32270.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x323dc.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x32938.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x32a94.
Definition tfib_A_asan_free : Z := 0x32e68.  Definition tfib_E_asan_free : Z := 0x32e90.
Definition tfib_A_Allocator_Deallocate : Z := 0x32e90.  Definition tfib_E_Allocator_Deallocate : Z := 0x33148.
Definition tfib_A_asan_malloc : Z := 0x33148.  Definition tfib_E_asan_malloc : Z := 0x331a4.
Definition tfib_A_Allocator_Allocate : Z := 0x331a4.  Definition tfib_E_Allocator_Allocate : Z := 0x33b2c.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34344.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x34488.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x34574.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x345d0.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x345d0.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x34820.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x34820.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x34914.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x34914.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x349fc.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x34e30.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x35014.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x35014.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x35198.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x352d0.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x35554.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x35554.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x356d4.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x356d4.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3589c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x3589c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x35a68.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x35a68.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x35b08.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x35b08.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x35c0c.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35f34.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x3607c.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x3607c.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x360b4.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x3684c.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x36b34.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x3720c.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x37384.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x37384.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x37534.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x37534.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x37718.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x37718.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x379f0.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x379f0.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x37e68.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x37e68.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x37f68.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x37f68.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x38270.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x38270.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x385e0.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x385e0.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x386f8.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x38a00.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x38afc.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x38afc.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x38be4.
Definition tfib_A_AsanActivate : Z := 0x38be4.  Definition tfib_E_AsanActivate : Z := 0x38cc0.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x3919c.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x39284.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3dd3c.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3de14.
Definition tfib_A_FakeStack_Create : Z := 0x3de14.  Definition tfib_E_FakeStack_Create : Z := 0x3df00.
Definition tfib_A_FakeStack_Allocate : Z := 0x3e1bc.  Definition tfib_E_FakeStack_Allocate : Z := 0x3e4a4.
Definition tfib_A_SetTLSFakeStack : Z := 0x3e5d8.  Definition tfib_E_SetTLSFakeStack : Z := 0x3e608.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3e77c.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3e90c.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3e608.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3e77c.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3e90c.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3eab8.

Definition tfib_A_asan_stack_malloc_5 : Z := 0x3eab8.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x3ecc4.

Definition tfib_A_FakeStack_SetShadow : Z := 0x3ed78.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3eeb4.
Definition tfib_A_asan_InitializeFlags : Z := 0x3eeb4.  Definition tfib_E_asan_InitializeFlags : Z := 0x3fee0.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x405ec.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x41408.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x41408.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x419d4.
Definition tfib_A_asan_register_globals : Z := 0x419d4.  Definition tfib_E_asan_register_globals : Z := 0x41a40.
Definition tfib_A_asan_unregister_globals : Z := 0x41a40.  Definition tfib_E_asan_unregister_globals : Z := 0x41aa8.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x42128.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x42398.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x42398.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x426a0.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x42e14.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x42f64.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x43980.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x43a98.
Definition tfib_A_strlen : Z := 0x43a98.  Definition tfib_E_strlen : Z := 0x43a9c.
Definition tfib_A_strnlen : Z := 0x43a9c.  Definition tfib_E_strnlen : Z := 0x43aa0.
Definition tfib_A_strcmp : Z := 0x43aa0.  Definition tfib_E_strcmp : Z := 0x43aa4.
Definition tfib_A_strchr : Z := 0x43ab4.  Definition tfib_E_strchr : Z := 0x43ab8.
Definition tfib_A_memcmp : Z := 0x43ac0.  Definition tfib_E_memcmp : Z := 0x43ac4.
Definition tfib_A_memcmp_2 : Z := 0x43ac4.  Definition tfib_E_memcmp_2 : Z := 0x43ac8.
Definition tfib_A_memchr : Z := 0x43ac8.  Definition tfib_E_memchr : Z := 0x43acc.
Definition tfib_A_frexpl : Z := 0x43acc.  Definition tfib_E_frexpl : Z := 0x43ad0.
Definition tfib_A_read : Z := 0x43ad0.  Definition tfib_E_read : Z := 0x43ad4.
Definition tfib_A_fwrite : Z := 0x43ad4.  Definition tfib_E_fwrite : Z := 0x43ad8.
Definition tfib_A_time : Z := 0x43ad8.  Definition tfib_E_time : Z := 0x43adc.
Definition tfib_A_gmtime_r : Z := 0x43adc.  Definition tfib_E_gmtime_r : Z := 0x43ae0.
Definition tfib_A_vprintf : Z := 0x43ae0.  Definition tfib_E_vprintf : Z := 0x43ae4.
Definition tfib_A_vfprintf : Z := 0x43ae4.  Definition tfib_E_vfprintf : Z := 0x43ae8.
Definition tfib_A_vsnprintf : Z := 0x43ae8.  Definition tfib_E_vsnprintf : Z := 0x43aec.
Definition tfib_A_vfprintf_2 : Z := 0x43aec.  Definition tfib_E_vfprintf_2 : Z := 0x43af0.
Definition tfib_A_thunk_417bc : Z := 0x43af0.  Definition tfib_E_thunk_417bc : Z := 0x43af4.
Definition tfib_A_clock_gettime : Z := 0x43af4.  Definition tfib_E_clock_gettime : Z := 0x43af8.
Definition tfib_A_wcrtomb : Z := 0x43af8.  Definition tfib_E_wcrtomb : Z := 0x43afc.
Definition tfib_A_wctomb : Z := 0x43afc.  Definition tfib_E_wctomb : Z := 0x43b00.
Definition tfib_A_thunk_417cc : Z := 0x43b00.  Definition tfib_E_thunk_417cc : Z := 0x43b08.
Definition tfib_A_pthread_attr_getstack : Z := 0x43b08.  Definition tfib_E_pthread_attr_getstack : Z := 0x43b0c.
Definition tfib_A_tls_get_addr_thunk : Z := 0x43b0c.  Definition tfib_E_tls_get_addr_thunk : Z := 0x43b10.
Definition tfib_A_thunk_417dc : Z := 0x43b10.  Definition tfib_E_thunk_417dc : Z := 0x43b14.
Definition tfib_A_thunk_417e4 : Z := 0x43b14.  Definition tfib_E_thunk_417e4 : Z := 0x43b18.
Definition tfib_A_thunk_417e8 : Z := 0x43b18.  Definition tfib_E_thunk_417e8 : Z := 0x43b1c.
Definition tfib_A_thunk_417ec : Z := 0x43b1c.  Definition tfib_E_thunk_417ec : Z := 0x43b20.
Definition tfib_A_thunk_417f0 : Z := 0x43b20.  Definition tfib_E_thunk_417f0 : Z := 0x43b24.
Definition tfib_A_sem_timedwait : Z := 0x43b24.  Definition tfib_E_sem_timedwait : Z := 0x43b28.
Definition tfib_A_thunk_417f8 : Z := 0x43b28.  Definition tfib_E_thunk_417f8 : Z := 0x43b2c.
Definition tfib_A_pthread_setcancelstate : Z := 0x43b2c.  Definition tfib_E_pthread_setcancelstate : Z := 0x43b30.
Definition tfib_A_send : Z := 0x43b30.  Definition tfib_E_send : Z := 0x43b34.
Definition tfib_A_sendto : Z := 0x43b34.  Definition tfib_E_sendto : Z := 0x43b38.
Definition tfib_A_sigaltstack : Z := 0x43b38.  Definition tfib_E_sigaltstack : Z := 0x43b3c.
Definition tfib_A_thunk_4180c : Z := 0x43b3c.  Definition tfib_E_thunk_4180c : Z := 0x43b40.
Definition tfib_A_icpt_strlen : Z := 0x43b48.  Definition tfib_E_icpt_strlen : Z := 0x43ddc.
Definition tfib_A_icpt_strnlen : Z := 0x43ddc.  Definition tfib_E_icpt_strnlen : Z := 0x44070.
Definition tfib_A_icpt_strcmp : Z := 0x44074.  Definition tfib_E_icpt_strcmp : Z := 0x445a4.
Definition tfib_A_icpt_strchr : Z := 0x45b70.  Definition tfib_E_icpt_strchr : Z := 0x45e50.
Definition tfib_A_icpt_memcmp : Z := 0x46e50.  Definition tfib_E_icpt_memcmp : Z := 0x46f0c.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x46f0c.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x46fc8.
Definition tfib_A_icpt_memchr : Z := 0x46fc8.  Definition tfib_E_icpt_memchr : Z := 0x47298.
Definition tfib_A_icpt_frexpl : Z := 0x47298.  Definition tfib_E_icpt_frexpl : Z := 0x47510.
Definition tfib_A_icpt_read : Z := 0x47510.  Definition tfib_E_icpt_read : Z := 0x47780.
Definition tfib_A_icpt_fwrite : Z := 0x47780.  Definition tfib_E_icpt_fwrite : Z := 0x479f4.
Definition tfib_A_icpt_time : Z := 0x479f4.  Definition tfib_E_icpt_time : Z := 0x47c90.
Definition tfib_A_icpt_gmtime_r : Z := 0x47e98.  Definition tfib_E_icpt_gmtime_r : Z := 0x480d8.
Definition tfib_A_icpt_vprintf : Z := 0x480d8.  Definition tfib_E_icpt_vprintf : Z := 0x48174.
Definition tfib_A_printf_common_format_interceptor : Z := 0x48174.  Definition tfib_E_printf_common_format_interceptor : Z := 0x48c3c.
Definition tfib_A_icpt_vfprintf : Z := 0x48c3c.  Definition tfib_E_icpt_vfprintf : Z := 0x48cf0.
Definition tfib_A_icpt_vsnprintf : Z := 0x48cf0.  Definition tfib_E_icpt_vsnprintf : Z := 0x49008.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x49008.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x490e0.
Definition tfib_A_icpt_clock_gettime : Z := 0x49184.  Definition tfib_E_icpt_clock_gettime : Z := 0x493dc.
Definition tfib_A_icpt_wcrtomb : Z := 0x493dc.  Definition tfib_E_icpt_wcrtomb : Z := 0x4994c.
Definition tfib_A_icpt_wctomb : Z := 0x4994c.  Definition tfib_E_icpt_wctomb : Z := 0x49ca8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x49d74.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4a15c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4a168.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4a1e4.

Definition tfib_A_icpt_sem_timedwait : Z := 0x4a3f0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4a688.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4a6b8.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4a8e0.
Definition tfib_A_icpt_send : Z := 0x4a8e0.  Definition tfib_E_icpt_send : Z := 0x4ab94.
Definition tfib_A_icpt_sendto : Z := 0x4ab94.  Definition tfib_E_icpt_sendto : Z := 0x4ae58.
Definition tfib_A_icpt_sigaltstack : Z := 0x4ae58.  Definition tfib_E_icpt_sigaltstack : Z := 0x4b0b4.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4b77c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4b92c.
Definition tfib_A_icpt_diouxXn : Z := 0x4b92c.  Definition tfib_E_icpt_diouxXn : Z := 0x4bac4.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x4c670.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x55348.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x55348.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x554a4.
Definition tfib_A_memset : Z := 0x55964.  Definition tfib_E_memset : Z := 0x55968.
Definition tfib_A_memcpy : Z := 0x55968.  Definition tfib_E_memcpy : Z := 0x5596c.
Definition tfib_A_asan_memcpy : Z := 0x5596c.  Definition tfib_E_asan_memcpy : Z := 0x55e08.
Definition tfib_A_asan_memset : Z := 0x55e08.  Definition tfib_E_asan_memset : Z := 0x56048.
Definition tfib_A_icpt_memset : Z := 0x56048.  Definition tfib_E_icpt_memset : Z := 0x56338.
Definition tfib_A_icpt_memcpy : Z := 0x56338.  Definition tfib_E_icpt_memcpy : Z := 0x56928.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x56928.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x56960.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x56960.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x56964.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x56964.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x56968.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x56968.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x569c8.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x56a14.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x56b50.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x56b50.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x56b54.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x56b54.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x56cbc.
Definition tfib_A_free : Z := 0x56cbc.  Definition tfib_E_free : Z := 0x56cc0.
Definition tfib_A_malloc : Z := 0x56cc0.  Definition tfib_E_malloc : Z := 0x56cc4.
Definition tfib_A_icpt_free : Z := 0x56cc8.  Definition tfib_E_icpt_free : Z := 0x56e98.
Definition tfib_A_icpt_malloc : Z := 0x56e98.  Definition tfib_E_icpt_malloc : Z := 0x56ff4.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x56ff4.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x570c0.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x572f8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x572fc.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x572fc.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x573fc.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x57724.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x57890.
Definition tfib_A_SetCanPoisonMemory : Z := 0x57d78.  Definition tfib_E_SetCanPoisonMemory : Z := 0x57d88.
Definition tfib_A_CanPoisonMemory : Z := 0x57d88.  Definition tfib_E_CanPoisonMemory : Z := 0x57d9c.
Definition tfib_A_PoisonShadow : Z := 0x57d9c.  Definition tfib_E_PoisonShadow : Z := 0x58298.
Definition tfib_A_MemToShadow_checked : Z := 0x58298.  Definition tfib_E_MemToShadow_checked : Z := 0x583d4.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x583d4.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x58574.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x58574.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x586f4.
Definition tfib_A_asan_region_is_poisoned : Z := 0x58724.  Definition tfib_E_asan_region_is_poisoned : Z := 0x58a68.
Definition tfib_A_AsanTSDInit : Z := 0x58e88.  Definition tfib_E_AsanTSDInit : Z := 0x58f04.
Definition tfib_A_AsanTSDGet : Z := 0x58f04.  Definition tfib_E_AsanTSDGet : Z := 0x58f44.
Definition tfib_A_AsanTSDSet : Z := 0x58f44.  Definition tfib_E_AsanTSDSet : Z := 0x58f84.
Definition tfib_A_PlatformTSDDtor : Z := 0x58f84.  Definition tfib_E_PlatformTSDDtor : Z := 0x59008.
Definition tfib_A_InstallAtForkHandler : Z := 0x59008.  Definition tfib_E_InstallAtForkHandler : Z := 0x59024.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x59084.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x590c8.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x597e0.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x599ec.
Definition tfib_A_ReportDoubleFree : Z := 0x5a0f4.  Definition tfib_E_ReportDoubleFree : Z := 0x5a384.
Definition tfib_A_ReportGenericError : Z := 0x5beb0.  Definition tfib_E_ReportGenericError : Z := 0x5c76c.
Definition tfib_A_AsanInited : Z := 0x5cef8.  Definition tfib_E_AsanInited : Z := 0x5cf10.
Definition tfib_A_asan_report_load1 : Z := 0x5cf10.  Definition tfib_E_asan_report_load1 : Z := 0x5cf60.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5cf60.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5cfb0.
Definition tfib_A_asan_report_load2 : Z := 0x5cfb0.  Definition tfib_E_asan_report_load2 : Z := 0x5d000.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5d000.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5d050.
Definition tfib_A_asan_report_load4 : Z := 0x5d050.  Definition tfib_E_asan_report_load4 : Z := 0x5d0a0.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5d0a0.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5d0f0.
Definition tfib_A_asan_report_load8 : Z := 0x5d0f0.  Definition tfib_E_asan_report_load8 : Z := 0x5d140.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5d140.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5d190.
Definition tfib_A_asan_report_load16 : Z := 0x5d190.  Definition tfib_E_asan_report_load16 : Z := 0x5d1e0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5d1e0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5d230.
Definition tfib_A_asan_report_store1 : Z := 0x5d230.  Definition tfib_E_asan_report_store1 : Z := 0x5d280.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5d280.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5d2d0.
Definition tfib_A_asan_report_store2 : Z := 0x5d2d0.  Definition tfib_E_asan_report_store2 : Z := 0x5d320.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5d320.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5d370.
Definition tfib_A_asan_report_store4 : Z := 0x5d370.  Definition tfib_E_asan_report_store4 : Z := 0x5d3c0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5d3c0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5d410.
Definition tfib_A_asan_report_store8 : Z := 0x5d410.  Definition tfib_E_asan_report_store8 : Z := 0x5d460.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5d460.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5d4b0.
Definition tfib_A_asan_report_store16 : Z := 0x5d4b0.  Definition tfib_E_asan_report_store16 : Z := 0x5d500.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5d500.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5d550.
Definition tfib_A_asan_report_load_n : Z := 0x5d550.  Definition tfib_E_asan_report_load_n : Z := 0x5d5a0.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5d5a0.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5d5f0.
Definition tfib_A_asan_report_store_n : Z := 0x5d5f0.  Definition tfib_E_asan_report_store_n : Z := 0x5d640.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5d640.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5d690.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5d690.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5d710.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5d710.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5dac4.
Definition tfib_A_AsanInitInternal : Z := 0x5db54.  Definition tfib_E_AsanInitInternal : Z := 0x5de08.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5de08.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5dea8.
Definition tfib_A_thunk_59674 : Z := 0x5e070.  Definition tfib_E_thunk_59674 : Z := 0x5e074.
Definition tfib_A_asan_init : Z := 0x5e074.  Definition tfib_E_asan_init : Z := 0x5e108.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5e108.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5e10c.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5e10c.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5e170.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5e2e4.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5e2ec.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5e370.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5e698.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5e698.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5e878.
Definition tfib_A_InitializeShadowMemory : Z := 0x5e878.  Definition tfib_E_InitializeShadowMemory : Z := 0x5eb80.
Definition tfib_A_SetMallocContextSize : Z := 0x5eb80.  Definition tfib_E_SetMallocContextSize : Z := 0x5eb90.
Definition tfib_A_GetMallocContextSize : Z := 0x5eb90.  Definition tfib_E_GetMallocContextSize : Z := 0x5eba0.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5eba0.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ecf0.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5f0d0.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5f370.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5f7d4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5f80c.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5fab4.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5fac0.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5fac0.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5fb4c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5fb4c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5fbb4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5fbb4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5fc2c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5fc2c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5fc94.
Definition tfib_A_IsAddrSuppressed : Z := 0x5fc94.  Definition tfib_E_IsAddrSuppressed : Z := 0x5fde0.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x6006c.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x60078.
Definition tfib_A_AsanThread_Create : Z := 0x601f8.  Definition tfib_E_AsanThread_Create : Z := 0x60394.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x603f0.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x60608.
Definition tfib_A_GetCurrentThread : Z := 0x60608.  Definition tfib_E_GetCurrentThread : Z := 0x60628.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x60628.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x607cc.
Definition tfib_A_AsanThread_stack_top : Z := 0x607cc.  Definition tfib_E_AsanThread_stack_top : Z := 0x60824.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x60824.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x6087c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x6087c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x60aac.
Definition tfib_A_AsanThread_Init : Z := 0x60aac.  Definition tfib_E_AsanThread_Init : Z := 0x60ea0.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x60ea0.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x60fac.
Definition tfib_A_CreateMainThread : Z := 0x60fe0.  Definition tfib_E_CreateMainThread : Z := 0x610f0.
Definition tfib_A_SetCurrentThread : Z := 0x610f0.  Definition tfib_E_SetCurrentThread : Z := 0x611d0.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x613d4.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x61510.
Definition tfib_A_weak_default_hook_ret : Z := 0x621e4.  Definition tfib_E_weak_default_hook_ret : Z := 0x621e8.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x621f0.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x62430.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x62684.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x627dc.
Definition tfib_A_internal_allocator_getter : Z := 0x62adc.  Definition tfib_E_internal_allocator_getter : Z := 0x62ae8.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x62ae8.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x62c34.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x62c34.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x62c80.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x62c80.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x62c8c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x62cbc.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x62cc8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x62cc8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x62cd4.
Definition tfib_A_IsRssLimitExceeded : Z := 0x62cd4.  Definition tfib_E_IsRssLimitExceeded : Z := 0x62ce4.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x62cf0.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x62fbc.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x62fbc.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x6337c.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x642d8.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x642e4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x642e4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x643bc.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x643bc.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x64458.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6497c.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x649c0.
Definition tfib_A_DecreaseTotalMmap : Z := 0x649c0.  Definition tfib_E_DecreaseTotalMmap : Z := 0x649e4.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x64c38.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x64d4c.
Definition tfib_A_RunMallocHooks : Z := 0x64ef0.  Definition tfib_E_RunMallocHooks : Z := 0x64fa8.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x64fa8.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x64fac.
Definition tfib_A_RunFreeHooks : Z := 0x64fac.  Definition tfib_E_RunFreeHooks : Z := 0x65058.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x65058.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x65060.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x65060.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x65064.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x6508c.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x650d8.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6539c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x655dc.
Definition tfib_A_sanitizer_set_report_path : Z := 0x65bd8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x65bf0.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x65bf0.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x65d34.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x65d34.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x65d3c.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x66084.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x67328.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x67328.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x6734c.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x67800.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x67b10.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x67b10.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x67c54.
Definition tfib_A_FlagParser_ParseString : Z := 0x67c54.  Definition tfib_E_FlagParser_ParseString : Z := 0x67d48.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x67edc.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x67f3c.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x67f3c.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x67f7c.
Definition tfib_A_internal_atoll : Z := 0x67f7c.  Definition tfib_E_internal_atoll : Z := 0x68068.
Definition tfib_A_internal_simple_strtoll : Z := 0x68068.  Definition tfib_E_internal_simple_strtoll : Z := 0x681c4.
Definition tfib_A_internal_memchr : Z := 0x681c4.  Definition tfib_E_internal_memchr : Z := 0x681e4.
Definition tfib_A_internal_memcmp : Z := 0x681e4.  Definition tfib_E_internal_memcmp : Z := 0x6821c.
Definition tfib_A_internal_memcpy : Z := 0x6821c.  Definition tfib_E_internal_memcpy : Z := 0x68240.
Definition tfib_A_internal_memmove : Z := 0x68240.  Definition tfib_E_internal_memmove : Z := 0x68298.
Definition tfib_A_internal_memset : Z := 0x68298.  Definition tfib_E_internal_memset : Z := 0x682f8.
Definition tfib_A_internal_strcspn : Z := 0x682f8.  Definition tfib_E_internal_strcspn : Z := 0x6834c.
Definition tfib_A_internal_strchr : Z := 0x6834c.  Definition tfib_E_internal_strchr : Z := 0x68380.
Definition tfib_A_internal_strdup : Z := 0x68380.  Definition tfib_E_internal_strdup : Z := 0x683ec.
Definition tfib_A_internal_strlen : Z := 0x683ec.  Definition tfib_E_internal_strlen : Z := 0x68408.
Definition tfib_A_internal_strcmp : Z := 0x68408.  Definition tfib_E_internal_strcmp : Z := 0x6844c.
Definition tfib_A_internal_strncmp : Z := 0x6844c.  Definition tfib_E_internal_strncmp : Z := 0x68498.
Definition tfib_A_internal_strchrnul : Z := 0x68498.  Definition tfib_E_internal_strchrnul : Z := 0x684e0.
Definition tfib_A_internal_strrchr : Z := 0x684e0.  Definition tfib_E_internal_strrchr : Z := 0x68520.
Definition tfib_A_internal_strnlen : Z := 0x68650.  Definition tfib_E_internal_strnlen : Z := 0x68680.
Definition tfib_A_internal_strncpy : Z := 0x686c4.  Definition tfib_E_internal_strncpy : Z := 0x68734.
Definition tfib_A_internal_strstr : Z := 0x68734.  Definition tfib_E_internal_strstr : Z := 0x687c8.
Definition tfib_A_mem_is_zero : Z := 0x687c8.  Definition tfib_E_mem_is_zero : Z := 0x6887c.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6887c.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6888c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6888c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x68a6c.
Definition tfib_A_internal_iserror : Z := 0x68a78.  Definition tfib_E_internal_iserror : Z := 0x68a98.
Definition tfib_A_internal_mmap : Z := 0x68a98.  Definition tfib_E_internal_mmap : Z := 0x68aa4.
Definition tfib_A_internal_munmap : Z := 0x68aa4.  Definition tfib_E_internal_munmap : Z := 0x68ab0.
Definition tfib_A_internal_mprotect : Z := 0x68ab0.  Definition tfib_E_internal_mprotect : Z := 0x68ac0.
Definition tfib_A_internal_madvise : Z := 0x68ac0.  Definition tfib_E_internal_madvise : Z := 0x68aec.
Definition tfib_A_internal_close : Z := 0x68aec.  Definition tfib_E_internal_close : Z := 0x68af8.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x68af8.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x68b1c.
Definition tfib_A_internal_read : Z := 0x68b1c.  Definition tfib_E_internal_read : Z := 0x68b54.
Definition tfib_A_internal_write : Z := 0x68b54.  Definition tfib_E_internal_write : Z := 0x68b8c.
Definition tfib_A_internal_ftruncate : Z := 0x68b8c.  Definition tfib_E_internal_ftruncate : Z := 0x68bc4.
Definition tfib_A_internal_dup : Z := 0x68bc4.  Definition tfib_E_internal_dup : Z := 0x68bd0.
Definition tfib_A_internal_dup2_dup3 : Z := 0x68bd0.  Definition tfib_E_internal_dup2_dup3 : Z := 0x68be0.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x68be0.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x68bf8.
Definition tfib_A_internal_sched_yield : Z := 0x68bf8.  Definition tfib_E_internal_sched_yield : Z := 0x68c04.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x68c04.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x68c50.
Definition tfib_A_internal_execve : Z := 0x68c50.  Definition tfib_E_internal_execve : Z := 0x68c5c.
Definition tfib_A_internal_exit_exit_group : Z := 0x68c5c.  Definition tfib_E_internal_exit_exit_group : Z := 0x68c70.
Definition tfib_A_FileExists_newfstatat : Z := 0x68c70.  Definition tfib_E_FileExists_newfstatat : Z := 0x68cf0.
Definition tfib_A_DirExists_newfstatat : Z := 0x68cf0.  Definition tfib_E_DirExists_newfstatat : Z := 0x68d54.
Definition tfib_A_GetTid_gettid : Z := 0x68d54.  Definition tfib_E_GetTid_gettid : Z := 0x68d60.
Definition tfib_A_GetEnv : Z := 0x68d60.  Definition tfib_E_GetEnv : Z := 0x68e90.
Definition tfib_A_FutexWait : Z := 0x68f94.  Definition tfib_E_FutexWait : Z := 0x68fb8.
Definition tfib_A_FutexWake : Z := 0x68fb8.  Definition tfib_E_FutexWake : Z := 0x68fdc.
Definition tfib_A_internal_ptrace : Z := 0x68fdc.  Definition tfib_E_internal_ptrace : Z := 0x68fe8.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x68fe8.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x68ff8.
Definition tfib_A_internal_getpid : Z := 0x68ff8.  Definition tfib_E_internal_getpid : Z := 0x69004.
Definition tfib_A_internal_getppid : Z := 0x69004.  Definition tfib_E_internal_getppid : Z := 0x69010.
Definition tfib_A_internal_prctl : Z := 0x69010.  Definition tfib_E_internal_prctl : Z := 0x6901c.
Definition tfib_A_internal_sigaltstack : Z := 0x6901c.  Definition tfib_E_internal_sigaltstack : Z := 0x69028.
Definition tfib_A_internal_fork_clone : Z := 0x69028.  Definition tfib_E_internal_fork_clone : Z := 0x69040.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x69040.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x6916c.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x69344.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x69740.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x698ac.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x699c4.
Definition tfib_A_GetPageSizeCached : Z := 0x699c4.  Definition tfib_E_GetPageSizeCached : Z := 0x699cc.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x699cc.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x69a78.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x69a78.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x69b98.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x69c60.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x69ce0.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x69ce0.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x69d3c.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x69d3c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x69e08.
Definition tfib_A_thunk_653ec : Z := 0x69f04.  Definition tfib_E_thunk_653ec : Z := 0x69f08.
Definition tfib_A_CheckASLR : Z := 0x69f08.  Definition tfib_E_CheckASLR : Z := 0x69f0c.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x6a158.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6a15c.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x6a15c.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x6a168.
Definition tfib_A_MmapOrDie : Z := 0x6a168.  Definition tfib_E_MmapOrDie : Z := 0x6a274.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6a274.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6a2e8.
Definition tfib_A_UnmapOrDie : Z := 0x6a2e8.  Definition tfib_E_UnmapOrDie : Z := 0x6a364.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6a364.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6a474.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6a6a0.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6a7a4.
Definition tfib_A_MmapFixedOrDie : Z := 0x6a7a4.  Definition tfib_E_MmapFixedOrDie : Z := 0x6a7b0.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6a7b0.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6a928.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6a928.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x6a934.
Definition tfib_A_thunk_66008 : Z := 0x6ab20.  Definition tfib_E_thunk_66008 : Z := 0x6ab24.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6ae44.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6b050.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x6b608.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6b614.
Definition tfib_A_Printf : Z := 0x6b618.  Definition tfib_E_Printf : Z := 0x6b664.
Definition tfib_A_SharedPrintfCode : Z := 0x6b664.  Definition tfib_E_SharedPrintfCode : Z := 0x6b6c0.
Definition tfib_A_Report : Z := 0x6b6c0.  Definition tfib_E_Report : Z := 0x6b70c.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6d204.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6d260.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6d260.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6d49c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6d49c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6d7c0.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6dd60.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6de30.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6de30.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6e180.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6e180.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6e190.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6e3cc.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6e410.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6e410.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6e470.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6e470.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6e8e8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6f1a8.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6f4cc.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6f4d4.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6f5d8.
Definition tfib_A_AddDieCallback : Z := 0x6fd88.  Definition tfib_E_AddDieCallback : Z := 0x6fe10.
Definition tfib_A_Die : Z := 0x6fed4.  Definition tfib_E_Die : Z := 0x6ff94.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6ff94.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6ffa0.
Definition tfib_A_CheckFailed : Z := 0x6ffa0.  Definition tfib_E_CheckFailed : Z := 0x70058.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x706b0.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x707a8.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x707a8.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x708d4.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x70afc.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x70b78.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x70bac.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x70e94.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x70e94.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x70e98.
Definition tfib_A_GetTls : Z := 0x70e98.  Definition tfib_E_GetTls : Z := 0x71288.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x71288.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x71358.
Definition tfib_A_AndroidLogInit : Z := 0x7173c.  Definition tfib_E_AndroidLogInit : Z := 0x71740.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x71770.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x717b8.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x717b8.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x71a04.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x71a04.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x71a08.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x71a08.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x71b14.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x71b14.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x71c18.
Definition tfib_A_thunk_6d37c : Z := 0x71e94.  Definition tfib_E_thunk_6d37c : Z := 0x71e98.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x71f3c.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x71f5c.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x71f5c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x71ffc.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x72048.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x7204c.
Definition tfib_A_SetAlternateSignalStack : Z := 0x72088.  Definition tfib_E_SetAlternateSignalStack : Z := 0x7214c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x7214c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x721d4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x721d4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x7224c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x7224c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x72330.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x723ec.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x72520.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x72758.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x72888.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x72888.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x728e8.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x728e8.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x729b4.
Definition tfib_A_MmapNoAccess : Z := 0x729c8.  Definition tfib_E_MmapNoAccess : Z := 0x729e8.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x729e8.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x72b34.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x72b34.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x72b44.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x7433c.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x74380.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x74380.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x743b0.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x747e4.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x74908.
Definition tfib_A_StackStore_Alloc : Z := 0x74908.  Definition tfib_E_StackStore_Alloc : Z := 0x74a3c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x752f0.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x753a4.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x76af8.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x76b54.
Definition tfib_A_StackDepotPut : Z := 0x76de0.  Definition tfib_E_StackDepotPut : Z := 0x76e00.
Definition tfib_A_StackDepotBase_Put : Z := 0x76e00.  Definition tfib_E_StackDepotBase_Put : Z := 0x77084.
Definition tfib_A_StackDepotBase_Get : Z := 0x77084.  Definition tfib_E_StackDepotBase_Get : Z := 0x77194.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x77574.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x77604.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x77604.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x77704.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x77764.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x7776c.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x7776c.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x778cc.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x778cc.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x77940.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x77dc8.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x77ee0.
Definition tfib_A_thunk_762d8 : Z := 0x7af2c.  Definition tfib_E_thunk_762d8 : Z := 0x7af30.
Definition tfib_A_thunk_77ab0 : Z := 0x7c704.  Definition tfib_E_thunk_77ab0 : Z := 0x7c708.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7e130.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7e1ec.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7e1ec.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7e2c4.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7e2c4.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x7e538.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7e864.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7e8a8.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7e8a8.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ec78.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7ef48.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7f000.
Definition tfib_A_thunk_7b6f8 : Z := 0x80358.  Definition tfib_E_thunk_7b6f8 : Z := 0x8035c.
Definition tfib_A_lsan_register_root_region : Z := 0x80f64.  Definition tfib_E_lsan_register_root_region : Z := 0x81294.
Definition tfib_A_lsan_unregister_root_region : Z := 0x81294.  Definition tfib_E_lsan_unregister_root_region : Z := 0x8171c.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x8171c.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x81728.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x842e0.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x842f8.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x8467c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x846f8.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x846f8.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x847a8.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x847a8.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x847c0.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x847c0.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x84908.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x84908.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x84914.
Definition tfib_A_asan_default_options_cli_c : Z := 0x84914.  Definition tfib_E_asan_default_options_cli_c : Z := 0x84920.
Definition tfib_A_main : Z := 0x84920.  Definition tfib_E_main : Z := 0x84be4.
Definition tfib_A_target_alloc_init : Z := 0x84be4.  Definition tfib_E_target_alloc_init : Z := 0x84be8.
Definition tfib_A_target_alloc_count : Z := 0x84be8.  Definition tfib_E_target_alloc_count : Z := 0x84bf0.
Definition tfib_A_target_run : Z := 0x84bf0.  Definition tfib_E_target_run : Z := 0x84d78.
Definition tfib_A_emit_printf : Z := 0x84d78.  Definition tfib_E_emit_printf : Z := 0x84dc0.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x84dc0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x86140.  Definition tfib_A_m_file : Z := 0x86140.  Definition tfib_E_m_file : Z := 0x86f58.  Definition tfib_A_check_segments : Z := 0x86f58.  Definition tfib_E_check_segments : Z := 0x870f8.  Definition tfib_A_check_role : Z := 0x870f8.  Definition tfib_E_check_role : Z := 0x8718c.  Definition tfib_A_check_model : Z := 0x8718c.  Definition tfib_E_check_model : Z := 0x87210.  Definition tfib_A_check_ignore : Z := 0x87210.  Definition tfib_E_check_ignore : Z := 0x87278.  Definition tfib_A_check_provenance : Z := 0x87278.  Definition tfib_E_check_provenance : Z := 0x8736c.  Definition tfib_A_check_refusals : Z := 0x8736c.  Definition tfib_E_check_refusals : Z := 0x8746c.  Definition tfib_A_check_address : Z := 0x8746c.  Definition tfib_E_check_address : Z := 0x874c0.  Definition tfib_A_check_knock_refused : Z := 0x874c0.  Definition tfib_E_check_knock_refused : Z := 0x874f4.  Definition tfib_A_m_find : Z := 0x874f4.  Definition tfib_E_m_find : Z := 0x875f0.  Definition tfib_A_check_absent : Z := 0x875f0.  Definition tfib_E_check_absent : Z := 0x87664.  Definition tfib_A_check_declared : Z := 0x87664.  Definition tfib_E_check_declared : Z := 0x8782c.  Definition tfib_A_m_refuse : Z := 0x8782c.  Definition tfib_E_m_refuse : Z := 0x879cc.  Definition tfib_A_ieq : Z := 0x87b70.  Definition tfib_E_ieq : Z := 0x87c94.  Definition tfib_A_reac_segconf_init : Z := 0x87e14.  Definition tfib_E_reac_segconf_init : Z := 0x87e38.  Definition tfib_A_reac_segconf_parse_file : Z := 0x87e38.  Definition tfib_E_reac_segconf_parse_file : Z := 0x892f8.  Definition tfib_A_refuse : Z := 0x892f8.  Definition tfib_E_refuse : Z := 0x89640.  Definition tfib_A_trim : Z := 0x89640.  Definition tfib_E_trim : Z := 0x89784.  Definition tfib_A_reac_segconf_parse : Z := 0x89784.  Definition tfib_E_reac_segconf_parse : Z := 0x897cc.  Definition tfib_A_cross_check : Z := 0x897cc.  Definition tfib_E_cross_check : Z := 0x89a84.  Definition tfib_A_reac_segconf_find : Z := 0x89a84.  Definition tfib_E_reac_segconf_find : Z := 0x89b78.  Definition tfib_A_reac_segconf_ignored : Z := 0x89b78.  Definition tfib_E_reac_segconf_ignored : Z := 0x89be0.  Definition tfib_A_reac_segconf_role : Z := 0x89be0.  Definition tfib_E_reac_segconf_role : Z := 0x89cbc.  Definition tfib_A_reac_segconf_role_file : Z := 0x89cbc.  Definition tfib_E_reac_segconf_role_file : Z := 0x89d60.  Definition tfib_A_reac_segconf_ignore_file : Z := 0x89d60.  Definition tfib_E_reac_segconf_ignore_file : Z := 0x89e04.  Definition tfib_A_reac_segconf_model : Z := 0x89e04.  Definition tfib_E_reac_segconf_model : Z := 0x89e7c.  Definition tfib_A_reac_segconf_declared : Z := 0x89e7c.  Definition tfib_E_reac_segconf_declared : Z := 0x8a218.  Definition tfib_A_reac_declared_vlan_split : Z := 0x8a218.  Definition tfib_E_reac_declared_vlan_split : Z := 0x8a408.  Definition tfib_A_name_ok : Z := 0x8a408.  Definition tfib_E_name_ok : Z := 0x8a514.  Definition tfib_A_reac_declared_vlan_add : Z := 0x8a514.  Definition tfib_E_reac_declared_vlan_add : Z := 0x8a7d8.  Definition tfib_A_fuzz_catalogue_row : Z := 0x8a7d8.  Definition tfib_E_fuzz_catalogue_row : Z := 0x8a8a0.  Definition tfib_A_reac_box_catalogue : Z := 0x8a8a0.  Definition tfib_E_reac_box_catalogue : Z := 0x8a8f4.  Definition tfib_A_reac_box_catalogue_by_token : Z := 0x8a8f4.  Definition tfib_E_reac_box_catalogue_by_token : Z := 0x8a934.
Definition tfib_A_asan_module_ctor : Z := 0x87dac.  Definition tfib_E_asan_module_ctor : Z := 0x87de4.




Definition tfib_A_asan_module_dtor : Z := 0x87de4.  Definition tfib_E_asan_module_dtor : Z := 0x87e14.



Definition tfib_A_extenddftf2 : Z := 0x8a944.  Definition tfib_E_extenddftf2 : Z := 0x8aad4.
Definition tfib_A_sysconf : Z := 0x90724.  Definition tfib_E_sysconf : Z := 0x9094c.
Definition tfib_A_init : Z := 0x90968.  Definition tfib_E_init : Z := 0x9096c.
Definition tfib_A_init_libc : Z := 0x9096c.  Definition tfib_E_init_libc : Z := 0x90b98.
Definition tfib_A_libc_start_init : Z := 0x90b98.  Definition tfib_E_libc_start_init : Z := 0x90be4.
Definition tfib_A_libc_start_main : Z := 0x90be4.  Definition tfib_E_libc_start_main : Z := 0x90c44.
Definition tfib_A_libc_start_main_stage2 : Z := 0x90c44.  Definition tfib_E_libc_start_main_stage2 : Z := 0x90c8c.
Definition tfib_A_init_tls : Z := 0x90d64.  Definition tfib_E_init_tls : Z := 0x91014.
Definition tfib_A_init_ssp : Z := 0x91014.  Definition tfib_E_init_ssp : Z := 0x91074.
Definition tfib_A_stack_chk_fail : Z := 0x91074.  Definition tfib_E_stack_chk_fail : Z := 0x9107c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x910c4.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x91158.
Definition tfib_A_Exit : Z := 0x91158.  Definition tfib_E_Exit : Z := 0x91174.
Definition tfib_A_funcs_on_exit : Z := 0x911a4.  Definition tfib_E_funcs_on_exit : Z := 0x9126c.
Definition tfib_A_fini_stub_ret : Z := 0x9126c.  Definition tfib_E_fini_stub_ret : Z := 0x91270.
Definition tfib_A_cxa_atexit_atexit : Z := 0x91270.  Definition tfib_E_cxa_atexit_atexit : Z := 0x91334.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x91334.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x91338.
Definition tfib_A_musl_exit_helper_stub : Z := 0x91338.  Definition tfib_E_musl_exit_helper_stub : Z := 0x9133c.
Definition tfib_A_libc_exit_fini : Z := 0x9133c.  Definition tfib_E_libc_exit_fini : Z := 0x91388.
Definition tfib_A_exit : Z := 0x91388.  Definition tfib_E_exit : Z := 0x913fc.
Definition tfib_A_open : Z := 0x915fc.  Definition tfib_E_open : Z := 0x916e0.
Definition tfib_A_syscall_ret : Z := 0x916e0.  Definition tfib_E_syscall_ret : Z := 0x91718.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x91718.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x918c0.
Definition tfib_A_calloc : Z := 0x91e84.  Definition tfib_E_calloc : Z := 0x91fbc.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x91fbc.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x91fc0.
Definition tfib_A_libc_free : Z := 0x91fc0.  Definition tfib_E_libc_free : Z := 0x9218c.
Definition tfib_A_get_meta : Z := 0x9218c.  Definition tfib_E_get_meta : Z := 0x9229c.
Definition tfib_A_alloc_meta : Z := 0x92674.  Definition tfib_E_alloc_meta : Z := 0x9294c.
Definition tfib_A_libc_malloc_impl : Z := 0x9294c.  Definition tfib_E_libc_malloc_impl : Z := 0x92cbc.
Definition tfib_A_alloc_slot : Z := 0x92cbc.  Definition tfib_E_alloc_slot : Z := 0x93560.
Definition tfib_A_enframe : Z := 0x93560.  Definition tfib_E_enframe : Z := 0x936b0.
Definition tfib_A_malloc_allzerop : Z := 0x936b0.  Definition tfib_E_malloc_allzerop : Z := 0x93828.
Definition tfib_A_getrlimit : Z := 0x954d8.  Definition tfib_E_getrlimit : Z := 0x955d0.
Definition tfib_A_getrusage : Z := 0x955d0.  Definition tfib_E_getrusage : Z := 0x955f8.
Definition tfib_A_setrlimit : Z := 0x955f8.  Definition tfib_E_setrlimit : Z := 0x956c0.
Definition tfib_A_mmap : Z := 0x95ae8.  Definition tfib_E_mmap : Z := 0x95bd4.
Definition tfib_A_mprotect : Z := 0x95bd4.  Definition tfib_E_mprotect : Z := 0x95c1c.
Definition tfib_A_munmap : Z := 0x95cf0.  Definition tfib_E_munmap : Z := 0x95d38.
Definition tfib_A_sched_yield : Z := 0x95ffc.  Definition tfib_E_sched_yield : Z := 0x96020.
Definition tfib_A_raise_tkill_path : Z := 0x9607c.  Definition tfib_E_raise_tkill_path : Z := 0x960f4.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x960f4.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x962c8.
Definition tfib_A_musl_sigaltstack : Z := 0x963c0.  Definition tfib_E_musl_sigaltstack : Z := 0x9644c.
Definition tfib_A_fprintf : Z := 0x96a28.  Definition tfib_E_fprintf : Z := 0x96a8c.
Definition tfib_A_lockfile : Z := 0x96a8c.  Definition tfib_E_lockfile : Z := 0x96b88.
Definition tfib_A_unlockfile : Z := 0x96b88.  Definition tfib_E_unlockfile : Z := 0x96be8.

Definition tfib_A_stdio_read : Z := 0x96778.  Definition tfib_E_stdio_read : Z := 0x96890.
Definition tfib_A_stdio_write : Z := 0x96898.  Definition tfib_E_stdio_write : Z := 0x96a28.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x96748.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9674c.
Definition tfib_A_stdio_close : Z := 0x9674c.  Definition tfib_E_stdio_close : Z := 0x96778.
Definition tfib_A_fwritex : Z := 0x9701c.  Definition tfib_E_fwritex : Z := 0x97154.
Definition tfib_A_musl_fwrite : Z := 0x97154.  Definition tfib_E_musl_fwrite : Z := 0x9720c.
Definition tfib_A_towrite : Z := 0x9720c.  Definition tfib_E_towrite : Z := 0x97260.
Definition tfib_A_stdio_exit : Z := 0x96e78.  Definition tfib_E_stdio_exit : Z := 0x9701c.
Definition tfib_A_ofl_lock : Z := 0x97260.  Definition tfib_E_ofl_lock : Z := 0x97290.
Definition tfib_A_musl_vfprintf : Z := 0x973dc.  Definition tfib_E_musl_vfprintf : Z := 0x9758c.
Definition tfib_A_printf_core : Z := 0x9758c.  Definition tfib_E_printf_core : Z := 0x983bc.
Definition tfib_A_pop_arg : Z := 0x983bc.  Definition tfib_E_pop_arg : Z := 0x984f0.
Definition tfib_A_pad : Z := 0x984f0.  Definition tfib_E_pad : Z := 0x985c4.
Definition tfib_A_fmt_fp : Z := 0x985c4.  Definition tfib_E_fmt_fp : Z := 0x99c8c.
Definition tfib_A_thunk_931e0 : Z := 0x91ad8.  Definition tfib_E_thunk_931e0 : Z := 0x91adc.
Definition tfib_A_musl_wctomb : Z := 0x95e64.  Definition tfib_E_musl_wctomb : Z := 0x95e88.
Definition tfib_A_musl_wcrtomb : Z := 0x95d38.  Definition tfib_E_musl_wcrtomb : Z := 0x95e64.
Definition tfib_A_fpclassifyl : Z := 0x940c8.  Definition tfib_E_fpclassifyl : Z := 0x9410c.
Definition tfib_A_letf2 : Z := 0x93900.  Definition tfib_E_letf2 : Z := 0x939c8.
Definition tfib_A_multf3 : Z := 0x939c8.  Definition tfib_E_multf3 : Z := 0x940c8.
Definition tfib_A_floatsitf : Z := 0x94924.  Definition tfib_E_floatsitf : Z := 0x94a2c.
Definition tfib_A_scalbn : Z := 0x95330.  Definition tfib_E_scalbn : Z := 0x953c8.
Definition tfib_A_subtf3 : Z := 0x94914.  Definition tfib_E_subtf3 : Z := 0x94924.
Definition tfib_A_addtf3 : Z := 0x9410c.  Definition tfib_E_addtf3 : Z := 0x948d8.
Definition tfib_A_fe_getround : Z := 0x948d8.  Definition tfib_E_fe_getround : Z := 0x94908.
Definition tfib_A_fixunstfsi : Z := 0x99c94.  Definition tfib_E_fixunstfsi : Z := 0x99d28.
Definition tfib_A_floatunsitf : Z := 0x99d28.  Definition tfib_E_floatunsitf : Z := 0x99e14.
Definition tfib_A_fixtfsi : Z := 0x953c8.  Definition tfib_E_fixtfsi : Z := 0x95470.
Definition tfib_A_divtf3 : Z := 0x94a2c.  Definition tfib_E_divtf3 : Z := 0x95330.
Definition tfib_A_musl_vprintf : Z := 0x9a4ec.  Definition tfib_E_musl_vprintf : Z := 0x9a508.
Definition tfib_A_stdout_write : Z := 0x9729c.  Definition tfib_E_stdout_write : Z := 0x9733c.
Definition tfib_A_thunk_95368 : Z := 0x9aaa0.  Definition tfib_E_thunk_95368 : Z := 0x9aaa4.
Definition tfib_A_musl_memcmp : Z := 0x9ab70.  Definition tfib_E_musl_memcmp : Z := 0x9aba0.
Definition tfib_A_musl_memcpy : Z := 0x9aba0.  Definition tfib_E_musl_memcpy : Z := 0x9afa4.
Definition tfib_A_musl_memset : Z := 0x9afd4.  Definition tfib_E_musl_memset : Z := 0x9b0cc.
Definition tfib_A_musl_strchr : Z := 0x9b180.  Definition tfib_E_musl_strchr : Z := 0x9b1bc.
Definition tfib_A_strchrnul : Z := 0x9b1bc.  Definition tfib_E_strchrnul : Z := 0x9b29c.
Definition tfib_A_musl_strlen : Z := 0x9b2d4.  Definition tfib_E_musl_strlen : Z := 0x9b364.
Definition tfib_A_musl_strnlen : Z := 0x9b634.  Definition tfib_E_musl_strnlen : Z := 0x9b678.
Definition tfib_A_musl_memchr : Z := 0x9aaa4.  Definition tfib_E_musl_memchr : Z := 0x9ab70.
Definition tfib_A_lock : Z := 0x9bdac.  Definition tfib_E_lock : Z := 0x9c034.
Definition tfib_A_unlock : Z := 0x9c034.  Definition tfib_E_unlock : Z := 0x9c0a8.
Definition tfib_A_syscall_cp_c : Z := 0x9c0a8.  Definition tfib_E_syscall_cp_c : Z := 0x9c0cc.
Definition tfib_A_syscall_cp_sccp : Z := 0x9c0cc.  Definition tfib_E_syscall_cp_sccp : Z := 0x9c0d0.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x9c0d0.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x9c0f4.
Definition tfib_A_pthread_atfork : Z := 0x9c10c.  Definition tfib_E_pthread_atfork : Z := 0x9c1b0.
Definition tfib_A_mremap : Z := 0x95c1c.  Definition tfib_E_mremap : Z := 0x95cf0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9d184.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9d1a0.
Definition tfib_A_pthread_key_create : Z := 0x9d52c.  Definition tfib_E_pthread_key_create : Z := 0x9d600.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x9d8a4.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x9d948.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x9d948.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x9da64.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9da64.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9da90.
Definition tfib_A_pthread_setspecific : Z := 0x9dac8.  Definition tfib_E_pthread_setspecific : Z := 0x9dafc.
Definition tfib_A_set_thread_area : Z := 0x9db04.  Definition tfib_E_set_thread_area : Z := 0x9db10.
Definition tfib_A_thunk_96f9c : Z := 0x9dafc.  Definition tfib_E_thunk_96f9c : Z := 0x9db04.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9e430.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9e4e8.
Definition tfib_A_close : Z := 0xa0b00.  Definition tfib_E_close : Z := 0xa0b54.
Definition tfib_A_musl_read : Z := 0xa0be0.  Definition tfib_E_musl_read : Z := 0xa0c14.
Definition tfib_A_vm_wait : Z := 0x9e140.  Definition tfib_E_vm_wait : Z := 0x9e190.
Definition tfib_D_str_sealed : Z := 0x11840.
Definition tfib_D_init_array_0_3 : Z := 0xa1c18.
Definition tfib_D_fini_array_0_1 : Z := 0xa1c38.
Definition tfib_D_GOT_common_flags : Z := 0xa3200.
Definition tfib_D_GOT_flags : Z := 0xa3208.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa3210.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa3218.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa3220.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa3228.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa3d78.
Definition tfib_D_environ_musl : Z := 0xa3ea0.
Definition tfib_D_REAL_read : Z := 0xa4f78.
Definition tfib_D_REAL_memcpy : Z := 0xa50a0.
Definition tfib_D_REAL_memset : Z := 0xa50a8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa9158.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa9fb8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xac7b8.
Definition tfib_D_asan_inited : Z := 0xad498.
Definition tfib_D_replace_intrin_cached : Z := 0xad499.
Definition tfib_D_kHighMemEnd : Z := 0xad4a0.
Definition tfib_D_kMidMemBeg : Z := 0xad4a8.
Definition tfib_D_kMidMemEnd : Z := 0xad4b0.
Definition tfib_D_malloc_context_size : Z := 0xad4bc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13e2e8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5ffa88.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x602000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x31f60.
Definition tfib_at_rw_lo : Z := 0xa4000.
Definition tfib_at_rw_len : Z := 0x55e000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x68298.
Definition tfib_at_x_imemcpy : Z := 0x6821c.
Definition tfib_at_x_memset : Z := 0x9afd4.
Definition tfib_at_x_memcpy : Z := 0x9aba0.
Definition tfib_at_x_memiszero : Z := 0x687c8.
Definition tfib_at_x_istrncpy : Z := 0x686c4.
Definition tfib_at_x_sealed : Z := 0x11840.
Definition tfib_at_x_popfree : Z := 0x3842c.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x909a4.
Definition tfib_at_x_envscan_k : Z := 0x909b0.
Definition tfib_at_x_pnscan : Z := 0x90a68.
Definition tfib_at_x_pnscan_k : Z := 0x90a74.
Definition tfib_at_stops_more : list Z := (0x360a0 :: 0x376c4 :: 0x58240 :: 0x5e848 :: 0x5e85c :: 0x5e870 :: 0x64314 :: 0x643e4 :: 0x71910 :: 0x7281c :: 0x729ac :: 0x7c704 :: nil)%list.
