(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22ecc.
Definition tfib_text_lo : Z := 0x30634.
Definition tfib_init_array_lo : Z := 0x9a0e8.  Definition tfib_init_array_hi : Z := 0x9a108.
Definition tfib_fini_array_lo : Z := 0x9a108.  Definition tfib_fini_array_hi : Z := 0x9a118.
Definition tfib_preinit_array_lo : Z := 0x9a118.  Definition tfib_preinit_array_hi : Z := 0x9a120.
Definition tfib_data_rel_ro_lo : Z := 0x9a120.  Definition tfib_data_rel_ro_hi : Z := 0x9a7d0.
Definition tfib_got_lo : Z := 0x9a7d0.  Definition tfib_got_hi : Z := 0x9b528.
Definition tfib_data_lo : Z := 0x9c528.  Definition tfib_data_hi : Z := 0x9f0d8.
Definition tfib_asan_globals_lo : Z := 0x9f0e0.  Definition tfib_asan_globals_hi : Z := 0x9fd20.
Definition tfib_bss_lo : Z := 0x9fd40.  Definition tfib_bss_hi : Z := 0x5f7c70.
Definition tfib_tbss_lo : Z := 0x990e8.  Definition tfib_tbss_hi : Z := 0x990fc.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f8000.
Definition tfib_entry : Z := 0x30634.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30634.  Definition tfib_E_start : Z := 0x3067c.
Definition tfib_A_do_init : Z := 0x3067c.  Definition tfib_E_do_init : Z := 0x306f0.
Definition tfib_A_do_fini : Z := 0x306f0.  Definition tfib_E_do_fini : Z := 0x30780.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30780.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x307bc.
Definition tfib_A_InitializeAllocator : Z := 0x3092c.  Definition tfib_E_InitializeAllocator : Z := 0x30944.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30944.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30ab0.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x3100c.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31168.
Definition tfib_A_asan_free : Z := 0x3153c.  Definition tfib_E_asan_free : Z := 0x31564.
Definition tfib_A_Allocator_Deallocate : Z := 0x31564.  Definition tfib_E_Allocator_Deallocate : Z := 0x3181c.
Definition tfib_A_asan_malloc : Z := 0x3181c.  Definition tfib_E_asan_malloc : Z := 0x31878.
Definition tfib_A_Allocator_Allocate : Z := 0x31878.  Definition tfib_E_Allocator_Allocate : Z := 0x32200.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32938.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32a7c.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32b68.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32bc4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32bc4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32e14.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32e14.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32f08.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x32f08.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x32ff0.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x33424.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x33608.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x33608.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x3378c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x338c4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33b48.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33b48.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33cc8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33cc8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33e90.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33e90.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3405c.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x3405c.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x340fc.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x340fc.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34200.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34528.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34670.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34670.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x346a8.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34e40.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35128.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35800.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35978.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35978.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35b28.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35b28.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35d0c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35d0c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x35fe4.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x35fe4.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x3645c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3645c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x3655c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x3655c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36864.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36864.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36bd4.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36bd4.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x36cec.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x36ff4.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x370f0.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x370f0.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x371d8.
Definition tfib_A_AsanActivate : Z := 0x371d8.  Definition tfib_E_AsanActivate : Z := 0x372b4.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37790.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x37878.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c330.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c408.
Definition tfib_A_FakeStack_Create : Z := 0x3c408.  Definition tfib_E_FakeStack_Create : Z := 0x3c4f4.
Definition tfib_A_FakeStack_Allocate : Z := 0x3c7b0.  Definition tfib_E_FakeStack_Allocate : Z := 0x3ca98.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cbcc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cbfc.
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3cbfc.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3cda8.

Definition tfib_A_check_absent : Z := 0x82bb4.  Definition tfib_E_check_absent : Z := 0x82bdc.  Definition tfib_A_check_role : Z := 0x82bdc.  Definition tfib_E_check_role : Z := 0x82c04.  Definition tfib_A_check_malformed : Z := 0x82c04.  Definition tfib_E_check_malformed : Z := 0x82c30.  Definition tfib_A_check_answer : Z := 0x82c30.  Definition tfib_E_check_answer : Z := 0x82c80.  Definition tfib_A_check_code : Z := 0x82c80.  Definition tfib_E_check_code : Z := 0x82ccc.  Definition tfib_A_pod_nearest : Z := 0x82ccc.  Definition tfib_E_pod_nearest : Z := 0x82e04.  Definition tfib_A_reac_role_refuse_code : Z := 0x82e6c.  Definition tfib_E_reac_role_refuse_code : Z := 0x82ec8.  Definition tfib_A_reac_role_cfg_changes : Z := 0x82ec8.  Definition tfib_E_reac_role_cfg_changes : Z := 0x82ed4.  Definition tfib_A_reac_role_cfg_apply_state : Z := 0x82ed4.  Definition tfib_E_reac_role_cfg_apply_state : Z := 0x82ef0.  Definition tfib_A_reac_role_prop_parse : Z := 0x82ef0.  Definition tfib_E_reac_role_prop_parse : Z := 0x83424.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7ff88.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82bb4.
Definition tfib_A_asan_InitializeFlags : Z := 0x3cee4.  Definition tfib_E_asan_InitializeFlags : Z := 0x3df10.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e61c.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f438.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3f438.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3fa04.
Definition tfib_A_asan_register_globals : Z := 0x3fa04.  Definition tfib_E_asan_register_globals : Z := 0x3fa70.
Definition tfib_A_asan_unregister_globals : Z := 0x3fa70.  Definition tfib_E_asan_unregister_globals : Z := 0x3fad8.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x40158.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x403c8.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x403c8.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x406d0.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40e44.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40f94.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x419b0.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x41ac8.
Definition tfib_A_strlen : Z := 0x41ac8.  Definition tfib_E_strlen : Z := 0x41acc.
Definition tfib_A_strnlen : Z := 0x41acc.  Definition tfib_E_strnlen : Z := 0x41ad0.
Definition tfib_A_strcmp : Z := 0x41ad0.  Definition tfib_E_strcmp : Z := 0x41ad4.
Definition tfib_A_strchr : Z := 0x41ad4.  Definition tfib_E_strchr : Z := 0x41ad8.
Definition tfib_A_memcmp : Z := 0x41ad8.  Definition tfib_E_memcmp : Z := 0x41adc.

Definition tfib_A_memchr : Z := 0x41adc.  Definition tfib_E_memchr : Z := 0x41ae0.
Definition tfib_A_frexpl : Z := 0x41ae0.  Definition tfib_E_frexpl : Z := 0x41ae4.
Definition tfib_A_read : Z := 0x41ae4.  Definition tfib_E_read : Z := 0x41ae8.
Definition tfib_A_fwrite : Z := 0x41ae8.  Definition tfib_E_fwrite : Z := 0x41aec.
Definition tfib_A_time : Z := 0x41aec.  Definition tfib_E_time : Z := 0x41af0.
Definition tfib_A_gmtime_r : Z := 0x41af0.  Definition tfib_E_gmtime_r : Z := 0x41af4.
Definition tfib_A_vprintf : Z := 0x41af4.  Definition tfib_E_vprintf : Z := 0x41af8.
Definition tfib_A_vfprintf : Z := 0x41af8.  Definition tfib_E_vfprintf : Z := 0x41afc.
Definition tfib_A_vsnprintf : Z := 0x41afc.  Definition tfib_E_vsnprintf : Z := 0x41b00.
Definition tfib_A_vfprintf_2 : Z := 0x41b00.  Definition tfib_E_vfprintf_2 : Z := 0x41b04.
Definition tfib_A_thunk_417bc : Z := 0x41b04.  Definition tfib_E_thunk_417bc : Z := 0x41b08.
Definition tfib_A_clock_gettime : Z := 0x41b08.  Definition tfib_E_clock_gettime : Z := 0x41b0c.
Definition tfib_A_wcrtomb : Z := 0x41b0c.  Definition tfib_E_wcrtomb : Z := 0x41b10.
Definition tfib_A_wctomb : Z := 0x41b10.  Definition tfib_E_wctomb : Z := 0x41b14.
Definition tfib_A_thunk_417cc : Z := 0x41b14.  Definition tfib_E_thunk_417cc : Z := 0x41b1c.
Definition tfib_A_pthread_attr_getstack : Z := 0x41b1c.  Definition tfib_E_pthread_attr_getstack : Z := 0x41b20.
Definition tfib_A_tls_get_addr_thunk : Z := 0x41b20.  Definition tfib_E_tls_get_addr_thunk : Z := 0x41b24.

Definition tfib_A_thunk_417dc : Z := 0x41b24.  Definition tfib_E_thunk_417dc : Z := 0x41b28.

Definition tfib_A_thunk_417e4 : Z := 0x41b28.  Definition tfib_E_thunk_417e4 : Z := 0x41b2c.
Definition tfib_A_thunk_417e8 : Z := 0x41b2c.  Definition tfib_E_thunk_417e8 : Z := 0x41b30.
Definition tfib_A_thunk_417ec : Z := 0x41b30.  Definition tfib_E_thunk_417ec : Z := 0x41b34.
Definition tfib_A_thunk_417f0 : Z := 0x41b34.  Definition tfib_E_thunk_417f0 : Z := 0x41b38.
Definition tfib_A_sem_timedwait : Z := 0x41b38.  Definition tfib_E_sem_timedwait : Z := 0x41b3c.
Definition tfib_A_thunk_417f8 : Z := 0x41b3c.  Definition tfib_E_thunk_417f8 : Z := 0x41b40.
Definition tfib_A_pthread_setcancelstate : Z := 0x41b40.  Definition tfib_E_pthread_setcancelstate : Z := 0x41b44.
Definition tfib_A_send : Z := 0x41b44.  Definition tfib_E_send : Z := 0x41b48.
Definition tfib_A_sendto : Z := 0x41b48.  Definition tfib_E_sendto : Z := 0x41b4c.
Definition tfib_A_sigaltstack : Z := 0x41b4c.  Definition tfib_E_sigaltstack : Z := 0x41b50.
Definition tfib_A_thunk_4180c : Z := 0x41b50.  Definition tfib_E_thunk_4180c : Z := 0x41b54.
Definition tfib_A_icpt_strlen : Z := 0x41b54.  Definition tfib_E_icpt_strlen : Z := 0x41de8.
Definition tfib_A_icpt_strnlen : Z := 0x41de8.  Definition tfib_E_icpt_strnlen : Z := 0x4207c.
Definition tfib_A_icpt_strcmp : Z := 0x42080.  Definition tfib_E_icpt_strcmp : Z := 0x425b0.
Definition tfib_A_icpt_strchr : Z := 0x425b0.  Definition tfib_E_icpt_strchr : Z := 0x42890.
Definition tfib_A_icpt_memcmp : Z := 0x43128.  Definition tfib_E_icpt_memcmp : Z := 0x431e4.

Definition tfib_A_icpt_memchr : Z := 0x431e4.  Definition tfib_E_icpt_memchr : Z := 0x434b4.
Definition tfib_A_icpt_frexpl : Z := 0x434b4.  Definition tfib_E_icpt_frexpl : Z := 0x4372c.
Definition tfib_A_icpt_read : Z := 0x4372c.  Definition tfib_E_icpt_read : Z := 0x4399c.
Definition tfib_A_icpt_fwrite : Z := 0x4399c.  Definition tfib_E_icpt_fwrite : Z := 0x43c10.
Definition tfib_A_icpt_time : Z := 0x43c10.  Definition tfib_E_icpt_time : Z := 0x43eac.
Definition tfib_A_icpt_gmtime_r : Z := 0x440b4.  Definition tfib_E_icpt_gmtime_r : Z := 0x442f4.
Definition tfib_A_icpt_vprintf : Z := 0x442f4.  Definition tfib_E_icpt_vprintf : Z := 0x44390.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44390.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44e58.
Definition tfib_A_icpt_vfprintf : Z := 0x44e58.  Definition tfib_E_icpt_vfprintf : Z := 0x44f0c.
Definition tfib_A_icpt_vsnprintf : Z := 0x44f0c.  Definition tfib_E_icpt_vsnprintf : Z := 0x45224.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x45224.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x452fc.
Definition tfib_A_icpt_clock_gettime : Z := 0x453a0.  Definition tfib_E_icpt_clock_gettime : Z := 0x455f8.
Definition tfib_A_icpt_wcrtomb : Z := 0x455f8.  Definition tfib_E_icpt_wcrtomb : Z := 0x45b68.
Definition tfib_A_icpt_wctomb : Z := 0x45b68.  Definition tfib_E_icpt_wctomb : Z := 0x45ec4.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45f90.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46378.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46384.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46400.


Definition tfib_A_icpt_sem_timedwait : Z := 0x4660c.  Definition tfib_E_icpt_sem_timedwait : Z := 0x468a4.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x468d4.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46afc.
Definition tfib_A_icpt_send : Z := 0x46afc.  Definition tfib_E_icpt_send : Z := 0x46db0.
Definition tfib_A_icpt_sendto : Z := 0x46db0.  Definition tfib_E_icpt_sendto : Z := 0x47074.
Definition tfib_A_icpt_sigaltstack : Z := 0x47074.  Definition tfib_E_icpt_sigaltstack : Z := 0x472d0.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x473a4.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47554.
Definition tfib_A_icpt_diouxXn : Z := 0x47554.  Definition tfib_E_icpt_diouxXn : Z := 0x476ec.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48298.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x50f70.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x50f70.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x510cc.
Definition tfib_A_memset : Z := 0x510cc.  Definition tfib_E_memset : Z := 0x510d0.
Definition tfib_A_memcpy : Z := 0x510d0.  Definition tfib_E_memcpy : Z := 0x510d4.
Definition tfib_A_asan_memcpy : Z := 0x510d4.  Definition tfib_E_asan_memcpy : Z := 0x51570.
Definition tfib_A_asan_memset : Z := 0x51570.  Definition tfib_E_asan_memset : Z := 0x517b0.
Definition tfib_A_icpt_memset : Z := 0x517b0.  Definition tfib_E_icpt_memset : Z := 0x51aa0.
Definition tfib_A_icpt_memcpy : Z := 0x51aa0.  Definition tfib_E_icpt_memcpy : Z := 0x52090.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52090.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x520c8.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x520c8.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x520cc.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x520cc.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x520d0.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x520d0.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52130.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x5217c.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x522b8.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x522b8.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x522bc.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x522bc.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52424.
Definition tfib_A_free : Z := 0x52424.  Definition tfib_E_free : Z := 0x52428.
Definition tfib_A_malloc : Z := 0x52428.  Definition tfib_E_malloc : Z := 0x5242c.
Definition tfib_A_icpt_free : Z := 0x5242c.  Definition tfib_E_icpt_free : Z := 0x525fc.
Definition tfib_A_icpt_malloc : Z := 0x525fc.  Definition tfib_E_icpt_malloc : Z := 0x52758.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x52758.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x52824.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52824.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52828.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x52828.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x52928.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x52c50.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x52dbc.
Definition tfib_A_SetCanPoisonMemory : Z := 0x532a4.  Definition tfib_E_SetCanPoisonMemory : Z := 0x532b4.
Definition tfib_A_CanPoisonMemory : Z := 0x532b4.  Definition tfib_E_CanPoisonMemory : Z := 0x532c8.
Definition tfib_A_PoisonShadow : Z := 0x532c8.  Definition tfib_E_PoisonShadow : Z := 0x537c4.
Definition tfib_A_MemToShadow_checked : Z := 0x537c4.  Definition tfib_E_MemToShadow_checked : Z := 0x53900.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53900.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53aa0.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x53aa0.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x53c20.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53c50.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53f94.
Definition tfib_A_AsanTSDInit : Z := 0x543b4.  Definition tfib_E_AsanTSDInit : Z := 0x54430.
Definition tfib_A_AsanTSDGet : Z := 0x54430.  Definition tfib_E_AsanTSDGet : Z := 0x54470.
Definition tfib_A_AsanTSDSet : Z := 0x54470.  Definition tfib_E_AsanTSDSet : Z := 0x544b0.
Definition tfib_A_PlatformTSDDtor : Z := 0x544b0.  Definition tfib_E_PlatformTSDDtor : Z := 0x54534.
Definition tfib_A_InstallAtForkHandler : Z := 0x54534.  Definition tfib_E_InstallAtForkHandler : Z := 0x54550.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x545b0.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x545f4.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x54d0c.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x54f18.
Definition tfib_A_ReportDoubleFree : Z := 0x55620.  Definition tfib_E_ReportDoubleFree : Z := 0x558b0.
Definition tfib_A_ReportGenericError : Z := 0x5718c.  Definition tfib_E_ReportGenericError : Z := 0x57a48.
Definition tfib_A_AsanInited : Z := 0x581d4.  Definition tfib_E_AsanInited : Z := 0x581ec.
Definition tfib_A_asan_report_load1 : Z := 0x581ec.  Definition tfib_E_asan_report_load1 : Z := 0x5823c.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5823c.  Definition tfib_E_asan_report_exp_load1 : Z := 0x5828c.
Definition tfib_A_asan_report_load2 : Z := 0x5828c.  Definition tfib_E_asan_report_load2 : Z := 0x582dc.
Definition tfib_A_asan_report_exp_load2 : Z := 0x582dc.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5832c.
Definition tfib_A_asan_report_load4 : Z := 0x5832c.  Definition tfib_E_asan_report_load4 : Z := 0x5837c.
Definition tfib_A_asan_report_exp_load4 : Z := 0x5837c.  Definition tfib_E_asan_report_exp_load4 : Z := 0x583cc.
Definition tfib_A_asan_report_load8 : Z := 0x583cc.  Definition tfib_E_asan_report_load8 : Z := 0x5841c.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5841c.  Definition tfib_E_asan_report_exp_load8 : Z := 0x5846c.
Definition tfib_A_asan_report_load16 : Z := 0x5846c.  Definition tfib_E_asan_report_load16 : Z := 0x584bc.
Definition tfib_A_asan_report_exp_load16 : Z := 0x584bc.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5850c.
Definition tfib_A_asan_report_store1 : Z := 0x5850c.  Definition tfib_E_asan_report_store1 : Z := 0x5855c.
Definition tfib_A_asan_report_exp_store1 : Z := 0x5855c.  Definition tfib_E_asan_report_exp_store1 : Z := 0x585ac.
Definition tfib_A_asan_report_store2 : Z := 0x585ac.  Definition tfib_E_asan_report_store2 : Z := 0x585fc.
Definition tfib_A_asan_report_exp_store2 : Z := 0x585fc.  Definition tfib_E_asan_report_exp_store2 : Z := 0x5864c.
Definition tfib_A_asan_report_store4 : Z := 0x5864c.  Definition tfib_E_asan_report_store4 : Z := 0x5869c.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5869c.  Definition tfib_E_asan_report_exp_store4 : Z := 0x586ec.
Definition tfib_A_asan_report_store8 : Z := 0x586ec.  Definition tfib_E_asan_report_store8 : Z := 0x5873c.
Definition tfib_A_asan_report_exp_store8 : Z := 0x5873c.  Definition tfib_E_asan_report_exp_store8 : Z := 0x5878c.
Definition tfib_A_asan_report_store16 : Z := 0x5878c.  Definition tfib_E_asan_report_store16 : Z := 0x587dc.
Definition tfib_A_asan_report_exp_store16 : Z := 0x587dc.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5882c.
Definition tfib_A_asan_report_load_n : Z := 0x5882c.  Definition tfib_E_asan_report_load_n : Z := 0x5887c.
Definition tfib_A_asan_report_exp_load_n : Z := 0x5887c.  Definition tfib_E_asan_report_exp_load_n : Z := 0x588cc.
Definition tfib_A_asan_report_store_n : Z := 0x588cc.  Definition tfib_E_asan_report_store_n : Z := 0x5891c.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5891c.  Definition tfib_E_asan_report_exp_store_n : Z := 0x5896c.
Definition tfib_A_InitializeHighMemEnd : Z := 0x5896c.  Definition tfib_E_InitializeHighMemEnd : Z := 0x589ec.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x589ec.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58da0.
Definition tfib_A_AsanInitInternal : Z := 0x58e30.  Definition tfib_E_AsanInitInternal : Z := 0x590e4.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x590e4.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59184.
Definition tfib_A_thunk_59674 : Z := 0x5934c.  Definition tfib_E_thunk_59674 : Z := 0x59350.
Definition tfib_A_asan_init : Z := 0x59350.  Definition tfib_E_asan_init : Z := 0x593e4.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x593e4.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x593e8.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x593e8.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5944c.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x595c0.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x595c8.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5964c.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59974.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59974.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59b54.
Definition tfib_A_InitializeShadowMemory : Z := 0x59b54.  Definition tfib_E_InitializeShadowMemory : Z := 0x59e5c.
Definition tfib_A_SetMallocContextSize : Z := 0x59e5c.  Definition tfib_E_SetMallocContextSize : Z := 0x59e6c.
Definition tfib_A_GetMallocContextSize : Z := 0x59e6c.  Definition tfib_E_GetMallocContextSize : Z := 0x59e7c.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59e7c.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59fcc.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5a3ac.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5a64c.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5aab0.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5aae8.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5ad90.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5ad9c.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ad9c.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5ae28.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5ae28.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5ae90.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5ae90.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5af08.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5af08.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5af70.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5af70.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5b0bc.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5b348.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5b354.
Definition tfib_A_AsanThread_Create : Z := 0x5b4d4.  Definition tfib_E_AsanThread_Create : Z := 0x5b670.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b6cc.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b8e4.
Definition tfib_A_GetCurrentThread : Z := 0x5b8e4.  Definition tfib_E_GetCurrentThread : Z := 0x5b904.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5b904.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5baa8.
Definition tfib_A_AsanThread_stack_top : Z := 0x5baa8.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bb00.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bb00.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bb58.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bb58.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bd88.
Definition tfib_A_AsanThread_Init : Z := 0x5bd88.  Definition tfib_E_AsanThread_Init : Z := 0x5c17c.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c17c.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c288.
Definition tfib_A_CreateMainThread : Z := 0x5c2bc.  Definition tfib_E_CreateMainThread : Z := 0x5c3cc.
Definition tfib_A_SetCurrentThread : Z := 0x5c3cc.  Definition tfib_E_SetCurrentThread : Z := 0x5c4ac.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c6b0.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c7ec.
Definition tfib_A_weak_default_hook_ret : Z := 0x5d4c0.  Definition tfib_E_weak_default_hook_ret : Z := 0x5d4c4.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5d4cc.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5d70c.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5d960.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5dab8.
Definition tfib_A_internal_allocator_getter : Z := 0x5dca4.  Definition tfib_E_internal_allocator_getter : Z := 0x5dcb0.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5dcb0.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ddfc.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ddfc.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5de48.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5de48.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5de54.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5de84.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5de90.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5de90.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5de9c.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5de9c.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5deac.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5deb8.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e184.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e184.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e544.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5f4a0.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5f4ac.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f4ac.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f584.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f584.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f620.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fb44.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fb88.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5fb88.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5fbac.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5fe00.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5ff14.
Definition tfib_A_RunMallocHooks : Z := 0x600b8.  Definition tfib_E_RunMallocHooks : Z := 0x60170.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60170.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60174.
Definition tfib_A_RunFreeHooks : Z := 0x60174.  Definition tfib_E_RunFreeHooks : Z := 0x60220.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x60220.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x60228.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x60228.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x6022c.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60254.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x602a0.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60564.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x607a4.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60da0.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60db8.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60db8.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x60efc.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60efc.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60f04.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x6124c.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x624f0.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x624f0.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62514.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x629c8.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62cd8.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62cd8.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62e1c.
Definition tfib_A_FlagParser_ParseString : Z := 0x62e1c.  Definition tfib_E_FlagParser_ParseString : Z := 0x62f10.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x630a4.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63104.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63104.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63144.
Definition tfib_A_internal_atoll : Z := 0x63144.  Definition tfib_E_internal_atoll : Z := 0x63230.
Definition tfib_A_internal_simple_strtoll : Z := 0x63230.  Definition tfib_E_internal_simple_strtoll : Z := 0x6338c.
Definition tfib_A_internal_memchr : Z := 0x6338c.  Definition tfib_E_internal_memchr : Z := 0x633ac.
Definition tfib_A_internal_memcmp : Z := 0x633ac.  Definition tfib_E_internal_memcmp : Z := 0x633e4.
Definition tfib_A_internal_memcpy : Z := 0x633e4.  Definition tfib_E_internal_memcpy : Z := 0x63408.
Definition tfib_A_internal_memmove : Z := 0x63408.  Definition tfib_E_internal_memmove : Z := 0x63460.
Definition tfib_A_internal_memset : Z := 0x63460.  Definition tfib_E_internal_memset : Z := 0x634c0.
Definition tfib_A_internal_strcspn : Z := 0x634c0.  Definition tfib_E_internal_strcspn : Z := 0x63514.
Definition tfib_A_internal_strcmp : Z := 0x63514.  Definition tfib_E_internal_strcmp : Z := 0x63548.
Definition tfib_A_internal_strdup : Z := 0x63548.  Definition tfib_E_internal_strdup : Z := 0x635b4.
Definition tfib_A_internal_strlen : Z := 0x635b4.  Definition tfib_E_internal_strlen : Z := 0x635d0.
Definition tfib_A_internal_strncmp : Z := 0x635d0.  Definition tfib_E_internal_strncmp : Z := 0x63614.
Definition tfib_A_internal_strchr : Z := 0x63614.  Definition tfib_E_internal_strchr : Z := 0x63660.
Definition tfib_A_internal_strchrnul : Z := 0x63660.  Definition tfib_E_internal_strchrnul : Z := 0x636a8.
Definition tfib_A_internal_strrchr : Z := 0x636a8.  Definition tfib_E_internal_strrchr : Z := 0x636e8.
Definition tfib_A_internal_strnlen : Z := 0x63818.  Definition tfib_E_internal_strnlen : Z := 0x63848.
Definition tfib_A_internal_strncpy : Z := 0x6388c.  Definition tfib_E_internal_strncpy : Z := 0x638fc.
Definition tfib_A_internal_strstr : Z := 0x638fc.  Definition tfib_E_internal_strstr : Z := 0x63990.
Definition tfib_A_mem_is_zero : Z := 0x63990.  Definition tfib_E_mem_is_zero : Z := 0x63a44.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a44.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a54.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63a54.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63c34.
Definition tfib_A_internal_iserror : Z := 0x63c40.  Definition tfib_E_internal_iserror : Z := 0x63c60.
Definition tfib_A_internal_mmap : Z := 0x63c60.  Definition tfib_E_internal_mmap : Z := 0x63c6c.
Definition tfib_A_internal_munmap : Z := 0x63c6c.  Definition tfib_E_internal_munmap : Z := 0x63c78.
Definition tfib_A_internal_mprotect : Z := 0x63c78.  Definition tfib_E_internal_mprotect : Z := 0x63c88.
Definition tfib_A_internal_madvise : Z := 0x63c88.  Definition tfib_E_internal_madvise : Z := 0x63cb4.
Definition tfib_A_internal_close : Z := 0x63cb4.  Definition tfib_E_internal_close : Z := 0x63cc0.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63cc0.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63ce4.
Definition tfib_A_internal_read : Z := 0x63ce4.  Definition tfib_E_internal_read : Z := 0x63d1c.
Definition tfib_A_internal_write : Z := 0x63d1c.  Definition tfib_E_internal_write : Z := 0x63d54.
Definition tfib_A_internal_ftruncate : Z := 0x63d54.  Definition tfib_E_internal_ftruncate : Z := 0x63d8c.
Definition tfib_A_internal_dup : Z := 0x63d8c.  Definition tfib_E_internal_dup : Z := 0x63d98.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63d98.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63da8.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63da8.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63dc0.
Definition tfib_A_internal_sched_yield : Z := 0x63dc0.  Definition tfib_E_internal_sched_yield : Z := 0x63dcc.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63dcc.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63e18.
Definition tfib_A_internal_execve : Z := 0x63e18.  Definition tfib_E_internal_execve : Z := 0x63e24.
Definition tfib_A_internal_exit_exit_group : Z := 0x63e24.  Definition tfib_E_internal_exit_exit_group : Z := 0x63e38.
Definition tfib_A_FileExists_newfstatat : Z := 0x63e38.  Definition tfib_E_FileExists_newfstatat : Z := 0x63eb8.
Definition tfib_A_DirExists_newfstatat : Z := 0x63eb8.  Definition tfib_E_DirExists_newfstatat : Z := 0x63f1c.
Definition tfib_A_GetTid_gettid : Z := 0x63f1c.  Definition tfib_E_GetTid_gettid : Z := 0x63f28.
Definition tfib_A_GetEnv : Z := 0x63f28.  Definition tfib_E_GetEnv : Z := 0x64058.
Definition tfib_A_FutexWait : Z := 0x6415c.  Definition tfib_E_FutexWait : Z := 0x64180.
Definition tfib_A_FutexWake : Z := 0x64180.  Definition tfib_E_FutexWake : Z := 0x641a4.
Definition tfib_A_internal_ptrace : Z := 0x641a4.  Definition tfib_E_internal_ptrace : Z := 0x641b0.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x641b0.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x641c0.
Definition tfib_A_internal_getpid : Z := 0x641c0.  Definition tfib_E_internal_getpid : Z := 0x641cc.
Definition tfib_A_internal_getppid : Z := 0x641cc.  Definition tfib_E_internal_getppid : Z := 0x641d8.
Definition tfib_A_internal_prctl : Z := 0x641d8.  Definition tfib_E_internal_prctl : Z := 0x641e4.
Definition tfib_A_internal_sigaltstack : Z := 0x641e4.  Definition tfib_E_internal_sigaltstack : Z := 0x641f0.
Definition tfib_A_internal_fork_clone : Z := 0x641f0.  Definition tfib_E_internal_fork_clone : Z := 0x64208.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64208.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64334.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6450c.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x64908.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64a74.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64b8c.
Definition tfib_A_GetPageSizeCached : Z := 0x64b8c.  Definition tfib_E_GetPageSizeCached : Z := 0x64b94.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64b94.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64c40.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64c40.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64d60.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64e28.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64ea8.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x64ea8.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x64f04.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64f04.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64fd0.
Definition tfib_A_thunk_653ec : Z := 0x650cc.  Definition tfib_E_thunk_653ec : Z := 0x650d0.
Definition tfib_A_CheckASLR : Z := 0x650d0.  Definition tfib_E_CheckASLR : Z := 0x650d4.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65320.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65324.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x65324.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x65330.
Definition tfib_A_MmapOrDie : Z := 0x65330.  Definition tfib_E_MmapOrDie : Z := 0x6543c.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6543c.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x654b0.
Definition tfib_A_UnmapOrDie : Z := 0x654b0.  Definition tfib_E_UnmapOrDie : Z := 0x6552c.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6552c.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6563c.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65868.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x6596c.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x6596c.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x65978.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65978.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65af0.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65af0.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65afc.
Definition tfib_A_thunk_66008 : Z := 0x65ce8.  Definition tfib_E_thunk_66008 : Z := 0x65cec.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6600c.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66218.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x667d0.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x667dc.
Definition tfib_A_Printf : Z := 0x667e0.  Definition tfib_E_Printf : Z := 0x6682c.
Definition tfib_A_SharedPrintfCode : Z := 0x6682c.  Definition tfib_E_SharedPrintfCode : Z := 0x66888.
Definition tfib_A_Report : Z := 0x66888.  Definition tfib_E_Report : Z := 0x668d4.
Definition tfib_A_SuppressionContext_ctor : Z := 0x683cc.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68428.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68428.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68664.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68664.  Definition tfib_E_SuppressionContext_Parse : Z := 0x68988.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68f28.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68ff8.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x68ff8.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69348.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69348.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x69358.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69594.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x695d8.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x695d8.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69638.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69638.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69ab0.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a370.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a694.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a69c.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a7a0.
Definition tfib_A_AddDieCallback : Z := 0x6af50.  Definition tfib_E_AddDieCallback : Z := 0x6afd8.
Definition tfib_A_Die : Z := 0x6b09c.  Definition tfib_E_Die : Z := 0x6b15c.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b15c.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b168.
Definition tfib_A_CheckFailed : Z := 0x6b168.  Definition tfib_E_CheckFailed : Z := 0x6b220.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b878.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6b970.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6b970.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6ba9c.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bcc4.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bd40.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6bd74.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c05c.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6c05c.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6c060.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c060.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6c450.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6c450.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6c520.
Definition tfib_A_AndroidLogInit : Z := 0x6c904.  Definition tfib_E_AndroidLogInit : Z := 0x6c908.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c938.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6c980.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c980.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6cbcc.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6cbcc.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6cbd0.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6cbd0.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6ccdc.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6ccdc.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6cde0.
Definition tfib_A_thunk_6d37c : Z := 0x6d05c.  Definition tfib_E_thunk_6d37c : Z := 0x6d060.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d104.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d124.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d124.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d1c4.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6d210.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6d214.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d250.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d314.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d314.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d39c.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d39c.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d414.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d414.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d4f8.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d5b4.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d6e8.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6d920.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6da50.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6da50.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6dab0.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6dab0.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6db7c.
Definition tfib_A_MprotectNoAccess : Z := 0x6db90.  Definition tfib_E_MprotectNoAccess : Z := 0x6dbb0.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6dbb0.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6dcfc.
Definition tfib_A_MmapFixedOrDie : Z := 0x6dcfc.  Definition tfib_E_MmapFixedOrDie : Z := 0x6dd0c.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x6f504.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x6f548.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6f548.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6f578.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6f9ac.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6fad0.
Definition tfib_A_StackStore_Alloc : Z := 0x6fad0.  Definition tfib_E_StackStore_Alloc : Z := 0x6fc04.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x704b8.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x7056c.

Definition tfib_A_StackDepotPut : Z := 0x71fa8.  Definition tfib_E_StackDepotPut : Z := 0x71fc8.
Definition tfib_A_StackDepotBase_Put : Z := 0x71fc8.  Definition tfib_E_StackDepotBase_Put : Z := 0x7224c.
Definition tfib_A_StackDepotBase_Get : Z := 0x7224c.  Definition tfib_E_StackDepotBase_Get : Z := 0x7235c.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x7273c.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x727cc.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x727cc.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x728cc.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x7292c.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x72934.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72934.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72a94.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72a94.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72b08.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72f90.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x730a8.
Definition tfib_A_thunk_762d8 : Z := 0x760f4.  Definition tfib_E_thunk_762d8 : Z := 0x760f8.
Definition tfib_A_thunk_77ab0 : Z := 0x778cc.  Definition tfib_E_thunk_77ab0 : Z := 0x778d0.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x792f8.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x793b4.
Definition tfib_A_Unwind_Trace_callback : Z := 0x793b4.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7948c.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x7948c.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x79700.
Definition tfib_A_lsan_flags_init_helper : Z := 0x79a2c.  Definition tfib_E_lsan_flags_init_helper : Z := 0x79a70.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79a70.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79e40.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a110.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a1c8.
Definition tfib_A_thunk_7b6f8 : Z := 0x7b520.  Definition tfib_E_thunk_7b6f8 : Z := 0x7b524.
Definition tfib_A_lsan_register_root_region : Z := 0x7c12c.  Definition tfib_E_lsan_register_root_region : Z := 0x7c45c.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c45c.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c8e4.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7c8e4.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7c8f0.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7f4a8.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7f4c0.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f844.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f8c0.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f8c0.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7f970.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f970.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f988.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f988.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fad0.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7fad0.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7fadc.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7fadc.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7fae8.
Definition tfib_A_main : Z := 0x7fae8.  Definition tfib_E_main : Z := 0x7fdac.
Definition tfib_A_target_alloc_init : Z := 0x7fdac.  Definition tfib_E_target_alloc_init : Z := 0x7fdb0.
Definition tfib_A_target_alloc_count : Z := 0x7fdb0.  Definition tfib_E_target_alloc_count : Z := 0x7fdb8.
Definition tfib_A_target_run : Z := 0x7fdb8.  Definition tfib_E_target_run : Z := 0x7ff40.
Definition tfib_A_emit_printf : Z := 0x7ff40.  Definition tfib_E_emit_printf : Z := 0x7ff88.


Definition tfib_A_asan_module_ctor : Z := 0x82e04.  Definition tfib_E_asan_module_ctor : Z := 0x82e3c.








Definition tfib_A_asan_module_dtor : Z := 0x82e3c.  Definition tfib_E_asan_module_dtor : Z := 0x82e6c.






Definition tfib_A_extenddftf2 : Z := 0x835b8.  Definition tfib_E_extenddftf2 : Z := 0x83748.
Definition tfib_A_sysconf : Z := 0x89e30.  Definition tfib_E_sysconf : Z := 0x8a058.
Definition tfib_A_init : Z := 0x8a058.  Definition tfib_E_init : Z := 0x8a05c.
Definition tfib_A_init_libc : Z := 0x8a05c.  Definition tfib_E_init_libc : Z := 0x8a288.
Definition tfib_A_libc_start_init : Z := 0x8a288.  Definition tfib_E_libc_start_init : Z := 0x8a2d4.
Definition tfib_A_libc_start_main : Z := 0x8a2d4.  Definition tfib_E_libc_start_main : Z := 0x8a334.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8a334.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8a37c.
Definition tfib_A_init_tls : Z := 0x8a454.  Definition tfib_E_init_tls : Z := 0x8a704.
Definition tfib_A_init_ssp : Z := 0x8a704.  Definition tfib_E_init_ssp : Z := 0x8a764.
Definition tfib_A_stack_chk_fail : Z := 0x8a764.  Definition tfib_E_stack_chk_fail : Z := 0x8a76c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8a7b4.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8a848.
Definition tfib_A_Exit : Z := 0x8a848.  Definition tfib_E_Exit : Z := 0x8a864.
Definition tfib_A_funcs_on_exit : Z := 0x8a894.  Definition tfib_E_funcs_on_exit : Z := 0x8a95c.
Definition tfib_A_fini_stub_ret : Z := 0x8a95c.  Definition tfib_E_fini_stub_ret : Z := 0x8a960.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8a960.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8aa24.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x8aa24.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x8aa28.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8aa28.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8aa2c.
Definition tfib_A_libc_exit_fini : Z := 0x8aa2c.  Definition tfib_E_libc_exit_fini : Z := 0x8aa78.
Definition tfib_A_exit : Z := 0x8aa78.  Definition tfib_E_exit : Z := 0x8aaec.
Definition tfib_A_open : Z := 0x8acec.  Definition tfib_E_open : Z := 0x8add0.
Definition tfib_A_syscall_ret : Z := 0x8add0.  Definition tfib_E_syscall_ret : Z := 0x8ae08.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8ae08.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8afb0.
Definition tfib_A_calloc : Z := 0x8b574.  Definition tfib_E_calloc : Z := 0x8b6ac.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8b6ac.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8b6b0.
Definition tfib_A_libc_free : Z := 0x8b6b0.  Definition tfib_E_libc_free : Z := 0x8b87c.
Definition tfib_A_get_meta : Z := 0x8b87c.  Definition tfib_E_get_meta : Z := 0x8b98c.
Definition tfib_A_alloc_meta : Z := 0x8bd64.  Definition tfib_E_alloc_meta : Z := 0x8c03c.
Definition tfib_A_libc_malloc_impl : Z := 0x8c03c.  Definition tfib_E_libc_malloc_impl : Z := 0x8c3ac.
Definition tfib_A_alloc_slot : Z := 0x8c3ac.  Definition tfib_E_alloc_slot : Z := 0x8cc50.
Definition tfib_A_enframe : Z := 0x8cc50.  Definition tfib_E_enframe : Z := 0x8cda0.
Definition tfib_A_malloc_allzerop : Z := 0x8cda0.  Definition tfib_E_malloc_allzerop : Z := 0x8cf18.
Definition tfib_A_getrlimit : Z := 0x8e2e8.  Definition tfib_E_getrlimit : Z := 0x8e3e0.
Definition tfib_A_getrusage : Z := 0x8e3e0.  Definition tfib_E_getrusage : Z := 0x8e408.
Definition tfib_A_setrlimit : Z := 0x8e408.  Definition tfib_E_setrlimit : Z := 0x8e4d0.
Definition tfib_A_mmap : Z := 0x8e8f8.  Definition tfib_E_mmap : Z := 0x8e9e4.
Definition tfib_A_mprotect : Z := 0x8e9e4.  Definition tfib_E_mprotect : Z := 0x8ea2c.
Definition tfib_A_munmap : Z := 0x8eb00.  Definition tfib_E_munmap : Z := 0x8eb48.
Definition tfib_A_sched_yield : Z := 0x8ee0c.  Definition tfib_E_sched_yield : Z := 0x8ee30.
Definition tfib_A_raise_tkill_path : Z := 0x8ee8c.  Definition tfib_E_raise_tkill_path : Z := 0x8ef04.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8ef04.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8f0d8.
Definition tfib_A_musl_sigaltstack : Z := 0x8f1d0.  Definition tfib_E_musl_sigaltstack : Z := 0x8f25c.
Definition tfib_A_fprintf : Z := 0x8f838.  Definition tfib_E_fprintf : Z := 0x8f89c.

Definition tfib_A_lockfile : Z := 0x8f89c.  Definition tfib_E_lockfile : Z := 0x8f998.
Definition tfib_A_unlockfile : Z := 0x8f998.  Definition tfib_E_unlockfile : Z := 0x8f9f8.



Definition tfib_A_stdio_read : Z := 0x8f588.  Definition tfib_E_stdio_read : Z := 0x8f6a0.
Definition tfib_A_stdio_write : Z := 0x8f6a8.  Definition tfib_E_stdio_write : Z := 0x8f838.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8f558.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8f55c.
Definition tfib_A_stdio_close : Z := 0x8f55c.  Definition tfib_E_stdio_close : Z := 0x8f588.
Definition tfib_A_fwritex : Z := 0x8fe2c.  Definition tfib_E_fwritex : Z := 0x8ff64.
Definition tfib_A_musl_fwrite : Z := 0x8ff64.  Definition tfib_E_musl_fwrite : Z := 0x9001c.
Definition tfib_A_towrite : Z := 0x9001c.  Definition tfib_E_towrite : Z := 0x90070.
Definition tfib_A_stdio_exit : Z := 0x8fc88.  Definition tfib_E_stdio_exit : Z := 0x8fe2c.
Definition tfib_A_ofl_lock : Z := 0x90070.  Definition tfib_E_ofl_lock : Z := 0x900a0.

Definition tfib_A_musl_vfprintf : Z := 0x901ec.  Definition tfib_E_musl_vfprintf : Z := 0x9039c.
Definition tfib_A_printf_core : Z := 0x9039c.  Definition tfib_E_printf_core : Z := 0x911cc.
Definition tfib_A_pop_arg : Z := 0x911cc.  Definition tfib_E_pop_arg : Z := 0x91300.
Definition tfib_A_pad : Z := 0x91300.  Definition tfib_E_pad : Z := 0x913d4.
Definition tfib_A_fmt_fp : Z := 0x913d4.  Definition tfib_E_fmt_fp : Z := 0x92a9c.
Definition tfib_A_thunk_931e0 : Z := 0x8b1c8.  Definition tfib_E_thunk_931e0 : Z := 0x8b1cc.
Definition tfib_A_musl_wctomb : Z := 0x8ec74.  Definition tfib_E_musl_wctomb : Z := 0x8ec98.
Definition tfib_A_musl_wcrtomb : Z := 0x8eb48.  Definition tfib_E_musl_wcrtomb : Z := 0x8ec74.
Definition tfib_A_fpclassifyl : Z := 0x8d6f0.  Definition tfib_E_fpclassifyl : Z := 0x8d734.
Definition tfib_A_letf2 : Z := 0x83434.  Definition tfib_E_letf2 : Z := 0x834fc.
Definition tfib_A_multf3 : Z := 0x8cff0.  Definition tfib_E_multf3 : Z := 0x8d6f0.
Definition tfib_A_floatsitf : Z := 0x8d734.  Definition tfib_E_floatsitf : Z := 0x8d83c.
Definition tfib_A_scalbn : Z := 0x8e140.  Definition tfib_E_scalbn : Z := 0x8e1d8.
Definition tfib_A_subtf3 : Z := 0x839c8.  Definition tfib_E_subtf3 : Z := 0x839d8.
Definition tfib_A_addtf3 : Z := 0x839d8.  Definition tfib_E_addtf3 : Z := 0x841a4.
Definition tfib_A_fe_getround : Z := 0x841a4.  Definition tfib_E_fe_getround : Z := 0x841d4.
Definition tfib_A_fixunstfsi : Z := 0x92aa4.  Definition tfib_E_fixunstfsi : Z := 0x92b38.
Definition tfib_A_floatunsitf : Z := 0x92b38.  Definition tfib_E_floatunsitf : Z := 0x92c24.
Definition tfib_A_fixtfsi : Z := 0x8e1d8.  Definition tfib_E_fixtfsi : Z := 0x8e280.
Definition tfib_A_divtf3 : Z := 0x8d83c.  Definition tfib_E_divtf3 : Z := 0x8e140.
Definition tfib_A_musl_vprintf : Z := 0x932fc.  Definition tfib_E_musl_vprintf : Z := 0x93318.
Definition tfib_A_stdout_write : Z := 0x900ac.  Definition tfib_E_stdout_write : Z := 0x9014c.

Definition tfib_A_musl_memcmp : Z := 0x9397c.  Definition tfib_E_musl_memcmp : Z := 0x939ac.
Definition tfib_A_musl_memcpy : Z := 0x939ac.  Definition tfib_E_musl_memcpy : Z := 0x93db0.
Definition tfib_A_musl_memset : Z := 0x93db0.  Definition tfib_E_musl_memset : Z := 0x93ea8.
Definition tfib_A_musl_strchr : Z := 0x93ea8.  Definition tfib_E_musl_strchr : Z := 0x93ee4.
Definition tfib_A_strchrnul : Z := 0x93ee4.  Definition tfib_E_strchrnul : Z := 0x93fc4.
Definition tfib_A_musl_strlen : Z := 0x93ffc.  Definition tfib_E_musl_strlen : Z := 0x9408c.
Definition tfib_A_musl_strnlen : Z := 0x94238.  Definition tfib_E_musl_strnlen : Z := 0x9427c.
Definition tfib_A_musl_memchr : Z := 0x938b0.  Definition tfib_E_musl_memchr : Z := 0x9397c.
Definition tfib_A_lock : Z := 0x9427c.  Definition tfib_E_lock : Z := 0x94504.
Definition tfib_A_unlock : Z := 0x94504.  Definition tfib_E_unlock : Z := 0x94578.
Definition tfib_A_syscall_cp_c : Z := 0x94578.  Definition tfib_E_syscall_cp_c : Z := 0x9459c.
Definition tfib_A_syscall_cp_sccp : Z := 0x9459c.  Definition tfib_E_syscall_cp_sccp : Z := 0x945a0.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x945a0.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x945c4.
Definition tfib_A_pthread_atfork : Z := 0x945dc.  Definition tfib_E_pthread_atfork : Z := 0x94680.
Definition tfib_A_mremap : Z := 0x8ea2c.  Definition tfib_E_mremap : Z := 0x8eb00.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x95654.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x95670.
Definition tfib_A_pthread_key_create : Z := 0x959fc.  Definition tfib_E_pthread_key_create : Z := 0x95ad0.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x95d74.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x95e18.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x95e18.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x95f34.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x95f34.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x95f60.
Definition tfib_A_pthread_setspecific : Z := 0x95f98.  Definition tfib_E_pthread_setspecific : Z := 0x95fcc.
Definition tfib_A_set_thread_area : Z := 0x95fd4.  Definition tfib_E_set_thread_area : Z := 0x95fe0.
Definition tfib_A_thunk_96f9c : Z := 0x95fcc.  Definition tfib_E_thunk_96f9c : Z := 0x95fd4.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x96900.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x969b8.
Definition tfib_A_close : Z := 0x98fd0.  Definition tfib_E_close : Z := 0x99024.
Definition tfib_A_musl_read : Z := 0x990b0.  Definition tfib_E_musl_read : Z := 0x990e4.
Definition tfib_A_vm_wait : Z := 0x96610.  Definition tfib_E_vm_wait : Z := 0x96660.
Definition tfib_D_str_sealed : Z := 0x11869.
Definition tfib_D_init_array_0_3 : Z := 0x9a0e8.
Definition tfib_D_fini_array_0_1 : Z := 0x9a108.
Definition tfib_D_GOT_common_flags : Z := 0x9a820.
Definition tfib_D_GOT_flags : Z := 0x9a828.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9a830.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9a838.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9a840.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9a848.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9b398.
Definition tfib_D_environ_musl : Z := 0x9b4c0.
Definition tfib_D_REAL_read : Z := 0x9c560.
Definition tfib_D_REAL_memcpy : Z := 0x9c688.
Definition tfib_D_REAL_memset : Z := 0x9c690.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9fd98.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa0bf8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa33f8.
Definition tfib_D_asan_inited : Z := 0xa40d8.
Definition tfib_D_replace_intrin_cached : Z := 0xa40d9.
Definition tfib_D_kHighMemEnd : Z := 0xa40e0.
Definition tfib_D_kMidMemBeg : Z := 0xa40e8.
Definition tfib_D_kMidMemEnd : Z := 0xa40f0.
Definition tfib_D_malloc_context_size : Z := 0xa40fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x134f28.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f6620.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f8000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30634.
Definition tfib_at_rw_lo : Z := 0x9c000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63460.
Definition tfib_at_x_imemcpy : Z := 0x633e4.
Definition tfib_at_x_memset : Z := 0x93db0.
Definition tfib_at_x_memcpy : Z := 0x939ac.
Definition tfib_at_x_memiszero : Z := 0x63990.
Definition tfib_at_x_istrncpy : Z := 0x6388c.
Definition tfib_at_x_sealed : Z := 0x11869.
Definition tfib_at_x_popfree : Z := 0x36a20.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8a094.
Definition tfib_at_x_envscan_k : Z := 0x8a0a0.
Definition tfib_at_x_pnscan : Z := 0x8a158.
Definition tfib_at_x_pnscan_k : Z := 0x8a164.
Definition tfib_at_stops_more : list Z := (0x34694 :: 0x35cb8 :: 0x5376c :: 0x59b24 :: 0x59b38 :: 0x59b4c :: 0x5f4dc :: 0x5f5ac :: 0x6cad8 :: 0x6d9e4 :: 0x6db74 :: 0x778cc :: nil)%list.
