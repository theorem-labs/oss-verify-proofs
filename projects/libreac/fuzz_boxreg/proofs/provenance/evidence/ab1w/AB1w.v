(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the function-range table (the tfib_A_ and tfib_E_ rows) regenerated from fuzz_boxreg.asan's symtab (st_value, st_value+st_size); merged cgif rows split, rows without a boxreg counterpart dropped; see NOTES.md. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2268c.
Definition tfib_text_lo : Z := 0x2ff58.  Definition tfib_text_hi : Z := 0x97920.
Definition tfib_init_array_lo : Z := 0x98920.  Definition tfib_init_array_hi : Z := 0x98940.
Definition tfib_fini_array_lo : Z := 0x98940.  Definition tfib_fini_array_hi : Z := 0x98950.
Definition tfib_preinit_array_lo : Z := 0x98950.  Definition tfib_preinit_array_hi : Z := 0x98958.
Definition tfib_data_rel_ro_lo : Z := 0x98958.  Definition tfib_data_rel_ro_hi : Z := 0x98e58.
Definition tfib_got_lo : Z := 0x98e58.  Definition tfib_got_hi : Z := 0x99bb0.
Definition tfib_data_lo : Z := 0x9abb0.  Definition tfib_data_hi : Z := 0x9d770.
Definition tfib_asan_globals_lo : Z := 0x9d770.  Definition tfib_asan_globals_hi : Z := 0x9d8b0.
Definition tfib_bss_lo : Z := 0x9d8c0.  Definition tfib_bss_hi : Z := 0x5f57f0.
Definition tfib_tbss_lo : Z := 0x97920.  Definition tfib_tbss_hi : Z := 0x97934.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f6000.
Definition tfib_entry : Z := 0x2ff58.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2ff58.  Definition tfib_E_start : Z := 0x2ffa0.
Definition tfib_A_do_init : Z := 0x2ffa0.  Definition tfib_E_do_init : Z := 0x30014.
Definition tfib_A_do_fini : Z := 0x30014.  Definition tfib_E_do_fini : Z := 0x300a4.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x300a4.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x300e0.
Definition tfib_A_InitializeAllocator : Z := 0x30250.  Definition tfib_E_InitializeAllocator : Z := 0x30268.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30268.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x303d4.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x30930.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30a8c.
Definition tfib_A_asan_free : Z := 0x30e60.  Definition tfib_E_asan_free : Z := 0x30e88.
Definition tfib_A_Allocator_Deallocate : Z := 0x30e88.  Definition tfib_E_Allocator_Deallocate : Z := 0x31140.
Definition tfib_A_asan_malloc : Z := 0x31140.  Definition tfib_E_asan_malloc : Z := 0x3119c.
Definition tfib_A_Allocator_Allocate : Z := 0x3119c.  Definition tfib_E_Allocator_Allocate : Z := 0x31b24.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x3225c.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x323a0.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x3248c.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x324e8.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x324e8.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32738.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32738.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3282c.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x3282c.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x32914.
Definition tfib_A_Quarantine_Recycle : Z := 0x32d48.  Definition tfib_E_Quarantine_Recycle : Z := 0x32f2c.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x32f2c.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x330b0.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x331e8.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x3346c.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x3346c.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x335ec.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x335ec.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x337b4.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x337b4.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33980.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x33980.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x33a20.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33a20.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33b24.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33e4c.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33f94.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x33f94.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x33fcc.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34764.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34a4c.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35124.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x3529c.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x3529c.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x3544c.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x3544c.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35630.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35630.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x35908.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x35908.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35d80.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35d80.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35e80.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35e80.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36188.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36188.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x364f8.
Definition tfib_A_RZSize2Log : Z := 0x364f8.  Definition tfib_E_RZSize2Log : Z := 0x36610.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x36918.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x36a14.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36a14.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36afc.
Definition tfib_A_AsanActivate : Z := 0x36afc.  Definition tfib_E_AsanActivate : Z := 0x36bd8.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x370b4.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x3719c.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3bc54.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bd2c.
Definition tfib_A_FakeStack_Create : Z := 0x3bd2c.  Definition tfib_E_FakeStack_Create : Z := 0x3be18.
Definition tfib_A_FakeStack_Allocate : Z := 0x3c0d4.  Definition tfib_E_FakeStack_Allocate : Z := 0x3c3bc.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c4f0.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c520.
(* cgif __asan_stack_malloc class 1 (0x3c8a4+0x190) has no twin; fuzz_boxreg.asan has only __asan_stack_malloc_3 0x3c520+0x1ac (107 insns), a new instance (CORE-PREP 1(a)) *)
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3c520.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3c6cc.
(* cgif __asan_stack_malloc class 2 (0x3ca34+0x19c): fuzz_boxreg.asan has no __asan_stack_malloc_2; dropped (CORE-PREP 1(a)) *)
Definition tfib_A_MemToShadow_3c6cc : Z := 0x3c6cc.  Definition tfib_E_MemToShadow_3c6cc : Z := 0x3c808.
Definition tfib_A_asan_InitializeFlags : Z := 0x3c808.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d834.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3df40.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ed5c.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3ed5c.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f328.
Definition tfib_A_asan_register_globals : Z := 0x3f328.  Definition tfib_E_asan_register_globals : Z := 0x3f394.
Definition tfib_A_asan_unregister_globals : Z := 0x3f394.  Definition tfib_E_asan_unregister_globals : Z := 0x3f3fc.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x3fa7c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x3fcec.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x3fcec.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x3fff4.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40768.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x408b8.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x412d4.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x413ec.
Definition tfib_A_strlen : Z := 0x413ec.  Definition tfib_E_strlen : Z := 0x413f0.
Definition tfib_A_strnlen : Z := 0x413f0.  Definition tfib_E_strnlen : Z := 0x413f4.
Definition tfib_A_strcmp : Z := 0x413f4.  Definition tfib_E_strcmp : Z := 0x413f8.
Definition tfib_A_strchr : Z := 0x413fc.  Definition tfib_E_strchr : Z := 0x41400.
Definition tfib_A_memcmp : Z := 0x41400.  Definition tfib_E_memcmp : Z := 0x41404.
Definition tfib_A_interceptor_trampoline_bcmp : Z := 0x41404.  Definition tfib_E_interceptor_trampoline_bcmp : Z := 0x41408.
Definition tfib_A_memchr : Z := 0x41408.  Definition tfib_E_memchr : Z := 0x4140c.
Definition tfib_A_frexpl : Z := 0x4140c.  Definition tfib_E_frexpl : Z := 0x41410.
Definition tfib_A_read : Z := 0x41410.  Definition tfib_E_read : Z := 0x41414.
Definition tfib_A_fwrite : Z := 0x41414.  Definition tfib_E_fwrite : Z := 0x41418.
Definition tfib_A_time : Z := 0x41418.  Definition tfib_E_time : Z := 0x4141c.
Definition tfib_A_gmtime_r : Z := 0x4141c.  Definition tfib_E_gmtime_r : Z := 0x41420.
Definition tfib_A_vprintf : Z := 0x41420.  Definition tfib_E_vprintf : Z := 0x41424.
Definition tfib_A_vfprintf : Z := 0x41424.  Definition tfib_E_vfprintf : Z := 0x41428.
Definition tfib_A_vsnprintf : Z := 0x41428.  Definition tfib_E_vsnprintf : Z := 0x4142c.
Definition tfib_A_interceptor_trampoline_fprintf : Z := 0x4142c.  Definition tfib_E_interceptor_trampoline_fprintf : Z := 0x41430.
Definition tfib_A_interceptor_trampoline_snprintf : Z := 0x41430.  Definition tfib_E_interceptor_trampoline_snprintf : Z := 0x41434.
Definition tfib_A_clock_gettime : Z := 0x41434.  Definition tfib_E_clock_gettime : Z := 0x41438.
Definition tfib_A_wcrtomb : Z := 0x41438.  Definition tfib_E_wcrtomb : Z := 0x4143c.
Definition tfib_A_wctomb : Z := 0x4143c.  Definition tfib_E_wctomb : Z := 0x41440.
(* cgif merged row thunk_417cc (0x41940+0x8) = boxreg __interceptor_trampoline_strerror + __interceptor_trampoline__exit; split, rows named by those symbols *)
Definition tfib_A_interceptor_trampoline_strerror : Z := 0x41440.  Definition tfib_E_interceptor_trampoline_strerror : Z := 0x41444.
Definition tfib_A_interceptor_trampoline__exit : Z := 0x41444.  Definition tfib_E_interceptor_trampoline__exit : Z := 0x41448.
Definition tfib_A_pthread_attr_getstack : Z := 0x41448.  Definition tfib_E_pthread_attr_getstack : Z := 0x4144c.
Definition tfib_A_tls_get_addr_thunk : Z := 0x4144c.  Definition tfib_E_tls_get_addr_thunk : Z := 0x41450.
(* cgif fopen trampoline (0x41950+0x4): fuzz_boxreg.asan has no fopen; dropped *)
Definition tfib_A_interceptor_trampoline_fflush : Z := 0x41450.  Definition tfib_E_interceptor_trampoline_fflush : Z := 0x41454.
(* cgif fclose trampoline (0x41958+0x4): fuzz_boxreg.asan has no fclose; dropped *)
Definition tfib_A_interceptor_trampoline_sem_init : Z := 0x41454.  Definition tfib_E_interceptor_trampoline_sem_init : Z := 0x41458.
Definition tfib_A_interceptor_trampoline_sem_destroy : Z := 0x41458.  Definition tfib_E_interceptor_trampoline_sem_destroy : Z := 0x4145c.
Definition tfib_A_interceptor_trampoline_sem_wait : Z := 0x4145c.  Definition tfib_E_interceptor_trampoline_sem_wait : Z := 0x41460.
Definition tfib_A_interceptor_trampoline_sem_trywait : Z := 0x41460.  Definition tfib_E_interceptor_trampoline_sem_trywait : Z := 0x41464.
Definition tfib_A_sem_timedwait : Z := 0x41464.  Definition tfib_E_sem_timedwait : Z := 0x41468.
Definition tfib_A_interceptor_trampoline_sem_post : Z := 0x41468.  Definition tfib_E_interceptor_trampoline_sem_post : Z := 0x4146c.
Definition tfib_A_pthread_setcancelstate : Z := 0x4146c.  Definition tfib_E_pthread_setcancelstate : Z := 0x41470.
Definition tfib_A_send : Z := 0x41470.  Definition tfib_E_send : Z := 0x41474.
Definition tfib_A_sendto : Z := 0x41474.  Definition tfib_E_sendto : Z := 0x41478.
Definition tfib_A_sigaltstack : Z := 0x41478.  Definition tfib_E_sigaltstack : Z := 0x4147c.
Definition tfib_A_interceptor_trampoline_sigaction : Z := 0x4147c.  Definition tfib_E_interceptor_trampoline_sigaction : Z := 0x41480.
Definition tfib_A_icpt_strlen : Z := 0x41480.  Definition tfib_E_icpt_strlen : Z := 0x41714.
Definition tfib_A_icpt_strnlen : Z := 0x41714.  Definition tfib_E_icpt_strnlen : Z := 0x419a8.
Definition tfib_A_icpt_strcmp : Z := 0x419ac.  Definition tfib_E_icpt_strcmp : Z := 0x41edc.
Definition tfib_A_icpt_strchr : Z := 0x424b8.  Definition tfib_E_icpt_strchr : Z := 0x42798.
Definition tfib_A_icpt_memcmp : Z := 0x43030.  Definition tfib_E_icpt_memcmp : Z := 0x430ec.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x430ec.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x431a8.
Definition tfib_A_icpt_memchr : Z := 0x431a8.  Definition tfib_E_icpt_memchr : Z := 0x43478.
Definition tfib_A_icpt_frexpl : Z := 0x43478.  Definition tfib_E_icpt_frexpl : Z := 0x436f0.
Definition tfib_A_icpt_read : Z := 0x436f0.  Definition tfib_E_icpt_read : Z := 0x43960.
Definition tfib_A_icpt_fwrite : Z := 0x43960.  Definition tfib_E_icpt_fwrite : Z := 0x43bd4.
Definition tfib_A_icpt_time : Z := 0x43bd4.  Definition tfib_E_icpt_time : Z := 0x43e70.
Definition tfib_A_icpt_gmtime_r : Z := 0x44078.  Definition tfib_E_icpt_gmtime_r : Z := 0x442b8.
Definition tfib_A_icpt_vprintf : Z := 0x442b8.  Definition tfib_E_icpt_vprintf : Z := 0x44354.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44354.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44e1c.
Definition tfib_A_icpt_vfprintf : Z := 0x44e1c.  Definition tfib_E_icpt_vfprintf : Z := 0x44ed0.
Definition tfib_A_icpt_vsnprintf : Z := 0x44ed0.  Definition tfib_E_icpt_vsnprintf : Z := 0x451e8.
Definition tfib_A_interceptor_fprintf : Z := 0x451e8.  Definition tfib_E_interceptor_fprintf : Z := 0x452c0.
Definition tfib_A_icpt_clock_gettime : Z := 0x45364.  Definition tfib_E_icpt_clock_gettime : Z := 0x455bc.
Definition tfib_A_icpt_wcrtomb : Z := 0x455bc.  Definition tfib_E_icpt_wcrtomb : Z := 0x45b2c.
Definition tfib_A_icpt_wctomb : Z := 0x45b2c.  Definition tfib_E_icpt_wctomb : Z := 0x45e88.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45f54.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4633c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46348.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x463c4.
(* cgif __interceptor_fopen (0x462f0+0x46c): fuzz_boxreg.asan has no fopen interceptor; dropped *)
(* cgif __interceptor_fclose (0x46868+0x1ac): fuzz_boxreg.asan has no fclose interceptor; dropped *)
Definition tfib_A_icpt_sem_timedwait : Z := 0x465d0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x46868.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46898.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46ac0.
Definition tfib_A_icpt_send : Z := 0x46ac0.  Definition tfib_E_icpt_send : Z := 0x46d74.
Definition tfib_A_icpt_sendto : Z := 0x46d74.  Definition tfib_E_icpt_sendto : Z := 0x47038.
Definition tfib_A_icpt_sigaltstack : Z := 0x47038.  Definition tfib_E_icpt_sigaltstack : Z := 0x47294.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47368.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47518.
Definition tfib_A_format_get_value_size : Z := 0x47518.  Definition tfib_E_format_get_value_size : Z := 0x476b0.
Definition tfib_A_ioctl_table_fill : Z := 0x4825c.  Definition tfib_E_ioctl_table_fill : Z := 0x50f34.
Definition tfib_A_Sort_ioctl_desc : Z := 0x50f34.  Definition tfib_E_Sort_ioctl_desc : Z := 0x51090.
Definition tfib_A_memset : Z := 0x51090.  Definition tfib_E_memset : Z := 0x51094.
Definition tfib_A_memcpy : Z := 0x51094.  Definition tfib_E_memcpy : Z := 0x51098.
Definition tfib_A_asan_memcpy : Z := 0x51098.  Definition tfib_E_asan_memcpy : Z := 0x51534.
Definition tfib_A_asan_memset : Z := 0x51534.  Definition tfib_E_asan_memset : Z := 0x51774.
Definition tfib_A_icpt_memset : Z := 0x51774.  Definition tfib_E_icpt_memset : Z := 0x51a64.
Definition tfib_A_icpt_memcpy : Z := 0x51a64.  Definition tfib_E_icpt_memcpy : Z := 0x52054.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52054.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5208c.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x5208c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52090.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52090.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52094.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52094.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x520f4.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52140.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x5227c.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x5227c.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52280.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52280.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x523e8.
Definition tfib_A_free : Z := 0x523e8.  Definition tfib_E_free : Z := 0x523ec.
Definition tfib_A_malloc : Z := 0x523ec.  Definition tfib_E_malloc : Z := 0x523f0.
Definition tfib_A_icpt_free : Z := 0x523f0.  Definition tfib_E_icpt_free : Z := 0x525c0.
Definition tfib_A_icpt_malloc : Z := 0x525c0.  Definition tfib_E_icpt_malloc : Z := 0x5271c.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x5271c.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x527e8.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x527e8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x527ec.
Definition tfib_A_TwoLevelMap_u8_Create : Z := 0x527ec.  Definition tfib_E_TwoLevelMap_u8_Create : Z := 0x528ec.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x52c14.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x52d80.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53268.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53278.
Definition tfib_A_CanPoisonMemory : Z := 0x53278.  Definition tfib_E_CanPoisonMemory : Z := 0x5328c.
Definition tfib_A_PoisonShadow : Z := 0x5328c.  Definition tfib_E_PoisonShadow : Z := 0x53788.
Definition tfib_A_MemToShadow_checked : Z := 0x53788.  Definition tfib_E_MemToShadow_checked : Z := 0x538c4.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x538c4.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53a64.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x53a64.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x53be4.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53c14.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53f58.
Definition tfib_A_AsanTSDInit : Z := 0x54378.  Definition tfib_E_AsanTSDInit : Z := 0x543f4.
Definition tfib_A_AsanTSDGet : Z := 0x543f4.  Definition tfib_E_AsanTSDGet : Z := 0x54434.
Definition tfib_A_AsanTSDSet : Z := 0x54434.  Definition tfib_E_AsanTSDSet : Z := 0x54474.
Definition tfib_A_PlatformTSDDtor : Z := 0x54474.  Definition tfib_E_PlatformTSDDtor : Z := 0x544f8.
Definition tfib_A_InstallAtForkHandler : Z := 0x544f8.  Definition tfib_E_InstallAtForkHandler : Z := 0x54514.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54574.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x545b8.
Definition tfib_A_ReportDeadlySignal : Z := 0x54cd0.  Definition tfib_E_ReportDeadlySignal : Z := 0x54edc.
Definition tfib_A_ReportDoubleFree : Z := 0x555e4.  Definition tfib_E_ReportDoubleFree : Z := 0x55874.
Definition tfib_A_ReportGenericError : Z := 0x57150.  Definition tfib_E_ReportGenericError : Z := 0x57a0c.
Definition tfib_A_AsanInited : Z := 0x58198.  Definition tfib_E_AsanInited : Z := 0x581b0.
Definition tfib_A_asan_report_load1 : Z := 0x581b0.  Definition tfib_E_asan_report_load1 : Z := 0x58200.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58200.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58250.
Definition tfib_A_asan_report_load2 : Z := 0x58250.  Definition tfib_E_asan_report_load2 : Z := 0x582a0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x582a0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x582f0.
Definition tfib_A_asan_report_load4 : Z := 0x582f0.  Definition tfib_E_asan_report_load4 : Z := 0x58340.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58340.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58390.
Definition tfib_A_asan_report_load8 : Z := 0x58390.  Definition tfib_E_asan_report_load8 : Z := 0x583e0.
Definition tfib_A_asan_report_exp_load8 : Z := 0x583e0.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58430.
Definition tfib_A_asan_report_load16 : Z := 0x58430.  Definition tfib_E_asan_report_load16 : Z := 0x58480.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58480.  Definition tfib_E_asan_report_exp_load16 : Z := 0x584d0.
Definition tfib_A_asan_report_store1 : Z := 0x584d0.  Definition tfib_E_asan_report_store1 : Z := 0x58520.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58520.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58570.
Definition tfib_A_asan_report_store2 : Z := 0x58570.  Definition tfib_E_asan_report_store2 : Z := 0x585c0.
Definition tfib_A_asan_report_exp_store2 : Z := 0x585c0.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58610.
Definition tfib_A_asan_report_store4 : Z := 0x58610.  Definition tfib_E_asan_report_store4 : Z := 0x58660.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58660.  Definition tfib_E_asan_report_exp_store4 : Z := 0x586b0.
Definition tfib_A_asan_report_store8 : Z := 0x586b0.  Definition tfib_E_asan_report_store8 : Z := 0x58700.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58700.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58750.
Definition tfib_A_asan_report_store16 : Z := 0x58750.  Definition tfib_E_asan_report_store16 : Z := 0x587a0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x587a0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x587f0.
Definition tfib_A_asan_report_load_n : Z := 0x587f0.  Definition tfib_E_asan_report_load_n : Z := 0x58840.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58840.  Definition tfib_E_asan_report_exp_load_n : Z := 0x58890.
Definition tfib_A_asan_report_store_n : Z := 0x58890.  Definition tfib_E_asan_report_store_n : Z := 0x588e0.
Definition tfib_A_asan_report_exp_store_n : Z := 0x588e0.  Definition tfib_E_asan_report_exp_store_n : Z := 0x58930.
Definition tfib_A_InitializeHighMemEnd : Z := 0x58930.  Definition tfib_E_InitializeHighMemEnd : Z := 0x589b0.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x589b0.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58d64.
Definition tfib_A_AsanInitInternal : Z := 0x58df4.  Definition tfib_E_AsanInitInternal : Z := 0x590a8.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x590a8.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59148.
Definition tfib_A_asan_set_death_callback : Z := 0x59310.  Definition tfib_E_asan_set_death_callback : Z := 0x59314.
Definition tfib_A_asan_init : Z := 0x59314.  Definition tfib_E_asan_init : Z := 0x593a8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x593a8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x593ac.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x593ac.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x59410.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59584.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x5958c.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59610.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59938.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59938.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59b18.
Definition tfib_A_InitializeShadowMemory : Z := 0x59b18.  Definition tfib_E_InitializeShadowMemory : Z := 0x59e20.
Definition tfib_A_SetMallocContextSize : Z := 0x59e20.  Definition tfib_E_SetMallocContextSize : Z := 0x59e30.
Definition tfib_A_GetMallocContextSize : Z := 0x59e30.  Definition tfib_E_GetMallocContextSize : Z := 0x59e40.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59e40.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59f90.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5a370.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5a610.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5aa74.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5aaac.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5ad54.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5ad60.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ad60.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5adec.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5adec.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5ae54.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5ae54.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5aecc.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5aecc.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5af34.
Definition tfib_A_IsAddrSuppressed : Z := 0x5af34.  Definition tfib_E_IsAddrSuppressed : Z := 0x5b080.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5b30c.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5b318.
Definition tfib_A_AsanThread_Create : Z := 0x5b498.  Definition tfib_E_AsanThread_Create : Z := 0x5b634.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b690.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b8a8.
Definition tfib_A_GetCurrentThread : Z := 0x5b8a8.  Definition tfib_E_GetCurrentThread : Z := 0x5b8c8.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5b8c8.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5ba6c.
Definition tfib_A_AsanThread_stack_top : Z := 0x5ba6c.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bac4.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bac4.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bb1c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bb1c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bd4c.
Definition tfib_A_AsanThread_Init : Z := 0x5bd4c.  Definition tfib_E_AsanThread_Init : Z := 0x5c140.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c140.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c24c.
Definition tfib_A_CreateMainThread : Z := 0x5c280.  Definition tfib_E_CreateMainThread : Z := 0x5c390.
Definition tfib_A_SetCurrentThread : Z := 0x5c390.  Definition tfib_E_SetCurrentThread : Z := 0x5c470.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c674.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c7b0.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5d484.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5d488.
Definition tfib_A_GetAsanThreadContext : Z := 0x5d490.  Definition tfib_E_GetAsanThreadContext : Z := 0x5d6d0.
Definition tfib_A_internal_allocator : Z := 0x5d924.  Definition tfib_E_internal_allocator : Z := 0x5da7c.
Definition tfib_A_internal_allocator_getter : Z := 0x5dc68.  Definition tfib_E_internal_allocator_getter : Z := 0x5dc74.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5dc74.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5ddc0.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ddc0.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5de0c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5de0c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5de18.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5de48.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5de54.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5de54.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5de60.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5de60.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5de70.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5de7c.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e148.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e148.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e508.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5f464.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5f470.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f470.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f548.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f548.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f5e4.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fb08.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fb4c.
Definition tfib_A_DecreaseTotalMmap : Z := 0x5fb4c.  Definition tfib_E_DecreaseTotalMmap : Z := 0x5fb70.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5fdc4.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5fed8.
Definition tfib_A_RunMallocHooks : Z := 0x6007c.  Definition tfib_E_RunMallocHooks : Z := 0x60134.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60134.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60138.
Definition tfib_A_RunFreeHooks : Z := 0x60138.  Definition tfib_E_RunFreeHooks : Z := 0x601e4.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x601e4.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x601ec.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x601ec.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x601f0.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60218.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60264.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60528.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60768.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60d64.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60d7c.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x60d7c.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x60ec0.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60ec0.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60ec8.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x61210.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x624b4.
Definition tfib_A_InitializeCommonFlags : Z := 0x624b4.  Definition tfib_E_InitializeCommonFlags : Z := 0x624d8.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x6298c.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62c9c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62c9c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62de0.
Definition tfib_A_FlagParser_ParseString : Z := 0x62de0.  Definition tfib_E_FlagParser_ParseString : Z := 0x62ed4.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63068.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x630c8.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x630c8.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63108.
Definition tfib_A_internal_atoll : Z := 0x63108.  Definition tfib_E_internal_atoll : Z := 0x631f4.
Definition tfib_A_internal_simple_strtoll : Z := 0x631f4.  Definition tfib_E_internal_simple_strtoll : Z := 0x63350.
Definition tfib_A_internal_memchr : Z := 0x63350.  Definition tfib_E_internal_memchr : Z := 0x63370.
Definition tfib_A_internal_memcmp : Z := 0x63370.  Definition tfib_E_internal_memcmp : Z := 0x633a8.
Definition tfib_A_internal_memcpy : Z := 0x633a8.  Definition tfib_E_internal_memcpy : Z := 0x633cc.
Definition tfib_A_internal_memmove : Z := 0x633cc.  Definition tfib_E_internal_memmove : Z := 0x63424.
Definition tfib_A_internal_memset : Z := 0x63424.  Definition tfib_E_internal_memset : Z := 0x63484.
Definition tfib_A_internal_strcspn : Z := 0x63484.  Definition tfib_E_internal_strcspn : Z := 0x634d8.
Definition tfib_A_internal_strcmp : Z := 0x634d8.  Definition tfib_E_internal_strcmp : Z := 0x6350c.
Definition tfib_A_internal_strdup : Z := 0x6350c.  Definition tfib_E_internal_strdup : Z := 0x63578.
Definition tfib_A_internal_strlen : Z := 0x63578.  Definition tfib_E_internal_strlen : Z := 0x63594.
Definition tfib_A_internal_strncmp : Z := 0x63594.  Definition tfib_E_internal_strncmp : Z := 0x635d8.
Definition tfib_A_internal_strchr : Z := 0x635d8.  Definition tfib_E_internal_strchr : Z := 0x63624.
Definition tfib_A_internal_strchrnul : Z := 0x63624.  Definition tfib_E_internal_strchrnul : Z := 0x6366c.
Definition tfib_A_internal_strrchr : Z := 0x6366c.  Definition tfib_E_internal_strrchr : Z := 0x636ac.
Definition tfib_A_internal_strnlen : Z := 0x637dc.  Definition tfib_E_internal_strnlen : Z := 0x6380c.
Definition tfib_A_internal_strncpy : Z := 0x63850.  Definition tfib_E_internal_strncpy : Z := 0x638c0.
Definition tfib_A_internal_strstr : Z := 0x638c0.  Definition tfib_E_internal_strstr : Z := 0x63954.
Definition tfib_A_mem_is_zero : Z := 0x63954.  Definition tfib_E_mem_is_zero : Z := 0x63a08.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a08.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a18.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63a18.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63bf8.
Definition tfib_A_internal_iserror : Z := 0x63c04.  Definition tfib_E_internal_iserror : Z := 0x63c24.
Definition tfib_A_internal_mmap : Z := 0x63c24.  Definition tfib_E_internal_mmap : Z := 0x63c30.
Definition tfib_A_internal_munmap : Z := 0x63c30.  Definition tfib_E_internal_munmap : Z := 0x63c3c.
Definition tfib_A_internal_mprotect : Z := 0x63c3c.  Definition tfib_E_internal_mprotect : Z := 0x63c4c.
Definition tfib_A_internal_madvise : Z := 0x63c4c.  Definition tfib_E_internal_madvise : Z := 0x63c78.
Definition tfib_A_internal_close : Z := 0x63c78.  Definition tfib_E_internal_close : Z := 0x63c84.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63c84.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63ca8.
Definition tfib_A_internal_read : Z := 0x63ca8.  Definition tfib_E_internal_read : Z := 0x63ce0.
Definition tfib_A_internal_write : Z := 0x63ce0.  Definition tfib_E_internal_write : Z := 0x63d18.
Definition tfib_A_internal_ftruncate : Z := 0x63d18.  Definition tfib_E_internal_ftruncate : Z := 0x63d50.
Definition tfib_A_internal_dup : Z := 0x63d50.  Definition tfib_E_internal_dup : Z := 0x63d5c.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63d5c.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63d6c.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63d6c.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63d84.
Definition tfib_A_internal_sched_yield : Z := 0x63d84.  Definition tfib_E_internal_sched_yield : Z := 0x63d90.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63d90.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63ddc.
Definition tfib_A_internal_execve : Z := 0x63ddc.  Definition tfib_E_internal_execve : Z := 0x63de8.
Definition tfib_A_internal_exit_exit_group : Z := 0x63de8.  Definition tfib_E_internal_exit_exit_group : Z := 0x63dfc.
Definition tfib_A_FileExists_newfstatat : Z := 0x63dfc.  Definition tfib_E_FileExists_newfstatat : Z := 0x63e7c.
Definition tfib_A_DirExists_newfstatat : Z := 0x63e7c.  Definition tfib_E_DirExists_newfstatat : Z := 0x63ee0.
Definition tfib_A_GetTid_gettid : Z := 0x63ee0.  Definition tfib_E_GetTid_gettid : Z := 0x63eec.
Definition tfib_A_GetEnv : Z := 0x63eec.  Definition tfib_E_GetEnv : Z := 0x6401c.
Definition tfib_A_FutexWait : Z := 0x64120.  Definition tfib_E_FutexWait : Z := 0x64144.
Definition tfib_A_FutexWake : Z := 0x64144.  Definition tfib_E_FutexWake : Z := 0x64168.
Definition tfib_A_internal_ptrace : Z := 0x64168.  Definition tfib_E_internal_ptrace : Z := 0x64174.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64174.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64184.
Definition tfib_A_internal_getpid : Z := 0x64184.  Definition tfib_E_internal_getpid : Z := 0x64190.
Definition tfib_A_internal_getppid : Z := 0x64190.  Definition tfib_E_internal_getppid : Z := 0x6419c.
Definition tfib_A_internal_prctl : Z := 0x6419c.  Definition tfib_E_internal_prctl : Z := 0x641a8.
Definition tfib_A_internal_sigaltstack : Z := 0x641a8.  Definition tfib_E_internal_sigaltstack : Z := 0x641b4.
Definition tfib_A_internal_fork_clone : Z := 0x641b4.  Definition tfib_E_internal_fork_clone : Z := 0x641cc.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x641cc.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x642f8.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x644d0.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x648cc.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64a38.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64b50.
Definition tfib_A_GetPageSize : Z := 0x64b50.  Definition tfib_E_GetPageSize : Z := 0x64b58.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64b58.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64c04.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64c04.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64d24.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64dec.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64e6c.
Definition tfib_A_GetHandleSignalMode : Z := 0x64e6c.  Definition tfib_E_GetHandleSignalMode : Z := 0x64ec8.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64ec8.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64f94.
Definition tfib_A_InitializePlatformEarly : Z := 0x65090.  Definition tfib_E_InitializePlatformEarly : Z := 0x65094.
Definition tfib_A_CheckASLR : Z := 0x65094.  Definition tfib_E_CheckASLR : Z := 0x65098.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x652e4.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x652e8.
Definition tfib_A_ErrorIsOOM : Z := 0x652e8.  Definition tfib_E_ErrorIsOOM : Z := 0x652f4.
Definition tfib_A_MmapOrDie : Z := 0x652f4.  Definition tfib_E_MmapOrDie : Z := 0x65400.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65400.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65474.
Definition tfib_A_UnmapOrDie : Z := 0x65474.  Definition tfib_E_UnmapOrDie : Z := 0x654f0.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x654f0.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65600.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6582c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x65930.
Definition tfib_A_MmapFixedOrDie : Z := 0x65930.  Definition tfib_E_MmapFixedOrDie : Z := 0x6593c.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6593c.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65ab4.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65ab4.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65ac0.
Definition tfib_A_CloseFile : Z := 0x65cac.  Definition tfib_E_CloseFile : Z := 0x65cb0.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x65fd0.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x661dc.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66794.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x667a0.
Definition tfib_A_Printf : Z := 0x667a4.  Definition tfib_E_Printf : Z := 0x667f0.
Definition tfib_A_SharedPrintfCode : Z := 0x667f0.  Definition tfib_E_SharedPrintfCode : Z := 0x6684c.
Definition tfib_A_Report : Z := 0x6684c.  Definition tfib_E_Report : Z := 0x66898.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68390.  Definition tfib_E_SuppressionContext_ctor : Z := 0x683ec.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x683ec.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68628.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68628.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6894c.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68eec.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68fbc.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x68fbc.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6930c.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6930c.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6931c.
Definition tfib_A_ThreadContextBase_ctor : Z := 0x69558.  Definition tfib_E_ThreadContextBase_ctor : Z := 0x6959c.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6959c.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x695fc.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x695fc.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69a74.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a334.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a658.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a660.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a764.
Definition tfib_A_AddDieCallback : Z := 0x6af14.  Definition tfib_E_AddDieCallback : Z := 0x6af9c.
Definition tfib_A_Die : Z := 0x6b060.  Definition tfib_E_Die : Z := 0x6b120.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b120.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b12c.
Definition tfib_A_CheckFailed : Z := 0x6b12c.  Definition tfib_E_CheckFailed : Z := 0x6b1e4.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b83c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6b934.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6b934.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6ba60.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bc88.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bd04.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6bd38.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c020.
Definition tfib_A_InitTlsSize : Z := 0x6c020.  Definition tfib_E_InitTlsSize : Z := 0x6c024.
Definition tfib_A_GetTls : Z := 0x6c024.  Definition tfib_E_GetTls : Z := 0x6c414.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c414.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6c4e4.
Definition tfib_A_AndroidLogInit : Z := 0x6c8c8.  Definition tfib_E_AndroidLogInit : Z := 0x6c8cc.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c8fc.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6c944.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c944.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6cb90.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6cb90.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6cb94.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6cb94.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6cca0.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6cca0.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6cda4.
Definition tfib_A_GetThreadSelf : Z := 0x6d020.  Definition tfib_E_GetThreadSelf : Z := 0x6d024.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d0c8.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d0e8.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d0e8.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d188.
Definition tfib_A_Atexit : Z := 0x6d1d4.  Definition tfib_E_Atexit : Z := 0x6d1d8.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d214.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d2d8.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d2d8.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d360.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d360.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d3d8.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d3d8.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d4bc.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d578.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d6ac.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6d8e4.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6da14.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6da14.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6da74.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6da74.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6db40.
Definition tfib_A_MmapNoAccess : Z := 0x6db54.  Definition tfib_E_MmapNoAccess : Z := 0x6db74.
(* cgif merged row MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser (0x6e0b8+0x14c) = boxreg ReservedAddressRange::Map + SealedRepairReservation; split *)
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6db74.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6dbe8.
Definition tfib_A_SealedRepairReservation : Z := 0x6dbe8.  Definition tfib_E_SealedRepairReservation : Z := 0x6dcc0.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6dcc0.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6dcd0.
Definition tfib_A_InitializeCoverage : Z := 0x6f4c8.  Definition tfib_E_InitializeCoverage : Z := 0x6f50c.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6f50c.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6f53c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6f970.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6fa94.
Definition tfib_A_StackStore_Alloc : Z := 0x6fa94.  Definition tfib_E_StackStore_Alloc : Z := 0x6fbc8.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x7047c.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70530.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71c84.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x71ce0.
Definition tfib_A_StackDepotPut : Z := 0x71f6c.  Definition tfib_E_StackDepotPut : Z := 0x71f8c.
Definition tfib_A_StackDepotBase_Put : Z := 0x71f8c.  Definition tfib_E_StackDepotBase_Put : Z := 0x72210.
Definition tfib_A_StackDepotGet : Z := 0x72210.  Definition tfib_E_StackDepotGet : Z := 0x72320.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x72700.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x72790.
Definition tfib_A_TwoLevelMap_StackDepotNode_Create : Z := 0x72790.  Definition tfib_E_TwoLevelMap_StackDepotNode_Create : Z := 0x72890.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x728f0.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x728f8.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x728f8.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72a58.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72a58.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72acc.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72f54.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7306c.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x760b8.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x760bc.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x77890.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x77894.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x792bc.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79378.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79378.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79450.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x79450.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x796c4.
Definition tfib_A_lsan_flags_init_helper : Z := 0x799f0.  Definition tfib_E_lsan_flags_init_helper : Z := 0x79a34.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79a34.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79e04.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a0d4.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a18c.
Definition tfib_A_DoRecoverableLeakCheckVoid : Z := 0x7b4e4.  Definition tfib_E_DoRecoverableLeakCheckVoid : Z := 0x7b4e8.
Definition tfib_A_lsan_register_root_region : Z := 0x7c0f0.  Definition tfib_E_lsan_register_root_region : Z := 0x7c420.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c420.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c8a8.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7c8a8.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7c8b4.
Definition tfib_A_DisabledInThisThread : Z := 0x7f46c.  Definition tfib_E_DisabledInThisThread : Z := 0x7f484.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f808.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f884.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f884.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7f934.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f934.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f94c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f94c.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fa94.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7fa94.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7faa0.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7faa0.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7faac.
Definition tfib_A_main : Z := 0x7faac.  Definition tfib_E_main : Z := 0x7fd70.
Definition tfib_A_target_alloc_init : Z := 0x7fd70.  Definition tfib_E_target_alloc_init : Z := 0x7fd74.
Definition tfib_A_target_alloc_count : Z := 0x7fd74.  Definition tfib_E_target_alloc_count : Z := 0x7fd7c.
(* cgif merged row target_run (0x802c0+0x188) = boxreg target_run + oft_exit_guard; split *)
Definition tfib_A_target_run : Z := 0x7fd7c.  Definition tfib_E_target_run : Z := 0x7fed4.
Definition tfib_A_oft_exit_guard : Z := 0x7fed4.  Definition tfib_E_oft_exit_guard : Z := 0x7ff04.
Definition tfib_A_emit_printf : Z := 0x7ff04.  Definition tfib_E_emit_printf : Z := 0x7ff4c.
(* cgif program function LLVMFuzzerTestOneInput (0x80490+0x6a8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function read_frameconfig (0x80b38+0x864): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_asan_module_ctor : Z := 0x815b4.  Definition tfib_E_asan_module_ctor : Z := 0x815ec.
(* cgif program function cgif_newgif (0x81404+0x614): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_writecb_or_freeCGIF (0x81a18+0xd0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function freeFrame_or_freeCGIF (0x81ae8+0x80): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_addframe (0x81b68+0xdb4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cmpPixel (0x8291c+0x1e4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function flushFrame (0x82b00+0x1394): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function freeFrame (0x83e94+0xc0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_close (0x83f54+0x224): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_asan_module_dtor : Z := 0x815ec.  Definition tfib_E_asan_module_dtor : Z := 0x8161c.
(* cgif program function cgif_raw_newgif (0x84178+0x71c): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_raw_addframe (0x84894+0xd28): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function LZW_GenerateStream (0x855bc+0x10c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_raw_close (0x86684+0xe0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function create_byte_list (0x86764+0x2c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function create_byte_list_block (0x86a2c+0x1a0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_extenddftf2 : Z := 0x81f44.  Definition tfib_E_extenddftf2 : Z := 0x820d4.
Definition tfib_A_sysconf : Z := 0x87d24.  Definition tfib_E_sysconf : Z := 0x87f4c.
Definition tfib_A_init : Z := 0x87f4c.  Definition tfib_E_init : Z := 0x87f50.
Definition tfib_A_init_libc : Z := 0x87f50.  Definition tfib_E_init_libc : Z := 0x8817c.
Definition tfib_A_libc_start_init : Z := 0x8817c.  Definition tfib_E_libc_start_init : Z := 0x881c8.
Definition tfib_A_libc_start_main : Z := 0x881c8.  Definition tfib_E_libc_start_main : Z := 0x88228.
Definition tfib_A_libc_start_main_stage2 : Z := 0x88228.  Definition tfib_E_libc_start_main_stage2 : Z := 0x88270.
Definition tfib_A_init_tls : Z := 0x88348.  Definition tfib_E_init_tls : Z := 0x885f8.
Definition tfib_A_init_ssp : Z := 0x885f8.  Definition tfib_E_init_ssp : Z := 0x88658.
Definition tfib_A_stack_chk_fail : Z := 0x88658.  Definition tfib_E_stack_chk_fail : Z := 0x88660.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x886a8.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8873c.
Definition tfib_A_Exit : Z := 0x8873c.  Definition tfib_E_Exit : Z := 0x88758.
Definition tfib_A_funcs_on_exit : Z := 0x88788.  Definition tfib_E_funcs_on_exit : Z := 0x88850.
Definition tfib_A_cxa_finalize : Z := 0x88850.  Definition tfib_E_cxa_finalize : Z := 0x88854.
Definition tfib_A_cxa_atexit_atexit : Z := 0x88854.  Definition tfib_E_cxa_atexit_atexit : Z := 0x88918.
Definition tfib_A_call : Z := 0x88918.  Definition tfib_E_call : Z := 0x8891c.
Definition tfib_A_fini : Z := 0x8891c.  Definition tfib_E_fini : Z := 0x88920.
Definition tfib_A_libc_exit_fini : Z := 0x88920.  Definition tfib_E_libc_exit_fini : Z := 0x8896c.
Definition tfib_A_exit : Z := 0x8896c.  Definition tfib_E_exit : Z := 0x889e0.
Definition tfib_A_open : Z := 0x88be0.  Definition tfib_E_open : Z := 0x88cc4.
Definition tfib_A_syscall_ret : Z := 0x88cc4.  Definition tfib_E_syscall_ret : Z := 0x88cfc.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x88cfc.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x88ea4.
Definition tfib_A_calloc : Z := 0x89468.  Definition tfib_E_calloc : Z := 0x895a0.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x895a0.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x895a4.
Definition tfib_A_libc_free : Z := 0x895a4.  Definition tfib_E_libc_free : Z := 0x89770.
Definition tfib_A_get_meta : Z := 0x89770.  Definition tfib_E_get_meta : Z := 0x89880.
Definition tfib_A_alloc_meta : Z := 0x89c58.  Definition tfib_E_alloc_meta : Z := 0x89f30.
Definition tfib_A_libc_malloc_impl : Z := 0x89f30.  Definition tfib_E_libc_malloc_impl : Z := 0x8a2a0.
Definition tfib_A_alloc_slot : Z := 0x8a2a0.  Definition tfib_E_alloc_slot : Z := 0x8ab44.
Definition tfib_A_enframe : Z := 0x8ab44.  Definition tfib_E_enframe : Z := 0x8ac94.
Definition tfib_A_malloc_allzerop : Z := 0x8ac94.  Definition tfib_E_malloc_allzerop : Z := 0x8ae0c.
Definition tfib_A_getrlimit : Z := 0x8cabc.  Definition tfib_E_getrlimit : Z := 0x8cbb4.
Definition tfib_A_getrusage : Z := 0x8cbb4.  Definition tfib_E_getrusage : Z := 0x8cbdc.
Definition tfib_A_setrlimit : Z := 0x8cbdc.  Definition tfib_E_setrlimit : Z := 0x8cca4.
Definition tfib_A_mmap : Z := 0x8d0cc.  Definition tfib_E_mmap : Z := 0x8d1b8.
Definition tfib_A_mprotect : Z := 0x8d1b8.  Definition tfib_E_mprotect : Z := 0x8d200.
Definition tfib_A_munmap : Z := 0x8d2d4.  Definition tfib_E_munmap : Z := 0x8d31c.
Definition tfib_A_sched_yield : Z := 0x8d5e0.  Definition tfib_E_sched_yield : Z := 0x8d604.
Definition tfib_A_raise_tkill_path : Z := 0x8d660.  Definition tfib_E_raise_tkill_path : Z := 0x8d6d8.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8d6d8.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8d8ac.
Definition tfib_A_musl_sigaltstack : Z := 0x8d9a4.  Definition tfib_E_musl_sigaltstack : Z := 0x8da30.
Definition tfib_A_dprintf : Z := 0x8e00c.  Definition tfib_E_dprintf : Z := 0x8e070.
(* cgif musl fclose (0x92ee4+0xcc): not linked into fuzz_boxreg.asan; dropped *)
Definition tfib_A_lockfile : Z := 0x8e070.  Definition tfib_E_lockfile : Z := 0x8e16c.
Definition tfib_A_unlockfile : Z := 0x8e16c.  Definition tfib_E_unlockfile : Z := 0x8e1cc.
(* cgif musl fopen (0x93540+0xdc): not linked into fuzz_boxreg.asan; dropped *)
(* cgif musl __fmodeflags (0x9361c+0xb4): not linked into fuzz_boxreg.asan; dropped *)
(* cgif musl __fdopen (0x929c4+0x1d8): not linked into fuzz_boxreg.asan; dropped *)
Definition tfib_A_stdio_read : Z := 0x8dd5c.  Definition tfib_E_stdio_read : Z := 0x8de74.
Definition tfib_A_stdio_write : Z := 0x8de7c.  Definition tfib_E_stdio_write : Z := 0x8e00c.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8dd2c.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8dd30.
Definition tfib_A_stdio_close : Z := 0x8dd30.  Definition tfib_E_stdio_close : Z := 0x8dd5c.
Definition tfib_A_fwritex : Z := 0x8e600.  Definition tfib_E_fwritex : Z := 0x8e738.
Definition tfib_A_musl_fwrite : Z := 0x8e738.  Definition tfib_E_musl_fwrite : Z := 0x8e7f0.
Definition tfib_A_towrite : Z := 0x8e7f0.  Definition tfib_E_towrite : Z := 0x8e844.
Definition tfib_A_stdio_exit : Z := 0x8e45c.  Definition tfib_E_stdio_exit : Z := 0x8e600.
Definition tfib_A_ofl_lock : Z := 0x8e844.  Definition tfib_E_ofl_lock : Z := 0x8e874.
(* cgif musl __ofl_add (0x93950+0x40): not linked into fuzz_boxreg.asan; dropped *)
Definition tfib_A_musl_vfprintf : Z := 0x8e9c0.  Definition tfib_E_musl_vfprintf : Z := 0x8eb70.
Definition tfib_A_printf_core : Z := 0x8eb70.  Definition tfib_E_printf_core : Z := 0x8f9a0.
Definition tfib_A_pop_arg : Z := 0x8f9a0.  Definition tfib_E_pop_arg : Z := 0x8fad4.
Definition tfib_A_pad : Z := 0x8fad4.  Definition tfib_E_pad : Z := 0x8fba8.
Definition tfib_A_fmt_fp : Z := 0x8fba8.  Definition tfib_E_fmt_fp : Z := 0x91270.
Definition tfib_A_lctrans : Z := 0x890bc.  Definition tfib_E_lctrans : Z := 0x890c0.
Definition tfib_A_musl_wctomb : Z := 0x8d448.  Definition tfib_E_musl_wctomb : Z := 0x8d46c.
Definition tfib_A_musl_wcrtomb : Z := 0x8d31c.  Definition tfib_E_musl_wcrtomb : Z := 0x8d448.
Definition tfib_A_fpclassifyl : Z := 0x8b6ac.  Definition tfib_E_fpclassifyl : Z := 0x8b6f0.
Definition tfib_A_letf2 : Z := 0x8aee4.  Definition tfib_E_letf2 : Z := 0x8afac.
Definition tfib_A_multf3 : Z := 0x8afac.  Definition tfib_E_multf3 : Z := 0x8b6ac.
Definition tfib_A_floatsitf : Z := 0x8bf08.  Definition tfib_E_floatsitf : Z := 0x8c010.
Definition tfib_A_scalbn : Z := 0x8c914.  Definition tfib_E_scalbn : Z := 0x8c9ac.
Definition tfib_A_subtf3 : Z := 0x8bef8.  Definition tfib_E_subtf3 : Z := 0x8bf08.
Definition tfib_A_addtf3 : Z := 0x8b6f0.  Definition tfib_E_addtf3 : Z := 0x8bebc.
Definition tfib_A_fe_getround : Z := 0x8bebc.  Definition tfib_E_fe_getround : Z := 0x8beec.
Definition tfib_A_fixunstfsi : Z := 0x91278.  Definition tfib_E_fixunstfsi : Z := 0x9130c.
Definition tfib_A_floatunsitf : Z := 0x9130c.  Definition tfib_E_floatunsitf : Z := 0x913f8.
Definition tfib_A_fixtfsi : Z := 0x8c9ac.  Definition tfib_E_fixtfsi : Z := 0x8ca54.
Definition tfib_A_divtf3 : Z := 0x8c010.  Definition tfib_E_divtf3 : Z := 0x8c914.
Definition tfib_A_musl_vprintf : Z := 0x91ad0.  Definition tfib_E_musl_vprintf : Z := 0x91aec.
Definition tfib_A_stdout_write : Z := 0x8e880.  Definition tfib_E_stdout_write : Z := 0x8e920.
Definition tfib_A_bcmp : Z := 0x92084.  Definition tfib_E_bcmp : Z := 0x92088.
Definition tfib_A_musl_memcmp : Z := 0x92154.  Definition tfib_E_musl_memcmp : Z := 0x92184.
Definition tfib_A_musl_memcpy : Z := 0x92184.  Definition tfib_E_musl_memcpy : Z := 0x92588.
Definition tfib_A_musl_memset : Z := 0x92588.  Definition tfib_E_musl_memset : Z := 0x92680.
Definition tfib_A_musl_strchr : Z := 0x92680.  Definition tfib_E_musl_strchr : Z := 0x926bc.
Definition tfib_A_strchrnul : Z := 0x926bc.  Definition tfib_E_strchrnul : Z := 0x9279c.
Definition tfib_A_musl_strlen : Z := 0x927d4.  Definition tfib_E_musl_strlen : Z := 0x92864.
Definition tfib_A_musl_strnlen : Z := 0x92a70.  Definition tfib_E_musl_strnlen : Z := 0x92ab4.
Definition tfib_A_musl_memchr : Z := 0x92088.  Definition tfib_E_musl_memchr : Z := 0x92154.
Definition tfib_A_lock : Z := 0x92ab4.  Definition tfib_E_lock : Z := 0x92d3c.
Definition tfib_A_unlock : Z := 0x92d3c.  Definition tfib_E_unlock : Z := 0x92db0.
Definition tfib_A_syscall_cp_c : Z := 0x92db0.  Definition tfib_E_syscall_cp_c : Z := 0x92dd4.
Definition tfib_A_syscall_cp_sccp : Z := 0x92dd4.  Definition tfib_E_syscall_cp_sccp : Z := 0x92dd8.
Definition tfib_A_tls_get_addr : Z := 0x92dd8.  Definition tfib_E_tls_get_addr : Z := 0x92dfc.
Definition tfib_A_pthread_atfork : Z := 0x92e14.  Definition tfib_E_pthread_atfork : Z := 0x92eb8.
Definition tfib_A_mremap : Z := 0x8d200.  Definition tfib_E_mremap : Z := 0x8d2d4.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x93e8c.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x93ea8.
Definition tfib_A_pthread_key_create : Z := 0x94234.  Definition tfib_E_pthread_key_create : Z := 0x94308.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x945ac.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x94650.
(* cgif merged row pthread_key_create_body_tsd_init (0x99700+0x11c) = boxreg __pthread_rwlock_wrlock + __pthread_rwlock_timedwrlock; split *)
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x94650.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x94658.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x94658.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x9476c.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x9476c.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x94798.
Definition tfib_A_pthread_setspecific : Z := 0x947d0.  Definition tfib_E_pthread_setspecific : Z := 0x94804.
Definition tfib_A_set_thread_area : Z := 0x9480c.  Definition tfib_E_set_thread_area : Z := 0x94818.
(* cgif merged row thunk_96f9c (0x998b4+0x8) = boxreg __pthread_testcancel + __testcancel; split, rows named by those symbols *)
Definition tfib_A_pthread_testcancel : Z := 0x94804.  Definition tfib_E_pthread_testcancel : Z := 0x94808.
Definition tfib_A_testcancel : Z := 0x94808.  Definition tfib_E_testcancel : Z := 0x9480c.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x95138.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x951f0.
Definition tfib_A_close : Z := 0x97808.  Definition tfib_E_close : Z := 0x9785c.
Definition tfib_A_musl_read : Z := 0x978e8.  Definition tfib_E_musl_read : Z := 0x9791c.
Definition tfib_A_vm_wait : Z := 0x94e48.  Definition tfib_E_vm_wait : Z := 0x94e98.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x98920.
Definition tfib_D_fini_array_0_1 : Z := 0x98940.
Definition tfib_D_GOT_common_flags : Z := 0x98ea8.
Definition tfib_D_GOT_flags : Z := 0x98eb0.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x98eb8.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x98ec0.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x98ec8.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x98ed0.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x99a20.
Definition tfib_D_environ_musl : Z := 0x99b48.
Definition tfib_D_REAL_read : Z := 0x9abf8.
Definition tfib_D_REAL_memcpy : Z := 0x9ad20.
Definition tfib_D_REAL_memset : Z := 0x9ad28.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9d918.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9e778.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa0f78.
Definition tfib_D_asan_inited : Z := 0xa1c58.
Definition tfib_D_replace_intrin_cached : Z := 0xa1c59.
Definition tfib_D_kHighMemEnd : Z := 0xa1c60.
Definition tfib_D_kMidMemBeg : Z := 0xa1c68.
Definition tfib_D_kMidMemEnd : Z := 0xa1c70.
Definition tfib_D_malloc_context_size : Z := 0xa1c7c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x132aa8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f41a0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f6000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2ff58.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63424.
Definition tfib_at_x_imemcpy : Z := 0x633a8.
Definition tfib_at_x_memset : Z := 0x92588.
Definition tfib_at_x_memcpy : Z := 0x92184.
Definition tfib_at_x_memiszero : Z := 0x63954.
Definition tfib_at_x_istrncpy : Z := 0x63850.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x36344.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x87f88.
Definition tfib_at_x_envscan_k : Z := 0x87f94.
Definition tfib_at_x_pnscan : Z := 0x8804c.
Definition tfib_at_x_pnscan_k : Z := 0x88058.
Definition tfib_at_stops_more : list Z := (0x33fb8 :: 0x355dc :: 0x53730 :: 0x59ae8 :: 0x59afc :: 0x59b10 :: 0x5f4a0 :: 0x5f570 :: 0x6ca9c :: 0x6d9a8 :: 0x6db38 :: 0x77890 :: nil)%list.
