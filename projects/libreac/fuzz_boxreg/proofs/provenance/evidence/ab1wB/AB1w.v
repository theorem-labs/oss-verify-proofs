(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the function-range table (the tfib_A_ and tfib_E_ rows) regenerated from fuzz_boxreg.asan's symtab (st_value, st_value+st_size); merged cgif rows split, rows without a boxreg counterpart dropped; see NOTES.md. *)
(* Modified by Theorem Labs, 2026-10: this is lib/B's copy, for the ASan+UBSan build fuzz_boxreg.asan-ubsan (sha256 7620eb05..., symbols 1d548458...). Every row keeps lib/A's name and is paired to that build BY SYMBOL and, where a name occurs more than once, BY CODE (instruction compare of the two builds); its two values are the asan-ubsan symbol's st_value and st_value + st_size. The section, image, entry and gp constants, the tfib_D_* cells and the tfib_at_* anchors are fuzz_boxreg.asan-ubsan's; see NOTES.md. *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2268c.
Definition tfib_text_lo : Z := 0x2ffb8.  Definition tfib_text_hi : Z := 0x97d40.
Definition tfib_init_array_lo : Z := 0x98d40.  Definition tfib_init_array_hi : Z := 0x98d60.
Definition tfib_fini_array_lo : Z := 0x98d60.  Definition tfib_fini_array_hi : Z := 0x98d70.
Definition tfib_preinit_array_lo : Z := 0x98d70.  Definition tfib_preinit_array_hi : Z := 0x98d78.
Definition tfib_data_rel_ro_lo : Z := 0x98d78.  Definition tfib_data_rel_ro_hi : Z := 0x99278.
Definition tfib_got_lo : Z := 0x99278.  Definition tfib_got_hi : Z := 0x99fd0.
Definition tfib_data_lo : Z := 0x9afd0.  Definition tfib_data_hi : Z := 0x9db90.
Definition tfib_asan_globals_lo : Z := 0x9db90.  Definition tfib_asan_globals_hi : Z := 0x9dcd0.
Definition tfib_bss_lo : Z := 0x9dd00.  Definition tfib_bss_hi : Z := 0x5f5c30.
Definition tfib_tbss_lo : Z := 0x97d40.  Definition tfib_tbss_hi : Z := 0x97d54.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_entry : Z := 0x2ffb8.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2ffb8.  Definition tfib_E_start : Z := 0x30000.
Definition tfib_A_do_init : Z := 0x30000.  Definition tfib_E_do_init : Z := 0x30074.
Definition tfib_A_do_fini : Z := 0x30074.  Definition tfib_E_do_fini : Z := 0x30104.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30104.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30140.
Definition tfib_A_InitializeAllocator : Z := 0x302b0.  Definition tfib_E_InitializeAllocator : Z := 0x302c8.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x302c8.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30434.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x30990.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30aec.
Definition tfib_A_asan_free : Z := 0x30ec0.  Definition tfib_E_asan_free : Z := 0x30ee8.
Definition tfib_A_Allocator_Deallocate : Z := 0x30ee8.  Definition tfib_E_Allocator_Deallocate : Z := 0x311a0.
Definition tfib_A_asan_malloc : Z := 0x311a0.  Definition tfib_E_asan_malloc : Z := 0x311fc.
Definition tfib_A_Allocator_Allocate : Z := 0x311fc.  Definition tfib_E_Allocator_Allocate : Z := 0x31b84.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x322bc.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32400.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x324ec.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32548.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32548.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32798.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32798.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3288c.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x3288c.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x32974.
Definition tfib_A_Quarantine_Recycle : Z := 0x32da8.  Definition tfib_E_Quarantine_Recycle : Z := 0x32f8c.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x32f8c.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x33110.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33248.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x334cc.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x334cc.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x3364c.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3364c.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33814.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33814.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x339e0.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x339e0.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x33a80.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33a80.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33b84.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33eac.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33ff4.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x33ff4.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x3402c.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x347c4.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34aac.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35184.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x352fc.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x352fc.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x354ac.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x354ac.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35690.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35690.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x35968.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x35968.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35de0.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35de0.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35ee0.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35ee0.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x361e8.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x361e8.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36558.
Definition tfib_A_RZSize2Log : Z := 0x36558.  Definition tfib_E_RZSize2Log : Z := 0x36670.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x36978.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x36a74.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36a74.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36b5c.
Definition tfib_A_AsanActivate : Z := 0x36b5c.  Definition tfib_E_AsanActivate : Z := 0x36c38.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37114.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x371fc.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3bcb4.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bd8c.
Definition tfib_A_FakeStack_Create : Z := 0x3bd8c.  Definition tfib_E_FakeStack_Create : Z := 0x3be78.
Definition tfib_A_FakeStack_Allocate : Z := 0x3c134.  Definition tfib_E_FakeStack_Allocate : Z := 0x3c41c.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c550.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c580.
(* cgif __asan_stack_malloc class 1 (0x3c8a4+0x190) has no twin; fuzz_boxreg.asan-ubsan has only __asan_stack_malloc_3 0x3c580+0x1ac (107 insns), a new instance (CORE-PREP 1(a)) *)
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3c580.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3c72c.
(* cgif __asan_stack_malloc class 2 (0x3ca34+0x19c): fuzz_boxreg.asan-ubsan has no __asan_stack_malloc_2; dropped (CORE-PREP 1(a)) *)
Definition tfib_A_MemToShadow_3c6cc : Z := 0x3c72c.  Definition tfib_E_MemToShadow_3c6cc : Z := 0x3c868.
Definition tfib_A_asan_InitializeFlags : Z := 0x3c868.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d894.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3dfa0.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3edbc.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3edbc.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f388.
Definition tfib_A_asan_register_globals : Z := 0x3f388.  Definition tfib_E_asan_register_globals : Z := 0x3f3f4.
Definition tfib_A_asan_unregister_globals : Z := 0x3f3f4.  Definition tfib_E_asan_unregister_globals : Z := 0x3f45c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x3fadc.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x3fd4c.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x3fd4c.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40054.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x407c8.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40918.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x41334.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x4144c.
Definition tfib_A_strlen : Z := 0x4144c.  Definition tfib_E_strlen : Z := 0x41450.
Definition tfib_A_strnlen : Z := 0x41450.  Definition tfib_E_strnlen : Z := 0x41454.
Definition tfib_A_strcmp : Z := 0x41454.  Definition tfib_E_strcmp : Z := 0x41458.
Definition tfib_A_strchr : Z := 0x4145c.  Definition tfib_E_strchr : Z := 0x41460.
Definition tfib_A_memcmp : Z := 0x41460.  Definition tfib_E_memcmp : Z := 0x41464.
Definition tfib_A_interceptor_trampoline_bcmp : Z := 0x41464.  Definition tfib_E_interceptor_trampoline_bcmp : Z := 0x41468.
Definition tfib_A_memchr : Z := 0x41468.  Definition tfib_E_memchr : Z := 0x4146c.
Definition tfib_A_frexpl : Z := 0x4146c.  Definition tfib_E_frexpl : Z := 0x41470.
Definition tfib_A_read : Z := 0x41470.  Definition tfib_E_read : Z := 0x41474.
Definition tfib_A_fwrite : Z := 0x41474.  Definition tfib_E_fwrite : Z := 0x41478.
Definition tfib_A_time : Z := 0x41478.  Definition tfib_E_time : Z := 0x4147c.
Definition tfib_A_gmtime_r : Z := 0x4147c.  Definition tfib_E_gmtime_r : Z := 0x41480.
Definition tfib_A_vprintf : Z := 0x41480.  Definition tfib_E_vprintf : Z := 0x41484.
Definition tfib_A_vfprintf : Z := 0x41484.  Definition tfib_E_vfprintf : Z := 0x41488.
Definition tfib_A_vsnprintf : Z := 0x41488.  Definition tfib_E_vsnprintf : Z := 0x4148c.
Definition tfib_A_interceptor_trampoline_fprintf : Z := 0x4148c.  Definition tfib_E_interceptor_trampoline_fprintf : Z := 0x41490.
Definition tfib_A_interceptor_trampoline_snprintf : Z := 0x41490.  Definition tfib_E_interceptor_trampoline_snprintf : Z := 0x41494.
Definition tfib_A_clock_gettime : Z := 0x41494.  Definition tfib_E_clock_gettime : Z := 0x41498.
Definition tfib_A_wcrtomb : Z := 0x41498.  Definition tfib_E_wcrtomb : Z := 0x4149c.
Definition tfib_A_wctomb : Z := 0x4149c.  Definition tfib_E_wctomb : Z := 0x414a0.
(* cgif merged row thunk_417cc (0x41940+0x8) = boxreg __interceptor_trampoline_strerror + __interceptor_trampoline__exit; split, rows named by those symbols *)
Definition tfib_A_interceptor_trampoline_strerror : Z := 0x414a0.  Definition tfib_E_interceptor_trampoline_strerror : Z := 0x414a4.
Definition tfib_A_interceptor_trampoline__exit : Z := 0x414a4.  Definition tfib_E_interceptor_trampoline__exit : Z := 0x414a8.
Definition tfib_A_pthread_attr_getstack : Z := 0x414a8.  Definition tfib_E_pthread_attr_getstack : Z := 0x414ac.
Definition tfib_A_tls_get_addr_thunk : Z := 0x414ac.  Definition tfib_E_tls_get_addr_thunk : Z := 0x414b0.
(* cgif fopen trampoline (0x41950+0x4): fuzz_boxreg.asan-ubsan has no fopen; dropped *)
Definition tfib_A_interceptor_trampoline_fflush : Z := 0x414b0.  Definition tfib_E_interceptor_trampoline_fflush : Z := 0x414b4.
(* cgif fclose trampoline (0x41958+0x4): fuzz_boxreg.asan-ubsan has no fclose; dropped *)
Definition tfib_A_interceptor_trampoline_sem_init : Z := 0x414b4.  Definition tfib_E_interceptor_trampoline_sem_init : Z := 0x414b8.
Definition tfib_A_interceptor_trampoline_sem_destroy : Z := 0x414b8.  Definition tfib_E_interceptor_trampoline_sem_destroy : Z := 0x414bc.
Definition tfib_A_interceptor_trampoline_sem_wait : Z := 0x414bc.  Definition tfib_E_interceptor_trampoline_sem_wait : Z := 0x414c0.
Definition tfib_A_interceptor_trampoline_sem_trywait : Z := 0x414c0.  Definition tfib_E_interceptor_trampoline_sem_trywait : Z := 0x414c4.
Definition tfib_A_sem_timedwait : Z := 0x414c4.  Definition tfib_E_sem_timedwait : Z := 0x414c8.
Definition tfib_A_interceptor_trampoline_sem_post : Z := 0x414c8.  Definition tfib_E_interceptor_trampoline_sem_post : Z := 0x414cc.
Definition tfib_A_pthread_setcancelstate : Z := 0x414cc.  Definition tfib_E_pthread_setcancelstate : Z := 0x414d0.
Definition tfib_A_send : Z := 0x414d0.  Definition tfib_E_send : Z := 0x414d4.
Definition tfib_A_sendto : Z := 0x414d4.  Definition tfib_E_sendto : Z := 0x414d8.
Definition tfib_A_sigaltstack : Z := 0x414d8.  Definition tfib_E_sigaltstack : Z := 0x414dc.
Definition tfib_A_interceptor_trampoline_sigaction : Z := 0x414dc.  Definition tfib_E_interceptor_trampoline_sigaction : Z := 0x414e0.
Definition tfib_A_icpt_strlen : Z := 0x414e0.  Definition tfib_E_icpt_strlen : Z := 0x41774.
Definition tfib_A_icpt_strnlen : Z := 0x41774.  Definition tfib_E_icpt_strnlen : Z := 0x41a08.
Definition tfib_A_icpt_strcmp : Z := 0x41a0c.  Definition tfib_E_icpt_strcmp : Z := 0x41f3c.
Definition tfib_A_icpt_strchr : Z := 0x42518.  Definition tfib_E_icpt_strchr : Z := 0x427f8.
Definition tfib_A_icpt_memcmp : Z := 0x43090.  Definition tfib_E_icpt_memcmp : Z := 0x4314c.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x4314c.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x43208.
Definition tfib_A_icpt_memchr : Z := 0x43208.  Definition tfib_E_icpt_memchr : Z := 0x434d8.
Definition tfib_A_icpt_frexpl : Z := 0x434d8.  Definition tfib_E_icpt_frexpl : Z := 0x43750.
Definition tfib_A_icpt_read : Z := 0x43750.  Definition tfib_E_icpt_read : Z := 0x439c0.
Definition tfib_A_icpt_fwrite : Z := 0x439c0.  Definition tfib_E_icpt_fwrite : Z := 0x43c34.
Definition tfib_A_icpt_time : Z := 0x43c34.  Definition tfib_E_icpt_time : Z := 0x43ed0.
Definition tfib_A_icpt_gmtime_r : Z := 0x440d8.  Definition tfib_E_icpt_gmtime_r : Z := 0x44318.
Definition tfib_A_icpt_vprintf : Z := 0x44318.  Definition tfib_E_icpt_vprintf : Z := 0x443b4.
Definition tfib_A_printf_common_format_interceptor : Z := 0x443b4.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44e7c.
Definition tfib_A_icpt_vfprintf : Z := 0x44e7c.  Definition tfib_E_icpt_vfprintf : Z := 0x44f30.
Definition tfib_A_icpt_vsnprintf : Z := 0x44f30.  Definition tfib_E_icpt_vsnprintf : Z := 0x45248.
Definition tfib_A_interceptor_fprintf : Z := 0x45248.  Definition tfib_E_interceptor_fprintf : Z := 0x45320.
Definition tfib_A_icpt_clock_gettime : Z := 0x453c4.  Definition tfib_E_icpt_clock_gettime : Z := 0x4561c.
Definition tfib_A_icpt_wcrtomb : Z := 0x4561c.  Definition tfib_E_icpt_wcrtomb : Z := 0x45b8c.
Definition tfib_A_icpt_wctomb : Z := 0x45b8c.  Definition tfib_E_icpt_wctomb : Z := 0x45ee8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45fb4.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4639c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x463a8.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46424.
(* cgif __interceptor_fopen (0x462f0+0x46c): fuzz_boxreg.asan-ubsan has no fopen interceptor; dropped *)
(* cgif __interceptor_fclose (0x46868+0x1ac): fuzz_boxreg.asan-ubsan has no fclose interceptor; dropped *)
Definition tfib_A_icpt_sem_timedwait : Z := 0x46630.  Definition tfib_E_icpt_sem_timedwait : Z := 0x468c8.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x468f8.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46b20.
Definition tfib_A_icpt_send : Z := 0x46b20.  Definition tfib_E_icpt_send : Z := 0x46dd4.
Definition tfib_A_icpt_sendto : Z := 0x46dd4.  Definition tfib_E_icpt_sendto : Z := 0x47098.
Definition tfib_A_icpt_sigaltstack : Z := 0x47098.  Definition tfib_E_icpt_sigaltstack : Z := 0x472f4.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x473c8.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47578.
Definition tfib_A_format_get_value_size : Z := 0x47578.  Definition tfib_E_format_get_value_size : Z := 0x47710.
Definition tfib_A_ioctl_table_fill : Z := 0x482bc.  Definition tfib_E_ioctl_table_fill : Z := 0x50f94.
Definition tfib_A_Sort_ioctl_desc : Z := 0x50f94.  Definition tfib_E_Sort_ioctl_desc : Z := 0x510f0.
Definition tfib_A_memset : Z := 0x510f0.  Definition tfib_E_memset : Z := 0x510f4.
Definition tfib_A_memcpy : Z := 0x510f4.  Definition tfib_E_memcpy : Z := 0x510f8.
Definition tfib_A_asan_memcpy : Z := 0x510f8.  Definition tfib_E_asan_memcpy : Z := 0x51594.
Definition tfib_A_asan_memset : Z := 0x51594.  Definition tfib_E_asan_memset : Z := 0x517d4.
Definition tfib_A_icpt_memset : Z := 0x517d4.  Definition tfib_E_icpt_memset : Z := 0x51ac4.
Definition tfib_A_icpt_memcpy : Z := 0x51ac4.  Definition tfib_E_icpt_memcpy : Z := 0x520b4.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x520b4.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x520ec.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x520ec.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x520f0.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x520f0.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x520f4.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x520f4.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52154.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x521a0.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x522dc.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x522dc.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x522e0.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x522e0.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52448.
Definition tfib_A_free : Z := 0x52448.  Definition tfib_E_free : Z := 0x5244c.
Definition tfib_A_malloc : Z := 0x5244c.  Definition tfib_E_malloc : Z := 0x52450.
Definition tfib_A_icpt_free : Z := 0x52450.  Definition tfib_E_icpt_free : Z := 0x52620.
Definition tfib_A_icpt_malloc : Z := 0x52620.  Definition tfib_E_icpt_malloc : Z := 0x5277c.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x5277c.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x52848.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52848.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x5284c.
Definition tfib_A_TwoLevelMap_u8_Create : Z := 0x5284c.  Definition tfib_E_TwoLevelMap_u8_Create : Z := 0x5294c.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x52c74.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x52de0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x532c8.  Definition tfib_E_SetCanPoisonMemory : Z := 0x532d8.
Definition tfib_A_CanPoisonMemory : Z := 0x532d8.  Definition tfib_E_CanPoisonMemory : Z := 0x532ec.
Definition tfib_A_PoisonShadow : Z := 0x532ec.  Definition tfib_E_PoisonShadow : Z := 0x537e8.
Definition tfib_A_MemToShadow_checked : Z := 0x537e8.  Definition tfib_E_MemToShadow_checked : Z := 0x53924.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53924.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53ac4.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x53ac4.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x53c44.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53c74.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53fb8.
Definition tfib_A_AsanTSDInit : Z := 0x543d8.  Definition tfib_E_AsanTSDInit : Z := 0x54454.
Definition tfib_A_AsanTSDGet : Z := 0x54454.  Definition tfib_E_AsanTSDGet : Z := 0x54494.
Definition tfib_A_AsanTSDSet : Z := 0x54494.  Definition tfib_E_AsanTSDSet : Z := 0x544d4.
Definition tfib_A_PlatformTSDDtor : Z := 0x544d4.  Definition tfib_E_PlatformTSDDtor : Z := 0x54558.
Definition tfib_A_InstallAtForkHandler : Z := 0x54558.  Definition tfib_E_InstallAtForkHandler : Z := 0x54574.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x545d4.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54618.
Definition tfib_A_ReportDeadlySignal : Z := 0x54d30.  Definition tfib_E_ReportDeadlySignal : Z := 0x54f3c.
Definition tfib_A_ReportDoubleFree : Z := 0x55644.  Definition tfib_E_ReportDoubleFree : Z := 0x558d4.
Definition tfib_A_ReportGenericError : Z := 0x571b0.  Definition tfib_E_ReportGenericError : Z := 0x57a6c.
Definition tfib_A_AsanInited : Z := 0x581f8.  Definition tfib_E_AsanInited : Z := 0x58210.
Definition tfib_A_asan_report_load1 : Z := 0x58210.  Definition tfib_E_asan_report_load1 : Z := 0x58260.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58260.  Definition tfib_E_asan_report_exp_load1 : Z := 0x582b0.
Definition tfib_A_asan_report_load2 : Z := 0x582b0.  Definition tfib_E_asan_report_load2 : Z := 0x58300.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58300.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58350.
Definition tfib_A_asan_report_load4 : Z := 0x58350.  Definition tfib_E_asan_report_load4 : Z := 0x583a0.
Definition tfib_A_asan_report_exp_load4 : Z := 0x583a0.  Definition tfib_E_asan_report_exp_load4 : Z := 0x583f0.
Definition tfib_A_asan_report_load8 : Z := 0x583f0.  Definition tfib_E_asan_report_load8 : Z := 0x58440.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58440.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58490.
Definition tfib_A_asan_report_load16 : Z := 0x58490.  Definition tfib_E_asan_report_load16 : Z := 0x584e0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x584e0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58530.
Definition tfib_A_asan_report_store1 : Z := 0x58530.  Definition tfib_E_asan_report_store1 : Z := 0x58580.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58580.  Definition tfib_E_asan_report_exp_store1 : Z := 0x585d0.
Definition tfib_A_asan_report_store2 : Z := 0x585d0.  Definition tfib_E_asan_report_store2 : Z := 0x58620.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58620.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58670.
Definition tfib_A_asan_report_store4 : Z := 0x58670.  Definition tfib_E_asan_report_store4 : Z := 0x586c0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x586c0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58710.
Definition tfib_A_asan_report_store8 : Z := 0x58710.  Definition tfib_E_asan_report_store8 : Z := 0x58760.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58760.  Definition tfib_E_asan_report_exp_store8 : Z := 0x587b0.
Definition tfib_A_asan_report_store16 : Z := 0x587b0.  Definition tfib_E_asan_report_store16 : Z := 0x58800.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58800.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58850.
Definition tfib_A_asan_report_load_n : Z := 0x58850.  Definition tfib_E_asan_report_load_n : Z := 0x588a0.
Definition tfib_A_asan_report_exp_load_n : Z := 0x588a0.  Definition tfib_E_asan_report_exp_load_n : Z := 0x588f0.
Definition tfib_A_asan_report_store_n : Z := 0x588f0.  Definition tfib_E_asan_report_store_n : Z := 0x58940.
Definition tfib_A_asan_report_exp_store_n : Z := 0x58940.  Definition tfib_E_asan_report_exp_store_n : Z := 0x58990.
Definition tfib_A_InitializeHighMemEnd : Z := 0x58990.  Definition tfib_E_InitializeHighMemEnd : Z := 0x58a10.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x58a10.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58dc4.
Definition tfib_A_AsanInitInternal : Z := 0x58e54.  Definition tfib_E_AsanInitInternal : Z := 0x59108.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59108.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x591a8.
Definition tfib_A_asan_set_death_callback : Z := 0x59370.  Definition tfib_E_asan_set_death_callback : Z := 0x59374.
Definition tfib_A_asan_init : Z := 0x59374.  Definition tfib_E_asan_init : Z := 0x59408.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59408.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5940c.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5940c.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x59470.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x595e4.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x595ec.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59670.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59998.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59998.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59b78.
Definition tfib_A_InitializeShadowMemory : Z := 0x59b78.  Definition tfib_E_InitializeShadowMemory : Z := 0x59e80.
Definition tfib_A_SetMallocContextSize : Z := 0x59e80.  Definition tfib_E_SetMallocContextSize : Z := 0x59e90.
Definition tfib_A_GetMallocContextSize : Z := 0x59e90.  Definition tfib_E_GetMallocContextSize : Z := 0x59ea0.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59ea0.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59ff0.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5a3d0.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5a670.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5aad4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5ab0c.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5adb4.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5adc0.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5adc0.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5ae4c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5ae4c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5aeb4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5aeb4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5af2c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5af2c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5af94.
Definition tfib_A_IsAddrSuppressed : Z := 0x5af94.  Definition tfib_E_IsAddrSuppressed : Z := 0x5b0e0.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5b36c.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5b378.
Definition tfib_A_AsanThread_Create : Z := 0x5b4f8.  Definition tfib_E_AsanThread_Create : Z := 0x5b694.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b6f0.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b908.
Definition tfib_A_GetCurrentThread : Z := 0x5b908.  Definition tfib_E_GetCurrentThread : Z := 0x5b928.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5b928.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5bacc.
Definition tfib_A_AsanThread_stack_top : Z := 0x5bacc.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bb24.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bb24.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bb7c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bb7c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bdac.
Definition tfib_A_AsanThread_Init : Z := 0x5bdac.  Definition tfib_E_AsanThread_Init : Z := 0x5c1a0.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c1a0.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c2ac.
Definition tfib_A_CreateMainThread : Z := 0x5c2e0.  Definition tfib_E_CreateMainThread : Z := 0x5c3f0.
Definition tfib_A_SetCurrentThread : Z := 0x5c3f0.  Definition tfib_E_SetCurrentThread : Z := 0x5c4d0.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c6d4.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c810.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5d4e4.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5d4e8.
Definition tfib_A_GetAsanThreadContext : Z := 0x5d4f0.  Definition tfib_E_GetAsanThreadContext : Z := 0x5d730.
Definition tfib_A_internal_allocator : Z := 0x5d984.  Definition tfib_E_internal_allocator : Z := 0x5dadc.
Definition tfib_A_internal_allocator_getter : Z := 0x5dcc8.  Definition tfib_E_internal_allocator_getter : Z := 0x5dcd4.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5dcd4.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5de20.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5de20.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5de6c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5de6c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5de78.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5dea8.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5deb4.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5deb4.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5dec0.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5dec0.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5ded0.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5dedc.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e1a8.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e1a8.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e568.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5f4c4.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5f4d0.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f4d0.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f5a8.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f5a8.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f644.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fb68.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fbac.
Definition tfib_A_DecreaseTotalMmap : Z := 0x5fbac.  Definition tfib_E_DecreaseTotalMmap : Z := 0x5fbd0.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5fe24.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5ff38.
Definition tfib_A_RunMallocHooks : Z := 0x600dc.  Definition tfib_E_RunMallocHooks : Z := 0x60194.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60194.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60198.
Definition tfib_A_RunFreeHooks : Z := 0x60198.  Definition tfib_E_RunFreeHooks : Z := 0x60244.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x60244.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x6024c.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x6024c.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x60250.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60278.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x602c4.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60588.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x607c8.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60dc4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60ddc.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x60ddc.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x60f20.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60f20.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60f28.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x61270.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x62514.
Definition tfib_A_InitializeCommonFlags : Z := 0x62514.  Definition tfib_E_InitializeCommonFlags : Z := 0x62538.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x629ec.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62cfc.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62cfc.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62e40.
Definition tfib_A_FlagParser_ParseString : Z := 0x62e40.  Definition tfib_E_FlagParser_ParseString : Z := 0x62f34.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x630c8.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63128.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63128.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63168.
Definition tfib_A_internal_atoll : Z := 0x63168.  Definition tfib_E_internal_atoll : Z := 0x63254.
Definition tfib_A_internal_simple_strtoll : Z := 0x63254.  Definition tfib_E_internal_simple_strtoll : Z := 0x633b0.
Definition tfib_A_internal_memchr : Z := 0x633b0.  Definition tfib_E_internal_memchr : Z := 0x633d0.
Definition tfib_A_internal_memcmp : Z := 0x633d0.  Definition tfib_E_internal_memcmp : Z := 0x63408.
Definition tfib_A_internal_memcpy : Z := 0x63408.  Definition tfib_E_internal_memcpy : Z := 0x6342c.
Definition tfib_A_internal_memmove : Z := 0x6342c.  Definition tfib_E_internal_memmove : Z := 0x63484.
Definition tfib_A_internal_memset : Z := 0x63484.  Definition tfib_E_internal_memset : Z := 0x634e4.
Definition tfib_A_internal_strcspn : Z := 0x634e4.  Definition tfib_E_internal_strcspn : Z := 0x63538.
Definition tfib_A_internal_strcmp : Z := 0x63538.  Definition tfib_E_internal_strcmp : Z := 0x6356c.
Definition tfib_A_internal_strdup : Z := 0x6356c.  Definition tfib_E_internal_strdup : Z := 0x635d8.
Definition tfib_A_internal_strlen : Z := 0x635d8.  Definition tfib_E_internal_strlen : Z := 0x635f4.
Definition tfib_A_internal_strncmp : Z := 0x635f4.  Definition tfib_E_internal_strncmp : Z := 0x63638.
Definition tfib_A_internal_strchr : Z := 0x63638.  Definition tfib_E_internal_strchr : Z := 0x63684.
Definition tfib_A_internal_strchrnul : Z := 0x63684.  Definition tfib_E_internal_strchrnul : Z := 0x636cc.
Definition tfib_A_internal_strrchr : Z := 0x636cc.  Definition tfib_E_internal_strrchr : Z := 0x6370c.
Definition tfib_A_internal_strnlen : Z := 0x6383c.  Definition tfib_E_internal_strnlen : Z := 0x6386c.
Definition tfib_A_internal_strncpy : Z := 0x638b0.  Definition tfib_E_internal_strncpy : Z := 0x63920.
Definition tfib_A_internal_strstr : Z := 0x63920.  Definition tfib_E_internal_strstr : Z := 0x639b4.
Definition tfib_A_mem_is_zero : Z := 0x639b4.  Definition tfib_E_mem_is_zero : Z := 0x63a68.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a68.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63a78.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63a78.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63c58.
Definition tfib_A_internal_iserror : Z := 0x63c64.  Definition tfib_E_internal_iserror : Z := 0x63c84.
Definition tfib_A_internal_mmap : Z := 0x63c84.  Definition tfib_E_internal_mmap : Z := 0x63c90.
Definition tfib_A_internal_munmap : Z := 0x63c90.  Definition tfib_E_internal_munmap : Z := 0x63c9c.
Definition tfib_A_internal_mprotect : Z := 0x63c9c.  Definition tfib_E_internal_mprotect : Z := 0x63cac.
Definition tfib_A_internal_madvise : Z := 0x63cac.  Definition tfib_E_internal_madvise : Z := 0x63cd8.
Definition tfib_A_internal_close : Z := 0x63cd8.  Definition tfib_E_internal_close : Z := 0x63ce4.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63ce4.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63d08.
Definition tfib_A_internal_read : Z := 0x63d08.  Definition tfib_E_internal_read : Z := 0x63d40.
Definition tfib_A_internal_write : Z := 0x63d40.  Definition tfib_E_internal_write : Z := 0x63d78.
Definition tfib_A_internal_ftruncate : Z := 0x63d78.  Definition tfib_E_internal_ftruncate : Z := 0x63db0.
Definition tfib_A_internal_dup : Z := 0x63db0.  Definition tfib_E_internal_dup : Z := 0x63dbc.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63dbc.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63dcc.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63dcc.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63de4.
Definition tfib_A_internal_sched_yield : Z := 0x63de4.  Definition tfib_E_internal_sched_yield : Z := 0x63df0.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63df0.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63e3c.
Definition tfib_A_internal_execve : Z := 0x63e3c.  Definition tfib_E_internal_execve : Z := 0x63e48.
Definition tfib_A_internal_exit_exit_group : Z := 0x63e48.  Definition tfib_E_internal_exit_exit_group : Z := 0x63e5c.
Definition tfib_A_FileExists_newfstatat : Z := 0x63e5c.  Definition tfib_E_FileExists_newfstatat : Z := 0x63edc.
Definition tfib_A_DirExists_newfstatat : Z := 0x63edc.  Definition tfib_E_DirExists_newfstatat : Z := 0x63f40.
Definition tfib_A_GetTid_gettid : Z := 0x63f40.  Definition tfib_E_GetTid_gettid : Z := 0x63f4c.
Definition tfib_A_GetEnv : Z := 0x63f4c.  Definition tfib_E_GetEnv : Z := 0x6407c.
Definition tfib_A_FutexWait : Z := 0x64180.  Definition tfib_E_FutexWait : Z := 0x641a4.
Definition tfib_A_FutexWake : Z := 0x641a4.  Definition tfib_E_FutexWake : Z := 0x641c8.
Definition tfib_A_internal_ptrace : Z := 0x641c8.  Definition tfib_E_internal_ptrace : Z := 0x641d4.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x641d4.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x641e4.
Definition tfib_A_internal_getpid : Z := 0x641e4.  Definition tfib_E_internal_getpid : Z := 0x641f0.
Definition tfib_A_internal_getppid : Z := 0x641f0.  Definition tfib_E_internal_getppid : Z := 0x641fc.
Definition tfib_A_internal_prctl : Z := 0x641fc.  Definition tfib_E_internal_prctl : Z := 0x64208.
Definition tfib_A_internal_sigaltstack : Z := 0x64208.  Definition tfib_E_internal_sigaltstack : Z := 0x64214.
Definition tfib_A_internal_fork_clone : Z := 0x64214.  Definition tfib_E_internal_fork_clone : Z := 0x6422c.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x6422c.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64358.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x64530.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x6492c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64a98.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64bb0.
Definition tfib_A_GetPageSize : Z := 0x64bb0.  Definition tfib_E_GetPageSize : Z := 0x64bb8.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64bb8.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64c64.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64c64.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64d84.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64e4c.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64ecc.
Definition tfib_A_GetHandleSignalMode : Z := 0x64ecc.  Definition tfib_E_GetHandleSignalMode : Z := 0x64f28.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64f28.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64ff4.
Definition tfib_A_InitializePlatformEarly : Z := 0x650f0.  Definition tfib_E_InitializePlatformEarly : Z := 0x650f4.
Definition tfib_A_CheckASLR : Z := 0x650f4.  Definition tfib_E_CheckASLR : Z := 0x650f8.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65344.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65348.
Definition tfib_A_ErrorIsOOM : Z := 0x65348.  Definition tfib_E_ErrorIsOOM : Z := 0x65354.
Definition tfib_A_MmapOrDie : Z := 0x65354.  Definition tfib_E_MmapOrDie : Z := 0x65460.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65460.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x654d4.
Definition tfib_A_UnmapOrDie : Z := 0x654d4.  Definition tfib_E_UnmapOrDie : Z := 0x65550.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65550.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65660.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6588c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x65990.
Definition tfib_A_MmapFixedOrDie : Z := 0x65990.  Definition tfib_E_MmapFixedOrDie : Z := 0x6599c.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x6599c.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65b14.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65b14.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65b20.
Definition tfib_A_CloseFile : Z := 0x65d0c.  Definition tfib_E_CloseFile : Z := 0x65d10.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66030.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x6623c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x667f4.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66800.
Definition tfib_A_Printf : Z := 0x66804.  Definition tfib_E_Printf : Z := 0x66850.
Definition tfib_A_SharedPrintfCode : Z := 0x66850.  Definition tfib_E_SharedPrintfCode : Z := 0x668ac.
Definition tfib_A_Report : Z := 0x668ac.  Definition tfib_E_Report : Z := 0x668f8.
Definition tfib_A_SuppressionContext_ctor : Z := 0x683f0.  Definition tfib_E_SuppressionContext_ctor : Z := 0x6844c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x6844c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68688.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68688.  Definition tfib_E_SuppressionContext_Parse : Z := 0x689ac.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68f4c.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6901c.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6901c.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x6936c.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6936c.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x6937c.
Definition tfib_A_ThreadContextBase_ctor : Z := 0x695b8.  Definition tfib_E_ThreadContextBase_ctor : Z := 0x695fc.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x695fc.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x6965c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6965c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69ad4.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a394.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a6b8.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a6c0.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a7c4.
Definition tfib_A_AddDieCallback : Z := 0x6af74.  Definition tfib_E_AddDieCallback : Z := 0x6affc.
Definition tfib_A_Die : Z := 0x6b0c0.  Definition tfib_E_Die : Z := 0x6b180.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b180.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b18c.
Definition tfib_A_CheckFailed : Z := 0x6b18c.  Definition tfib_E_CheckFailed : Z := 0x6b244.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b89c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6b994.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6b994.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6bac0.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bce8.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bd64.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6bd98.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c080.
Definition tfib_A_InitTlsSize : Z := 0x6c080.  Definition tfib_E_InitTlsSize : Z := 0x6c084.
Definition tfib_A_GetTls : Z := 0x6c084.  Definition tfib_E_GetTls : Z := 0x6c474.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c474.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6c544.
Definition tfib_A_AndroidLogInit : Z := 0x6c928.  Definition tfib_E_AndroidLogInit : Z := 0x6c92c.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c95c.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6c9a4.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c9a4.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6cbf0.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6cbf0.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6cbf4.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6cbf4.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6cd00.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6cd00.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6ce04.
Definition tfib_A_GetThreadSelf : Z := 0x6d080.  Definition tfib_E_GetThreadSelf : Z := 0x6d084.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d128.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d148.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d148.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d1e8.
Definition tfib_A_Atexit : Z := 0x6d234.  Definition tfib_E_Atexit : Z := 0x6d238.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d274.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d338.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d338.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d3c0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d3c0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d438.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d438.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d51c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d5d8.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d70c.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6d944.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6da74.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6da74.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6dad4.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6dad4.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6dba0.
Definition tfib_A_MmapNoAccess : Z := 0x6dbb4.  Definition tfib_E_MmapNoAccess : Z := 0x6dbd4.
(* cgif merged row MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser (0x6e0b8+0x14c) = boxreg ReservedAddressRange::Map + SealedRepairReservation; split *)
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6dbd4.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6dc48.
Definition tfib_A_SealedRepairReservation : Z := 0x6dc48.  Definition tfib_E_SealedRepairReservation : Z := 0x6dd20.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6dd20.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6dd30.
Definition tfib_A_InitializeCoverage : Z := 0x6f528.  Definition tfib_E_InitializeCoverage : Z := 0x6f56c.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6f56c.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6f59c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6f9d0.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6faf4.
Definition tfib_A_StackStore_Alloc : Z := 0x6faf4.  Definition tfib_E_StackStore_Alloc : Z := 0x6fc28.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x704dc.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70590.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71ce4.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x71d40.
Definition tfib_A_StackDepotPut : Z := 0x71fcc.  Definition tfib_E_StackDepotPut : Z := 0x71fec.
Definition tfib_A_StackDepotBase_Put : Z := 0x71fec.  Definition tfib_E_StackDepotBase_Put : Z := 0x72270.
Definition tfib_A_StackDepotGet : Z := 0x72270.  Definition tfib_E_StackDepotGet : Z := 0x72380.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x72760.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x727f0.
Definition tfib_A_TwoLevelMap_StackDepotNode_Create : Z := 0x727f0.  Definition tfib_E_TwoLevelMap_StackDepotNode_Create : Z := 0x728f0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x72950.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x72958.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72958.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72ab8.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72ab8.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72b2c.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72fb4.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x730cc.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x76118.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x7611c.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x778f0.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x778f4.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7931c.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x793d8.
Definition tfib_A_Unwind_Trace_callback : Z := 0x793d8.  Definition tfib_E_Unwind_Trace_callback : Z := 0x794b0.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x794b0.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x79724.
Definition tfib_A_lsan_flags_init_helper : Z := 0x79a50.  Definition tfib_E_lsan_flags_init_helper : Z := 0x79a94.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79a94.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79e64.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a134.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a1ec.
Definition tfib_A_DoRecoverableLeakCheckVoid : Z := 0x7b544.  Definition tfib_E_DoRecoverableLeakCheckVoid : Z := 0x7b548.
Definition tfib_A_lsan_register_root_region : Z := 0x7c150.  Definition tfib_E_lsan_register_root_region : Z := 0x7c480.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c480.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c908.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7c908.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7c914.
Definition tfib_A_DisabledInThisThread : Z := 0x7f4cc.  Definition tfib_E_DisabledInThisThread : Z := 0x7f4e4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f868.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f8e4.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f8e4.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7f994.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f994.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7f9ac.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f9ac.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7faf4.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7faf4.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7fb00.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7fb00.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7fb0c.
Definition tfib_A_main : Z := 0x7fb0c.  Definition tfib_E_main : Z := 0x7fdd0.
Definition tfib_A_target_alloc_init : Z := 0x7fdd0.  Definition tfib_E_target_alloc_init : Z := 0x7fdd4.
Definition tfib_A_target_alloc_count : Z := 0x7fdd4.  Definition tfib_E_target_alloc_count : Z := 0x7fddc.
(* cgif merged row target_run (0x802c0+0x188) = boxreg target_run + oft_exit_guard; split *)
Definition tfib_A_target_run : Z := 0x7fddc.  Definition tfib_E_target_run : Z := 0x7ff34.
Definition tfib_A_oft_exit_guard : Z := 0x7ff34.  Definition tfib_E_oft_exit_guard : Z := 0x7ff64.
Definition tfib_A_emit_printf : Z := 0x7ff64.  Definition tfib_E_emit_printf : Z := 0x7ffac.
(* cgif program function LLVMFuzzerTestOneInput (0x80490+0x6a8): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function read_frameconfig (0x80b38+0x864): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_asan_module_ctor : Z := 0x8182c.  Definition tfib_E_asan_module_ctor : Z := 0x81864.
(* cgif program function cgif_newgif (0x81404+0x614): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_writecb_or_freeCGIF (0x81a18+0xd0): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function freeFrame_or_freeCGIF (0x81ae8+0x80): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_addframe (0x81b68+0xdb4): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cmpPixel (0x8291c+0x1e4): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function flushFrame (0x82b00+0x1394): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function freeFrame (0x83e94+0xc0): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_close (0x83f54+0x224): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_asan_module_dtor : Z := 0x81864.  Definition tfib_E_asan_module_dtor : Z := 0x81894.
(* cgif program function cgif_raw_newgif (0x84178+0x71c): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_raw_addframe (0x84894+0xd28): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function LZW_GenerateStream (0x855bc+0x10c8): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function cgif_raw_close (0x86684+0xe0): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function create_byte_list (0x86764+0x2c8): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
(* cgif program function create_byte_list_block (0x86a2c+0x1a0): fuzz_boxreg.asan-ubsan is a different program; dropped (boxreg program lane listed in NOTES.md) *)
Definition tfib_A_extenddftf2 : Z := 0x82368.  Definition tfib_E_extenddftf2 : Z := 0x824f8.
Definition tfib_A_sysconf : Z := 0x88148.  Definition tfib_E_sysconf : Z := 0x88370.
Definition tfib_A_init : Z := 0x88370.  Definition tfib_E_init : Z := 0x88374.
Definition tfib_A_init_libc : Z := 0x88374.  Definition tfib_E_init_libc : Z := 0x885a0.
Definition tfib_A_libc_start_init : Z := 0x885a0.  Definition tfib_E_libc_start_init : Z := 0x885ec.
Definition tfib_A_libc_start_main : Z := 0x885ec.  Definition tfib_E_libc_start_main : Z := 0x8864c.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8864c.  Definition tfib_E_libc_start_main_stage2 : Z := 0x88694.
Definition tfib_A_init_tls : Z := 0x8876c.  Definition tfib_E_init_tls : Z := 0x88a1c.
Definition tfib_A_init_ssp : Z := 0x88a1c.  Definition tfib_E_init_ssp : Z := 0x88a7c.
Definition tfib_A_stack_chk_fail : Z := 0x88a7c.  Definition tfib_E_stack_chk_fail : Z := 0x88a84.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x88acc.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x88b60.
Definition tfib_A_Exit : Z := 0x88b60.  Definition tfib_E_Exit : Z := 0x88b7c.
Definition tfib_A_funcs_on_exit : Z := 0x88bac.  Definition tfib_E_funcs_on_exit : Z := 0x88c74.
Definition tfib_A_cxa_finalize : Z := 0x88c74.  Definition tfib_E_cxa_finalize : Z := 0x88c78.
Definition tfib_A_cxa_atexit_atexit : Z := 0x88c78.  Definition tfib_E_cxa_atexit_atexit : Z := 0x88d3c.
Definition tfib_A_call : Z := 0x88d3c.  Definition tfib_E_call : Z := 0x88d40.
Definition tfib_A_fini : Z := 0x88d40.  Definition tfib_E_fini : Z := 0x88d44.
Definition tfib_A_libc_exit_fini : Z := 0x88d44.  Definition tfib_E_libc_exit_fini : Z := 0x88d90.
Definition tfib_A_exit : Z := 0x88d90.  Definition tfib_E_exit : Z := 0x88e04.
Definition tfib_A_open : Z := 0x89004.  Definition tfib_E_open : Z := 0x890e8.
Definition tfib_A_syscall_ret : Z := 0x890e8.  Definition tfib_E_syscall_ret : Z := 0x89120.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x89120.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x892c8.
Definition tfib_A_calloc : Z := 0x8988c.  Definition tfib_E_calloc : Z := 0x899c4.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x899c4.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x899c8.
Definition tfib_A_libc_free : Z := 0x899c8.  Definition tfib_E_libc_free : Z := 0x89b94.
Definition tfib_A_get_meta : Z := 0x89b94.  Definition tfib_E_get_meta : Z := 0x89ca4.
Definition tfib_A_alloc_meta : Z := 0x8a07c.  Definition tfib_E_alloc_meta : Z := 0x8a354.
Definition tfib_A_libc_malloc_impl : Z := 0x8a354.  Definition tfib_E_libc_malloc_impl : Z := 0x8a6c4.
Definition tfib_A_alloc_slot : Z := 0x8a6c4.  Definition tfib_E_alloc_slot : Z := 0x8af68.
Definition tfib_A_enframe : Z := 0x8af68.  Definition tfib_E_enframe : Z := 0x8b0b8.
Definition tfib_A_malloc_allzerop : Z := 0x8b0b8.  Definition tfib_E_malloc_allzerop : Z := 0x8b230.
Definition tfib_A_getrlimit : Z := 0x8cee0.  Definition tfib_E_getrlimit : Z := 0x8cfd8.
Definition tfib_A_getrusage : Z := 0x8cfd8.  Definition tfib_E_getrusage : Z := 0x8d000.
Definition tfib_A_setrlimit : Z := 0x8d000.  Definition tfib_E_setrlimit : Z := 0x8d0c8.
Definition tfib_A_mmap : Z := 0x8d4f0.  Definition tfib_E_mmap : Z := 0x8d5dc.
Definition tfib_A_mprotect : Z := 0x8d5dc.  Definition tfib_E_mprotect : Z := 0x8d624.
Definition tfib_A_munmap : Z := 0x8d6f8.  Definition tfib_E_munmap : Z := 0x8d740.
Definition tfib_A_sched_yield : Z := 0x8da04.  Definition tfib_E_sched_yield : Z := 0x8da28.
Definition tfib_A_raise_tkill_path : Z := 0x8da84.  Definition tfib_E_raise_tkill_path : Z := 0x8dafc.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8dafc.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8dcd0.
Definition tfib_A_musl_sigaltstack : Z := 0x8ddc8.  Definition tfib_E_musl_sigaltstack : Z := 0x8de54.
Definition tfib_A_dprintf : Z := 0x8e430.  Definition tfib_E_dprintf : Z := 0x8e494.
(* cgif musl fclose (0x92ee4+0xcc): not linked into fuzz_boxreg.asan-ubsan; dropped *)
Definition tfib_A_lockfile : Z := 0x8e494.  Definition tfib_E_lockfile : Z := 0x8e590.
Definition tfib_A_unlockfile : Z := 0x8e590.  Definition tfib_E_unlockfile : Z := 0x8e5f0.
(* cgif musl fopen (0x93540+0xdc): not linked into fuzz_boxreg.asan-ubsan; dropped *)
(* cgif musl __fmodeflags (0x9361c+0xb4): not linked into fuzz_boxreg.asan-ubsan; dropped *)
(* cgif musl __fdopen (0x929c4+0x1d8): not linked into fuzz_boxreg.asan-ubsan; dropped *)
Definition tfib_A_stdio_read : Z := 0x8e180.  Definition tfib_E_stdio_read : Z := 0x8e298.
Definition tfib_A_stdio_write : Z := 0x8e2a0.  Definition tfib_E_stdio_write : Z := 0x8e430.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8e150.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8e154.
Definition tfib_A_stdio_close : Z := 0x8e154.  Definition tfib_E_stdio_close : Z := 0x8e180.
Definition tfib_A_fwritex : Z := 0x8ea24.  Definition tfib_E_fwritex : Z := 0x8eb5c.
Definition tfib_A_musl_fwrite : Z := 0x8eb5c.  Definition tfib_E_musl_fwrite : Z := 0x8ec14.
Definition tfib_A_towrite : Z := 0x8ec14.  Definition tfib_E_towrite : Z := 0x8ec68.
Definition tfib_A_stdio_exit : Z := 0x8e880.  Definition tfib_E_stdio_exit : Z := 0x8ea24.
Definition tfib_A_ofl_lock : Z := 0x8ec68.  Definition tfib_E_ofl_lock : Z := 0x8ec98.
(* cgif musl __ofl_add (0x93950+0x40): not linked into fuzz_boxreg.asan-ubsan; dropped *)
Definition tfib_A_musl_vfprintf : Z := 0x8ede4.  Definition tfib_E_musl_vfprintf : Z := 0x8ef94.
Definition tfib_A_printf_core : Z := 0x8ef94.  Definition tfib_E_printf_core : Z := 0x8fdc4.
Definition tfib_A_pop_arg : Z := 0x8fdc4.  Definition tfib_E_pop_arg : Z := 0x8fef8.
Definition tfib_A_pad : Z := 0x8fef8.  Definition tfib_E_pad : Z := 0x8ffcc.
Definition tfib_A_fmt_fp : Z := 0x8ffcc.  Definition tfib_E_fmt_fp : Z := 0x91694.
Definition tfib_A_lctrans : Z := 0x894e0.  Definition tfib_E_lctrans : Z := 0x894e4.
Definition tfib_A_musl_wctomb : Z := 0x8d86c.  Definition tfib_E_musl_wctomb : Z := 0x8d890.
Definition tfib_A_musl_wcrtomb : Z := 0x8d740.  Definition tfib_E_musl_wcrtomb : Z := 0x8d86c.
Definition tfib_A_fpclassifyl : Z := 0x8bad0.  Definition tfib_E_fpclassifyl : Z := 0x8bb14.
Definition tfib_A_letf2 : Z := 0x8b308.  Definition tfib_E_letf2 : Z := 0x8b3d0.
Definition tfib_A_multf3 : Z := 0x8b3d0.  Definition tfib_E_multf3 : Z := 0x8bad0.
Definition tfib_A_floatsitf : Z := 0x8c32c.  Definition tfib_E_floatsitf : Z := 0x8c434.
Definition tfib_A_scalbn : Z := 0x8cd38.  Definition tfib_E_scalbn : Z := 0x8cdd0.
Definition tfib_A_subtf3 : Z := 0x8c31c.  Definition tfib_E_subtf3 : Z := 0x8c32c.
Definition tfib_A_addtf3 : Z := 0x8bb14.  Definition tfib_E_addtf3 : Z := 0x8c2e0.
Definition tfib_A_fe_getround : Z := 0x8c2e0.  Definition tfib_E_fe_getround : Z := 0x8c310.
Definition tfib_A_fixunstfsi : Z := 0x9169c.  Definition tfib_E_fixunstfsi : Z := 0x91730.
Definition tfib_A_floatunsitf : Z := 0x91730.  Definition tfib_E_floatunsitf : Z := 0x9181c.
Definition tfib_A_fixtfsi : Z := 0x8cdd0.  Definition tfib_E_fixtfsi : Z := 0x8ce78.
Definition tfib_A_divtf3 : Z := 0x8c434.  Definition tfib_E_divtf3 : Z := 0x8cd38.
Definition tfib_A_musl_vprintf : Z := 0x91ef4.  Definition tfib_E_musl_vprintf : Z := 0x91f10.
Definition tfib_A_stdout_write : Z := 0x8eca4.  Definition tfib_E_stdout_write : Z := 0x8ed44.
Definition tfib_A_bcmp : Z := 0x924a8.  Definition tfib_E_bcmp : Z := 0x924ac.
Definition tfib_A_musl_memcmp : Z := 0x92578.  Definition tfib_E_musl_memcmp : Z := 0x925a8.
Definition tfib_A_musl_memcpy : Z := 0x925a8.  Definition tfib_E_musl_memcpy : Z := 0x929ac.
Definition tfib_A_musl_memset : Z := 0x929ac.  Definition tfib_E_musl_memset : Z := 0x92aa4.
Definition tfib_A_musl_strchr : Z := 0x92aa4.  Definition tfib_E_musl_strchr : Z := 0x92ae0.
Definition tfib_A_strchrnul : Z := 0x92ae0.  Definition tfib_E_strchrnul : Z := 0x92bc0.
Definition tfib_A_musl_strlen : Z := 0x92bf8.  Definition tfib_E_musl_strlen : Z := 0x92c88.
Definition tfib_A_musl_strnlen : Z := 0x92e94.  Definition tfib_E_musl_strnlen : Z := 0x92ed8.
Definition tfib_A_musl_memchr : Z := 0x924ac.  Definition tfib_E_musl_memchr : Z := 0x92578.
Definition tfib_A_lock : Z := 0x92ed8.  Definition tfib_E_lock : Z := 0x93160.
Definition tfib_A_unlock : Z := 0x93160.  Definition tfib_E_unlock : Z := 0x931d4.
Definition tfib_A_syscall_cp_c : Z := 0x931d4.  Definition tfib_E_syscall_cp_c : Z := 0x931f8.
Definition tfib_A_syscall_cp_sccp : Z := 0x931f8.  Definition tfib_E_syscall_cp_sccp : Z := 0x931fc.
Definition tfib_A_tls_get_addr : Z := 0x931fc.  Definition tfib_E_tls_get_addr : Z := 0x93220.
Definition tfib_A_pthread_atfork : Z := 0x93238.  Definition tfib_E_pthread_atfork : Z := 0x932dc.
Definition tfib_A_mremap : Z := 0x8d624.  Definition tfib_E_mremap : Z := 0x8d6f8.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x942b0.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x942cc.
Definition tfib_A_pthread_key_create : Z := 0x94658.  Definition tfib_E_pthread_key_create : Z := 0x9472c.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x949d0.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x94a74.
(* cgif merged row pthread_key_create_body_tsd_init (0x99700+0x11c) = boxreg __pthread_rwlock_wrlock + __pthread_rwlock_timedwrlock; split *)
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x94a74.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x94a7c.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x94a7c.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x94b90.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x94b90.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x94bbc.
Definition tfib_A_pthread_setspecific : Z := 0x94bf4.  Definition tfib_E_pthread_setspecific : Z := 0x94c28.
Definition tfib_A_set_thread_area : Z := 0x94c30.  Definition tfib_E_set_thread_area : Z := 0x94c3c.
(* cgif merged row thunk_96f9c (0x998b4+0x8) = boxreg __pthread_testcancel + __testcancel; split, rows named by those symbols *)
Definition tfib_A_pthread_testcancel : Z := 0x94c28.  Definition tfib_E_pthread_testcancel : Z := 0x94c2c.
Definition tfib_A_testcancel : Z := 0x94c2c.  Definition tfib_E_testcancel : Z := 0x94c30.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9555c.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x95614.
Definition tfib_A_close : Z := 0x97c2c.  Definition tfib_E_close : Z := 0x97c80.
Definition tfib_A_musl_read : Z := 0x97d0c.  Definition tfib_E_musl_read : Z := 0x97d40.
Definition tfib_A_vm_wait : Z := 0x9526c.  Definition tfib_E_vm_wait : Z := 0x952bc.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x98d40.
Definition tfib_D_fini_array_0_1 : Z := 0x98d60.
Definition tfib_D_GOT_common_flags : Z := 0x992c8.
Definition tfib_D_GOT_flags : Z := 0x992d0.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x992d8.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x992e0.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x992e8.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x992f0.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x99e40.
Definition tfib_D_environ_musl : Z := 0x99f68.
Definition tfib_D_REAL_read : Z := 0x9b018.
Definition tfib_D_REAL_memcpy : Z := 0x9b140.
Definition tfib_D_REAL_memset : Z := 0x9b148.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9dd58.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9ebb8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa13b8.
Definition tfib_D_asan_inited : Z := 0xa2098.
Definition tfib_D_replace_intrin_cached : Z := 0xa2099.
Definition tfib_D_kHighMemEnd : Z := 0xa20a0.
Definition tfib_D_kMidMemBeg : Z := 0xa20a8.
Definition tfib_D_kMidMemEnd : Z := 0xa20b0.
Definition tfib_D_malloc_context_size : Z := 0xa20bc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x132ee8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f45e0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2ffb8.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63484.
Definition tfib_at_x_imemcpy : Z := 0x63408.
Definition tfib_at_x_memset : Z := 0x929ac.
Definition tfib_at_x_memcpy : Z := 0x925a8.
Definition tfib_at_x_memiszero : Z := 0x639b4.
Definition tfib_at_x_istrncpy : Z := 0x638b0.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x363a4.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x883ac.
Definition tfib_at_x_envscan_k : Z := 0x883b8.
Definition tfib_at_x_pnscan : Z := 0x88470.
Definition tfib_at_x_pnscan_k : Z := 0x8847c.
Definition tfib_at_stops_more : list Z := (0x34018 :: 0x3563c :: 0x53790 :: 0x59b48 :: 0x59b5c :: 0x59b70 :: 0x5f500 :: 0x5f5d0 :: 0x6cafc :: 0x6da08 :: 0x6db98 :: 0x778f0 :: nil)%list.
