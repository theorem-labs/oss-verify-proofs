(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/A/AB1w.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22584.
Definition tfib_text_lo : Z := 0x2fbf0.  Definition tfib_text_hi : Z := 0x95a88.
Definition tfib_init_array_lo : Z := 0x96a88.  Definition tfib_init_array_hi : Z := 0x96aa8.
Definition tfib_fini_array_lo : Z := 0x96aa8.  Definition tfib_fini_array_hi : Z := 0x96ab8.
Definition tfib_preinit_array_lo : Z := 0x96ab8.  Definition tfib_preinit_array_hi : Z := 0x96ac0.
Definition tfib_data_rel_ro_lo : Z := 0x96ac0.  Definition tfib_data_rel_ro_hi : Z := 0x96fc0.
Definition tfib_got_lo : Z := 0x96fc0.  Definition tfib_got_hi : Z := 0x97d18.
Definition tfib_data_lo : Z := 0x98d18.  Definition tfib_data_hi : Z := 0x9b8c8.
Definition tfib_asan_globals_lo : Z := 0x9b8d0.  Definition tfib_asan_globals_hi : Z := 0x9b910.
Definition tfib_bss_lo : Z := 0x9b940.  Definition tfib_bss_hi : Z := 0x5f3870.
Definition tfib_tbss_lo : Z := 0x95a88.  Definition tfib_tbss_hi : Z := 0x95a9c.
Definition tfib_img_lo : Z := IMG_LO.  Definition tfib_img_hi : Z := IMG_TOP.
Definition tfib_entry : Z := 0x2fbf0.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2fbf0.  Definition tfib_E_start : Z := 0x2fc38.
Definition tfib_A_do_init : Z := 0x2fc38.  Definition tfib_E_do_init : Z := 0x2fcac.
Definition tfib_A_do_fini : Z := 0x2fcac.  Definition tfib_E_do_fini : Z := 0x2fd3c.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x2fd3c.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x2fd78.
Definition tfib_A_InitializeAllocator : Z := 0x2fee8.  Definition tfib_E_InitializeAllocator : Z := 0x2ff00.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x2ff00.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x3006c.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x305c8.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30724.
Definition tfib_A_asan_free : Z := 0x30af8.  Definition tfib_E_asan_free : Z := 0x30b20.
Definition tfib_A_Allocator_Deallocate : Z := 0x30b20.  Definition tfib_E_Allocator_Deallocate : Z := 0x30dd8.
Definition tfib_A_asan_malloc : Z := 0x30dd8.  Definition tfib_E_asan_malloc : Z := 0x30e34.
Definition tfib_A_Allocator_Allocate : Z := 0x30e34.  Definition tfib_E_Allocator_Allocate : Z := 0x317bc.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x31ef4.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32038.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32124.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32180.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32180.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x323d0.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x323d0.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x324c4.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x324c4.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x325ac.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x329e0.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x32bc4.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x32bc4.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x32d48.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x32e80.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33104.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33104.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33284.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33284.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3344c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x3344c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33618.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x33618.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x336b8.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x336b8.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x337bc.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33ae4.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33c2c.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x33c2c.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x33c64.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x343fc.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x346e4.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x34dbc.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x34f34.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x34f34.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x350e4.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x350e4.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x352c8.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x352c8.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x355a0.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x355a0.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35a18.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35a18.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35b18.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35b18.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x35e20.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x35e20.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36190.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36190.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x362a8.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x365b0.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x366ac.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x366ac.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36794.
Definition tfib_A_AsanActivate : Z := 0x36794.  Definition tfib_E_AsanActivate : Z := 0x36870.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x36d4c.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x36e34.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3b8ec.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3b9c4.
Definition tfib_A_FakeStack_Create : Z := 0x3b9c4.  Definition tfib_E_FakeStack_Create : Z := 0x3bab0.
Definition tfib_A_FakeStack_Allocate : Z := 0x3bd6c.  Definition tfib_E_FakeStack_Allocate : Z := 0x3c054.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c188.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c1b8.

Definition tfib_A_asan_stack_malloc_1 : Z := 0x3c1b8.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3c348.


Definition tfib_A_FakeStack_SetShadow : Z := 0x3c348.  Definition tfib_E_FakeStack_SetShadow : Z := 0x3c484.
Definition tfib_A_asan_InitializeFlags : Z := 0x3c484.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d4b0.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3dbbc.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e9d8.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3e9d8.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3efa4.
Definition tfib_A_asan_register_globals : Z := 0x3efa4.  Definition tfib_E_asan_register_globals : Z := 0x3f010.
Definition tfib_A_asan_unregister_globals : Z := 0x3f010.  Definition tfib_E_asan_unregister_globals : Z := 0x3f078.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x3f6f8.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x3f968.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x3f968.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x3fc70.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x403e4.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40534.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x40f50.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x41068.
Definition tfib_A_strlen : Z := 0x41068.  Definition tfib_E_strlen : Z := 0x4106c.
Definition tfib_A_strnlen : Z := 0x4106c.  Definition tfib_E_strnlen : Z := 0x41070.
Definition tfib_A_strcmp : Z := 0x41070.  Definition tfib_E_strcmp : Z := 0x41074.
Definition tfib_A_strchr : Z := 0x41074.  Definition tfib_E_strchr : Z := 0x41078.
Definition tfib_A_memcmp : Z := 0x41078.  Definition tfib_E_memcmp : Z := 0x4107c.
Definition tfib_A_check_no_overread : Z := 0x7f4fc.  Definition tfib_E_check_no_overread : Z := 0x7f62c.  Definition tfib_A_check_value : Z := 0x7f62c.  Definition tfib_E_check_value : Z := 0x7f888.  Definition tfib_A_check_clamp : Z := 0x7f888.  Definition tfib_E_check_clamp : Z := 0x7fbfc.  Definition tfib_A_rp_hot_clamp : Z := 0x7fc64.  Definition tfib_E_rp_hot_clamp : Z := 0x7fef0.  Definition tfib_A_rp_uci_int : Z := 0x7fef0.  Definition tfib_E_rp_uci_int : Z := 0x80104.
Definition tfib_A_memchr : Z := 0x4107c.  Definition tfib_E_memchr : Z := 0x41080.
Definition tfib_A_frexpl : Z := 0x41080.  Definition tfib_E_frexpl : Z := 0x41084.
Definition tfib_A_read : Z := 0x41084.  Definition tfib_E_read : Z := 0x41088.
Definition tfib_A_fwrite : Z := 0x41088.  Definition tfib_E_fwrite : Z := 0x4108c.
Definition tfib_A_time : Z := 0x4108c.  Definition tfib_E_time : Z := 0x41090.
Definition tfib_A_gmtime_r : Z := 0x41090.  Definition tfib_E_gmtime_r : Z := 0x41094.
Definition tfib_A_vprintf : Z := 0x41094.  Definition tfib_E_vprintf : Z := 0x41098.
Definition tfib_A_vfprintf : Z := 0x41098.  Definition tfib_E_vfprintf : Z := 0x4109c.
Definition tfib_A_vsnprintf : Z := 0x4109c.  Definition tfib_E_vsnprintf : Z := 0x410a0.
Definition tfib_A_vfprintf_2 : Z := 0x410a0.  Definition tfib_E_vfprintf_2 : Z := 0x410a4.
Definition tfib_A_thunk_417bc : Z := 0x410a4.  Definition tfib_E_thunk_417bc : Z := 0x410a8.
Definition tfib_A_clock_gettime : Z := 0x410a8.  Definition tfib_E_clock_gettime : Z := 0x410ac.
Definition tfib_A_wcrtomb : Z := 0x410ac.  Definition tfib_E_wcrtomb : Z := 0x410b0.
Definition tfib_A_wctomb : Z := 0x410b0.  Definition tfib_E_wctomb : Z := 0x410b4.
Definition tfib_A_thunk_417cc : Z := 0x410b4.  Definition tfib_E_thunk_417cc : Z := 0x410bc.
Definition tfib_A_pthread_attr_getstack : Z := 0x410bc.  Definition tfib_E_pthread_attr_getstack : Z := 0x410c0.
Definition tfib_A_tls_get_addr_thunk : Z := 0x410c0.  Definition tfib_E_tls_get_addr_thunk : Z := 0x410c4.
Definition tfib_A_thunk_417dc : Z := 0x410c4.  Definition tfib_E_thunk_417dc : Z := 0x410c8.
Definition tfib_A_thunk_417e4 : Z := 0x410c8.  Definition tfib_E_thunk_417e4 : Z := 0x410cc.
Definition tfib_A_thunk_417e8 : Z := 0x410cc.  Definition tfib_E_thunk_417e8 : Z := 0x410d0.
Definition tfib_A_thunk_417ec : Z := 0x410d0.  Definition tfib_E_thunk_417ec : Z := 0x410d4.
Definition tfib_A_thunk_417f0 : Z := 0x410d4.  Definition tfib_E_thunk_417f0 : Z := 0x410d8.
Definition tfib_A_sem_timedwait : Z := 0x410d8.  Definition tfib_E_sem_timedwait : Z := 0x410dc.
Definition tfib_A_thunk_417f8 : Z := 0x410dc.  Definition tfib_E_thunk_417f8 : Z := 0x410e0.
Definition tfib_A_pthread_setcancelstate : Z := 0x410e0.  Definition tfib_E_pthread_setcancelstate : Z := 0x410e4.
Definition tfib_A_send : Z := 0x410e4.  Definition tfib_E_send : Z := 0x410e8.
Definition tfib_A_sendto : Z := 0x410e8.  Definition tfib_E_sendto : Z := 0x410ec.
Definition tfib_A_sigaltstack : Z := 0x410ec.  Definition tfib_E_sigaltstack : Z := 0x410f0.
Definition tfib_A_thunk_4180c : Z := 0x410f0.  Definition tfib_E_thunk_4180c : Z := 0x410f4.
Definition tfib_A_icpt_strlen : Z := 0x410f4.  Definition tfib_E_icpt_strlen : Z := 0x41388.
Definition tfib_A_icpt_strnlen : Z := 0x41388.  Definition tfib_E_icpt_strnlen : Z := 0x4161c.
Definition tfib_A_icpt_strcmp : Z := 0x41620.  Definition tfib_E_icpt_strcmp : Z := 0x41b50.
Definition tfib_A_icpt_strchr : Z := 0x41b50.  Definition tfib_E_icpt_strchr : Z := 0x41e30.
Definition tfib_A_icpt_memcmp : Z := 0x426c8.  Definition tfib_E_icpt_memcmp : Z := 0x42784.

Definition tfib_A_icpt_memchr : Z := 0x42784.  Definition tfib_E_icpt_memchr : Z := 0x42a54.
Definition tfib_A_icpt_frexpl : Z := 0x42a54.  Definition tfib_E_icpt_frexpl : Z := 0x42ccc.
Definition tfib_A_icpt_read : Z := 0x42ccc.  Definition tfib_E_icpt_read : Z := 0x42f3c.
Definition tfib_A_icpt_fwrite : Z := 0x42f3c.  Definition tfib_E_icpt_fwrite : Z := 0x431b0.
Definition tfib_A_icpt_time : Z := 0x431b0.  Definition tfib_E_icpt_time : Z := 0x4344c.
Definition tfib_A_icpt_gmtime_r : Z := 0x43654.  Definition tfib_E_icpt_gmtime_r : Z := 0x43894.
Definition tfib_A_icpt_vprintf : Z := 0x43894.  Definition tfib_E_icpt_vprintf : Z := 0x43930.
Definition tfib_A_printf_common_format_interceptor : Z := 0x43930.  Definition tfib_E_printf_common_format_interceptor : Z := 0x443f8.
Definition tfib_A_icpt_vfprintf : Z := 0x443f8.  Definition tfib_E_icpt_vfprintf : Z := 0x444ac.
Definition tfib_A_icpt_vsnprintf : Z := 0x444ac.  Definition tfib_E_icpt_vsnprintf : Z := 0x447c4.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x447c4.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x4489c.
Definition tfib_A_icpt_clock_gettime : Z := 0x44940.  Definition tfib_E_icpt_clock_gettime : Z := 0x44b98.
Definition tfib_A_icpt_wcrtomb : Z := 0x44b98.  Definition tfib_E_icpt_wcrtomb : Z := 0x45108.
Definition tfib_A_icpt_wctomb : Z := 0x45108.  Definition tfib_E_icpt_wctomb : Z := 0x45464.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45530.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45918.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45924.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x459a0.
Definition tfib_A_icpt_sem_timedwait : Z := 0x45bac.  Definition tfib_E_icpt_sem_timedwait : Z := 0x45e44.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x45e74.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4609c.
Definition tfib_A_icpt_send : Z := 0x4609c.  Definition tfib_E_icpt_send : Z := 0x46350.
Definition tfib_A_icpt_sendto : Z := 0x46350.  Definition tfib_E_icpt_sendto : Z := 0x46614.
Definition tfib_A_icpt_sigaltstack : Z := 0x46614.  Definition tfib_E_icpt_sigaltstack : Z := 0x46870.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46944.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x46af4.
Definition tfib_A_icpt_diouxXn : Z := 0x46af4.  Definition tfib_E_icpt_diouxXn : Z := 0x46c8c.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x47838.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x50510.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x50510.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x5066c.
Definition tfib_A_memset : Z := 0x5066c.  Definition tfib_E_memset : Z := 0x50670.
Definition tfib_A_memcpy : Z := 0x50670.  Definition tfib_E_memcpy : Z := 0x50674.
Definition tfib_A_asan_memcpy : Z := 0x50674.  Definition tfib_E_asan_memcpy : Z := 0x50b10.

Definition tfib_A_icpt_memset : Z := 0x50b10.  Definition tfib_E_icpt_memset : Z := 0x50e00.
Definition tfib_A_icpt_memcpy : Z := 0x50e00.  Definition tfib_E_icpt_memcpy : Z := 0x513f0.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x513f0.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51428.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51428.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x5142c.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x5142c.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51430.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x51430.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x51490.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x514dc.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51618.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x51618.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x5161c.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x5161c.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x51784.
Definition tfib_A_free : Z := 0x51784.  Definition tfib_E_free : Z := 0x51788.
Definition tfib_A_malloc : Z := 0x51788.  Definition tfib_E_malloc : Z := 0x5178c.
Definition tfib_A_icpt_free : Z := 0x5178c.  Definition tfib_E_icpt_free : Z := 0x5195c.
Definition tfib_A_icpt_malloc : Z := 0x5195c.  Definition tfib_E_icpt_malloc : Z := 0x51ab8.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x51ab8.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x51b84.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x51b84.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x51b88.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x51b88.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x51c88.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x51fb0.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x5211c.
Definition tfib_A_SetCanPoisonMemory : Z := 0x52604.  Definition tfib_E_SetCanPoisonMemory : Z := 0x52614.
Definition tfib_A_CanPoisonMemory : Z := 0x52614.  Definition tfib_E_CanPoisonMemory : Z := 0x52628.
Definition tfib_A_PoisonShadow : Z := 0x52628.  Definition tfib_E_PoisonShadow : Z := 0x52b24.
Definition tfib_A_MemToShadow_checked : Z := 0x52b24.  Definition tfib_E_MemToShadow_checked : Z := 0x52c60.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x52c60.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x52e00.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x52e00.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x52f80.
Definition tfib_A_asan_region_is_poisoned : Z := 0x52fb0.  Definition tfib_E_asan_region_is_poisoned : Z := 0x532f4.
Definition tfib_A_AsanTSDInit : Z := 0x53714.  Definition tfib_E_AsanTSDInit : Z := 0x53790.
Definition tfib_A_AsanTSDGet : Z := 0x53790.  Definition tfib_E_AsanTSDGet : Z := 0x537d0.
Definition tfib_A_AsanTSDSet : Z := 0x537d0.  Definition tfib_E_AsanTSDSet : Z := 0x53810.
Definition tfib_A_PlatformTSDDtor : Z := 0x53810.  Definition tfib_E_PlatformTSDDtor : Z := 0x53894.
Definition tfib_A_InstallAtForkHandler : Z := 0x53894.  Definition tfib_E_InstallAtForkHandler : Z := 0x538b0.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x53910.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x53954.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x5406c.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x54278.
Definition tfib_A_ReportDoubleFree : Z := 0x54980.  Definition tfib_E_ReportDoubleFree : Z := 0x54c10.
Definition tfib_A_ReportGenericError : Z := 0x564ec.  Definition tfib_E_ReportGenericError : Z := 0x56da8.
Definition tfib_A_AsanInited : Z := 0x57534.  Definition tfib_E_AsanInited : Z := 0x5754c.
Definition tfib_A_asan_report_load1 : Z := 0x5754c.  Definition tfib_E_asan_report_load1 : Z := 0x5759c.
Definition tfib_A_asan_report_exp_load1 : Z := 0x5759c.  Definition tfib_E_asan_report_exp_load1 : Z := 0x575ec.
Definition tfib_A_asan_report_load2 : Z := 0x575ec.  Definition tfib_E_asan_report_load2 : Z := 0x5763c.
Definition tfib_A_asan_report_exp_load2 : Z := 0x5763c.  Definition tfib_E_asan_report_exp_load2 : Z := 0x5768c.
Definition tfib_A_asan_report_load4 : Z := 0x5768c.  Definition tfib_E_asan_report_load4 : Z := 0x576dc.
Definition tfib_A_asan_report_exp_load4 : Z := 0x576dc.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5772c.
Definition tfib_A_asan_report_load8 : Z := 0x5772c.  Definition tfib_E_asan_report_load8 : Z := 0x5777c.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5777c.  Definition tfib_E_asan_report_exp_load8 : Z := 0x577cc.
Definition tfib_A_asan_report_load16 : Z := 0x577cc.  Definition tfib_E_asan_report_load16 : Z := 0x5781c.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5781c.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5786c.
Definition tfib_A_asan_report_store1 : Z := 0x5786c.  Definition tfib_E_asan_report_store1 : Z := 0x578bc.
Definition tfib_A_asan_report_exp_store1 : Z := 0x578bc.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5790c.
Definition tfib_A_asan_report_store2 : Z := 0x5790c.  Definition tfib_E_asan_report_store2 : Z := 0x5795c.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5795c.  Definition tfib_E_asan_report_exp_store2 : Z := 0x579ac.
Definition tfib_A_asan_report_store4 : Z := 0x579ac.  Definition tfib_E_asan_report_store4 : Z := 0x579fc.
Definition tfib_A_asan_report_exp_store4 : Z := 0x579fc.  Definition tfib_E_asan_report_exp_store4 : Z := 0x57a4c.
Definition tfib_A_asan_report_store8 : Z := 0x57a4c.  Definition tfib_E_asan_report_store8 : Z := 0x57a9c.
Definition tfib_A_asan_report_exp_store8 : Z := 0x57a9c.  Definition tfib_E_asan_report_exp_store8 : Z := 0x57aec.
Definition tfib_A_asan_report_store16 : Z := 0x57aec.  Definition tfib_E_asan_report_store16 : Z := 0x57b3c.
Definition tfib_A_asan_report_exp_store16 : Z := 0x57b3c.  Definition tfib_E_asan_report_exp_store16 : Z := 0x57b8c.
Definition tfib_A_asan_report_load_n : Z := 0x57b8c.  Definition tfib_E_asan_report_load_n : Z := 0x57bdc.
Definition tfib_A_asan_report_exp_load_n : Z := 0x57bdc.  Definition tfib_E_asan_report_exp_load_n : Z := 0x57c2c.
Definition tfib_A_asan_report_store_n : Z := 0x57c2c.  Definition tfib_E_asan_report_store_n : Z := 0x57c7c.
Definition tfib_A_asan_report_exp_store_n : Z := 0x57c7c.  Definition tfib_E_asan_report_exp_store_n : Z := 0x57ccc.
Definition tfib_A_InitializeHighMemEnd : Z := 0x57ccc.  Definition tfib_E_InitializeHighMemEnd : Z := 0x57d4c.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x57d4c.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58100.
Definition tfib_A_AsanInitInternal : Z := 0x58190.  Definition tfib_E_AsanInitInternal : Z := 0x58444.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x58444.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x584e4.
Definition tfib_A_thunk_59674 : Z := 0x586ac.  Definition tfib_E_thunk_59674 : Z := 0x586b0.
Definition tfib_A_asan_init : Z := 0x586b0.  Definition tfib_E_asan_init : Z := 0x58744.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x58744.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x58748.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x58748.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x587ac.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x58920.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x58928.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x589ac.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x58cd4.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x58cd4.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x58eb4.
Definition tfib_A_InitializeShadowMemory : Z := 0x58eb4.  Definition tfib_E_InitializeShadowMemory : Z := 0x591bc.
Definition tfib_A_SetMallocContextSize : Z := 0x591bc.  Definition tfib_E_SetMallocContextSize : Z := 0x591cc.
Definition tfib_A_GetMallocContextSize : Z := 0x591cc.  Definition tfib_E_GetMallocContextSize : Z := 0x591dc.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x591dc.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5932c.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5970c.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x599ac.
Definition tfib_A_GetCurrentThreadStats : Z := 0x59e10.  Definition tfib_E_GetCurrentThreadStats : Z := 0x59e48.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5a0f0.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5a0fc.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5a0fc.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5a188.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5a188.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5a1f0.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5a1f0.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5a268.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5a268.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5a2d0.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5a2d0.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5a41c.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5a6a8.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5a6b4.
Definition tfib_A_AsanThread_Create : Z := 0x5a834.  Definition tfib_E_AsanThread_Create : Z := 0x5a9d0.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5aa2c.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5ac44.
Definition tfib_A_GetCurrentThread : Z := 0x5ac44.  Definition tfib_E_GetCurrentThread : Z := 0x5ac64.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5ac64.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5ae08.
Definition tfib_A_AsanThread_stack_top : Z := 0x5ae08.  Definition tfib_E_AsanThread_stack_top : Z := 0x5ae60.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5ae60.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5aeb8.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5aeb8.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5b0e8.
Definition tfib_A_AsanThread_Init : Z := 0x5b0e8.  Definition tfib_E_AsanThread_Init : Z := 0x5b4dc.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5b4dc.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5b5e8.
Definition tfib_A_CreateMainThread : Z := 0x5b61c.  Definition tfib_E_CreateMainThread : Z := 0x5b72c.
Definition tfib_A_SetCurrentThread : Z := 0x5b72c.  Definition tfib_E_SetCurrentThread : Z := 0x5b80c.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5ba10.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5bb4c.
Definition tfib_A_weak_default_hook_ret : Z := 0x5c820.  Definition tfib_E_weak_default_hook_ret : Z := 0x5c824.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5c82c.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5ca6c.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5ccc0.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5ce18.
Definition tfib_A_internal_allocator_getter : Z := 0x5d004.  Definition tfib_E_internal_allocator_getter : Z := 0x5d010.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5d010.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5d15c.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5d15c.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5d1a8.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5d1a8.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5d1b4.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5d1e4.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5d1f0.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5d1f0.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5d1fc.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5d1fc.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5d20c.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5d218.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5d4e4.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5d4e4.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5d8a4.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5e800.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5e80c.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5e80c.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5e8e4.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5e8e4.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5e980.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5eea4.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5eee8.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5eee8.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5ef0c.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5f160.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5f274.
Definition tfib_A_RunMallocHooks : Z := 0x5f418.  Definition tfib_E_RunMallocHooks : Z := 0x5f4d0.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x5f4d0.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x5f4d4.
Definition tfib_A_RunFreeHooks : Z := 0x5f4d4.  Definition tfib_E_RunFreeHooks : Z := 0x5f580.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x5f580.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x5f588.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x5f588.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x5f58c.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x5f5b4.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x5f600.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x5f8c4.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x5fb04.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60100.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60118.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60118.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x6025c.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x6025c.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60264.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x605ac.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x61850.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x61850.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x61874.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x61d28.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62038.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62038.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x6217c.
Definition tfib_A_FlagParser_ParseString : Z := 0x6217c.  Definition tfib_E_FlagParser_ParseString : Z := 0x62270.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x62404.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x62464.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x62464.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x624a4.
Definition tfib_A_internal_atoll : Z := 0x624a4.  Definition tfib_E_internal_atoll : Z := 0x62590.
Definition tfib_A_internal_simple_strtoll : Z := 0x62590.  Definition tfib_E_internal_simple_strtoll : Z := 0x626ec.
Definition tfib_A_internal_memchr : Z := 0x626ec.  Definition tfib_E_internal_memchr : Z := 0x6270c.
Definition tfib_A_internal_memcmp : Z := 0x6270c.  Definition tfib_E_internal_memcmp : Z := 0x62744.
Definition tfib_A_internal_memcpy : Z := 0x62744.  Definition tfib_E_internal_memcpy : Z := 0x62768.
Definition tfib_A_internal_memmove : Z := 0x62768.  Definition tfib_E_internal_memmove : Z := 0x627c0.
Definition tfib_A_internal_memset : Z := 0x627c0.  Definition tfib_E_internal_memset : Z := 0x62820.
Definition tfib_A_internal_strcspn : Z := 0x62820.  Definition tfib_E_internal_strcspn : Z := 0x62874.
Definition tfib_A_internal_strcmp : Z := 0x62874.  Definition tfib_E_internal_strcmp : Z := 0x628a8.
Definition tfib_A_internal_strdup : Z := 0x628a8.  Definition tfib_E_internal_strdup : Z := 0x62914.
Definition tfib_A_internal_strlen : Z := 0x62914.  Definition tfib_E_internal_strlen : Z := 0x62930.
Definition tfib_A_internal_strncmp : Z := 0x62930.  Definition tfib_E_internal_strncmp : Z := 0x62974.
Definition tfib_A_internal_strchr : Z := 0x62974.  Definition tfib_E_internal_strchr : Z := 0x629c0.
Definition tfib_A_internal_strchrnul : Z := 0x629c0.  Definition tfib_E_internal_strchrnul : Z := 0x62a08.
Definition tfib_A_internal_strrchr : Z := 0x62a08.  Definition tfib_E_internal_strrchr : Z := 0x62a48.
Definition tfib_A_internal_strnlen : Z := 0x62b78.  Definition tfib_E_internal_strnlen : Z := 0x62ba8.
Definition tfib_A_internal_strncpy : Z := 0x62bec.  Definition tfib_E_internal_strncpy : Z := 0x62c5c.
Definition tfib_A_internal_strstr : Z := 0x62c5c.  Definition tfib_E_internal_strstr : Z := 0x62cf0.
Definition tfib_A_mem_is_zero : Z := 0x62cf0.  Definition tfib_E_mem_is_zero : Z := 0x62da4.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x62da4.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x62db4.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x62db4.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x62f94.
Definition tfib_A_internal_iserror : Z := 0x62fa0.  Definition tfib_E_internal_iserror : Z := 0x62fc0.
Definition tfib_A_internal_mmap : Z := 0x62fc0.  Definition tfib_E_internal_mmap : Z := 0x62fcc.
Definition tfib_A_internal_munmap : Z := 0x62fcc.  Definition tfib_E_internal_munmap : Z := 0x62fd8.
Definition tfib_A_internal_mprotect : Z := 0x62fd8.  Definition tfib_E_internal_mprotect : Z := 0x62fe8.
Definition tfib_A_internal_madvise : Z := 0x62fe8.  Definition tfib_E_internal_madvise : Z := 0x63014.
Definition tfib_A_internal_close : Z := 0x63014.  Definition tfib_E_internal_close : Z := 0x63020.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63020.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63044.
Definition tfib_A_internal_read : Z := 0x63044.  Definition tfib_E_internal_read : Z := 0x6307c.
Definition tfib_A_internal_write : Z := 0x6307c.  Definition tfib_E_internal_write : Z := 0x630b4.
Definition tfib_A_internal_ftruncate : Z := 0x630b4.  Definition tfib_E_internal_ftruncate : Z := 0x630ec.
Definition tfib_A_internal_dup : Z := 0x630ec.  Definition tfib_E_internal_dup : Z := 0x630f8.
Definition tfib_A_internal_dup2_dup3 : Z := 0x630f8.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63108.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63108.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63120.
Definition tfib_A_internal_sched_yield : Z := 0x63120.  Definition tfib_E_internal_sched_yield : Z := 0x6312c.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x6312c.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63178.
Definition tfib_A_internal_execve : Z := 0x63178.  Definition tfib_E_internal_execve : Z := 0x63184.
Definition tfib_A_internal_exit_exit_group : Z := 0x63184.  Definition tfib_E_internal_exit_exit_group : Z := 0x63198.
Definition tfib_A_FileExists_newfstatat : Z := 0x63198.  Definition tfib_E_FileExists_newfstatat : Z := 0x63218.
Definition tfib_A_DirExists_newfstatat : Z := 0x63218.  Definition tfib_E_DirExists_newfstatat : Z := 0x6327c.
Definition tfib_A_GetTid_gettid : Z := 0x6327c.  Definition tfib_E_GetTid_gettid : Z := 0x63288.
Definition tfib_A_GetEnv : Z := 0x63288.  Definition tfib_E_GetEnv : Z := 0x633b8.
Definition tfib_A_FutexWait : Z := 0x634bc.  Definition tfib_E_FutexWait : Z := 0x634e0.
Definition tfib_A_FutexWake : Z := 0x634e0.  Definition tfib_E_FutexWake : Z := 0x63504.
Definition tfib_A_internal_ptrace : Z := 0x63504.  Definition tfib_E_internal_ptrace : Z := 0x63510.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x63510.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x63520.
Definition tfib_A_internal_getpid : Z := 0x63520.  Definition tfib_E_internal_getpid : Z := 0x6352c.
Definition tfib_A_internal_getppid : Z := 0x6352c.  Definition tfib_E_internal_getppid : Z := 0x63538.
Definition tfib_A_internal_prctl : Z := 0x63538.  Definition tfib_E_internal_prctl : Z := 0x63544.
Definition tfib_A_internal_sigaltstack : Z := 0x63544.  Definition tfib_E_internal_sigaltstack : Z := 0x63550.
Definition tfib_A_internal_fork_clone : Z := 0x63550.  Definition tfib_E_internal_fork_clone : Z := 0x63568.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x63568.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x63694.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x6386c.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x63c68.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x63dd4.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x63eec.
Definition tfib_A_GetPageSizeCached : Z := 0x63eec.  Definition tfib_E_GetPageSizeCached : Z := 0x63ef4.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x63ef4.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x63fa0.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x63fa0.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x640c0.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64188.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64208.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x64208.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x64264.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64264.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64330.
Definition tfib_A_thunk_653ec : Z := 0x6442c.  Definition tfib_E_thunk_653ec : Z := 0x64430.
Definition tfib_A_CheckASLR : Z := 0x64430.  Definition tfib_E_CheckASLR : Z := 0x64434.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x64680.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x64684.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x64684.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x64690.
Definition tfib_A_MmapOrDie : Z := 0x64690.  Definition tfib_E_MmapOrDie : Z := 0x6479c.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x6479c.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x64810.
Definition tfib_A_UnmapOrDie : Z := 0x64810.  Definition tfib_E_UnmapOrDie : Z := 0x6488c.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6488c.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x6499c.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x64bc8.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x64ccc.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x64ccc.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x64cd8.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x64cd8.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x64e50.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x64e50.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x64e5c.
Definition tfib_A_thunk_66008 : Z := 0x65048.  Definition tfib_E_thunk_66008 : Z := 0x6504c.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x6536c.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x65578.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x65b30.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x65b3c.
Definition tfib_A_Printf : Z := 0x65b40.  Definition tfib_E_Printf : Z := 0x65b8c.
Definition tfib_A_SharedPrintfCode : Z := 0x65b8c.  Definition tfib_E_SharedPrintfCode : Z := 0x65be8.
Definition tfib_A_Report : Z := 0x65be8.  Definition tfib_E_Report : Z := 0x65c34.
Definition tfib_A_SuppressionContext_ctor : Z := 0x6772c.  Definition tfib_E_SuppressionContext_ctor : Z := 0x67788.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x67788.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x679c4.
Definition tfib_A_SuppressionContext_Parse : Z := 0x679c4.  Definition tfib_E_SuppressionContext_Parse : Z := 0x67ce8.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68288.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68358.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x68358.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x686a8.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x686a8.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x686b8.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x688f4.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x68938.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x68938.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x68998.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x68998.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x68e10.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x696d0.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x699f4.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x699fc.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x69b00.
Definition tfib_A_AddDieCallback : Z := 0x6a2b0.  Definition tfib_E_AddDieCallback : Z := 0x6a338.
Definition tfib_A_Die : Z := 0x6a3fc.  Definition tfib_E_Die : Z := 0x6a4bc.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6a4bc.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6a4c8.
Definition tfib_A_CheckFailed : Z := 0x6a4c8.  Definition tfib_E_CheckFailed : Z := 0x6a580.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6abd8.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6acd0.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6acd0.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6adfc.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6b024.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6b0a0.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6b0d4.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6b3bc.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6b3bc.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6b3c0.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6b3c0.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6b7b0.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6b7b0.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6b880.
Definition tfib_A_AndroidLogInit : Z := 0x6bc64.  Definition tfib_E_AndroidLogInit : Z := 0x6bc68.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6bc98.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6bce0.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6bce0.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6bf2c.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6bf2c.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6bf30.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6bf30.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6c03c.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6c03c.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6c140.
Definition tfib_A_thunk_6d37c : Z := 0x6c3bc.  Definition tfib_E_thunk_6d37c : Z := 0x6c3c0.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6c464.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6c484.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6c484.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6c524.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6c570.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6c574.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6c5b0.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6c674.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6c674.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6c6fc.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6c6fc.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6c774.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6c774.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6c858.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6c914.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6ca48.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6cc80.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6cdb0.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6cdb0.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6ce10.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ce10.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6cedc.
Definition tfib_A_MprotectNoAccess : Z := 0x6cef0.  Definition tfib_E_MprotectNoAccess : Z := 0x6cf10.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6cf10.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6d05c.
Definition tfib_A_MmapFixedOrDie : Z := 0x6d05c.  Definition tfib_E_MmapFixedOrDie : Z := 0x6d06c.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x6e864.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x6e8a8.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6e8a8.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6e8d8.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6ed0c.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6ee30.
Definition tfib_A_StackStore_Alloc : Z := 0x6ee30.  Definition tfib_E_StackStore_Alloc : Z := 0x6ef64.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x6f818.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x6f8cc.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71020.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x7107c.
Definition tfib_A_StackDepotPut : Z := 0x71308.  Definition tfib_E_StackDepotPut : Z := 0x71328.
Definition tfib_A_StackDepotBase_Put : Z := 0x71328.  Definition tfib_E_StackDepotBase_Put : Z := 0x715ac.
Definition tfib_A_StackDepotBase_Get : Z := 0x715ac.  Definition tfib_E_StackDepotBase_Get : Z := 0x716bc.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x71a9c.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x71b2c.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x71b2c.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x71c2c.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x71c8c.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x71c94.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x71c94.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x71df4.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x71df4.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x71e68.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x722f0.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72408.
Definition tfib_A_thunk_762d8 : Z := 0x75454.  Definition tfib_E_thunk_762d8 : Z := 0x75458.
Definition tfib_A_thunk_77ab0 : Z := 0x76c2c.  Definition tfib_E_thunk_77ab0 : Z := 0x76c30.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x78658.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x78714.
Definition tfib_A_Unwind_Trace_callback : Z := 0x78714.  Definition tfib_E_Unwind_Trace_callback : Z := 0x787ec.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x787ec.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x78a60.
Definition tfib_A_lsan_flags_init_helper : Z := 0x78d8c.  Definition tfib_E_lsan_flags_init_helper : Z := 0x78dd0.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x78dd0.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x791a0.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x79470.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x79528.
Definition tfib_A_thunk_7b6f8 : Z := 0x7a880.  Definition tfib_E_thunk_7b6f8 : Z := 0x7a884.
Definition tfib_A_lsan_register_root_region : Z := 0x7b48c.  Definition tfib_E_lsan_register_root_region : Z := 0x7b7bc.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7b7bc.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7bc44.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7bc44.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7bc50.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7e808.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7e820.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7eba4.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7ec20.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7ec20.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7ecd0.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7ecd0.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7ece8.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7ece8.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7ee30.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7ee30.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7ee3c.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7ee3c.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7ee48.
Definition tfib_A_main : Z := 0x7ee48.  Definition tfib_E_main : Z := 0x7f10c.
Definition tfib_A_target_alloc_init : Z := 0x7f10c.  Definition tfib_E_target_alloc_init : Z := 0x7f110.
Definition tfib_A_target_alloc_count : Z := 0x7f110.  Definition tfib_E_target_alloc_count : Z := 0x7f118.
Definition tfib_A_target_run : Z := 0x7f118.  Definition tfib_E_target_run : Z := 0x7f2a0.
Definition tfib_A_emit_printf : Z := 0x7f2a0.  Definition tfib_E_emit_printf : Z := 0x7f2e8.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7f2e8.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7f4fc.

Definition tfib_A_asan_module_ctor : Z := 0x7fbfc.  Definition tfib_E_asan_module_ctor : Z := 0x7fc34.
Definition tfib_A_asan_module_dtor : Z := 0x7fc34.  Definition tfib_E_asan_module_dtor : Z := 0x7fc64.





















Definition tfib_A_extenddftf2 : Z := 0x80114.  Definition tfib_E_extenddftf2 : Z := 0x802a4.
Definition tfib_A_sysconf : Z := 0x85ef4.  Definition tfib_E_sysconf : Z := 0x8611c.
Definition tfib_A_init : Z := 0x8611c.  Definition tfib_E_init : Z := 0x86120.
Definition tfib_A_init_libc : Z := 0x86120.  Definition tfib_E_init_libc : Z := 0x8634c.
Definition tfib_A_libc_start_init : Z := 0x8634c.  Definition tfib_E_libc_start_init : Z := 0x86398.
Definition tfib_A_libc_start_main : Z := 0x86398.  Definition tfib_E_libc_start_main : Z := 0x863f8.
Definition tfib_A_libc_start_main_stage2 : Z := 0x863f8.  Definition tfib_E_libc_start_main_stage2 : Z := 0x86440.
Definition tfib_A_init_tls : Z := 0x86518.  Definition tfib_E_init_tls : Z := 0x867c8.
Definition tfib_A_init_ssp : Z := 0x867c8.  Definition tfib_E_init_ssp : Z := 0x86828.
Definition tfib_A_stack_chk_fail : Z := 0x86828.  Definition tfib_E_stack_chk_fail : Z := 0x86830.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x86878.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8690c.
Definition tfib_A_Exit : Z := 0x8690c.  Definition tfib_E_Exit : Z := 0x86928.
Definition tfib_A_funcs_on_exit : Z := 0x86958.  Definition tfib_E_funcs_on_exit : Z := 0x86a20.
Definition tfib_A_fini_stub_ret : Z := 0x86a20.  Definition tfib_E_fini_stub_ret : Z := 0x86a24.
Definition tfib_A_cxa_atexit_atexit : Z := 0x86a24.  Definition tfib_E_cxa_atexit_atexit : Z := 0x86ae8.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x86ae8.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x86aec.
Definition tfib_A_musl_exit_helper_stub : Z := 0x86aec.  Definition tfib_E_musl_exit_helper_stub : Z := 0x86af0.
Definition tfib_A_libc_exit_fini : Z := 0x86af0.  Definition tfib_E_libc_exit_fini : Z := 0x86b3c.
Definition tfib_A_exit : Z := 0x86b3c.  Definition tfib_E_exit : Z := 0x86bb0.
Definition tfib_A_open : Z := 0x86db0.  Definition tfib_E_open : Z := 0x86e94.
Definition tfib_A_syscall_ret : Z := 0x86e94.  Definition tfib_E_syscall_ret : Z := 0x86ecc.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x86ecc.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x87074.
Definition tfib_A_calloc : Z := 0x87638.  Definition tfib_E_calloc : Z := 0x87770.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x87770.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x87774.
Definition tfib_A_libc_free : Z := 0x87774.  Definition tfib_E_libc_free : Z := 0x87940.
Definition tfib_A_get_meta : Z := 0x87940.  Definition tfib_E_get_meta : Z := 0x87a50.
Definition tfib_A_alloc_meta : Z := 0x87e28.  Definition tfib_E_alloc_meta : Z := 0x88100.
Definition tfib_A_libc_malloc_impl : Z := 0x88100.  Definition tfib_E_libc_malloc_impl : Z := 0x88470.
Definition tfib_A_alloc_slot : Z := 0x88470.  Definition tfib_E_alloc_slot : Z := 0x88d14.
Definition tfib_A_enframe : Z := 0x88d14.  Definition tfib_E_enframe : Z := 0x88e64.
Definition tfib_A_malloc_allzerop : Z := 0x88e64.  Definition tfib_E_malloc_allzerop : Z := 0x88fdc.
Definition tfib_A_getrlimit : Z := 0x8ac8c.  Definition tfib_E_getrlimit : Z := 0x8ad84.
Definition tfib_A_getrusage : Z := 0x8ad84.  Definition tfib_E_getrusage : Z := 0x8adac.
Definition tfib_A_setrlimit : Z := 0x8adac.  Definition tfib_E_setrlimit : Z := 0x8ae74.
Definition tfib_A_mmap : Z := 0x8b29c.  Definition tfib_E_mmap : Z := 0x8b388.
Definition tfib_A_mprotect : Z := 0x8b388.  Definition tfib_E_mprotect : Z := 0x8b3d0.
Definition tfib_A_munmap : Z := 0x8b4a4.  Definition tfib_E_munmap : Z := 0x8b4ec.
Definition tfib_A_sched_yield : Z := 0x8b7b0.  Definition tfib_E_sched_yield : Z := 0x8b7d4.
Definition tfib_A_raise_tkill_path : Z := 0x8b830.  Definition tfib_E_raise_tkill_path : Z := 0x8b8a8.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8b8a8.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8ba7c.
Definition tfib_A_musl_sigaltstack : Z := 0x8bb74.  Definition tfib_E_musl_sigaltstack : Z := 0x8bc00.
Definition tfib_A_fprintf : Z := 0x8c1dc.  Definition tfib_E_fprintf : Z := 0x8c240.
Definition tfib_A_lockfile : Z := 0x8c240.  Definition tfib_E_lockfile : Z := 0x8c33c.
Definition tfib_A_unlockfile : Z := 0x8c33c.  Definition tfib_E_unlockfile : Z := 0x8c39c.
Definition tfib_A_stdio_read : Z := 0x8bf2c.  Definition tfib_E_stdio_read : Z := 0x8c044.
Definition tfib_A_stdio_write : Z := 0x8c04c.  Definition tfib_E_stdio_write : Z := 0x8c1dc.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8befc.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8bf00.
Definition tfib_A_stdio_close : Z := 0x8bf00.  Definition tfib_E_stdio_close : Z := 0x8bf2c.
Definition tfib_A_fwritex : Z := 0x8c7d0.  Definition tfib_E_fwritex : Z := 0x8c908.
Definition tfib_A_musl_fwrite : Z := 0x8c908.  Definition tfib_E_musl_fwrite : Z := 0x8c9c0.
Definition tfib_A_towrite : Z := 0x8c9c0.  Definition tfib_E_towrite : Z := 0x8ca14.
Definition tfib_A_stdio_exit : Z := 0x8c62c.  Definition tfib_E_stdio_exit : Z := 0x8c7d0.
Definition tfib_A_ofl_lock : Z := 0x8ca14.  Definition tfib_E_ofl_lock : Z := 0x8ca44.
Definition tfib_A_musl_vfprintf : Z := 0x8cb90.  Definition tfib_E_musl_vfprintf : Z := 0x8cd40.
Definition tfib_A_printf_core : Z := 0x8cd40.  Definition tfib_E_printf_core : Z := 0x8db70.
Definition tfib_A_pop_arg : Z := 0x8db70.  Definition tfib_E_pop_arg : Z := 0x8dca4.
Definition tfib_A_pad : Z := 0x8dca4.  Definition tfib_E_pad : Z := 0x8dd78.
Definition tfib_A_fmt_fp : Z := 0x8dd78.  Definition tfib_E_fmt_fp : Z := 0x8f440.
Definition tfib_A_thunk_931e0 : Z := 0x8728c.  Definition tfib_E_thunk_931e0 : Z := 0x87290.
Definition tfib_A_musl_wctomb : Z := 0x8b618.  Definition tfib_E_musl_wctomb : Z := 0x8b63c.
Definition tfib_A_musl_wcrtomb : Z := 0x8b4ec.  Definition tfib_E_musl_wcrtomb : Z := 0x8b618.
Definition tfib_A_fpclassifyl : Z := 0x8987c.  Definition tfib_E_fpclassifyl : Z := 0x898c0.
Definition tfib_A_letf2 : Z := 0x890b4.  Definition tfib_E_letf2 : Z := 0x8917c.
Definition tfib_A_multf3 : Z := 0x8917c.  Definition tfib_E_multf3 : Z := 0x8987c.
Definition tfib_A_floatsitf : Z := 0x8a0d8.  Definition tfib_E_floatsitf : Z := 0x8a1e0.
Definition tfib_A_scalbn : Z := 0x8aae4.  Definition tfib_E_scalbn : Z := 0x8ab7c.
Definition tfib_A_subtf3 : Z := 0x8a0c8.  Definition tfib_E_subtf3 : Z := 0x8a0d8.
Definition tfib_A_addtf3 : Z := 0x898c0.  Definition tfib_E_addtf3 : Z := 0x8a08c.
Definition tfib_A_fe_getround : Z := 0x8a08c.  Definition tfib_E_fe_getround : Z := 0x8a0bc.
Definition tfib_A_fixunstfsi : Z := 0x8f448.  Definition tfib_E_fixunstfsi : Z := 0x8f4dc.
Definition tfib_A_floatunsitf : Z := 0x8f4dc.  Definition tfib_E_floatunsitf : Z := 0x8f5c8.
Definition tfib_A_fixtfsi : Z := 0x8ab7c.  Definition tfib_E_fixtfsi : Z := 0x8ac24.
Definition tfib_A_divtf3 : Z := 0x8a1e0.  Definition tfib_E_divtf3 : Z := 0x8aae4.
Definition tfib_A_musl_vprintf : Z := 0x8fca0.  Definition tfib_E_musl_vprintf : Z := 0x8fcbc.
Definition tfib_A_stdout_write : Z := 0x8ca50.  Definition tfib_E_stdout_write : Z := 0x8caf0.

Definition tfib_A_musl_memcmp : Z := 0x90320.  Definition tfib_E_musl_memcmp : Z := 0x90350.
Definition tfib_A_musl_memcpy : Z := 0x90350.  Definition tfib_E_musl_memcpy : Z := 0x90754.
Definition tfib_A_musl_memset : Z := 0x90754.  Definition tfib_E_musl_memset : Z := 0x9084c.
Definition tfib_A_musl_strchr : Z := 0x9084c.  Definition tfib_E_musl_strchr : Z := 0x90888.
Definition tfib_A_strchrnul : Z := 0x90888.  Definition tfib_E_strchrnul : Z := 0x90968.
Definition tfib_A_musl_strlen : Z := 0x909a0.  Definition tfib_E_musl_strlen : Z := 0x90a30.
Definition tfib_A_musl_strnlen : Z := 0x90bdc.  Definition tfib_E_musl_strnlen : Z := 0x90c20.
Definition tfib_A_musl_memchr : Z := 0x90254.  Definition tfib_E_musl_memchr : Z := 0x90320.
Definition tfib_A_lock : Z := 0x90c20.  Definition tfib_E_lock : Z := 0x90ea8.
Definition tfib_A_unlock : Z := 0x90ea8.  Definition tfib_E_unlock : Z := 0x90f1c.
Definition tfib_A_syscall_cp_c : Z := 0x90f1c.  Definition tfib_E_syscall_cp_c : Z := 0x90f40.
Definition tfib_A_syscall_cp_sccp : Z := 0x90f40.  Definition tfib_E_syscall_cp_sccp : Z := 0x90f44.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x90f44.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x90f68.
Definition tfib_A_pthread_atfork : Z := 0x90f80.  Definition tfib_E_pthread_atfork : Z := 0x91024.
Definition tfib_A_mremap : Z := 0x8b3d0.  Definition tfib_E_mremap : Z := 0x8b4a4.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x91ff8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x92014.
Definition tfib_A_pthread_key_create : Z := 0x923a0.  Definition tfib_E_pthread_key_create : Z := 0x92474.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x92718.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x927bc.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x927bc.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x928d8.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x928d8.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x92904.
Definition tfib_A_pthread_setspecific : Z := 0x9293c.  Definition tfib_E_pthread_setspecific : Z := 0x92970.
Definition tfib_A_set_thread_area : Z := 0x92978.  Definition tfib_E_set_thread_area : Z := 0x92984.
Definition tfib_A_thunk_96f9c : Z := 0x92970.  Definition tfib_E_thunk_96f9c : Z := 0x92978.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x932a4.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9335c.
Definition tfib_A_close : Z := 0x95974.  Definition tfib_E_close : Z := 0x959c8.
Definition tfib_A_musl_read : Z := 0x95a54.  Definition tfib_E_musl_read : Z := 0x95a88.
Definition tfib_A_vm_wait : Z := 0x92fb4.  Definition tfib_E_vm_wait : Z := 0x93004.
Definition tfib_D_str_sealed : Z := 0x117fe.
Definition tfib_D_init_array_0_3 : Z := 0x96a88.
Definition tfib_D_fini_array_0_1 : Z := 0x96aa8.
Definition tfib_D_GOT_common_flags : Z := 0x97010.
Definition tfib_D_GOT_flags : Z := 0x97018.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x97020.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x97028.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x97030.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x97038.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x97b88.
Definition tfib_D_environ_musl : Z := 0x97cb0.
Definition tfib_D_REAL_read : Z := 0x98d50.
Definition tfib_D_REAL_memcpy : Z := 0x98e78.
Definition tfib_D_REAL_memset : Z := 0x98e80.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9b998.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9c7f8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0x9eff8.
Definition tfib_D_asan_inited : Z := 0x9fcd8.
Definition tfib_D_replace_intrin_cached : Z := 0x9fcd9.
Definition tfib_D_kHighMemEnd : Z := 0x9fce0.
Definition tfib_D_kMidMemBeg : Z := 0x9fce8.
Definition tfib_D_kMidMemEnd : Z := 0x9fcf0.
Definition tfib_D_malloc_context_size : Z := 0x9fcfc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x130b28.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f2220.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f4000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2fbf0.
Definition tfib_at_rw_lo : Z := 0x98000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x627c0.
Definition tfib_at_x_imemcpy : Z := 0x62744.
Definition tfib_at_x_memset : Z := 0x90754.
Definition tfib_at_x_memcpy : Z := 0x90350.
Definition tfib_at_x_memiszero : Z := 0x62cf0.
Definition tfib_at_x_istrncpy : Z := 0x62bec.
Definition tfib_at_x_sealed : Z := 0x117fe.
Definition tfib_at_x_popfree : Z := 0x35fdc.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x86158.
Definition tfib_at_x_envscan_k : Z := 0x86164.
Definition tfib_at_x_pnscan : Z := 0x8621c.
Definition tfib_at_x_pnscan_k : Z := 0x86228.
Definition tfib_at_stops_more : list Z := (0x33c50 :: 0x35274 :: 0x52acc :: 0x58e84 :: 0x58e98 :: 0x58eac :: 0x5e83c :: 0x5e90c :: 0x6be38 :: 0x6cd44 :: 0x6ced4 :: 0x76c2c :: nil)%list.
