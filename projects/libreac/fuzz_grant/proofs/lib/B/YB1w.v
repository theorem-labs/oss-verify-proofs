(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10 [image A's note, kept from grant A's header; its numbers are fuzz_grant.asan's]: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). Image B (fuzz_grant.asan-ubsan fde52226dc48, symbol table 5a5ee7c02b4e): SetTLSFakeStack ends at 0x3cf4c, and the side-stack rows are __asan_stack_malloc_0, _1, _2, _4, _6 and __asan_stack_free_6, each [st_value, st_value + st_size) of image B's symbol. *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22c8c.
Definition tfib_text_lo : Z := 0x30984.  Definition tfib_text_hi : Z := 0x9bfc8.
Definition tfib_init_array_lo : Z := 0x9cfc8.  Definition tfib_init_array_hi : Z := 0x9cfe8.
Definition tfib_fini_array_lo : Z := 0x9cfe8.  Definition tfib_fini_array_hi : Z := 0x9cff8.
Definition tfib_preinit_array_lo : Z := 0x9cff8.  Definition tfib_preinit_array_hi : Z := 0x9d000.
Definition tfib_data_rel_ro_lo : Z := 0x9d000.  Definition tfib_data_rel_ro_hi : Z := 0x9d670.
Definition tfib_got_lo : Z := 0x9d670.  Definition tfib_got_hi : Z := 0x9e3c8.
Definition tfib_data_lo : Z := 0x9f3c8.  Definition tfib_data_hi : Z := 0xa1f80.
Definition tfib_asan_globals_lo : Z := 0xa1f80.  Definition tfib_asan_globals_hi : Z := 0xa22c0.
Definition tfib_bss_lo : Z := 0xa22c0.  Definition tfib_bss_hi : Z := 0x5fa1f0.
Definition tfib_tbss_lo : Z := 0x9bfc8.  Definition tfib_tbss_hi : Z := 0x9bfdc.
Definition tfib_img_lo : Z := IMG_LO.  Definition tfib_img_hi : Z := IMG_TOP.
Definition tfib_entry : Z := 0x30984.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30984.
Definition tfib_A_do_init : Z := 0x309cc.  Definition tfib_E_do_init : Z := 0x30a40.
Definition tfib_A_do_fini : Z := 0x30a40.  Definition tfib_E_do_fini : Z := 0x30ad0.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30ad0.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30b0c.
Definition tfib_A_InitializeAllocator : Z := 0x30c7c.  Definition tfib_E_InitializeAllocator : Z := 0x30c94.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30c94.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30e00.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x3135c.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x314b8.
Definition tfib_A_asan_free : Z := 0x3188c.  Definition tfib_E_asan_free : Z := 0x318b4.
Definition tfib_A_Allocator_Deallocate : Z := 0x318b4.  Definition tfib_E_Allocator_Deallocate : Z := 0x31b6c.
Definition tfib_A_asan_malloc : Z := 0x31b6c.  Definition tfib_E_asan_malloc : Z := 0x31bc8.
Definition tfib_A_Allocator_Allocate : Z := 0x31bc8.  Definition tfib_E_Allocator_Allocate : Z := 0x32550.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32eb8.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f14.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32f14.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33164.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33164.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33258.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33c14.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33e98.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33e98.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34018.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34018.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x341e0.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x341e0.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x343ac.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x3444c.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34550.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34878.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x349c0.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35b50.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35cc8.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35e78.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3605c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x3605c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36334.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36334.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x367ac.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x367ac.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x368ac.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x368ac.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36bb4.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36bb4.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36f24.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37440.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37528.
Definition tfib_A_AsanActivate : Z := 0x37528.  Definition tfib_E_AsanActivate : Z := 0x37604.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c680.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c758.
Definition tfib_A_FakeStack_Create : Z := 0x3c758.  Definition tfib_E_FakeStack_Create : Z := 0x3c844.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cf1c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cf4c.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3cf4c.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d0c0.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d0c0.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d250.
Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d250.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3d3ec.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3d3ec.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3d5b8.
(* Image B links two side-stack functions that image A does not: their rows are from fuzz_grant.asan-ubsan's symbols (address, address + size). *)
Definition tfib_A_asan_stack_malloc_6 : Z := 0x3d5b8.  Definition tfib_E_asan_stack_malloc_6 : Z := 0x3d754.
Definition tfib_A_asan_stack_free_6 : Z := 0x3d754.  Definition tfib_E_asan_stack_free_6 : Z := 0x3d79c.
Definition tfib_A_asan_InitializeFlags : Z := 0x3d8d8.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e904.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f010.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fe2c.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3fe2c.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x403f8.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x40b4c.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40dbc.
Definition tfib_A_thunk_417bc : Z := 0x424fc.  Definition tfib_E_thunk_417bc : Z := 0x42500.
Definition tfib_A_thunk_417cc : Z := 0x4250c.  Definition tfib_E_thunk_417cc : Z := 0x42514.
Definition tfib_A_thunk_417dc : Z := 0x4251c.  Definition tfib_E_thunk_417dc : Z := 0x42520.
Definition tfib_A_thunk_417e4 : Z := 0x42520.  Definition tfib_E_thunk_417e4 : Z := 0x42524.
Definition tfib_A_thunk_417e8 : Z := 0x42524.  Definition tfib_E_thunk_417e8 : Z := 0x42528.
Definition tfib_A_thunk_417ec : Z := 0x42528.  Definition tfib_E_thunk_417ec : Z := 0x4252c.
Definition tfib_A_thunk_417f0 : Z := 0x4252c.  Definition tfib_E_thunk_417f0 : Z := 0x42530.
Definition tfib_A_thunk_417f8 : Z := 0x42534.  Definition tfib_E_thunk_417f8 : Z := 0x42538.
Definition tfib_A_thunk_4180c : Z := 0x42548.  Definition tfib_E_thunk_4180c : Z := 0x4254c.
Definition tfib_A_icpt_strlen : Z := 0x4254c.  Definition tfib_E_icpt_strlen : Z := 0x427e0.
Definition tfib_A_icpt_strnlen : Z := 0x427e0.  Definition tfib_E_icpt_strnlen : Z := 0x42a74.
Definition tfib_A_icpt_strcmp : Z := 0x42a78.  Definition tfib_E_icpt_strcmp : Z := 0x42fa8.
Definition tfib_A_icpt_strchr : Z := 0x42fa8.  Definition tfib_E_icpt_strchr : Z := 0x43288.
Definition tfib_A_icpt_memcmp : Z := 0x43b20.  Definition tfib_E_icpt_memcmp : Z := 0x43bdc.
Definition tfib_A_icpt_memchr : Z := 0x43c98.  Definition tfib_E_icpt_memchr : Z := 0x43f68.
Definition tfib_A_icpt_frexpl : Z := 0x43f68.  Definition tfib_E_icpt_frexpl : Z := 0x441e0.
Definition tfib_A_icpt_read : Z := 0x441e0.  Definition tfib_E_icpt_read : Z := 0x44450.
Definition tfib_A_icpt_fwrite : Z := 0x44450.  Definition tfib_E_icpt_fwrite : Z := 0x446c4.
Definition tfib_A_icpt_time : Z := 0x446c4.  Definition tfib_E_icpt_time : Z := 0x44960.
Definition tfib_A_icpt_gmtime_r : Z := 0x44b68.  Definition tfib_E_icpt_gmtime_r : Z := 0x44da8.
Definition tfib_A_icpt_vprintf : Z := 0x44da8.  Definition tfib_E_icpt_vprintf : Z := 0x44e44.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44e44.  Definition tfib_E_printf_common_format_interceptor : Z := 0x4590c.
Definition tfib_A_icpt_vfprintf : Z := 0x4590c.  Definition tfib_E_icpt_vfprintf : Z := 0x459c0.
Definition tfib_A_icpt_vsnprintf : Z := 0x459c0.  Definition tfib_E_icpt_vsnprintf : Z := 0x45cd8.
Definition tfib_A_icpt_clock_gettime : Z := 0x45e54.  Definition tfib_E_icpt_clock_gettime : Z := 0x460ac.
Definition tfib_A_icpt_wcrtomb : Z := 0x460ac.  Definition tfib_E_icpt_wcrtomb : Z := 0x4661c.
Definition tfib_A_icpt_wctomb : Z := 0x4661c.  Definition tfib_E_icpt_wctomb : Z := 0x46978.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46a44.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46e2c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46e38.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46eb4.
Definition tfib_A_icpt_sem_timedwait : Z := 0x470c0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47358.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47388.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x475b0.
Definition tfib_A_icpt_send : Z := 0x475b0.  Definition tfib_E_icpt_send : Z := 0x47864.
Definition tfib_A_icpt_sendto : Z := 0x47864.  Definition tfib_E_icpt_sendto : Z := 0x47b28.
Definition tfib_A_icpt_sigaltstack : Z := 0x47b28.  Definition tfib_E_icpt_sigaltstack : Z := 0x47d84.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47e58.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x48008.
Definition tfib_A_asan_memcpy : Z := 0x51b88.  Definition tfib_E_asan_memcpy : Z := 0x52024.
Definition tfib_A_asan_memset : Z := 0x52024.  Definition tfib_E_asan_memset : Z := 0x52264.
Definition tfib_A_icpt_memset : Z := 0x52264.  Definition tfib_E_icpt_memset : Z := 0x52554.
Definition tfib_A_icpt_memcpy : Z := 0x52554.  Definition tfib_E_icpt_memcpy : Z := 0x52b44.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52b44.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52b7c.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52b7c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52b80.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52b80.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52b84.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52c30.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52d6c.
Definition tfib_A_icpt_free : Z := 0x52ee0.  Definition tfib_E_icpt_free : Z := 0x530b0.
Definition tfib_A_icpt_malloc : Z := 0x530b0.  Definition tfib_E_icpt_malloc : Z := 0x5320c.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x532d8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x532dc.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53d58.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53d68.
Definition tfib_A_CanPoisonMemory : Z := 0x53d68.  Definition tfib_E_CanPoisonMemory : Z := 0x53d7c.
Definition tfib_A_PoisonShadow : Z := 0x53d7c.  Definition tfib_E_PoisonShadow : Z := 0x54278.
Definition tfib_A_MemToShadow_checked : Z := 0x54278.  Definition tfib_E_MemToShadow_checked : Z := 0x543b4.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54704.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54a48.
Definition tfib_A_AsanTSDInit : Z := 0x54e68.  Definition tfib_E_AsanTSDInit : Z := 0x54ee4.
Definition tfib_A_AsanTSDGet : Z := 0x54ee4.  Definition tfib_E_AsanTSDGet : Z := 0x54f24.
Definition tfib_A_AsanTSDSet : Z := 0x54f24.  Definition tfib_E_AsanTSDSet : Z := 0x54f64.
Definition tfib_A_PlatformTSDDtor : Z := 0x54f64.  Definition tfib_E_PlatformTSDDtor : Z := 0x54fe8.
Definition tfib_A_InstallAtForkHandler : Z := 0x54fe8.  Definition tfib_E_InstallAtForkHandler : Z := 0x55004.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x55064.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x550a8.
Definition tfib_A_ReportDoubleFree : Z := 0x560d4.  Definition tfib_E_ReportDoubleFree : Z := 0x56364.
Definition tfib_A_ReportGenericError : Z := 0x57c40.  Definition tfib_E_ReportGenericError : Z := 0x584fc.
Definition tfib_A_AsanInited : Z := 0x58c88.  Definition tfib_E_AsanInited : Z := 0x58ca0.
Definition tfib_A_asan_report_load1 : Z := 0x58ca0.  Definition tfib_E_asan_report_load1 : Z := 0x58cf0.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58cf0.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58d40.
Definition tfib_A_asan_report_load2 : Z := 0x58d40.  Definition tfib_E_asan_report_load2 : Z := 0x58d90.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58d90.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58de0.
Definition tfib_A_asan_report_load4 : Z := 0x58de0.  Definition tfib_E_asan_report_load4 : Z := 0x58e30.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58e30.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58e80.
Definition tfib_A_asan_report_load8 : Z := 0x58e80.  Definition tfib_E_asan_report_load8 : Z := 0x58ed0.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58ed0.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58f20.
Definition tfib_A_asan_report_load16 : Z := 0x58f20.  Definition tfib_E_asan_report_load16 : Z := 0x58f70.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58f70.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58fc0.
Definition tfib_A_asan_report_store1 : Z := 0x58fc0.  Definition tfib_E_asan_report_store1 : Z := 0x59010.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59010.  Definition tfib_E_asan_report_exp_store1 : Z := 0x59060.
Definition tfib_A_asan_report_store2 : Z := 0x59060.  Definition tfib_E_asan_report_store2 : Z := 0x590b0.
Definition tfib_A_asan_report_exp_store2 : Z := 0x590b0.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59100.
Definition tfib_A_asan_report_store4 : Z := 0x59100.  Definition tfib_E_asan_report_store4 : Z := 0x59150.
Definition tfib_A_asan_report_exp_store4 : Z := 0x59150.  Definition tfib_E_asan_report_exp_store4 : Z := 0x591a0.
Definition tfib_A_asan_report_store8 : Z := 0x591a0.  Definition tfib_E_asan_report_store8 : Z := 0x591f0.
Definition tfib_A_asan_report_exp_store8 : Z := 0x591f0.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59240.
Definition tfib_A_asan_report_store16 : Z := 0x59240.  Definition tfib_E_asan_report_store16 : Z := 0x59290.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59290.  Definition tfib_E_asan_report_exp_store16 : Z := 0x592e0.
Definition tfib_A_asan_report_load_n : Z := 0x592e0.  Definition tfib_E_asan_report_load_n : Z := 0x59330.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59330.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59380.
Definition tfib_A_asan_report_store_n : Z := 0x59380.  Definition tfib_E_asan_report_store_n : Z := 0x593d0.
Definition tfib_A_asan_report_exp_store_n : Z := 0x593d0.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59420.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59420.  Definition tfib_E_InitializeHighMemEnd : Z := 0x594a0.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x594a0.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59854.
Definition tfib_A_AsanInitInternal : Z := 0x598e4.  Definition tfib_E_AsanInitInternal : Z := 0x59b98.
Definition tfib_A_thunk_59674 : Z := 0x59e00.  Definition tfib_E_thunk_59674 : Z := 0x59e04.
Definition tfib_A_asan_init : Z := 0x59e04.  Definition tfib_E_asan_init : Z := 0x59e98.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59e98.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59e9c.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a100.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a428.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a608.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a910.
Definition tfib_A_SetMallocContextSize : Z := 0x5a910.  Definition tfib_E_SetMallocContextSize : Z := 0x5a920.
Definition tfib_A_GetMallocContextSize : Z := 0x5a920.  Definition tfib_E_GetMallocContextSize : Z := 0x5a930.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a930.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5aa80.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b564.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b59c.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b850.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b8dc.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b8dc.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b944.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b944.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b9bc.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b9bc.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5ba24.
Definition tfib_A_AsanThread_Create : Z := 0x5bf88.  Definition tfib_E_AsanThread_Create : Z := 0x5c124.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c180.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c398.
Definition tfib_A_GetCurrentThread : Z := 0x5c398.  Definition tfib_E_GetCurrentThread : Z := 0x5c3b8.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c55c.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c5b4.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c5b4.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c60c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c60c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c83c.
Definition tfib_A_AsanThread_Init : Z := 0x5c83c.  Definition tfib_E_AsanThread_Init : Z := 0x5cc30.
Definition tfib_A_CreateMainThread : Z := 0x5cd70.  Definition tfib_E_CreateMainThread : Z := 0x5ce80.
Definition tfib_A_SetCurrentThread : Z := 0x5ce80.  Definition tfib_E_SetCurrentThread : Z := 0x5cf60.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d164.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5d2a0.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e8b0.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e8fc.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e8fc.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e908.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e938.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e944.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e944.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e950.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e96c.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5ec38.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ec38.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5eff8.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5ff60.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x60038.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x60038.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x600d4.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x605f8.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6063c.
Definition tfib_A_RunMallocHooks : Z := 0x60b6c.  Definition tfib_E_RunMallocHooks : Z := 0x60c24.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60c24.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60c28.
Definition tfib_A_RunFreeHooks : Z := 0x60c28.  Definition tfib_E_RunFreeHooks : Z := 0x60cd4.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61018.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61258.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61854.  Definition tfib_E_sanitizer_set_report_path : Z := 0x6186c.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x6347c.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x6378c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x6378c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x638d0.
Definition tfib_A_FlagParser_ParseString : Z := 0x638d0.  Definition tfib_E_FlagParser_ParseString : Z := 0x639c4.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63bb8.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63bf8.
Definition tfib_A_internal_atoll : Z := 0x63bf8.  Definition tfib_E_internal_atoll : Z := 0x63ce4.
Definition tfib_A_internal_simple_strtoll : Z := 0x63ce4.  Definition tfib_E_internal_simple_strtoll : Z := 0x63e40.
Definition tfib_A_internal_memchr : Z := 0x63e40.  Definition tfib_E_internal_memchr : Z := 0x63e60.
Definition tfib_A_internal_memcmp : Z := 0x63e60.  Definition tfib_E_internal_memcmp : Z := 0x63e98.
Definition tfib_A_internal_memcpy : Z := 0x63e98.  Definition tfib_E_internal_memcpy : Z := 0x63ebc.
Definition tfib_A_internal_memmove : Z := 0x63ebc.  Definition tfib_E_internal_memmove : Z := 0x63f14.
Definition tfib_A_internal_memset : Z := 0x63f14.  Definition tfib_E_internal_memset : Z := 0x63f74.
Definition tfib_A_internal_strcspn : Z := 0x63f74.  Definition tfib_E_internal_strcspn : Z := 0x63fc8.
Definition tfib_A_internal_strdup : Z := 0x63ffc.  Definition tfib_E_internal_strdup : Z := 0x64068.
Definition tfib_A_internal_strlen : Z := 0x64068.  Definition tfib_E_internal_strlen : Z := 0x64084.
Definition tfib_A_internal_strchrnul : Z := 0x64114.  Definition tfib_E_internal_strchrnul : Z := 0x6415c.
Definition tfib_A_internal_strrchr : Z := 0x6415c.  Definition tfib_E_internal_strrchr : Z := 0x6419c.
Definition tfib_A_internal_strnlen : Z := 0x642cc.  Definition tfib_E_internal_strnlen : Z := 0x642fc.
Definition tfib_A_internal_strncpy : Z := 0x64340.  Definition tfib_E_internal_strncpy : Z := 0x643b0.
Definition tfib_A_internal_strstr : Z := 0x643b0.  Definition tfib_E_internal_strstr : Z := 0x64444.
Definition tfib_A_mem_is_zero : Z := 0x64444.  Definition tfib_E_mem_is_zero : Z := 0x644f8.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x644f8.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64508.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64508.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x646e8.
Definition tfib_A_internal_iserror : Z := 0x646f4.  Definition tfib_E_internal_iserror : Z := 0x64714.
Definition tfib_A_internal_mmap : Z := 0x64714.  Definition tfib_E_internal_mmap : Z := 0x64720.
Definition tfib_A_internal_munmap : Z := 0x64720.  Definition tfib_E_internal_munmap : Z := 0x6472c.
Definition tfib_A_internal_mprotect : Z := 0x6472c.  Definition tfib_E_internal_mprotect : Z := 0x6473c.
Definition tfib_A_internal_madvise : Z := 0x6473c.  Definition tfib_E_internal_madvise : Z := 0x64768.
Definition tfib_A_internal_close : Z := 0x64768.  Definition tfib_E_internal_close : Z := 0x64774.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64774.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64798.
Definition tfib_A_internal_read : Z := 0x64798.  Definition tfib_E_internal_read : Z := 0x647d0.
Definition tfib_A_internal_write : Z := 0x647d0.  Definition tfib_E_internal_write : Z := 0x64808.
Definition tfib_A_internal_ftruncate : Z := 0x64808.  Definition tfib_E_internal_ftruncate : Z := 0x64840.
Definition tfib_A_internal_dup : Z := 0x64840.  Definition tfib_E_internal_dup : Z := 0x6484c.
Definition tfib_A_internal_dup2_dup3 : Z := 0x6484c.  Definition tfib_E_internal_dup2_dup3 : Z := 0x6485c.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x6485c.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64874.
Definition tfib_A_internal_sched_yield : Z := 0x64874.  Definition tfib_E_internal_sched_yield : Z := 0x64880.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64880.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x648cc.
Definition tfib_A_internal_execve : Z := 0x648cc.  Definition tfib_E_internal_execve : Z := 0x648d8.
Definition tfib_A_internal_exit_exit_group : Z := 0x648d8.  Definition tfib_E_internal_exit_exit_group : Z := 0x648ec.
Definition tfib_A_FileExists_newfstatat : Z := 0x648ec.  Definition tfib_E_FileExists_newfstatat : Z := 0x6496c.
Definition tfib_A_DirExists_newfstatat : Z := 0x6496c.  Definition tfib_E_DirExists_newfstatat : Z := 0x649d0.
Definition tfib_A_GetTid_gettid : Z := 0x649d0.  Definition tfib_E_GetTid_gettid : Z := 0x649dc.
Definition tfib_A_GetEnv : Z := 0x649dc.  Definition tfib_E_GetEnv : Z := 0x64b0c.
Definition tfib_A_FutexWait : Z := 0x64c10.  Definition tfib_E_FutexWait : Z := 0x64c34.
Definition tfib_A_FutexWake : Z := 0x64c34.  Definition tfib_E_FutexWake : Z := 0x64c58.
Definition tfib_A_internal_ptrace : Z := 0x64c58.  Definition tfib_E_internal_ptrace : Z := 0x64c64.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64c64.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64c74.
Definition tfib_A_internal_getpid : Z := 0x64c74.  Definition tfib_E_internal_getpid : Z := 0x64c80.
Definition tfib_A_internal_getppid : Z := 0x64c80.  Definition tfib_E_internal_getppid : Z := 0x64c8c.
Definition tfib_A_internal_prctl : Z := 0x64c8c.  Definition tfib_E_internal_prctl : Z := 0x64c98.
Definition tfib_A_internal_sigaltstack : Z := 0x64c98.  Definition tfib_E_internal_sigaltstack : Z := 0x64ca4.
Definition tfib_A_internal_fork_clone : Z := 0x64ca4.  Definition tfib_E_internal_fork_clone : Z := 0x64cbc.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64cbc.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64de8.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65528.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65640.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65648.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x656f4.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x656f4.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65814.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x658dc.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x6595c.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x659b8.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65a84.
Definition tfib_A_thunk_653ec : Z := 0x65b80.  Definition tfib_E_thunk_653ec : Z := 0x65b84.
Definition tfib_A_CheckASLR : Z := 0x65b84.  Definition tfib_E_CheckASLR : Z := 0x65b88.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65dd4.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65dd8.
Definition tfib_A_MmapOrDie : Z := 0x65de4.  Definition tfib_E_MmapOrDie : Z := 0x65ef0.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65ef0.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65f64.
Definition tfib_A_UnmapOrDie : Z := 0x65f64.  Definition tfib_E_UnmapOrDie : Z := 0x65fe0.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65fe0.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x660f0.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6631c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66420.
Definition tfib_A_thunk_66008 : Z := 0x6679c.  Definition tfib_E_thunk_66008 : Z := 0x667a0.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66ac0.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66ccc.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67284.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67290.
Definition tfib_A_Printf : Z := 0x67294.  Definition tfib_E_Printf : Z := 0x672e0.
Definition tfib_A_SharedPrintfCode : Z := 0x672e0.  Definition tfib_E_SharedPrintfCode : Z := 0x6733c.
Definition tfib_A_Report : Z := 0x6733c.  Definition tfib_E_Report : Z := 0x67388.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68e80.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68edc.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68edc.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x69118.
Definition tfib_A_SuppressionContext_Parse : Z := 0x69118.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6943c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a0ec.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a564.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6ae24.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b148.
Definition tfib_A_AddDieCallback : Z := 0x6ba04.  Definition tfib_E_AddDieCallback : Z := 0x6ba8c.
Definition tfib_A_Die : Z := 0x6bb50.  Definition tfib_E_Die : Z := 0x6bc10.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6bc10.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6bc1c.
Definition tfib_A_CheckFailed : Z := 0x6bc1c.  Definition tfib_E_CheckFailed : Z := 0x6bcd4.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c32c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c424.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c424.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c550.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c828.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6cb10.
Definition tfib_A_AndroidLogInit : Z := 0x6d3b8.  Definition tfib_E_AndroidLogInit : Z := 0x6d3bc.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d3ec.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d434.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d434.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d680.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d790.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d894.
Definition tfib_A_thunk_6d37c : Z := 0x6db10.  Definition tfib_E_thunk_6d37c : Z := 0x6db14.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6dbd8.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6dc78.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6dd04.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6ddc8.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6ddc8.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6de50.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6de50.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6dec8.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6dec8.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dfac.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e068.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e19c.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70460.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70584.
Definition tfib_A_StackStore_Alloc : Z := 0x70584.  Definition tfib_E_StackStore_Alloc : Z := 0x706b8.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70f6c.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x71020.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72774.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x727d0.
Definition tfib_A_StackDepotPut : Z := 0x72a5c.  Definition tfib_E_StackDepotPut : Z := 0x72a7c.
Definition tfib_A_StackDepotBase_Put : Z := 0x72a7c.  Definition tfib_E_StackDepotBase_Put : Z := 0x72d00.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x733e0.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x733e8.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73548.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x735bc.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73a44.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73b5c.
Definition tfib_A_thunk_762d8 : Z := 0x76ba8.  Definition tfib_E_thunk_762d8 : Z := 0x76bac.
Definition tfib_A_thunk_77ab0 : Z := 0x78380.  Definition tfib_E_thunk_77ab0 : Z := 0x78384.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79dac.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79e68.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79e68.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79f40.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a524.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a8f4.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7abc4.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7ac7c.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bfd4.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bfd8.
Definition tfib_A_lsan_register_root_region : Z := 0x7cbe0.  Definition tfib_E_lsan_register_root_region : Z := 0x7cf10.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cf10.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d398.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x802f8.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80374.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80374.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80424.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x8043c.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80584.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80584.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80590.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80590.  Definition tfib_E_asan_default_options_cli_c : Z := 0x8059c.
Definition tfib_A_main : Z := 0x8059c.  Definition tfib_E_main : Z := 0x80860.
Definition tfib_A_target_alloc_init : Z := 0x80860.  Definition tfib_E_target_alloc_init : Z := 0x80864.
Definition tfib_A_target_alloc_count : Z := 0x80864.  Definition tfib_E_target_alloc_count : Z := 0x8086c.
Definition tfib_A_target_run : Z := 0x8086c.
Definition tfib_A_emit_printf : Z := 0x809f4.  Definition tfib_E_emit_printf : Z := 0x80a3c.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80a3c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82074.
Definition tfib_A_check_groupa : Z := 0x82074.  Definition tfib_E_check_groupa : Z := 0x82434.
Definition tfib_A_asan_module_ctor : Z := 0x824ec.  Definition tfib_E_asan_module_ctor : Z := 0x82524.
Definition tfib_A_asan_module_dtor : Z := 0x82524.  Definition tfib_E_asan_module_dtor : Z := 0x82554.
Definition tfib_A_reac_ctrl_checksum_verify : Z := 0x8260c.  Definition tfib_E_reac_ctrl_checksum_verify : Z := 0x82694.
Definition tfib_A_reac_ctrl_parse : Z := 0x82774.  Definition tfib_E_reac_ctrl_parse : Z := 0x831f8.
Definition tfib_A_kind_of_link1 : Z := 0x831f8.  Definition tfib_E_kind_of_link1 : Z := 0x8326c.
Definition tfib_A_reac_ctrl_stamp_headamp : Z := 0x8326c.  Definition tfib_E_reac_ctrl_stamp_headamp : Z := 0x834dc.
Definition tfib_A_reac_ctrl_headamp_record_verify : Z := 0x834dc.  Definition tfib_E_reac_ctrl_headamp_record_verify : Z := 0x835dc.
Definition tfib_A_reac_ctrl_identity_poll_block : Z := 0x835dc.  Definition tfib_E_reac_ctrl_identity_poll_block : Z := 0x8363c.
Definition tfib_A_reac_ctrl_build_grant_sweep : Z := 0x8363c.  Definition tfib_E_reac_ctrl_build_grant_sweep : Z := 0x83bfc.
Definition tfib_A_ctrl_lay_block : Z := 0x83bfc.  Definition tfib_E_ctrl_lay_block : Z := 0x83fdc.
Definition tfib_A_ctrl_finish : Z := 0x83fdc.  Definition tfib_E_ctrl_finish : Z := 0x840d0.
Definition tfib_A_reac_box_model_block : Z := 0x840d0.  Definition tfib_E_reac_box_model_block : Z := 0x84e4c.
Definition tfib_A_build_dt1_single : Z := 0x84e4c.  Definition tfib_E_build_dt1_single : Z := 0x85004.
Definition tfib_A_reac_grant_alloc_fits : Z := 0x85518.  Definition tfib_E_reac_grant_alloc_fits : Z := 0x85554.
Definition tfib_A_reac_grant_allocate : Z := 0x85554.  Definition tfib_E_reac_grant_allocate : Z := 0x855fc.
Definition tfib_A_reac_grant_build_sweep : Z := 0x855fc.  Definition tfib_E_reac_grant_build_sweep : Z := 0x85a70.
Definition tfib_A_reac_headamp_tx_init : Z := 0x85a70.  Definition tfib_E_reac_headamp_tx_init : Z := 0x85a90.
Definition tfib_A_reac_headamp_tx_set : Z := 0x85a90.  Definition tfib_E_reac_headamp_tx_set : Z := 0x85bf0.
Definition tfib_A_reac_headamp_default : Z := 0x85bf0.  Definition tfib_E_reac_headamp_default : Z := 0x85c00.
Definition tfib_A_reac_headamp_tx_effective : Z := 0x85c00.  Definition tfib_E_reac_headamp_tx_effective : Z := 0x85ce4.
Definition tfib_A_reac_headamp_tx_arm_scene : Z := 0x85ce4.  Definition tfib_E_reac_headamp_tx_arm_scene : Z := 0x85e78.
Definition tfib_A_reac_headamp_tx_set_resweep : Z := 0x85e78.  Definition tfib_E_reac_headamp_tx_set_resweep : Z := 0x85efc.
Definition tfib_A_reac_headamp_tx_next : Z := 0x85efc.  Definition tfib_E_reac_headamp_tx_next : Z := 0x86640.
Definition tfib_A_extenddftf2 : Z := 0x86650.  Definition tfib_E_extenddftf2 : Z := 0x867e0.
Definition tfib_A_sysconf : Z := 0x8c430.  Definition tfib_E_sysconf : Z := 0x8c658.
Definition tfib_A_init : Z := 0x8c658.  Definition tfib_E_init : Z := 0x8c65c.
Definition tfib_A_init_libc : Z := 0x8c65c.  Definition tfib_E_init_libc : Z := 0x8c888.
Definition tfib_A_libc_start_init : Z := 0x8c888.  Definition tfib_E_libc_start_init : Z := 0x8c8d4.
Definition tfib_A_libc_start_main : Z := 0x8c8d4.  Definition tfib_E_libc_start_main : Z := 0x8c934.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8c934.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8c97c.
Definition tfib_A_init_tls : Z := 0x8ca54.  Definition tfib_E_init_tls : Z := 0x8cd04.
Definition tfib_A_init_ssp : Z := 0x8cd04.  Definition tfib_E_init_ssp : Z := 0x8cd64.
Definition tfib_A_stack_chk_fail : Z := 0x8cd64.  Definition tfib_E_stack_chk_fail : Z := 0x8cd6c.
Definition tfib_A_Exit : Z := 0x8ce48.  Definition tfib_E_Exit : Z := 0x8ce64.
Definition tfib_A_funcs_on_exit : Z := 0x8ce94.  Definition tfib_E_funcs_on_exit : Z := 0x8cf5c.
Definition tfib_A_libc_exit_fini : Z := 0x8d02c.  Definition tfib_E_libc_exit_fini : Z := 0x8d078.
Definition tfib_A_exit : Z := 0x8d078.  Definition tfib_E_exit : Z := 0x8d0ec.
Definition tfib_A_open : Z := 0x8d2ec.  Definition tfib_E_open : Z := 0x8d3d0.
Definition tfib_A_syscall_ret : Z := 0x8d3d0.  Definition tfib_E_syscall_ret : Z := 0x8d408.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8d408.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8d5b0.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8dcac.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8dcb0.
Definition tfib_A_libc_free : Z := 0x8dcb0.  Definition tfib_E_libc_free : Z := 0x8de7c.
Definition tfib_A_get_meta : Z := 0x8de7c.  Definition tfib_E_get_meta : Z := 0x8df8c.
Definition tfib_A_alloc_meta : Z := 0x8e364.  Definition tfib_E_alloc_meta : Z := 0x8e63c.
Definition tfib_A_libc_malloc_impl : Z := 0x8e63c.  Definition tfib_E_libc_malloc_impl : Z := 0x8e9ac.
Definition tfib_A_alloc_slot : Z := 0x8e9ac.  Definition tfib_E_alloc_slot : Z := 0x8f250.
Definition tfib_A_enframe : Z := 0x8f250.  Definition tfib_E_enframe : Z := 0x8f3a0.
Definition tfib_A_malloc_allzerop : Z := 0x8f3a0.  Definition tfib_E_malloc_allzerop : Z := 0x8f518.
Definition tfib_A_getrlimit : Z := 0x911c8.  Definition tfib_E_getrlimit : Z := 0x912c0.
Definition tfib_A_getrusage : Z := 0x912c0.  Definition tfib_E_getrusage : Z := 0x912e8.
Definition tfib_A_setrlimit : Z := 0x912e8.  Definition tfib_E_setrlimit : Z := 0x913b0.
Definition tfib_A_mmap : Z := 0x917d8.  Definition tfib_E_mmap : Z := 0x918c4.
Definition tfib_A_mprotect : Z := 0x918c4.  Definition tfib_E_mprotect : Z := 0x9190c.
Definition tfib_A_munmap : Z := 0x919e0.  Definition tfib_E_munmap : Z := 0x91a28.
Definition tfib_A_sched_yield : Z := 0x91cec.  Definition tfib_E_sched_yield : Z := 0x91d10.
Definition tfib_A_raise_tkill_path : Z := 0x91d6c.  Definition tfib_E_raise_tkill_path : Z := 0x91de4.
Definition tfib_A_musl_sigaltstack : Z := 0x920b0.  Definition tfib_E_musl_sigaltstack : Z := 0x9213c.
Definition tfib_A_lockfile : Z := 0x9277c.  Definition tfib_E_lockfile : Z := 0x92878.
Definition tfib_A_unlockfile : Z := 0x92878.  Definition tfib_E_unlockfile : Z := 0x928d8.
Definition tfib_A_stdio_read : Z := 0x92468.  Definition tfib_E_stdio_read : Z := 0x92580.
Definition tfib_A_stdio_write : Z := 0x92588.  Definition tfib_E_stdio_write : Z := 0x92718.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x92438.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9243c.
Definition tfib_A_stdio_close : Z := 0x9243c.  Definition tfib_E_stdio_close : Z := 0x92468.
Definition tfib_A_fwritex : Z := 0x92d0c.  Definition tfib_E_fwritex : Z := 0x92e44.
Definition tfib_A_musl_fwrite : Z := 0x92e44.  Definition tfib_E_musl_fwrite : Z := 0x92efc.
Definition tfib_A_towrite : Z := 0x92efc.  Definition tfib_E_towrite : Z := 0x92f50.
Definition tfib_A_stdio_exit : Z := 0x92b68.  Definition tfib_E_stdio_exit : Z := 0x92d0c.
Definition tfib_A_ofl_lock : Z := 0x92f50.  Definition tfib_E_ofl_lock : Z := 0x92f80.
Definition tfib_A_musl_vfprintf : Z := 0x930cc.  Definition tfib_E_musl_vfprintf : Z := 0x9327c.
Definition tfib_A_printf_core : Z := 0x9327c.  Definition tfib_E_printf_core : Z := 0x940ac.
Definition tfib_A_pop_arg : Z := 0x940ac.  Definition tfib_E_pop_arg : Z := 0x941e0.
Definition tfib_A_pad : Z := 0x941e0.  Definition tfib_E_pad : Z := 0x942b4.
Definition tfib_A_fmt_fp : Z := 0x942b4.  Definition tfib_E_fmt_fp : Z := 0x9597c.
Definition tfib_A_thunk_931e0 : Z := 0x8d7c8.  Definition tfib_E_thunk_931e0 : Z := 0x8d7cc.
Definition tfib_A_musl_wctomb : Z := 0x91b54.  Definition tfib_E_musl_wctomb : Z := 0x91b78.
Definition tfib_A_musl_wcrtomb : Z := 0x91a28.  Definition tfib_E_musl_wcrtomb : Z := 0x91b54.
Definition tfib_A_fpclassifyl : Z := 0x8fdb8.  Definition tfib_E_fpclassifyl : Z := 0x8fdfc.
Definition tfib_A_letf2 : Z := 0x8f5f0.  Definition tfib_E_letf2 : Z := 0x8f6b8.
Definition tfib_A_multf3 : Z := 0x8f6b8.  Definition tfib_E_multf3 : Z := 0x8fdb8.
Definition tfib_A_floatsitf : Z := 0x90614.  Definition tfib_E_floatsitf : Z := 0x9071c.
Definition tfib_A_scalbn : Z := 0x91020.  Definition tfib_E_scalbn : Z := 0x910b8.
Definition tfib_A_subtf3 : Z := 0x90604.  Definition tfib_E_subtf3 : Z := 0x90614.
Definition tfib_A_addtf3 : Z := 0x8fdfc.  Definition tfib_E_addtf3 : Z := 0x905c8.
Definition tfib_A_fe_getround : Z := 0x905c8.  Definition tfib_E_fe_getround : Z := 0x905f8.
Definition tfib_A_fixunstfsi : Z := 0x95984.  Definition tfib_E_fixunstfsi : Z := 0x95a18.
Definition tfib_A_floatunsitf : Z := 0x95a18.  Definition tfib_E_floatunsitf : Z := 0x95b04.
Definition tfib_A_fixtfsi : Z := 0x910b8.  Definition tfib_E_fixtfsi : Z := 0x91160.
Definition tfib_A_divtf3 : Z := 0x9071c.  Definition tfib_E_divtf3 : Z := 0x91020.
Definition tfib_A_musl_vprintf : Z := 0x961dc.  Definition tfib_E_musl_vprintf : Z := 0x961f8.
Definition tfib_A_stdout_write : Z := 0x92f8c.  Definition tfib_E_stdout_write : Z := 0x9302c.
Definition tfib_A_thunk_95368 : Z := 0x96790.  Definition tfib_E_thunk_95368 : Z := 0x96794.
Definition tfib_A_musl_memcmp : Z := 0x96860.  Definition tfib_E_musl_memcmp : Z := 0x96890.
Definition tfib_A_musl_memcpy : Z := 0x96890.  Definition tfib_E_musl_memcpy : Z := 0x96c94.
Definition tfib_A_musl_memset : Z := 0x96c94.  Definition tfib_E_musl_memset : Z := 0x96d8c.
Definition tfib_A_musl_strchr : Z := 0x96d8c.  Definition tfib_E_musl_strchr : Z := 0x96dc8.
Definition tfib_A_strchrnul : Z := 0x96dc8.  Definition tfib_E_strchrnul : Z := 0x96ea8.
Definition tfib_A_musl_strlen : Z := 0x96ee0.  Definition tfib_E_musl_strlen : Z := 0x96f70.
Definition tfib_A_musl_strnlen : Z := 0x9711c.  Definition tfib_E_musl_strnlen : Z := 0x97160.
Definition tfib_A_musl_memchr : Z := 0x96794.  Definition tfib_E_musl_memchr : Z := 0x96860.
Definition tfib_A_lock : Z := 0x97160.  Definition tfib_E_lock : Z := 0x973e8.
Definition tfib_A_unlock : Z := 0x973e8.  Definition tfib_E_unlock : Z := 0x9745c.
Definition tfib_A_syscall_cp_c : Z := 0x9745c.  Definition tfib_E_syscall_cp_c : Z := 0x97480.
Definition tfib_A_syscall_cp_sccp : Z := 0x97480.  Definition tfib_E_syscall_cp_sccp : Z := 0x97484.
Definition tfib_A_pthread_atfork : Z := 0x974c0.  Definition tfib_E_pthread_atfork : Z := 0x97564.
Definition tfib_A_mremap : Z := 0x9190c.  Definition tfib_E_mremap : Z := 0x919e0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x98538.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x98554.
Definition tfib_A_pthread_key_create : Z := 0x988e0.  Definition tfib_E_pthread_key_create : Z := 0x989b4.
Definition tfib_A_pthread_setspecific : Z := 0x98e7c.  Definition tfib_E_pthread_setspecific : Z := 0x98eb0.
Definition tfib_A_set_thread_area : Z := 0x98eb8.
Definition tfib_A_thunk_96f9c : Z := 0x98eb0.  Definition tfib_E_thunk_96f9c : Z := 0x98eb8.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x997e4.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9989c.
Definition tfib_A_close : Z := 0x9beb4.  Definition tfib_E_close : Z := 0x9bf08.
Definition tfib_A_musl_read : Z := 0x9bf94.  Definition tfib_E_musl_read : Z := 0x9bfc8.
Definition tfib_A_vm_wait : Z := 0x994f4.  Definition tfib_E_vm_wait : Z := 0x99544.
Definition tfib_D_str_sealed : Z := 0x11806.
Definition tfib_D_init_array_0_3 : Z := 0x9cfc8.
Definition tfib_D_fini_array_0_1 : Z := 0x9cfe8.
Definition tfib_D_GOT_common_flags : Z := 0x9d6c0.
Definition tfib_D_GOT_flags : Z := 0x9d6c8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9d6d0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9d6d8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9d6e0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9d6e8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9e238.
Definition tfib_D_environ_musl : Z := 0x9e360.
Definition tfib_D_REAL_read : Z := 0x9f408.
Definition tfib_D_REAL_memcpy : Z := 0x9f530.
Definition tfib_D_REAL_memset : Z := 0x9f538.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa2318.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa3178.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa5978.
Definition tfib_D_asan_inited : Z := 0xa6658.
Definition tfib_D_replace_intrin_cached : Z := 0xa6659.
Definition tfib_D_kHighMemEnd : Z := 0xa6660.
Definition tfib_D_kMidMemBeg : Z := 0xa6668.
Definition tfib_D_kMidMemEnd : Z := 0xa6670.
Definition tfib_D_malloc_context_size : Z := 0xa667c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1374a8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f8ba0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fb000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30984.
Definition tfib_at_rw_lo : Z := 0x9f000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63f14.
Definition tfib_at_x_imemcpy : Z := 0x63e98.
Definition tfib_at_x_memset : Z := 0x96c94.
Definition tfib_at_x_memcpy : Z := 0x96890.
Definition tfib_at_x_memiszero : Z := 0x64444.
Definition tfib_at_x_istrncpy : Z := 0x64340.
Definition tfib_at_x_sealed : Z := 0x11806.
Definition tfib_at_x_popfree : Z := 0x36d70.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8c694.
Definition tfib_at_x_envscan_k : Z := 0x8c6a0.
Definition tfib_at_x_pnscan : Z := 0x8c758.
Definition tfib_at_x_pnscan_k : Z := 0x8c764.
Definition tfib_at_stops_more : list Z := (0x349e4 :: 0x36008 :: 0x54220 :: 0x5a5d8 :: 0x5a5ec :: 0x5a600 :: 0x5ff90 :: 0x60060 :: 0x6d58c :: 0x6e498 :: 0x6e628 :: 0x78380 :: nil)%list.
