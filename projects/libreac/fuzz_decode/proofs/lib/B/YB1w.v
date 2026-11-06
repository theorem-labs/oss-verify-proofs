(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1w.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the function rows are keyed by name to fuzz_decode.asan-ubsan's own FUNC symbols (unstripped .symtab) and each tfib_E_ is st_value + st_size (provenance/core-reloc/B/yb1w/yb1w_regen.py); of the six rows the relocation had moved with cgif's span, target_run no longer covers the next function, start keeps only its start cell (its end cell tfib_E_start is removed: _start has st_size 0 in the .symtab, so the cell cannot be checked, and nothing reads it), and the other four (thunk_417cc, MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser, pthread_key_create_body_tsd_init, thunk_96f9c) are removed as false by the name rule and read by nothing; and the three rows the relocation dropped are back, read off the same symbols (asan_stack_malloc_0, StackDepotNode_store_hash_helper, LLVMFuzzerTestOneInput). *)
(* Modified by Theorem Labs, 2026-10: tfib_img_lo / tfib_img_hi are the numerals vm_compute gives for the unit's Reusable/YImgTop.v IMG_LO / IMG_TOP, as image A's A/AB1w.v does (RELOC-GATES G17). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x226cc.
Definition tfib_text_lo : Z := 0x30054.  Definition tfib_text_hi : Z := 0x97d50.
Definition tfib_init_array_lo : Z := 0x98d50.  Definition tfib_init_array_hi : Z := 0x98d70.
Definition tfib_fini_array_lo : Z := 0x98d70.  Definition tfib_fini_array_hi : Z := 0x98d80.
Definition tfib_preinit_array_lo : Z := 0x98d80.  Definition tfib_preinit_array_hi : Z := 0x98d88.
Definition tfib_data_rel_ro_lo : Z := 0x98d88.  Definition tfib_data_rel_ro_hi : Z := 0x99288.
Definition tfib_got_lo : Z := 0x99288.  Definition tfib_got_hi : Z := 0x99ff8.
Definition tfib_data_lo : Z := 0x9aff8.  Definition tfib_data_hi : Z := 0x9dbb0.
Definition tfib_asan_globals_lo : Z := 0x9dbb0.  Definition tfib_asan_globals_hi : Z := 0x9dc70.
Definition tfib_bss_lo : Z := 0x9dc80.  Definition tfib_bss_hi : Z := 0x5f5bb8.
Definition tfib_tbss_lo : Z := 0x97d50.  Definition tfib_tbss_hi : Z := 0x97d64.
(* decode: YImgTop COMPUTES IMG_LO / IMG_TOP (the donor states numerals); the body here is the numeral vm_compute
   gives for YImgTop's term (no numeral written), so the donor's `unfold ...; lia` proofs see a number. *)
Definition tfib_img_lo : Z := ltac:(let v := eval vm_compute in IMG_LO in exact v).  Definition tfib_img_hi : Z := ltac:(let v := eval vm_compute in IMG_TOP in exact v).
Definition tfib_entry : Z := 0x30054.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30054.
Definition tfib_A_do_init : Z := 0x3009c.  Definition tfib_E_do_init : Z := 0x30110.
Definition tfib_A_do_fini : Z := 0x30110.  Definition tfib_E_do_fini : Z := 0x301a0.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x301a0.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x301dc.
Definition tfib_A_InitializeAllocator : Z := 0x3034c.  Definition tfib_E_InitializeAllocator : Z := 0x30364.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30364.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x304d0.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x30a2c.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30b88.
Definition tfib_A_asan_free : Z := 0x30f5c.  Definition tfib_E_asan_free : Z := 0x30f84.
Definition tfib_A_Allocator_Deallocate : Z := 0x30f84.  Definition tfib_E_Allocator_Deallocate : Z := 0x3123c.
Definition tfib_A_asan_malloc : Z := 0x3123c.  Definition tfib_E_asan_malloc : Z := 0x31298.
Definition tfib_A_Allocator_Allocate : Z := 0x31298.  Definition tfib_E_Allocator_Allocate : Z := 0x31c20.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32668.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x326c4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x326c4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32914.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32914.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32a08.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x333c4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33648.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33648.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x337c8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x337c8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33990.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33990.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33b5c.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33bfc.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33d00.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34028.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34170.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35300.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35478.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35628.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3580c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x3580c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x35ae4.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x35ae4.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35f5c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35f5c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x3605c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x3605c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36364.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36364.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x366d4.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36bf0.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36cd8.
Definition tfib_A_AsanActivate : Z := 0x36cd8.  Definition tfib_E_AsanActivate : Z := 0x36db4.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3be30.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bf08.
Definition tfib_A_FakeStack_Create : Z := 0x3bf08.  Definition tfib_E_FakeStack_Create : Z := 0x3bff4.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c6cc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c6fc.
Definition tfib_A_check_round_trip : Z := 0x80d54.  Definition tfib_E_check_round_trip : Z := 0x81070.  Definition tfib_A_check_braid : Z := 0x81070.  Definition tfib_E_check_braid : Z := 0x81414.  Definition tfib_A_reac_frame_is_reac : Z := 0x8144c.  Definition tfib_E_reac_frame_is_reac : Z := 0x814f8.  Definition tfib_A_reac_frame_counter : Z := 0x814f8.  Definition tfib_E_reac_frame_counter : Z := 0x8158c.  Definition tfib_A_reac_frame_clean_len : Z := 0x8158c.  Definition tfib_E_reac_frame_clean_len : Z := 0x815cc.  Definition tfib_A_reac_frame_inspect : Z := 0x815fc.  Definition tfib_E_reac_frame_inspect : Z := 0x81788.  Definition tfib_A_reac_decode : Z := 0x81788.  Definition tfib_E_reac_decode : Z := 0x81a8c.  Definition tfib_A_reac_decode_plain_le : Z := 0x81a8c.  Definition tfib_E_reac_decode_plain_le : Z := 0x81cfc.  Definition tfib_A_reac_braid_encode : Z := 0x81cfc.  Definition tfib_E_reac_braid_encode : Z := 0x81fe8.  Definition tfib_A_reac_upstream_channels : Z := 0x81fe8.  Definition tfib_E_reac_upstream_channels : Z := 0x82038.  Definition tfib_A_reac_upstream_decode : Z := 0x82038.  Definition tfib_E_reac_upstream_decode : Z := 0x823c8.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3c6fc.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3c870.

Definition tfib_A_asan_InitializeFlags : Z := 0x3c9ac.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d9d8.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e0e4.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ef00.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3ef00.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f4cc.


Definition tfib_A_icpt_strlen : Z := 0x41620.  Definition tfib_E_icpt_strlen : Z := 0x418b4.
Definition tfib_A_icpt_strnlen : Z := 0x418b4.  Definition tfib_E_icpt_strnlen : Z := 0x41b48.
Definition tfib_A_icpt_strcmp : Z := 0x41b4c.  Definition tfib_E_icpt_strcmp : Z := 0x4207c.
Definition tfib_A_icpt_strchr : Z := 0x4207c.  Definition tfib_E_icpt_strchr : Z := 0x4235c.
Definition tfib_A_icpt_memcmp : Z := 0x42bf4.  Definition tfib_E_icpt_memcmp : Z := 0x42cb0.
Definition tfib_A_icpt_memchr : Z := 0x42d6c.  Definition tfib_E_icpt_memchr : Z := 0x4303c.
Definition tfib_A_icpt_frexpl : Z := 0x4303c.  Definition tfib_E_icpt_frexpl : Z := 0x432b4.
Definition tfib_A_icpt_read : Z := 0x432b4.  Definition tfib_E_icpt_read : Z := 0x43524.
Definition tfib_A_icpt_fwrite : Z := 0x43524.  Definition tfib_E_icpt_fwrite : Z := 0x43798.
Definition tfib_A_icpt_time : Z := 0x43798.  Definition tfib_E_icpt_time : Z := 0x43a34.
Definition tfib_A_icpt_gmtime_r : Z := 0x43c3c.  Definition tfib_E_icpt_gmtime_r : Z := 0x43e7c.
Definition tfib_A_icpt_vprintf : Z := 0x43e7c.  Definition tfib_E_icpt_vprintf : Z := 0x43f18.
Definition tfib_A_printf_common_format_interceptor : Z := 0x43f18.  Definition tfib_E_printf_common_format_interceptor : Z := 0x449e0.
Definition tfib_A_icpt_vfprintf : Z := 0x449e0.  Definition tfib_E_icpt_vfprintf : Z := 0x44a94.
Definition tfib_A_icpt_vsnprintf : Z := 0x44a94.  Definition tfib_E_icpt_vsnprintf : Z := 0x44dac.
Definition tfib_A_icpt_clock_gettime : Z := 0x44f28.  Definition tfib_E_icpt_clock_gettime : Z := 0x45180.
Definition tfib_A_icpt_wcrtomb : Z := 0x45180.  Definition tfib_E_icpt_wcrtomb : Z := 0x456f0.
Definition tfib_A_icpt_wctomb : Z := 0x456f0.  Definition tfib_E_icpt_wctomb : Z := 0x45a4c.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45b18.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45f00.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45f0c.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45f88.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46194.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4642c.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4645c.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46684.
Definition tfib_A_icpt_send : Z := 0x46684.  Definition tfib_E_icpt_send : Z := 0x46938.
Definition tfib_A_icpt_sendto : Z := 0x46938.  Definition tfib_E_icpt_sendto : Z := 0x46bfc.
Definition tfib_A_icpt_sigaltstack : Z := 0x46bfc.  Definition tfib_E_icpt_sigaltstack : Z := 0x46e58.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46f2c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x470dc.
Definition tfib_A_asan_memcpy : Z := 0x50c5c.  Definition tfib_E_asan_memcpy : Z := 0x510f8.
Definition tfib_A_asan_memset : Z := 0x510f8.  Definition tfib_E_asan_memset : Z := 0x51338.
Definition tfib_A_icpt_memset : Z := 0x51338.  Definition tfib_E_icpt_memset : Z := 0x51628.
Definition tfib_A_icpt_memcpy : Z := 0x51628.  Definition tfib_E_icpt_memcpy : Z := 0x51c18.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51c18.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51c50.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51c50.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x51c54.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x51c54.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51c58.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51d04.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51e40.
Definition tfib_A_free : Z := 0x51fac.  Definition tfib_E_free : Z := 0x51fb0.
Definition tfib_A_malloc : Z := 0x51fb0.  Definition tfib_E_malloc : Z := 0x51fb4.
Definition tfib_A_icpt_free : Z := 0x51fb8.  Definition tfib_E_icpt_free : Z := 0x52188.
Definition tfib_A_icpt_malloc : Z := 0x52188.  Definition tfib_E_icpt_malloc : Z := 0x522e4.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x525e8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x525ec.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53068.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53078.
Definition tfib_A_CanPoisonMemory : Z := 0x53078.  Definition tfib_E_CanPoisonMemory : Z := 0x5308c.
Definition tfib_A_PoisonShadow : Z := 0x5308c.  Definition tfib_E_PoisonShadow : Z := 0x53588.
Definition tfib_A_MemToShadow_checked : Z := 0x53588.  Definition tfib_E_MemToShadow_checked : Z := 0x536c4.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53a14.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53d58.
Definition tfib_A_AsanTSDInit : Z := 0x54178.  Definition tfib_E_AsanTSDInit : Z := 0x541f4.
Definition tfib_A_AsanTSDGet : Z := 0x541f4.  Definition tfib_E_AsanTSDGet : Z := 0x54234.
Definition tfib_A_AsanTSDSet : Z := 0x54234.  Definition tfib_E_AsanTSDSet : Z := 0x54274.
Definition tfib_A_PlatformTSDDtor : Z := 0x54274.  Definition tfib_E_PlatformTSDDtor : Z := 0x542f8.
Definition tfib_A_InstallAtForkHandler : Z := 0x542f8.  Definition tfib_E_InstallAtForkHandler : Z := 0x54314.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54374.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x543b8.
Definition tfib_A_ReportDoubleFree : Z := 0x553e4.  Definition tfib_E_ReportDoubleFree : Z := 0x55674.
Definition tfib_A_ReportGenericError : Z := 0x571a0.  Definition tfib_E_ReportGenericError : Z := 0x57a5c.
Definition tfib_A_AsanInited : Z := 0x581e8.  Definition tfib_E_AsanInited : Z := 0x58200.
Definition tfib_A_asan_report_load1 : Z := 0x58200.  Definition tfib_E_asan_report_load1 : Z := 0x58250.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58250.  Definition tfib_E_asan_report_exp_load1 : Z := 0x582a0.
Definition tfib_A_asan_report_load2 : Z := 0x582a0.  Definition tfib_E_asan_report_load2 : Z := 0x582f0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x582f0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58340.
Definition tfib_A_asan_report_load4 : Z := 0x58340.  Definition tfib_E_asan_report_load4 : Z := 0x58390.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58390.  Definition tfib_E_asan_report_exp_load4 : Z := 0x583e0.
Definition tfib_A_asan_report_load8 : Z := 0x583e0.  Definition tfib_E_asan_report_load8 : Z := 0x58430.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58430.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58480.
Definition tfib_A_asan_report_load16 : Z := 0x58480.  Definition tfib_E_asan_report_load16 : Z := 0x584d0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x584d0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58520.
Definition tfib_A_asan_report_store1 : Z := 0x58520.  Definition tfib_E_asan_report_store1 : Z := 0x58570.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58570.  Definition tfib_E_asan_report_exp_store1 : Z := 0x585c0.
Definition tfib_A_asan_report_store2 : Z := 0x585c0.  Definition tfib_E_asan_report_store2 : Z := 0x58610.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58610.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58660.
Definition tfib_A_asan_report_store4 : Z := 0x58660.  Definition tfib_E_asan_report_store4 : Z := 0x586b0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x586b0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58700.
Definition tfib_A_asan_report_store8 : Z := 0x58700.  Definition tfib_E_asan_report_store8 : Z := 0x58750.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58750.  Definition tfib_E_asan_report_exp_store8 : Z := 0x587a0.
Definition tfib_A_asan_report_store16 : Z := 0x587a0.  Definition tfib_E_asan_report_store16 : Z := 0x587f0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x587f0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58840.
Definition tfib_A_asan_report_load_n : Z := 0x58840.  Definition tfib_E_asan_report_load_n : Z := 0x58890.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58890.  Definition tfib_E_asan_report_exp_load_n : Z := 0x588e0.
Definition tfib_A_asan_report_store_n : Z := 0x588e0.  Definition tfib_E_asan_report_store_n : Z := 0x58930.
Definition tfib_A_asan_report_exp_store_n : Z := 0x58930.  Definition tfib_E_asan_report_exp_store_n : Z := 0x58980.
Definition tfib_A_InitializeHighMemEnd : Z := 0x58980.  Definition tfib_E_InitializeHighMemEnd : Z := 0x58a00.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x58a00.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58db4.
Definition tfib_A_AsanInitInternal : Z := 0x58e44.  Definition tfib_E_AsanInitInternal : Z := 0x590f8.
Definition tfib_A_asan_init : Z := 0x59364.  Definition tfib_E_asan_init : Z := 0x593f8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x593f8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x593fc.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59660.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59988.
Definition tfib_A_InitializeShadowMemory : Z := 0x59b68.  Definition tfib_E_InitializeShadowMemory : Z := 0x59e70.
Definition tfib_A_SetMallocContextSize : Z := 0x59e70.  Definition tfib_E_SetMallocContextSize : Z := 0x59e80.
Definition tfib_A_GetMallocContextSize : Z := 0x59e80.  Definition tfib_E_GetMallocContextSize : Z := 0x59e90.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59e90.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59fe0.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5aac4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5aafc.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5adb0.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5ae3c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5ae3c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5aea4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5aea4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5af1c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5af1c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5af84.
Definition tfib_A_AsanThread_Create : Z := 0x5b4e8.  Definition tfib_E_AsanThread_Create : Z := 0x5b684.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b6e0.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b8f8.
Definition tfib_A_GetCurrentThread : Z := 0x5b8f8.  Definition tfib_E_GetCurrentThread : Z := 0x5b918.
Definition tfib_A_AsanThread_stack_top : Z := 0x5babc.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bb14.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bb14.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bb6c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bb6c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bd9c.
Definition tfib_A_AsanThread_Init : Z := 0x5bd9c.  Definition tfib_E_AsanThread_Init : Z := 0x5c190.
Definition tfib_A_CreateMainThread : Z := 0x5c2d0.  Definition tfib_E_CreateMainThread : Z := 0x5c3e0.
Definition tfib_A_SetCurrentThread : Z := 0x5c3e0.  Definition tfib_E_SetCurrentThread : Z := 0x5c4c0.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c6c4.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c800.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5df24.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5df70.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5df70.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5df7c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5dfac.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5dfb8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5dfb8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5dfc4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f5d4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f6ac.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f6ac.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f748.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fc6c.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fcb0.
Definition tfib_A_RunMallocHooks : Z := 0x601e0.  Definition tfib_E_RunMallocHooks : Z := 0x60298.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60298.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x6029c.
Definition tfib_A_RunFreeHooks : Z := 0x6029c.  Definition tfib_E_RunFreeHooks : Z := 0x60348.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6068c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x608cc.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60ec8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60ee0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x62af0.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62e00.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62e00.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62f44.
Definition tfib_A_FlagParser_ParseString : Z := 0x62f44.  Definition tfib_E_FlagParser_ParseString : Z := 0x63038.
Definition tfib_A_internal_atoll : Z := 0x6326c.  Definition tfib_E_internal_atoll : Z := 0x63358.
Definition tfib_A_internal_simple_strtoll : Z := 0x63358.  Definition tfib_E_internal_simple_strtoll : Z := 0x634b4.
Definition tfib_A_internal_memchr : Z := 0x634b4.  Definition tfib_E_internal_memchr : Z := 0x634d4.
Definition tfib_A_internal_memcmp : Z := 0x634d4.  Definition tfib_E_internal_memcmp : Z := 0x6350c.
Definition tfib_A_internal_memcpy : Z := 0x6350c.  Definition tfib_E_internal_memcpy : Z := 0x63530.
Definition tfib_A_internal_memmove : Z := 0x63530.  Definition tfib_E_internal_memmove : Z := 0x63588.
Definition tfib_A_internal_memset : Z := 0x63588.  Definition tfib_E_internal_memset : Z := 0x635e8.
Definition tfib_A_internal_strcspn : Z := 0x635e8.  Definition tfib_E_internal_strcspn : Z := 0x6363c.
Definition tfib_A_internal_strdup : Z := 0x63670.  Definition tfib_E_internal_strdup : Z := 0x636dc.
Definition tfib_A_internal_strlen : Z := 0x636dc.  Definition tfib_E_internal_strlen : Z := 0x636f8.
Definition tfib_A_internal_strchrnul : Z := 0x63788.  Definition tfib_E_internal_strchrnul : Z := 0x637d0.
Definition tfib_A_internal_strrchr : Z := 0x637d0.  Definition tfib_E_internal_strrchr : Z := 0x63810.
Definition tfib_A_internal_strnlen : Z := 0x63940.  Definition tfib_E_internal_strnlen : Z := 0x63970.
Definition tfib_A_internal_strncpy : Z := 0x639b4.  Definition tfib_E_internal_strncpy : Z := 0x63a24.
Definition tfib_A_internal_strstr : Z := 0x63a24.  Definition tfib_E_internal_strstr : Z := 0x63ab8.
Definition tfib_A_mem_is_zero : Z := 0x63ab8.  Definition tfib_E_mem_is_zero : Z := 0x63b6c.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63b6c.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63b7c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63b7c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63d5c.
Definition tfib_A_internal_iserror : Z := 0x63d68.  Definition tfib_E_internal_iserror : Z := 0x63d88.
Definition tfib_A_internal_mmap : Z := 0x63d88.  Definition tfib_E_internal_mmap : Z := 0x63d94.
Definition tfib_A_internal_munmap : Z := 0x63d94.  Definition tfib_E_internal_munmap : Z := 0x63da0.
Definition tfib_A_internal_mprotect : Z := 0x63da0.  Definition tfib_E_internal_mprotect : Z := 0x63db0.
Definition tfib_A_internal_madvise : Z := 0x63db0.  Definition tfib_E_internal_madvise : Z := 0x63ddc.
Definition tfib_A_internal_close : Z := 0x63ddc.  Definition tfib_E_internal_close : Z := 0x63de8.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63de8.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63e0c.
Definition tfib_A_internal_read : Z := 0x63e0c.  Definition tfib_E_internal_read : Z := 0x63e44.
Definition tfib_A_internal_write : Z := 0x63e44.  Definition tfib_E_internal_write : Z := 0x63e7c.
Definition tfib_A_internal_ftruncate : Z := 0x63e7c.  Definition tfib_E_internal_ftruncate : Z := 0x63eb4.
Definition tfib_A_internal_dup : Z := 0x63eb4.  Definition tfib_E_internal_dup : Z := 0x63ec0.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63ec0.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63ed0.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63ed0.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63ee8.
Definition tfib_A_internal_sched_yield : Z := 0x63ee8.  Definition tfib_E_internal_sched_yield : Z := 0x63ef4.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63ef4.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63f40.
Definition tfib_A_internal_execve : Z := 0x63f40.  Definition tfib_E_internal_execve : Z := 0x63f4c.
Definition tfib_A_internal_exit_exit_group : Z := 0x63f4c.  Definition tfib_E_internal_exit_exit_group : Z := 0x63f60.
Definition tfib_A_FileExists_newfstatat : Z := 0x63f60.  Definition tfib_E_FileExists_newfstatat : Z := 0x63fe0.
Definition tfib_A_DirExists_newfstatat : Z := 0x63fe0.  Definition tfib_E_DirExists_newfstatat : Z := 0x64044.
Definition tfib_A_GetTid_gettid : Z := 0x64044.  Definition tfib_E_GetTid_gettid : Z := 0x64050.
Definition tfib_A_GetEnv : Z := 0x64050.  Definition tfib_E_GetEnv : Z := 0x64180.
Definition tfib_A_FutexWait : Z := 0x64284.  Definition tfib_E_FutexWait : Z := 0x642a8.
Definition tfib_A_FutexWake : Z := 0x642a8.  Definition tfib_E_FutexWake : Z := 0x642cc.
Definition tfib_A_internal_ptrace : Z := 0x642cc.  Definition tfib_E_internal_ptrace : Z := 0x642d8.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x642d8.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x642e8.
Definition tfib_A_internal_getpid : Z := 0x642e8.  Definition tfib_E_internal_getpid : Z := 0x642f4.
Definition tfib_A_internal_getppid : Z := 0x642f4.  Definition tfib_E_internal_getppid : Z := 0x64300.
Definition tfib_A_internal_prctl : Z := 0x64300.  Definition tfib_E_internal_prctl : Z := 0x6430c.
Definition tfib_A_internal_sigaltstack : Z := 0x6430c.  Definition tfib_E_internal_sigaltstack : Z := 0x64318.
Definition tfib_A_internal_fork_clone : Z := 0x64318.  Definition tfib_E_internal_fork_clone : Z := 0x64330.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64330.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x6445c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64b9c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64cb4.
Definition tfib_A_GetPageSizeCached : Z := 0x64cb4.  Definition tfib_E_GetPageSizeCached : Z := 0x64cbc.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64cbc.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64d68.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64d68.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64e88.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64f50.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64fd0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6502c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x650f8.
Definition tfib_A_CheckASLR : Z := 0x651f8.  Definition tfib_E_CheckASLR : Z := 0x651fc.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65448.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6544c.
Definition tfib_A_MmapOrDie : Z := 0x65458.  Definition tfib_E_MmapOrDie : Z := 0x65564.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65564.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x655d8.
Definition tfib_A_UnmapOrDie : Z := 0x655d8.  Definition tfib_E_UnmapOrDie : Z := 0x65654.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65654.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65764.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65990.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x65a94.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66134.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66340.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x668f8.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66904.
Definition tfib_A_Printf : Z := 0x66908.  Definition tfib_E_Printf : Z := 0x66954.
Definition tfib_A_SharedPrintfCode : Z := 0x66954.  Definition tfib_E_SharedPrintfCode : Z := 0x669b0.
Definition tfib_A_Report : Z := 0x669b0.  Definition tfib_E_Report : Z := 0x669fc.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68550.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6878c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6878c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x68ab0.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69760.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69bd8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a498.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a7bc.
Definition tfib_A_AddDieCallback : Z := 0x6b078.  Definition tfib_E_AddDieCallback : Z := 0x6b100.
Definition tfib_A_Die : Z := 0x6b1c4.  Definition tfib_E_Die : Z := 0x6b284.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b284.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b290.
Definition tfib_A_CheckFailed : Z := 0x6b290.  Definition tfib_E_CheckFailed : Z := 0x6b348.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b9a0.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6ba98.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6ba98.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6bbc4.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6be9c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c184.
Definition tfib_A_AndroidLogInit : Z := 0x6ca2c.  Definition tfib_E_AndroidLogInit : Z := 0x6ca30.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6ca60.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6caa8.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6caa8.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ccf4.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6ce04.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6cf08.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d24c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d2ec.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d378.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d43c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d43c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d4c4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d4c4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d53c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d53c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d620.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d6dc.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d810.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6fad4.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6fbf8.
Definition tfib_A_StackStore_Alloc : Z := 0x6fbf8.  Definition tfib_E_StackStore_Alloc : Z := 0x6fd2c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x705e0.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70694.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71de8.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x71e44.
Definition tfib_A_StackDepotPut : Z := 0x720d0.  Definition tfib_E_StackDepotPut : Z := 0x720f0.
Definition tfib_A_StackDepotBase_Put : Z := 0x720f0.  Definition tfib_E_StackDepotBase_Put : Z := 0x72374.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x72a54.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x72a5c.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72bbc.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72c30.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x730b8.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x731d0.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79420.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x794dc.
Definition tfib_A_Unwind_Trace_callback : Z := 0x794dc.  Definition tfib_E_Unwind_Trace_callback : Z := 0x795b4.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79b98.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79f68.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a238.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a2f0.
Definition tfib_A_lsan_register_root_region : Z := 0x7c254.  Definition tfib_E_lsan_register_root_region : Z := 0x7c584.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c584.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7ca0c.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f96c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f9e8.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f9e8.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7fa98.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fab0.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fbf8.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7fbf8.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7fc04.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7fc04.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7fc10.
Definition tfib_A_main : Z := 0x7fc10.  Definition tfib_E_main : Z := 0x7fed4.
Definition tfib_A_target_alloc_init : Z := 0x7fed4.  Definition tfib_E_target_alloc_init : Z := 0x7fed8.
Definition tfib_A_target_alloc_count : Z := 0x7fed8.  Definition tfib_E_target_alloc_count : Z := 0x7fee0.
Definition tfib_A_target_run : Z := 0x7fee0.  Definition tfib_E_target_run : Z := 0x80038.
Definition tfib_A_emit_printf : Z := 0x80068.  Definition tfib_E_emit_printf : Z := 0x800b0.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x800b0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x80d54.

Definition tfib_A_asan_module_ctor : Z := 0x81414.  Definition tfib_E_asan_module_ctor : Z := 0x8144c.








Definition tfib_A_asan_module_dtor : Z := 0x815cc.  Definition tfib_E_asan_module_dtor : Z := 0x815fc.






Definition tfib_A_extenddftf2 : Z := 0x823d8.  Definition tfib_E_extenddftf2 : Z := 0x82568.
Definition tfib_A_sysconf : Z := 0x881b8.  Definition tfib_E_sysconf : Z := 0x883e0.
Definition tfib_A_init : Z := 0x883e0.  Definition tfib_E_init : Z := 0x883e4.
Definition tfib_A_init_libc : Z := 0x883e4.  Definition tfib_E_init_libc : Z := 0x88610.
Definition tfib_A_libc_start_init : Z := 0x88610.  Definition tfib_E_libc_start_init : Z := 0x8865c.
Definition tfib_A_libc_start_main : Z := 0x8865c.  Definition tfib_E_libc_start_main : Z := 0x886bc.
Definition tfib_A_libc_start_main_stage2 : Z := 0x886bc.  Definition tfib_E_libc_start_main_stage2 : Z := 0x88704.
Definition tfib_A_init_tls : Z := 0x887dc.  Definition tfib_E_init_tls : Z := 0x88a8c.
Definition tfib_A_init_ssp : Z := 0x88a8c.  Definition tfib_E_init_ssp : Z := 0x88aec.
Definition tfib_A_stack_chk_fail : Z := 0x88aec.  Definition tfib_E_stack_chk_fail : Z := 0x88af4.
Definition tfib_A_Exit : Z := 0x88bd0.  Definition tfib_E_Exit : Z := 0x88bec.
Definition tfib_A_funcs_on_exit : Z := 0x88c1c.  Definition tfib_E_funcs_on_exit : Z := 0x88ce4.
Definition tfib_A_libc_exit_fini : Z := 0x88db4.  Definition tfib_E_libc_exit_fini : Z := 0x88e00.
Definition tfib_A_exit : Z := 0x88e00.  Definition tfib_E_exit : Z := 0x88e74.
Definition tfib_A_open : Z := 0x89074.  Definition tfib_E_open : Z := 0x89158.
Definition tfib_A_syscall_ret : Z := 0x89158.  Definition tfib_E_syscall_ret : Z := 0x89190.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x89190.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x89338.
Definition tfib_A_calloc : Z := 0x898fc.  Definition tfib_E_calloc : Z := 0x89a34.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x89a34.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x89a38.
Definition tfib_A_libc_free : Z := 0x89a38.  Definition tfib_E_libc_free : Z := 0x89c04.
Definition tfib_A_get_meta : Z := 0x89c04.  Definition tfib_E_get_meta : Z := 0x89d14.
Definition tfib_A_alloc_meta : Z := 0x8a0ec.  Definition tfib_E_alloc_meta : Z := 0x8a3c4.
Definition tfib_A_libc_malloc_impl : Z := 0x8a3c4.  Definition tfib_E_libc_malloc_impl : Z := 0x8a734.
Definition tfib_A_alloc_slot : Z := 0x8a734.  Definition tfib_E_alloc_slot : Z := 0x8afd8.
Definition tfib_A_enframe : Z := 0x8afd8.  Definition tfib_E_enframe : Z := 0x8b128.
Definition tfib_A_malloc_allzerop : Z := 0x8b128.  Definition tfib_E_malloc_allzerop : Z := 0x8b2a0.
Definition tfib_A_getrlimit : Z := 0x8cf50.  Definition tfib_E_getrlimit : Z := 0x8d048.
Definition tfib_A_getrusage : Z := 0x8d048.  Definition tfib_E_getrusage : Z := 0x8d070.
Definition tfib_A_setrlimit : Z := 0x8d070.  Definition tfib_E_setrlimit : Z := 0x8d138.
Definition tfib_A_mmap : Z := 0x8d560.  Definition tfib_E_mmap : Z := 0x8d64c.
Definition tfib_A_mprotect : Z := 0x8d64c.  Definition tfib_E_mprotect : Z := 0x8d694.
Definition tfib_A_munmap : Z := 0x8d768.  Definition tfib_E_munmap : Z := 0x8d7b0.
Definition tfib_A_sched_yield : Z := 0x8da74.  Definition tfib_E_sched_yield : Z := 0x8da98.
Definition tfib_A_raise_tkill_path : Z := 0x8daf4.  Definition tfib_E_raise_tkill_path : Z := 0x8db6c.
Definition tfib_A_musl_sigaltstack : Z := 0x8de38.  Definition tfib_E_musl_sigaltstack : Z := 0x8dec4.

Definition tfib_A_lockfile : Z := 0x8e504.  Definition tfib_E_lockfile : Z := 0x8e600.
Definition tfib_A_unlockfile : Z := 0x8e600.  Definition tfib_E_unlockfile : Z := 0x8e660.



Definition tfib_A_stdio_read : Z := 0x8e1f0.  Definition tfib_E_stdio_read : Z := 0x8e308.
Definition tfib_A_stdio_write : Z := 0x8e310.  Definition tfib_E_stdio_write : Z := 0x8e4a0.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8e1c0.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8e1c4.
Definition tfib_A_stdio_close : Z := 0x8e1c4.  Definition tfib_E_stdio_close : Z := 0x8e1f0.
Definition tfib_A_fwritex : Z := 0x8ea94.  Definition tfib_E_fwritex : Z := 0x8ebcc.
Definition tfib_A_musl_fwrite : Z := 0x8ebcc.  Definition tfib_E_musl_fwrite : Z := 0x8ec84.
Definition tfib_A_towrite : Z := 0x8ec84.  Definition tfib_E_towrite : Z := 0x8ecd8.
Definition tfib_A_stdio_exit : Z := 0x8e8f0.  Definition tfib_E_stdio_exit : Z := 0x8ea94.
Definition tfib_A_ofl_lock : Z := 0x8ecd8.  Definition tfib_E_ofl_lock : Z := 0x8ed08.

Definition tfib_A_musl_vfprintf : Z := 0x8ee54.  Definition tfib_E_musl_vfprintf : Z := 0x8f004.
Definition tfib_A_printf_core : Z := 0x8f004.  Definition tfib_E_printf_core : Z := 0x8fe34.
Definition tfib_A_pop_arg : Z := 0x8fe34.  Definition tfib_E_pop_arg : Z := 0x8ff68.
Definition tfib_A_pad : Z := 0x8ff68.  Definition tfib_E_pad : Z := 0x9003c.
Definition tfib_A_fmt_fp : Z := 0x9003c.  Definition tfib_E_fmt_fp : Z := 0x91704.
Definition tfib_A_musl_wctomb : Z := 0x8d8dc.  Definition tfib_E_musl_wctomb : Z := 0x8d900.
Definition tfib_A_musl_wcrtomb : Z := 0x8d7b0.  Definition tfib_E_musl_wcrtomb : Z := 0x8d8dc.
Definition tfib_A_fpclassifyl : Z := 0x8bb40.  Definition tfib_E_fpclassifyl : Z := 0x8bb84.
Definition tfib_A_letf2 : Z := 0x8b378.  Definition tfib_E_letf2 : Z := 0x8b440.
Definition tfib_A_multf3 : Z := 0x8b440.  Definition tfib_E_multf3 : Z := 0x8bb40.
Definition tfib_A_floatsitf : Z := 0x8c39c.  Definition tfib_E_floatsitf : Z := 0x8c4a4.
Definition tfib_A_scalbn : Z := 0x8cda8.  Definition tfib_E_scalbn : Z := 0x8ce40.
Definition tfib_A_subtf3 : Z := 0x8c38c.  Definition tfib_E_subtf3 : Z := 0x8c39c.
Definition tfib_A_addtf3 : Z := 0x8bb84.  Definition tfib_E_addtf3 : Z := 0x8c350.
Definition tfib_A_fe_getround : Z := 0x8c350.  Definition tfib_E_fe_getround : Z := 0x8c380.
Definition tfib_A_fixunstfsi : Z := 0x9170c.  Definition tfib_E_fixunstfsi : Z := 0x917a0.
Definition tfib_A_floatunsitf : Z := 0x917a0.  Definition tfib_E_floatunsitf : Z := 0x9188c.
Definition tfib_A_fixtfsi : Z := 0x8ce40.  Definition tfib_E_fixtfsi : Z := 0x8cee8.
Definition tfib_A_divtf3 : Z := 0x8c4a4.  Definition tfib_E_divtf3 : Z := 0x8cda8.
Definition tfib_A_musl_vprintf : Z := 0x91f64.  Definition tfib_E_musl_vprintf : Z := 0x91f80.
Definition tfib_A_stdout_write : Z := 0x8ed14.  Definition tfib_E_stdout_write : Z := 0x8edb4.
Definition tfib_A_musl_memcmp : Z := 0x925e8.  Definition tfib_E_musl_memcmp : Z := 0x92618.
Definition tfib_A_musl_memcpy : Z := 0x92618.  Definition tfib_E_musl_memcpy : Z := 0x92a1c.
Definition tfib_A_musl_memset : Z := 0x92a1c.  Definition tfib_E_musl_memset : Z := 0x92b14.
Definition tfib_A_musl_strchr : Z := 0x92b14.  Definition tfib_E_musl_strchr : Z := 0x92b50.
Definition tfib_A_strchrnul : Z := 0x92b50.  Definition tfib_E_strchrnul : Z := 0x92c30.
Definition tfib_A_musl_strlen : Z := 0x92c68.  Definition tfib_E_musl_strlen : Z := 0x92cf8.
Definition tfib_A_musl_strnlen : Z := 0x92ea4.  Definition tfib_E_musl_strnlen : Z := 0x92ee8.
Definition tfib_A_musl_memchr : Z := 0x9251c.  Definition tfib_E_musl_memchr : Z := 0x925e8.
Definition tfib_A_lock : Z := 0x92ee8.  Definition tfib_E_lock : Z := 0x93170.
Definition tfib_A_unlock : Z := 0x93170.  Definition tfib_E_unlock : Z := 0x931e4.
Definition tfib_A_syscall_cp_c : Z := 0x931e4.  Definition tfib_E_syscall_cp_c : Z := 0x93208.
Definition tfib_A_syscall_cp_sccp : Z := 0x93208.  Definition tfib_E_syscall_cp_sccp : Z := 0x9320c.
Definition tfib_A_pthread_atfork : Z := 0x93248.  Definition tfib_E_pthread_atfork : Z := 0x932ec.
Definition tfib_A_mremap : Z := 0x8d694.  Definition tfib_E_mremap : Z := 0x8d768.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x942c0.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x942dc.
Definition tfib_A_pthread_key_create : Z := 0x94668.  Definition tfib_E_pthread_key_create : Z := 0x9473c.
Definition tfib_A_pthread_setspecific : Z := 0x94c04.  Definition tfib_E_pthread_setspecific : Z := 0x94c38.
Definition tfib_A_set_thread_area : Z := 0x94c40.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9556c.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x95624.
Definition tfib_A_close : Z := 0x97c3c.  Definition tfib_E_close : Z := 0x97c90.
Definition tfib_A_musl_read : Z := 0x97d1c.  Definition tfib_E_musl_read : Z := 0x97d50.
Definition tfib_A_vm_wait : Z := 0x9527c.  Definition tfib_E_vm_wait : Z := 0x952cc.
Definition tfib_D_str_sealed : Z := 0x1181e.
Definition tfib_D_init_array_0_3 : Z := 0x98d50.
Definition tfib_D_fini_array_0_1 : Z := 0x98d70.
Definition tfib_D_GOT_common_flags : Z := 0x992d8.
Definition tfib_D_GOT_flags : Z := 0x992e0.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x992e8.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x992f0.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x992f8.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x99300.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x99e50.
Definition tfib_D_environ_musl : Z := 0x99f90.
Definition tfib_D_REAL_read : Z := 0x9b038.
Definition tfib_D_REAL_memcpy : Z := 0x9b160.
Definition tfib_D_REAL_memset : Z := 0x9b168.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa1338.
Definition tfib_D_asan_inited : Z := 0xa2018.
Definition tfib_D_replace_intrin_cached : Z := 0xa2019.
Definition tfib_D_kHighMemEnd : Z := 0xa2020.
Definition tfib_D_kMidMemBeg : Z := 0xa2028.
Definition tfib_D_kMidMemEnd : Z := 0xa2030.
Definition tfib_D_malloc_context_size : Z := 0xa203c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x132e68.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f4568.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f6000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30054.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63588.
Definition tfib_at_x_imemcpy : Z := 0x6350c.
Definition tfib_at_x_memset : Z := 0x92a1c.
Definition tfib_at_x_memcpy : Z := 0x92618.
Definition tfib_at_x_memiszero : Z := 0x63ab8.
Definition tfib_at_x_istrncpy : Z := 0x639b4.
Definition tfib_at_x_sealed : Z := 0x1181e.
Definition tfib_at_x_popfree : Z := 0x36520.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8841c.
Definition tfib_at_x_envscan_k : Z := 0x88428.
Definition tfib_at_x_pnscan : Z := 0x884e0.
Definition tfib_at_x_pnscan_k : Z := 0x884ec.
Definition tfib_at_stops_more : list Z := (0x34194 :: 0x357b8 :: 0x53530 :: 0x59b38 :: 0x59b4c :: 0x59b60 :: 0x5f604 :: 0x5f6d4 :: 0x6cc00 :: 0x6db0c :: 0x6dc9c :: 0x779f4 :: nil)%list.
