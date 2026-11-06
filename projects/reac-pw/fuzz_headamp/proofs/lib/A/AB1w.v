(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB1w.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22df4.
Definition tfib_text_lo : Z := 0x306e4.
Definition tfib_init_array_lo : Z := 0x9bc48.  Definition tfib_init_array_hi : Z := 0x9bc68.
Definition tfib_fini_array_lo : Z := 0x9bc68.  Definition tfib_fini_array_hi : Z := 0x9bc78.
Definition tfib_preinit_array_lo : Z := 0x9bc78.  Definition tfib_preinit_array_hi : Z := 0x9bc80.
Definition tfib_data_rel_ro_lo : Z := 0x9bc80.  Definition tfib_data_rel_ro_hi : Z := 0x9c310.
Definition tfib_got_lo : Z := 0x9c310.  Definition tfib_got_hi : Z := 0x9d068.
Definition tfib_data_lo : Z := 0x9e068.  Definition tfib_data_hi : Z := 0xa0c20.
Definition tfib_asan_globals_lo : Z := 0xa0c20.  Definition tfib_asan_globals_hi : Z := 0xa16e0.
Definition tfib_bss_lo : Z := 0xa1700.  Definition tfib_bss_hi : Z := 0x5f9630.
Definition tfib_tbss_lo : Z := 0x9ac48.  Definition tfib_tbss_hi : Z := 0x9ac5c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x306e4.  Definition tfib_gp : Z := 0x10800.

Definition tfib_A_do_init : Z := 0x3072c.  Definition tfib_E_do_init : Z := 0x307a0.
Definition tfib_A_do_fini : Z := 0x307a0.  Definition tfib_E_do_fini : Z := 0x30830.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30830.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x3086c.
Definition tfib_A_InitializeAllocator : Z := 0x309dc.  Definition tfib_E_InitializeAllocator : Z := 0x309f4.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x309f4.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30b60.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x310bc.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31218.
Definition tfib_A_asan_free : Z := 0x315ec.  Definition tfib_E_asan_free : Z := 0x31614.
Definition tfib_A_Allocator_Deallocate : Z := 0x31614.  Definition tfib_E_Allocator_Deallocate : Z := 0x318cc.
Definition tfib_A_asan_malloc : Z := 0x318cc.  Definition tfib_E_asan_malloc : Z := 0x31928.
Definition tfib_A_Allocator_Allocate : Z := 0x31928.  Definition tfib_E_Allocator_Allocate : Z := 0x322b0.

Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32c18.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32c74.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32c74.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32ec4.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32ec4.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32fb8.



Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33974.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33bf8.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33bf8.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33d78.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33d78.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33f40.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33f40.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3410c.

Definition tfib_A_InternalMmapVector_Realloc : Z := 0x341ac.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x342b0.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x345d8.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34720.

Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34ef0.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x351d8.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x358b0.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35a28.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35a28.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35bd8.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35bd8.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35dbc.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35dbc.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36094.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36094.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x3650c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3650c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x3660c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x3660c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36914.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36914.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36c84.


Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x371a0.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37288.
Definition tfib_A_AsanActivate : Z := 0x37288.  Definition tfib_E_AsanActivate : Z := 0x37364.

Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c3e0.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c4b8.
Definition tfib_A_FakeStack_Create : Z := 0x3c4b8.  Definition tfib_E_FakeStack_Create : Z := 0x3c5a4.

Definition tfib_A_SetTLSFakeStack : Z := 0x3cc7c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3ccac.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3ccac.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3ce78.

Definition tfib_A_check_no_overrun : Z := 0x83e3c.  Definition tfib_E_check_no_overrun : Z := 0x83ee8.  Definition tfib_A_check_count : Z := 0x83ee8.  Definition tfib_E_check_count : Z := 0x83f7c.  Definition tfib_A_check_cells_valid : Z := 0x83f7c.  Definition tfib_E_check_cells_valid : Z := 0x8405c.  Definition tfib_A_check_object : Z := 0x8405c.  Definition tfib_E_check_object : Z := 0x84148.  Definition tfib_A_check_cells : Z := 0x84148.  Definition tfib_E_check_cells : Z := 0x842e8.  Definition tfib_A_check_keys : Z := 0x842e8.  Definition tfib_E_check_keys : Z := 0x84368.  Definition tfib_A_check_refusal : Z := 0x84368.  Definition tfib_E_check_refusal : Z := 0x843e8.  Definition tfib_A_check_plain : Z := 0x843e8.  Definition tfib_E_check_plain : Z := 0x84544.  Definition tfib_A_reac_headamp_prop_parse : Z := 0x845ac.  Definition tfib_E_reac_headamp_prop_parse : Z := 0x845b4.  Definition tfib_A_reac_headamp_prop_parse_result : Z := 0x845b4.  Definition tfib_E_reac_headamp_prop_parse_result : Z := 0x84f24.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80bc0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83e3c.
Definition tfib_A_asan_InitializeFlags : Z := 0x3cfb4.  Definition tfib_E_asan_InitializeFlags : Z := 0x3dfe0.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e6ec.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f508.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3f508.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3fad4.


Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x40228.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40498.

























Definition tfib_A_tls_get_addr_thunk : Z := 0x41bf4.  Definition tfib_E_tls_get_addr_thunk : Z := 0x41bf8.














Definition tfib_A_icpt_strlen : Z := 0x41c2c.  Definition tfib_E_icpt_strlen : Z := 0x41ec0.
Definition tfib_A_icpt_strnlen : Z := 0x41ec0.  Definition tfib_E_icpt_strnlen : Z := 0x42154.
Definition tfib_A_icpt_strcmp : Z := 0x42158.  Definition tfib_E_icpt_strcmp : Z := 0x42688.
Definition tfib_A_icpt_strchr : Z := 0x42c64.  Definition tfib_E_icpt_strchr : Z := 0x42f44.
Definition tfib_A_icpt_memcmp : Z := 0x437dc.  Definition tfib_E_icpt_memcmp : Z := 0x43898.

Definition tfib_A_icpt_memchr : Z := 0x43898.  Definition tfib_E_icpt_memchr : Z := 0x43b68.
Definition tfib_A_icpt_frexpl : Z := 0x43b68.  Definition tfib_E_icpt_frexpl : Z := 0x43de0.
Definition tfib_A_icpt_read : Z := 0x43de0.  Definition tfib_E_icpt_read : Z := 0x44050.
Definition tfib_A_icpt_fwrite : Z := 0x44050.  Definition tfib_E_icpt_fwrite : Z := 0x442c4.
Definition tfib_A_icpt_time : Z := 0x442c4.  Definition tfib_E_icpt_time : Z := 0x44560.
Definition tfib_A_icpt_gmtime_r : Z := 0x44768.  Definition tfib_E_icpt_gmtime_r : Z := 0x449a8.
Definition tfib_A_icpt_vprintf : Z := 0x449a8.  Definition tfib_E_icpt_vprintf : Z := 0x44a44.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44a44.  Definition tfib_E_printf_common_format_interceptor : Z := 0x4550c.
Definition tfib_A_icpt_vfprintf : Z := 0x4550c.  Definition tfib_E_icpt_vfprintf : Z := 0x455c0.
Definition tfib_A_icpt_vsnprintf : Z := 0x455c0.  Definition tfib_E_icpt_vsnprintf : Z := 0x458d8.

Definition tfib_A_icpt_clock_gettime : Z := 0x45a54.  Definition tfib_E_icpt_clock_gettime : Z := 0x45cac.
Definition tfib_A_icpt_wcrtomb : Z := 0x45cac.  Definition tfib_E_icpt_wcrtomb : Z := 0x4621c.
Definition tfib_A_icpt_wctomb : Z := 0x4621c.  Definition tfib_E_icpt_wctomb : Z := 0x46578.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46644.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46a2c.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46a38.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46ab4.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46cc0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x46f58.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46f88.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x471b0.
Definition tfib_A_icpt_send : Z := 0x471b0.  Definition tfib_E_icpt_send : Z := 0x47464.
Definition tfib_A_icpt_sendto : Z := 0x47464.  Definition tfib_E_icpt_sendto : Z := 0x47728.
Definition tfib_A_icpt_sigaltstack : Z := 0x47728.  Definition tfib_E_icpt_sigaltstack : Z := 0x47984.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b1c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47ccc.





Definition tfib_A_asan_memcpy : Z := 0x51d0c.  Definition tfib_E_asan_memcpy : Z := 0x521a8.
Definition tfib_A_asan_memset : Z := 0x521a8.  Definition tfib_E_asan_memset : Z := 0x523e8.
Definition tfib_A_icpt_memset : Z := 0x523e8.  Definition tfib_E_icpt_memset : Z := 0x526d8.
Definition tfib_A_icpt_memcpy : Z := 0x526d8.  Definition tfib_E_icpt_memcpy : Z := 0x52cc8.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52cc8.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52d00.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52d00.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52d04.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52d04.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52d08.

Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52db4.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52ef0.


Definition tfib_A_free : Z := 0x5305c.  Definition tfib_E_free : Z := 0x53060.
Definition tfib_A_malloc : Z := 0x53060.  Definition tfib_E_malloc : Z := 0x53064.
Definition tfib_A_icpt_free : Z := 0x53064.  Definition tfib_E_icpt_free : Z := 0x53234.
Definition tfib_A_icpt_malloc : Z := 0x53234.  Definition tfib_E_icpt_malloc : Z := 0x53390.

Definition tfib_A_ReplaceSystemMalloc : Z := 0x5345c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x53460.


Definition tfib_A_SetCanPoisonMemory : Z := 0x53edc.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53eec.
Definition tfib_A_CanPoisonMemory : Z := 0x53eec.  Definition tfib_E_CanPoisonMemory : Z := 0x53f00.
Definition tfib_A_PoisonShadow : Z := 0x53f00.  Definition tfib_E_PoisonShadow : Z := 0x543fc.
Definition tfib_A_MemToShadow_checked : Z := 0x543fc.  Definition tfib_E_MemToShadow_checked : Z := 0x54538.


Definition tfib_A_asan_region_is_poisoned : Z := 0x54888.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54bcc.
Definition tfib_A_AsanTSDInit : Z := 0x54fec.  Definition tfib_E_AsanTSDInit : Z := 0x55068.
Definition tfib_A_AsanTSDGet : Z := 0x55068.  Definition tfib_E_AsanTSDGet : Z := 0x550a8.
Definition tfib_A_AsanTSDSet : Z := 0x550a8.  Definition tfib_E_AsanTSDSet : Z := 0x550e8.
Definition tfib_A_PlatformTSDDtor : Z := 0x550e8.  Definition tfib_E_PlatformTSDDtor : Z := 0x5516c.
Definition tfib_A_InstallAtForkHandler : Z := 0x5516c.  Definition tfib_E_InstallAtForkHandler : Z := 0x55188.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x551e8.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5522c.

Definition tfib_A_ReportDoubleFree : Z := 0x56258.  Definition tfib_E_ReportDoubleFree : Z := 0x564e8.
Definition tfib_A_ReportGenericError : Z := 0x57dc4.  Definition tfib_E_ReportGenericError : Z := 0x58680.
Definition tfib_A_AsanInited : Z := 0x58e0c.  Definition tfib_E_AsanInited : Z := 0x58e24.
Definition tfib_A_asan_report_load1 : Z := 0x58e24.  Definition tfib_E_asan_report_load1 : Z := 0x58e74.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58e74.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58ec4.
Definition tfib_A_asan_report_load2 : Z := 0x58ec4.  Definition tfib_E_asan_report_load2 : Z := 0x58f14.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58f14.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58f64.
Definition tfib_A_asan_report_load4 : Z := 0x58f64.  Definition tfib_E_asan_report_load4 : Z := 0x58fb4.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58fb4.  Definition tfib_E_asan_report_exp_load4 : Z := 0x59004.
Definition tfib_A_asan_report_load8 : Z := 0x59004.  Definition tfib_E_asan_report_load8 : Z := 0x59054.
Definition tfib_A_asan_report_exp_load8 : Z := 0x59054.  Definition tfib_E_asan_report_exp_load8 : Z := 0x590a4.
Definition tfib_A_asan_report_load16 : Z := 0x590a4.  Definition tfib_E_asan_report_load16 : Z := 0x590f4.
Definition tfib_A_asan_report_exp_load16 : Z := 0x590f4.  Definition tfib_E_asan_report_exp_load16 : Z := 0x59144.
Definition tfib_A_asan_report_store1 : Z := 0x59144.  Definition tfib_E_asan_report_store1 : Z := 0x59194.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59194.  Definition tfib_E_asan_report_exp_store1 : Z := 0x591e4.
Definition tfib_A_asan_report_store2 : Z := 0x591e4.  Definition tfib_E_asan_report_store2 : Z := 0x59234.
Definition tfib_A_asan_report_exp_store2 : Z := 0x59234.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59284.
Definition tfib_A_asan_report_store4 : Z := 0x59284.  Definition tfib_E_asan_report_store4 : Z := 0x592d4.
Definition tfib_A_asan_report_exp_store4 : Z := 0x592d4.  Definition tfib_E_asan_report_exp_store4 : Z := 0x59324.
Definition tfib_A_asan_report_store8 : Z := 0x59324.  Definition tfib_E_asan_report_store8 : Z := 0x59374.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59374.  Definition tfib_E_asan_report_exp_store8 : Z := 0x593c4.
Definition tfib_A_asan_report_store16 : Z := 0x593c4.  Definition tfib_E_asan_report_store16 : Z := 0x59414.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59414.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59464.
Definition tfib_A_asan_report_load_n : Z := 0x59464.  Definition tfib_E_asan_report_load_n : Z := 0x594b4.
Definition tfib_A_asan_report_exp_load_n : Z := 0x594b4.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59504.
Definition tfib_A_asan_report_store_n : Z := 0x59504.  Definition tfib_E_asan_report_store_n : Z := 0x59554.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59554.  Definition tfib_E_asan_report_exp_store_n : Z := 0x595a4.
Definition tfib_A_InitializeHighMemEnd : Z := 0x595a4.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59624.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59624.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x599d8.
Definition tfib_A_AsanInitInternal : Z := 0x59a68.  Definition tfib_E_AsanInitInternal : Z := 0x59d1c.


Definition tfib_A_asan_init : Z := 0x59f88.  Definition tfib_E_asan_init : Z := 0x5a01c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a01c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a020.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a020.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a084.

Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a284.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a5ac.

Definition tfib_A_InitializeShadowMemory : Z := 0x5a78c.  Definition tfib_E_InitializeShadowMemory : Z := 0x5aa94.
Definition tfib_A_SetMallocContextSize : Z := 0x5aa94.  Definition tfib_E_SetMallocContextSize : Z := 0x5aaa4.
Definition tfib_A_GetMallocContextSize : Z := 0x5aaa4.  Definition tfib_E_GetMallocContextSize : Z := 0x5aab4.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5aab4.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ac04.

Definition tfib_A_GetCurrentThreadStats : Z := 0x5b6e8.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b720.

Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b9d4.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5ba60.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5ba60.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5bac8.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5bac8.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5bb40.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5bb40.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5bba8.


Definition tfib_A_AsanThread_Create : Z := 0x5c10c.  Definition tfib_E_AsanThread_Create : Z := 0x5c2a8.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c304.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c51c.
Definition tfib_A_GetCurrentThread : Z := 0x5c51c.  Definition tfib_E_GetCurrentThread : Z := 0x5c53c.

Definition tfib_A_AsanThread_stack_top : Z := 0x5c6e0.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c738.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c738.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c790.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c790.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c9c0.
Definition tfib_A_AsanThread_Init : Z := 0x5c9c0.  Definition tfib_E_AsanThread_Init : Z := 0x5cdb4.

Definition tfib_A_CreateMainThread : Z := 0x5cef4.  Definition tfib_E_CreateMainThread : Z := 0x5d004.
Definition tfib_A_SetCurrentThread : Z := 0x5d004.  Definition tfib_E_SetCurrentThread : Z := 0x5d0e4.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d2e8.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5d424.





Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ea34.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5ea80.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5ea80.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5ea8c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5eabc.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5eac8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5eac8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5ead4.

Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5eaf0.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5edbc.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5edbc.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f17c.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x600d8.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x600e4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x600e4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x601bc.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x601bc.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x60258.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x6077c.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x607c0.

Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60a38.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60b4c.
Definition tfib_A_RunMallocHooks : Z := 0x60cf0.  Definition tfib_E_RunMallocHooks : Z := 0x60da8.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60da8.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60dac.
Definition tfib_A_RunFreeHooks : Z := 0x60dac.  Definition tfib_E_RunFreeHooks : Z := 0x60e58.


Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60e8c.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60ed8.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6119c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x613dc.
Definition tfib_A_sanitizer_set_report_path : Z := 0x619d8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x619f0.




Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63600.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63910.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63910.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63a54.
Definition tfib_A_FlagParser_ParseString : Z := 0x63a54.  Definition tfib_E_FlagParser_ParseString : Z := 0x63b48.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63cdc.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63d3c.

Definition tfib_A_internal_atoll : Z := 0x63d7c.  Definition tfib_E_internal_atoll : Z := 0x63e68.
Definition tfib_A_internal_simple_strtoll : Z := 0x63e68.  Definition tfib_E_internal_simple_strtoll : Z := 0x63fc4.
Definition tfib_A_internal_memchr : Z := 0x63fc4.  Definition tfib_E_internal_memchr : Z := 0x63fe4.
Definition tfib_A_internal_memcmp : Z := 0x63fe4.  Definition tfib_E_internal_memcmp : Z := 0x6401c.
Definition tfib_A_internal_memcpy : Z := 0x6401c.  Definition tfib_E_internal_memcpy : Z := 0x64040.
Definition tfib_A_internal_memmove : Z := 0x64040.  Definition tfib_E_internal_memmove : Z := 0x64098.
Definition tfib_A_internal_memset : Z := 0x64098.  Definition tfib_E_internal_memset : Z := 0x640f8.
Definition tfib_A_internal_strcspn : Z := 0x640f8.  Definition tfib_E_internal_strcspn : Z := 0x6414c.

Definition tfib_A_internal_strdup : Z := 0x64180.  Definition tfib_E_internal_strdup : Z := 0x641ec.
Definition tfib_A_internal_strlen : Z := 0x641ec.  Definition tfib_E_internal_strlen : Z := 0x64208.


Definition tfib_A_internal_strchrnul : Z := 0x64298.  Definition tfib_E_internal_strchrnul : Z := 0x642e0.
Definition tfib_A_internal_strrchr : Z := 0x642e0.  Definition tfib_E_internal_strrchr : Z := 0x64320.
Definition tfib_A_internal_strnlen : Z := 0x64450.  Definition tfib_E_internal_strnlen : Z := 0x64480.
Definition tfib_A_internal_strncpy : Z := 0x644c4.  Definition tfib_E_internal_strncpy : Z := 0x64534.
Definition tfib_A_internal_strstr : Z := 0x64534.  Definition tfib_E_internal_strstr : Z := 0x645c8.
Definition tfib_A_mem_is_zero : Z := 0x645c8.  Definition tfib_E_mem_is_zero : Z := 0x6467c.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6467c.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6468c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6468c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6486c.
Definition tfib_A_internal_iserror : Z := 0x64878.  Definition tfib_E_internal_iserror : Z := 0x64898.
Definition tfib_A_internal_mmap : Z := 0x64898.  Definition tfib_E_internal_mmap : Z := 0x648a4.
Definition tfib_A_internal_munmap : Z := 0x648a4.  Definition tfib_E_internal_munmap : Z := 0x648b0.
Definition tfib_A_internal_mprotect : Z := 0x648b0.  Definition tfib_E_internal_mprotect : Z := 0x648c0.
Definition tfib_A_internal_madvise : Z := 0x648c0.  Definition tfib_E_internal_madvise : Z := 0x648ec.
Definition tfib_A_internal_close : Z := 0x648ec.  Definition tfib_E_internal_close : Z := 0x648f8.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x648f8.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x6491c.
Definition tfib_A_internal_read : Z := 0x6491c.  Definition tfib_E_internal_read : Z := 0x64954.
Definition tfib_A_internal_write : Z := 0x64954.  Definition tfib_E_internal_write : Z := 0x6498c.
Definition tfib_A_internal_ftruncate : Z := 0x6498c.  Definition tfib_E_internal_ftruncate : Z := 0x649c4.
Definition tfib_A_internal_dup : Z := 0x649c4.  Definition tfib_E_internal_dup : Z := 0x649d0.
Definition tfib_A_internal_dup2_dup3 : Z := 0x649d0.  Definition tfib_E_internal_dup2_dup3 : Z := 0x649e0.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x649e0.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x649f8.
Definition tfib_A_internal_sched_yield : Z := 0x649f8.  Definition tfib_E_internal_sched_yield : Z := 0x64a04.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64a04.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64a50.
Definition tfib_A_internal_execve : Z := 0x64a50.  Definition tfib_E_internal_execve : Z := 0x64a5c.
Definition tfib_A_internal_exit_exit_group : Z := 0x64a5c.  Definition tfib_E_internal_exit_exit_group : Z := 0x64a70.
Definition tfib_A_FileExists_newfstatat : Z := 0x64a70.  Definition tfib_E_FileExists_newfstatat : Z := 0x64af0.
Definition tfib_A_DirExists_newfstatat : Z := 0x64af0.  Definition tfib_E_DirExists_newfstatat : Z := 0x64b54.
Definition tfib_A_GetTid_gettid : Z := 0x64b54.  Definition tfib_E_GetTid_gettid : Z := 0x64b60.
Definition tfib_A_GetEnv : Z := 0x64b60.  Definition tfib_E_GetEnv : Z := 0x64c90.
Definition tfib_A_FutexWait : Z := 0x64d94.  Definition tfib_E_FutexWait : Z := 0x64db8.
Definition tfib_A_FutexWake : Z := 0x64db8.  Definition tfib_E_FutexWake : Z := 0x64ddc.
Definition tfib_A_internal_ptrace : Z := 0x64ddc.  Definition tfib_E_internal_ptrace : Z := 0x64de8.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64de8.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64df8.
Definition tfib_A_internal_getpid : Z := 0x64df8.  Definition tfib_E_internal_getpid : Z := 0x64e04.
Definition tfib_A_internal_getppid : Z := 0x64e04.  Definition tfib_E_internal_getppid : Z := 0x64e10.
Definition tfib_A_internal_prctl : Z := 0x64e10.  Definition tfib_E_internal_prctl : Z := 0x64e1c.
Definition tfib_A_internal_sigaltstack : Z := 0x64e1c.  Definition tfib_E_internal_sigaltstack : Z := 0x64e28.
Definition tfib_A_internal_fork_clone : Z := 0x64e28.  Definition tfib_E_internal_fork_clone : Z := 0x64e40.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64e40.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64f6c.

Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x656ac.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x657c4.

Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x657cc.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65878.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65878.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65998.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65a60.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65ae0.

Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65b3c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65c08.

Definition tfib_A_CheckASLR : Z := 0x65d08.  Definition tfib_E_CheckASLR : Z := 0x65d0c.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65f58.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65f5c.

Definition tfib_A_MmapOrDie : Z := 0x65f68.  Definition tfib_E_MmapOrDie : Z := 0x66074.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x66074.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x660e8.
Definition tfib_A_UnmapOrDie : Z := 0x660e8.  Definition tfib_E_UnmapOrDie : Z := 0x66164.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x66164.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66274.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x664a0.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x665a4.

Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x665b0.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66728.


Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66c44.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66e50.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67408.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67414.
Definition tfib_A_Printf : Z := 0x67418.  Definition tfib_E_Printf : Z := 0x67464.
Definition tfib_A_SharedPrintfCode : Z := 0x67464.  Definition tfib_E_SharedPrintfCode : Z := 0x674c0.
Definition tfib_A_Report : Z := 0x674c0.  Definition tfib_E_Report : Z := 0x6750c.
Definition tfib_A_SuppressionContext_ctor : Z := 0x69004.  Definition tfib_E_SuppressionContext_ctor : Z := 0x69060.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x69060.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6929c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6929c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x695c0.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69b60.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69c30.




Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a270.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a6e8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6afa8.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b2cc.

Definition tfib_A_AddDieCallback : Z := 0x6bb88.  Definition tfib_E_AddDieCallback : Z := 0x6bc10.
Definition tfib_A_Die : Z := 0x6bcd4.  Definition tfib_E_Die : Z := 0x6bd94.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6bd94.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6bda0.
Definition tfib_A_CheckFailed : Z := 0x6bda0.  Definition tfib_E_CheckFailed : Z := 0x6be58.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c4b0.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c5a8.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c5a8.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c6d4.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c8fc.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c978.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c9ac.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6cc94.



Definition tfib_A_AndroidLogInit : Z := 0x6d53c.  Definition tfib_E_AndroidLogInit : Z := 0x6d540.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d570.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d5b8.



Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d914.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6da18.


Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6dd5c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6ddfc.

Definition tfib_A_SetAlternateSignalStack : Z := 0x6de88.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6df4c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6df4c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6dfd4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6dfd4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e04c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e04c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e130.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e1ec.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e320.


Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e6e8.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e7b4.





Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x705e4.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70708.
Definition tfib_A_StackStore_Alloc : Z := 0x70708.  Definition tfib_E_StackStore_Alloc : Z := 0x7083c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x710f0.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x711a4.

Definition tfib_A_StackDepotPut : Z := 0x72be0.  Definition tfib_E_StackDepotPut : Z := 0x72c00.
Definition tfib_A_StackDepotBase_Put : Z := 0x72c00.  Definition tfib_E_StackDepotBase_Put : Z := 0x72e84.
Definition tfib_A_StackDepotBase_Get : Z := 0x72e84.  Definition tfib_E_StackDepotBase_Get : Z := 0x72f94.


Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73564.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x7356c.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x7356c.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x736cc.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x736cc.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73740.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73bc8.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73ce0.


Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79f30.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79fec.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79fec.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a0c4.

Definition tfib_A_lsan_flags_init_helper : Z := 0x7a664.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7a6a8.

Definition tfib_A_lsan_InitCommonLsan : Z := 0x7ad48.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7ae00.

Definition tfib_A_lsan_register_root_region : Z := 0x7cd64.  Definition tfib_E_lsan_register_root_region : Z := 0x7d094.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d094.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d51c.


Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x8047c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x804f8.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x804f8.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x805a8.

Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x805c0.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80708.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80708.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80714.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80714.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80720.
Definition tfib_A_main : Z := 0x80720.  Definition tfib_E_main : Z := 0x809e4.
Definition tfib_A_target_alloc_init : Z := 0x809e4.  Definition tfib_E_target_alloc_init : Z := 0x809e8.
Definition tfib_A_target_alloc_count : Z := 0x809e8.  Definition tfib_E_target_alloc_count : Z := 0x809f0.

Definition tfib_A_emit_printf : Z := 0x80b78.  Definition tfib_E_emit_printf : Z := 0x80bc0.


Definition tfib_A_asan_module_ctor : Z := 0x84544.  Definition tfib_E_asan_module_ctor : Z := 0x8457c.








Definition tfib_A_asan_module_dtor : Z := 0x8457c.  Definition tfib_E_asan_module_dtor : Z := 0x845ac.






Definition tfib_A_extenddftf2 : Z := 0x850b8.  Definition tfib_E_extenddftf2 : Z := 0x85248.
Definition tfib_A_sysconf : Z := 0x8b930.  Definition tfib_E_sysconf : Z := 0x8bb58.
Definition tfib_A_init : Z := 0x8bb58.  Definition tfib_E_init : Z := 0x8bb5c.
Definition tfib_A_init_libc : Z := 0x8bb5c.  Definition tfib_E_init_libc : Z := 0x8bd88.
Definition tfib_A_libc_start_init : Z := 0x8bd88.  Definition tfib_E_libc_start_init : Z := 0x8bdd4.
Definition tfib_A_libc_start_main : Z := 0x8bdd4.  Definition tfib_E_libc_start_main : Z := 0x8be34.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8be34.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8be7c.
Definition tfib_A_init_tls : Z := 0x8bf54.  Definition tfib_E_init_tls : Z := 0x8c204.
Definition tfib_A_init_ssp : Z := 0x8c204.  Definition tfib_E_init_ssp : Z := 0x8c264.
Definition tfib_A_stack_chk_fail : Z := 0x8c264.  Definition tfib_E_stack_chk_fail : Z := 0x8c26c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c2b4.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c348.
Definition tfib_A_Exit : Z := 0x8c348.  Definition tfib_E_Exit : Z := 0x8c364.
Definition tfib_A_funcs_on_exit : Z := 0x8c394.  Definition tfib_E_funcs_on_exit : Z := 0x8c45c.

Definition tfib_A_cxa_atexit_atexit : Z := 0x8c460.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8c524.

Definition tfib_A_musl_exit_helper_stub : Z := 0x8c528.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8c52c.
Definition tfib_A_libc_exit_fini : Z := 0x8c52c.  Definition tfib_E_libc_exit_fini : Z := 0x8c578.
Definition tfib_A_exit : Z := 0x8c578.  Definition tfib_E_exit : Z := 0x8c5ec.
Definition tfib_A_open : Z := 0x8c7ec.  Definition tfib_E_open : Z := 0x8c8d0.
Definition tfib_A_syscall_ret : Z := 0x8c8d0.  Definition tfib_E_syscall_ret : Z := 0x8c908.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8c908.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8cab0.
Definition tfib_A_calloc : Z := 0x8d074.  Definition tfib_E_calloc : Z := 0x8d1ac.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8d1ac.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8d1b0.
Definition tfib_A_libc_free : Z := 0x8d1b0.  Definition tfib_E_libc_free : Z := 0x8d37c.
Definition tfib_A_get_meta : Z := 0x8d37c.  Definition tfib_E_get_meta : Z := 0x8d48c.
Definition tfib_A_alloc_meta : Z := 0x8d864.  Definition tfib_E_alloc_meta : Z := 0x8db3c.
Definition tfib_A_libc_malloc_impl : Z := 0x8db3c.  Definition tfib_E_libc_malloc_impl : Z := 0x8deac.
Definition tfib_A_alloc_slot : Z := 0x8deac.  Definition tfib_E_alloc_slot : Z := 0x8e750.
Definition tfib_A_enframe : Z := 0x8e750.  Definition tfib_E_enframe : Z := 0x8e8a0.
Definition tfib_A_malloc_allzerop : Z := 0x8e8a0.  Definition tfib_E_malloc_allzerop : Z := 0x8ea18.
Definition tfib_A_getrlimit : Z := 0x8fde8.  Definition tfib_E_getrlimit : Z := 0x8fee0.
Definition tfib_A_getrusage : Z := 0x8fee0.  Definition tfib_E_getrusage : Z := 0x8ff08.
Definition tfib_A_setrlimit : Z := 0x8ff08.  Definition tfib_E_setrlimit : Z := 0x8ffd0.
Definition tfib_A_mmap : Z := 0x903f8.  Definition tfib_E_mmap : Z := 0x904e4.
Definition tfib_A_mprotect : Z := 0x904e4.  Definition tfib_E_mprotect : Z := 0x9052c.
Definition tfib_A_munmap : Z := 0x90600.  Definition tfib_E_munmap : Z := 0x90648.
Definition tfib_A_sched_yield : Z := 0x9090c.  Definition tfib_E_sched_yield : Z := 0x90930.
Definition tfib_A_raise_tkill_path : Z := 0x9098c.  Definition tfib_E_raise_tkill_path : Z := 0x90a04.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x90a04.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x90bd8.
Definition tfib_A_musl_sigaltstack : Z := 0x90cd0.  Definition tfib_E_musl_sigaltstack : Z := 0x90d5c.


Definition tfib_A_lockfile : Z := 0x9139c.  Definition tfib_E_lockfile : Z := 0x91498.
Definition tfib_A_unlockfile : Z := 0x91498.  Definition tfib_E_unlockfile : Z := 0x914f8.



Definition tfib_A_stdio_read : Z := 0x91088.  Definition tfib_E_stdio_read : Z := 0x911a0.
Definition tfib_A_stdio_write : Z := 0x911a8.  Definition tfib_E_stdio_write : Z := 0x91338.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x91058.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x9105c.
Definition tfib_A_stdio_close : Z := 0x9105c.  Definition tfib_E_stdio_close : Z := 0x91088.
Definition tfib_A_fwritex : Z := 0x9192c.  Definition tfib_E_fwritex : Z := 0x91a64.
Definition tfib_A_musl_fwrite : Z := 0x91a64.  Definition tfib_E_musl_fwrite : Z := 0x91b1c.
Definition tfib_A_towrite : Z := 0x91b1c.  Definition tfib_E_towrite : Z := 0x91b70.
Definition tfib_A_stdio_exit : Z := 0x91788.  Definition tfib_E_stdio_exit : Z := 0x9192c.
Definition tfib_A_ofl_lock : Z := 0x91b70.  Definition tfib_E_ofl_lock : Z := 0x91ba0.

Definition tfib_A_musl_vfprintf : Z := 0x91cec.  Definition tfib_E_musl_vfprintf : Z := 0x91e9c.
Definition tfib_A_printf_core : Z := 0x91e9c.  Definition tfib_E_printf_core : Z := 0x92ccc.
Definition tfib_A_pop_arg : Z := 0x92ccc.  Definition tfib_E_pop_arg : Z := 0x92e00.
Definition tfib_A_pad : Z := 0x92e00.  Definition tfib_E_pad : Z := 0x92ed4.
Definition tfib_A_fmt_fp : Z := 0x92ed4.  Definition tfib_E_fmt_fp : Z := 0x9459c.

Definition tfib_A_musl_wctomb : Z := 0x90774.  Definition tfib_E_musl_wctomb : Z := 0x90798.
Definition tfib_A_musl_wcrtomb : Z := 0x90648.  Definition tfib_E_musl_wcrtomb : Z := 0x90774.
Definition tfib_A_fpclassifyl : Z := 0x8f1f0.  Definition tfib_E_fpclassifyl : Z := 0x8f234.
Definition tfib_A_letf2 : Z := 0x84f34.  Definition tfib_E_letf2 : Z := 0x84ffc.
Definition tfib_A_multf3 : Z := 0x8eaf0.  Definition tfib_E_multf3 : Z := 0x8f1f0.
Definition tfib_A_floatsitf : Z := 0x8f234.  Definition tfib_E_floatsitf : Z := 0x8f33c.
Definition tfib_A_scalbn : Z := 0x8fc40.  Definition tfib_E_scalbn : Z := 0x8fcd8.
Definition tfib_A_subtf3 : Z := 0x854c8.  Definition tfib_E_subtf3 : Z := 0x854d8.
Definition tfib_A_addtf3 : Z := 0x854d8.  Definition tfib_E_addtf3 : Z := 0x85ca4.
Definition tfib_A_fe_getround : Z := 0x85ca4.  Definition tfib_E_fe_getround : Z := 0x85cd4.
Definition tfib_A_fixunstfsi : Z := 0x945a4.  Definition tfib_E_fixunstfsi : Z := 0x94638.
Definition tfib_A_floatunsitf : Z := 0x94638.  Definition tfib_E_floatunsitf : Z := 0x94724.
Definition tfib_A_fixtfsi : Z := 0x8fcd8.  Definition tfib_E_fixtfsi : Z := 0x8fd80.
Definition tfib_A_divtf3 : Z := 0x8f33c.  Definition tfib_E_divtf3 : Z := 0x8fc40.
Definition tfib_A_musl_vprintf : Z := 0x94dfc.  Definition tfib_E_musl_vprintf : Z := 0x94e18.
Definition tfib_A_stdout_write : Z := 0x91bac.  Definition tfib_E_stdout_write : Z := 0x91c4c.

Definition tfib_A_musl_memcmp : Z := 0x9547c.  Definition tfib_E_musl_memcmp : Z := 0x954ac.
Definition tfib_A_musl_memcpy : Z := 0x954ac.  Definition tfib_E_musl_memcpy : Z := 0x958b0.
Definition tfib_A_musl_memset : Z := 0x958b0.  Definition tfib_E_musl_memset : Z := 0x959a8.
Definition tfib_A_musl_strchr : Z := 0x959a8.  Definition tfib_E_musl_strchr : Z := 0x959e4.
Definition tfib_A_strchrnul : Z := 0x959e4.  Definition tfib_E_strchrnul : Z := 0x95ac4.
Definition tfib_A_musl_strlen : Z := 0x95afc.  Definition tfib_E_musl_strlen : Z := 0x95b8c.
Definition tfib_A_musl_strnlen : Z := 0x95d98.  Definition tfib_E_musl_strnlen : Z := 0x95ddc.
Definition tfib_A_musl_memchr : Z := 0x953b0.  Definition tfib_E_musl_memchr : Z := 0x9547c.
Definition tfib_A_lock : Z := 0x95ddc.  Definition tfib_E_lock : Z := 0x96064.
Definition tfib_A_unlock : Z := 0x96064.  Definition tfib_E_unlock : Z := 0x960d8.
Definition tfib_A_syscall_cp_c : Z := 0x960d8.  Definition tfib_E_syscall_cp_c : Z := 0x960fc.
Definition tfib_A_syscall_cp_sccp : Z := 0x960fc.  Definition tfib_E_syscall_cp_sccp : Z := 0x96100.

Definition tfib_A_pthread_atfork : Z := 0x9613c.  Definition tfib_E_pthread_atfork : Z := 0x961e0.
Definition tfib_A_mremap : Z := 0x9052c.  Definition tfib_E_mremap : Z := 0x90600.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x971b4.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x971d0.
Definition tfib_A_pthread_key_create : Z := 0x9755c.  Definition tfib_E_pthread_key_create : Z := 0x97630.



Definition tfib_A_pthread_setspecific : Z := 0x97af8.  Definition tfib_E_pthread_setspecific : Z := 0x97b2c.
Definition tfib_A_set_thread_area : Z := 0x97b34.  Definition tfib_E_set_thread_area : Z := 0x97b40.

Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98460.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98518.
Definition tfib_A_close : Z := 0x9ab30.  Definition tfib_E_close : Z := 0x9ab84.
Definition tfib_A_musl_read : Z := 0x9ac10.  Definition tfib_E_musl_read : Z := 0x9ac44.
Definition tfib_A_vm_wait : Z := 0x98170.  Definition tfib_E_vm_wait : Z := 0x981c0.
Definition tfib_D_str_sealed : Z := 0x11860.
Definition tfib_D_init_array_0_3 : Z := 0x9bc48.
Definition tfib_D_fini_array_0_1 : Z := 0x9bc68.
Definition tfib_D_GOT_common_flags : Z := 0x9c360.
Definition tfib_D_GOT_flags : Z := 0x9c368.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c370.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c378.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c380.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c388.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9ced8.
Definition tfib_D_environ_musl : Z := 0x9d000.
Definition tfib_D_REAL_read : Z := 0x9e0a8.
Definition tfib_D_REAL_memcpy : Z := 0x9e1d0.
Definition tfib_D_REAL_memset : Z := 0x9e1d8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa1758.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa25b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa4db8.
Definition tfib_D_asan_inited : Z := 0xa5a98.
Definition tfib_D_replace_intrin_cached : Z := 0xa5a99.
Definition tfib_D_kHighMemEnd : Z := 0xa5aa0.
Definition tfib_D_kMidMemBeg : Z := 0xa5aa8.
Definition tfib_D_kMidMemEnd : Z := 0xa5ab0.
Definition tfib_D_malloc_context_size : Z := 0xa5abc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1368e8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f7fe0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x306e4.
Definition tfib_at_rw_lo : Z := 0x9e000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x64098.
Definition tfib_at_x_imemcpy : Z := 0x6401c.
Definition tfib_at_x_memset : Z := 0x958b0.
Definition tfib_at_x_memcpy : Z := 0x954ac.
Definition tfib_at_x_memiszero : Z := 0x645c8.
Definition tfib_at_x_istrncpy : Z := 0x644c4.
Definition tfib_at_x_sealed : Z := 0x11860.
Definition tfib_at_x_popfree : Z := 0x36ad0.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8bb94.
Definition tfib_at_x_envscan_k : Z := 0x8bba0.
Definition tfib_at_x_pnscan : Z := 0x8bc58.
Definition tfib_at_x_pnscan_k : Z := 0x8bc64.
Definition tfib_at_stops_more : list Z := (0x34744 :: 0x35d68 :: 0x543a4 :: 0x5a75c :: 0x5a770 :: 0x5a784 :: 0x60114 :: 0x601e4 :: 0x6d710 :: 0x6e61c :: 0x6e7ac :: 0x78504 :: nil)%list.
