(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB1w.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AB1w.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AB1w.v was made and quote its ASan-build values. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22e34.
Definition tfib_text_lo : Z := 0x30764.
Definition tfib_init_array_lo : Z := 0x9c0c0.  Definition tfib_init_array_hi : Z := 0x9c0e0.
Definition tfib_fini_array_lo : Z := 0x9c0e0.  Definition tfib_fini_array_hi : Z := 0x9c0f0.
Definition tfib_preinit_array_lo : Z := 0x9c0f0.  Definition tfib_preinit_array_hi : Z := 0x9c0f8.
Definition tfib_data_rel_ro_lo : Z := 0x9c100.  Definition tfib_data_rel_ro_hi : Z := 0x9c790.
Definition tfib_got_lo : Z := 0x9c790.  Definition tfib_got_hi : Z := 0x9d4e8.
Definition tfib_data_lo : Z := 0x9e4e8.  Definition tfib_data_hi : Z := 0xa10a0.
Definition tfib_asan_globals_lo : Z := 0xa10a0.  Definition tfib_asan_globals_hi : Z := 0xa1b60.
Definition tfib_bss_lo : Z := 0xa1b80.  Definition tfib_bss_hi : Z := 0x5f9ab0.
Definition tfib_tbss_lo : Z := 0x9b0c0.  Definition tfib_tbss_hi : Z := 0x9b0d4.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x30764.  Definition tfib_gp : Z := 0x10800.

Definition tfib_A_do_init : Z := 0x307ac.  Definition tfib_E_do_init : Z := 0x30820.
Definition tfib_A_do_fini : Z := 0x30820.  Definition tfib_E_do_fini : Z := 0x308b0.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x308b0.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x308ec.
Definition tfib_A_InitializeAllocator : Z := 0x30a5c.  Definition tfib_E_InitializeAllocator : Z := 0x30a74.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30a74.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30be0.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x3113c.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31298.
Definition tfib_A_asan_free : Z := 0x3166c.  Definition tfib_E_asan_free : Z := 0x31694.
Definition tfib_A_Allocator_Deallocate : Z := 0x31694.  Definition tfib_E_Allocator_Deallocate : Z := 0x3194c.
Definition tfib_A_asan_malloc : Z := 0x3194c.  Definition tfib_E_asan_malloc : Z := 0x319a8.
Definition tfib_A_Allocator_Allocate : Z := 0x319a8.  Definition tfib_E_Allocator_Allocate : Z := 0x32330.

Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32c98.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32cf4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32cf4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32f44.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32f44.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33038.



Definition tfib_A_QuarantineCallback_Recycle : Z := 0x339f4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33c78.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33c78.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33df8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33df8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33fc0.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33fc0.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3418c.

Definition tfib_A_InternalMmapVector_Realloc : Z := 0x3422c.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34330.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34658.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x347a0.

Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34f70.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35258.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35930.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35aa8.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35aa8.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35c58.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35c58.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35e3c.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35e3c.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36114.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36114.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x3658c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3658c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x3668c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x3668c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36994.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36994.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36d04.


Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37220.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37308.
Definition tfib_A_AsanActivate : Z := 0x37308.  Definition tfib_E_AsanActivate : Z := 0x373e4.

Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c460.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c538.
Definition tfib_A_FakeStack_Create : Z := 0x3c538.  Definition tfib_E_FakeStack_Create : Z := 0x3c624.

Definition tfib_A_SetTLSFakeStack : Z := 0x3ccfc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cd2c.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3cd2c.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3cef8.

Definition tfib_A_check_no_overrun : Z := 0x83e7c.  Definition tfib_E_check_no_overrun : Z := 0x83f2c.  Definition tfib_A_check_count : Z := 0x83f2c.  Definition tfib_E_check_count : Z := 0x83fcc.  Definition tfib_A_check_cells_valid : Z := 0x83fcc.  Definition tfib_E_check_cells_valid : Z := 0x840c0.  Definition tfib_A_check_object : Z := 0x840c0.  Definition tfib_E_check_object : Z := 0x841c0.  Definition tfib_A_check_cells : Z := 0x841c0.  Definition tfib_E_check_cells : Z := 0x843a4.  Definition tfib_A_check_keys : Z := 0x843a4.  Definition tfib_E_check_keys : Z := 0x84438.  Definition tfib_A_check_refusal : Z := 0x84438.  Definition tfib_E_check_refusal : Z := 0x844cc.  Definition tfib_A_check_plain : Z := 0x844cc.  Definition tfib_E_check_plain : Z := 0x84634.  Definition tfib_A_reac_headamp_prop_parse : Z := 0x849a4.  Definition tfib_E_reac_headamp_prop_parse : Z := 0x849ac.  Definition tfib_A_reac_headamp_prop_parse_result : Z := 0x849ac.  Definition tfib_E_reac_headamp_prop_parse_result : Z := 0x8539c.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80c40.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83e7c.
Definition tfib_A_asan_InitializeFlags : Z := 0x3d034.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e060.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e76c.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f588.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3f588.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3fb54.


Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x402a8.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40518.

























Definition tfib_A_tls_get_addr_thunk : Z := 0x41c74.  Definition tfib_E_tls_get_addr_thunk : Z := 0x41c78.














Definition tfib_A_icpt_strlen : Z := 0x41cac.  Definition tfib_E_icpt_strlen : Z := 0x41f40.
Definition tfib_A_icpt_strnlen : Z := 0x41f40.  Definition tfib_E_icpt_strnlen : Z := 0x421d4.
Definition tfib_A_icpt_strcmp : Z := 0x421d8.  Definition tfib_E_icpt_strcmp : Z := 0x42708.
Definition tfib_A_icpt_strchr : Z := 0x42ce4.  Definition tfib_E_icpt_strchr : Z := 0x42fc4.
Definition tfib_A_icpt_memcmp : Z := 0x4385c.  Definition tfib_E_icpt_memcmp : Z := 0x43918.

Definition tfib_A_icpt_memchr : Z := 0x43918.  Definition tfib_E_icpt_memchr : Z := 0x43be8.
Definition tfib_A_icpt_frexpl : Z := 0x43be8.  Definition tfib_E_icpt_frexpl : Z := 0x43e60.
Definition tfib_A_icpt_read : Z := 0x43e60.  Definition tfib_E_icpt_read : Z := 0x440d0.
Definition tfib_A_icpt_fwrite : Z := 0x440d0.  Definition tfib_E_icpt_fwrite : Z := 0x44344.
Definition tfib_A_icpt_time : Z := 0x44344.  Definition tfib_E_icpt_time : Z := 0x445e0.
Definition tfib_A_icpt_gmtime_r : Z := 0x447e8.  Definition tfib_E_icpt_gmtime_r : Z := 0x44a28.
Definition tfib_A_icpt_vprintf : Z := 0x44a28.  Definition tfib_E_icpt_vprintf : Z := 0x44ac4.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44ac4.  Definition tfib_E_printf_common_format_interceptor : Z := 0x4558c.
Definition tfib_A_icpt_vfprintf : Z := 0x4558c.  Definition tfib_E_icpt_vfprintf : Z := 0x45640.
Definition tfib_A_icpt_vsnprintf : Z := 0x45640.  Definition tfib_E_icpt_vsnprintf : Z := 0x45958.

Definition tfib_A_icpt_clock_gettime : Z := 0x45ad4.  Definition tfib_E_icpt_clock_gettime : Z := 0x45d2c.
Definition tfib_A_icpt_wcrtomb : Z := 0x45d2c.  Definition tfib_E_icpt_wcrtomb : Z := 0x4629c.
Definition tfib_A_icpt_wctomb : Z := 0x4629c.  Definition tfib_E_icpt_wctomb : Z := 0x465f8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x466c4.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46aac.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46ab8.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b34.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46d40.  Definition tfib_E_icpt_sem_timedwait : Z := 0x46fd8.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47008.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47230.
Definition tfib_A_icpt_send : Z := 0x47230.  Definition tfib_E_icpt_send : Z := 0x474e4.
Definition tfib_A_icpt_sendto : Z := 0x474e4.  Definition tfib_E_icpt_sendto : Z := 0x477a8.
Definition tfib_A_icpt_sigaltstack : Z := 0x477a8.  Definition tfib_E_icpt_sigaltstack : Z := 0x47a04.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b9c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47d4c.





Definition tfib_A_asan_memcpy : Z := 0x51d8c.  Definition tfib_E_asan_memcpy : Z := 0x52228.
Definition tfib_A_asan_memset : Z := 0x52228.  Definition tfib_E_asan_memset : Z := 0x52468.
Definition tfib_A_icpt_memset : Z := 0x52468.  Definition tfib_E_icpt_memset : Z := 0x52758.
Definition tfib_A_icpt_memcpy : Z := 0x52758.  Definition tfib_E_icpt_memcpy : Z := 0x52d48.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52d48.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52d80.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52d80.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52d84.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52d84.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52d88.

Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52e34.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52f70.


Definition tfib_A_free : Z := 0x530dc.  Definition tfib_E_free : Z := 0x530e0.
Definition tfib_A_malloc : Z := 0x530e0.  Definition tfib_E_malloc : Z := 0x530e4.
Definition tfib_A_icpt_free : Z := 0x530e4.  Definition tfib_E_icpt_free : Z := 0x532b4.
Definition tfib_A_icpt_malloc : Z := 0x532b4.  Definition tfib_E_icpt_malloc : Z := 0x53410.

Definition tfib_A_ReplaceSystemMalloc : Z := 0x534dc.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x534e0.


Definition tfib_A_SetCanPoisonMemory : Z := 0x53f5c.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53f6c.
Definition tfib_A_CanPoisonMemory : Z := 0x53f6c.  Definition tfib_E_CanPoisonMemory : Z := 0x53f80.
Definition tfib_A_PoisonShadow : Z := 0x53f80.  Definition tfib_E_PoisonShadow : Z := 0x5447c.
Definition tfib_A_MemToShadow_checked : Z := 0x5447c.  Definition tfib_E_MemToShadow_checked : Z := 0x545b8.


Definition tfib_A_asan_region_is_poisoned : Z := 0x54908.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54c4c.
Definition tfib_A_AsanTSDInit : Z := 0x5506c.  Definition tfib_E_AsanTSDInit : Z := 0x550e8.
Definition tfib_A_AsanTSDGet : Z := 0x550e8.  Definition tfib_E_AsanTSDGet : Z := 0x55128.
Definition tfib_A_AsanTSDSet : Z := 0x55128.  Definition tfib_E_AsanTSDSet : Z := 0x55168.
Definition tfib_A_PlatformTSDDtor : Z := 0x55168.  Definition tfib_E_PlatformTSDDtor : Z := 0x551ec.
Definition tfib_A_InstallAtForkHandler : Z := 0x551ec.  Definition tfib_E_InstallAtForkHandler : Z := 0x55208.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x55268.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x552ac.

Definition tfib_A_ReportDoubleFree : Z := 0x562d8.  Definition tfib_E_ReportDoubleFree : Z := 0x56568.
Definition tfib_A_ReportGenericError : Z := 0x57e44.  Definition tfib_E_ReportGenericError : Z := 0x58700.
Definition tfib_A_AsanInited : Z := 0x58e8c.  Definition tfib_E_AsanInited : Z := 0x58ea4.
Definition tfib_A_asan_report_load1 : Z := 0x58ea4.  Definition tfib_E_asan_report_load1 : Z := 0x58ef4.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58ef4.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58f44.
Definition tfib_A_asan_report_load2 : Z := 0x58f44.  Definition tfib_E_asan_report_load2 : Z := 0x58f94.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58f94.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58fe4.
Definition tfib_A_asan_report_load4 : Z := 0x58fe4.  Definition tfib_E_asan_report_load4 : Z := 0x59034.
Definition tfib_A_asan_report_exp_load4 : Z := 0x59034.  Definition tfib_E_asan_report_exp_load4 : Z := 0x59084.
Definition tfib_A_asan_report_load8 : Z := 0x59084.  Definition tfib_E_asan_report_load8 : Z := 0x590d4.
Definition tfib_A_asan_report_exp_load8 : Z := 0x590d4.  Definition tfib_E_asan_report_exp_load8 : Z := 0x59124.
Definition tfib_A_asan_report_load16 : Z := 0x59124.  Definition tfib_E_asan_report_load16 : Z := 0x59174.
Definition tfib_A_asan_report_exp_load16 : Z := 0x59174.  Definition tfib_E_asan_report_exp_load16 : Z := 0x591c4.
Definition tfib_A_asan_report_store1 : Z := 0x591c4.  Definition tfib_E_asan_report_store1 : Z := 0x59214.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59214.  Definition tfib_E_asan_report_exp_store1 : Z := 0x59264.
Definition tfib_A_asan_report_store2 : Z := 0x59264.  Definition tfib_E_asan_report_store2 : Z := 0x592b4.
Definition tfib_A_asan_report_exp_store2 : Z := 0x592b4.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59304.
Definition tfib_A_asan_report_store4 : Z := 0x59304.  Definition tfib_E_asan_report_store4 : Z := 0x59354.
Definition tfib_A_asan_report_exp_store4 : Z := 0x59354.  Definition tfib_E_asan_report_exp_store4 : Z := 0x593a4.
Definition tfib_A_asan_report_store8 : Z := 0x593a4.  Definition tfib_E_asan_report_store8 : Z := 0x593f4.
Definition tfib_A_asan_report_exp_store8 : Z := 0x593f4.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59444.
Definition tfib_A_asan_report_store16 : Z := 0x59444.  Definition tfib_E_asan_report_store16 : Z := 0x59494.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59494.  Definition tfib_E_asan_report_exp_store16 : Z := 0x594e4.
Definition tfib_A_asan_report_load_n : Z := 0x594e4.  Definition tfib_E_asan_report_load_n : Z := 0x59534.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59534.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59584.
Definition tfib_A_asan_report_store_n : Z := 0x59584.  Definition tfib_E_asan_report_store_n : Z := 0x595d4.
Definition tfib_A_asan_report_exp_store_n : Z := 0x595d4.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59624.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59624.  Definition tfib_E_InitializeHighMemEnd : Z := 0x596a4.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x596a4.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59a58.
Definition tfib_A_AsanInitInternal : Z := 0x59ae8.  Definition tfib_E_AsanInitInternal : Z := 0x59d9c.


Definition tfib_A_asan_init : Z := 0x5a008.  Definition tfib_E_asan_init : Z := 0x5a09c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a09c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a0a0.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a0a0.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a104.

Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a304.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a62c.

Definition tfib_A_InitializeShadowMemory : Z := 0x5a80c.  Definition tfib_E_InitializeShadowMemory : Z := 0x5ab14.
Definition tfib_A_SetMallocContextSize : Z := 0x5ab14.  Definition tfib_E_SetMallocContextSize : Z := 0x5ab24.
Definition tfib_A_GetMallocContextSize : Z := 0x5ab24.  Definition tfib_E_GetMallocContextSize : Z := 0x5ab34.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ab34.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5ac84.

Definition tfib_A_GetCurrentThreadStats : Z := 0x5b768.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b7a0.

Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ba54.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5bae0.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5bae0.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5bb48.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5bb48.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5bbc0.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5bbc0.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5bc28.


Definition tfib_A_AsanThread_Create : Z := 0x5c18c.  Definition tfib_E_AsanThread_Create : Z := 0x5c328.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c384.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c59c.
Definition tfib_A_GetCurrentThread : Z := 0x5c59c.  Definition tfib_E_GetCurrentThread : Z := 0x5c5bc.

Definition tfib_A_AsanThread_stack_top : Z := 0x5c760.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c7b8.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c7b8.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c810.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c810.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ca40.
Definition tfib_A_AsanThread_Init : Z := 0x5ca40.  Definition tfib_E_AsanThread_Init : Z := 0x5ce34.

Definition tfib_A_CreateMainThread : Z := 0x5cf74.  Definition tfib_E_CreateMainThread : Z := 0x5d084.
Definition tfib_A_SetCurrentThread : Z := 0x5d084.  Definition tfib_E_SetCurrentThread : Z := 0x5d164.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d368.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5d4a4.





Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5eab4.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5eb00.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5eb00.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5eb0c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5eb3c.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5eb48.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5eb48.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5eb54.

Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5eb70.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5ee3c.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ee3c.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f1fc.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x60158.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x60164.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x60164.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x6023c.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x6023c.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x602d8.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x607fc.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60840.

Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60ab8.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60bcc.
Definition tfib_A_RunMallocHooks : Z := 0x60d70.  Definition tfib_E_RunMallocHooks : Z := 0x60e28.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60e28.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60e2c.
Definition tfib_A_RunFreeHooks : Z := 0x60e2c.  Definition tfib_E_RunFreeHooks : Z := 0x60ed8.


Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60f0c.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60f58.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6121c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6145c.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61a58.  Definition tfib_E_sanitizer_set_report_path : Z := 0x61a70.




Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63680.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63990.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63990.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63ad4.
Definition tfib_A_FlagParser_ParseString : Z := 0x63ad4.  Definition tfib_E_FlagParser_ParseString : Z := 0x63bc8.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63d5c.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63dbc.

Definition tfib_A_internal_atoll : Z := 0x63dfc.  Definition tfib_E_internal_atoll : Z := 0x63ee8.
Definition tfib_A_internal_simple_strtoll : Z := 0x63ee8.  Definition tfib_E_internal_simple_strtoll : Z := 0x64044.
Definition tfib_A_internal_memchr : Z := 0x64044.  Definition tfib_E_internal_memchr : Z := 0x64064.
Definition tfib_A_internal_memcmp : Z := 0x64064.  Definition tfib_E_internal_memcmp : Z := 0x6409c.
Definition tfib_A_internal_memcpy : Z := 0x6409c.  Definition tfib_E_internal_memcpy : Z := 0x640c0.
Definition tfib_A_internal_memmove : Z := 0x640c0.  Definition tfib_E_internal_memmove : Z := 0x64118.
Definition tfib_A_internal_memset : Z := 0x64118.  Definition tfib_E_internal_memset : Z := 0x64178.
Definition tfib_A_internal_strcspn : Z := 0x64178.  Definition tfib_E_internal_strcspn : Z := 0x641cc.

Definition tfib_A_internal_strdup : Z := 0x64200.  Definition tfib_E_internal_strdup : Z := 0x6426c.
Definition tfib_A_internal_strlen : Z := 0x6426c.  Definition tfib_E_internal_strlen : Z := 0x64288.


Definition tfib_A_internal_strchrnul : Z := 0x64318.  Definition tfib_E_internal_strchrnul : Z := 0x64360.
Definition tfib_A_internal_strrchr : Z := 0x64360.  Definition tfib_E_internal_strrchr : Z := 0x643a0.
Definition tfib_A_internal_strnlen : Z := 0x644d0.  Definition tfib_E_internal_strnlen : Z := 0x64500.
Definition tfib_A_internal_strncpy : Z := 0x64544.  Definition tfib_E_internal_strncpy : Z := 0x645b4.
Definition tfib_A_internal_strstr : Z := 0x645b4.  Definition tfib_E_internal_strstr : Z := 0x64648.
Definition tfib_A_mem_is_zero : Z := 0x64648.  Definition tfib_E_mem_is_zero : Z := 0x646fc.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x646fc.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x6470c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x6470c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x648ec.
Definition tfib_A_internal_iserror : Z := 0x648f8.  Definition tfib_E_internal_iserror : Z := 0x64918.
Definition tfib_A_internal_mmap : Z := 0x64918.  Definition tfib_E_internal_mmap : Z := 0x64924.
Definition tfib_A_internal_munmap : Z := 0x64924.  Definition tfib_E_internal_munmap : Z := 0x64930.
Definition tfib_A_internal_mprotect : Z := 0x64930.  Definition tfib_E_internal_mprotect : Z := 0x64940.
Definition tfib_A_internal_madvise : Z := 0x64940.  Definition tfib_E_internal_madvise : Z := 0x6496c.
Definition tfib_A_internal_close : Z := 0x6496c.  Definition tfib_E_internal_close : Z := 0x64978.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64978.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x6499c.
Definition tfib_A_internal_read : Z := 0x6499c.  Definition tfib_E_internal_read : Z := 0x649d4.
Definition tfib_A_internal_write : Z := 0x649d4.  Definition tfib_E_internal_write : Z := 0x64a0c.
Definition tfib_A_internal_ftruncate : Z := 0x64a0c.  Definition tfib_E_internal_ftruncate : Z := 0x64a44.
Definition tfib_A_internal_dup : Z := 0x64a44.  Definition tfib_E_internal_dup : Z := 0x64a50.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64a50.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64a60.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64a60.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x64a78.
Definition tfib_A_internal_sched_yield : Z := 0x64a78.  Definition tfib_E_internal_sched_yield : Z := 0x64a84.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x64a84.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64ad0.
Definition tfib_A_internal_execve : Z := 0x64ad0.  Definition tfib_E_internal_execve : Z := 0x64adc.
Definition tfib_A_internal_exit_exit_group : Z := 0x64adc.  Definition tfib_E_internal_exit_exit_group : Z := 0x64af0.
Definition tfib_A_FileExists_newfstatat : Z := 0x64af0.  Definition tfib_E_FileExists_newfstatat : Z := 0x64b70.
Definition tfib_A_DirExists_newfstatat : Z := 0x64b70.  Definition tfib_E_DirExists_newfstatat : Z := 0x64bd4.
Definition tfib_A_GetTid_gettid : Z := 0x64bd4.  Definition tfib_E_GetTid_gettid : Z := 0x64be0.
Definition tfib_A_GetEnv : Z := 0x64be0.  Definition tfib_E_GetEnv : Z := 0x64d10.
Definition tfib_A_FutexWait : Z := 0x64e14.  Definition tfib_E_FutexWait : Z := 0x64e38.
Definition tfib_A_FutexWake : Z := 0x64e38.  Definition tfib_E_FutexWake : Z := 0x64e5c.
Definition tfib_A_internal_ptrace : Z := 0x64e5c.  Definition tfib_E_internal_ptrace : Z := 0x64e68.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64e68.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64e78.
Definition tfib_A_internal_getpid : Z := 0x64e78.  Definition tfib_E_internal_getpid : Z := 0x64e84.
Definition tfib_A_internal_getppid : Z := 0x64e84.  Definition tfib_E_internal_getppid : Z := 0x64e90.
Definition tfib_A_internal_prctl : Z := 0x64e90.  Definition tfib_E_internal_prctl : Z := 0x64e9c.
Definition tfib_A_internal_sigaltstack : Z := 0x64e9c.  Definition tfib_E_internal_sigaltstack : Z := 0x64ea8.
Definition tfib_A_internal_fork_clone : Z := 0x64ea8.  Definition tfib_E_internal_fork_clone : Z := 0x64ec0.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x64ec0.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64fec.

Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x6572c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65844.

Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6584c.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x658f8.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x658f8.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x65a18.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65ae0.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65b60.

Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65bbc.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65c88.

Definition tfib_A_CheckASLR : Z := 0x65d88.  Definition tfib_E_CheckASLR : Z := 0x65d8c.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65fd8.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65fdc.

Definition tfib_A_MmapOrDie : Z := 0x65fe8.  Definition tfib_E_MmapOrDie : Z := 0x660f4.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x660f4.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x66168.
Definition tfib_A_UnmapOrDie : Z := 0x66168.  Definition tfib_E_UnmapOrDie : Z := 0x661e4.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x661e4.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x662f4.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x66520.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66624.

Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66630.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x667a8.


Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x66cc4.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66ed0.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67488.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67494.
Definition tfib_A_Printf : Z := 0x67498.  Definition tfib_E_Printf : Z := 0x674e4.
Definition tfib_A_SharedPrintfCode : Z := 0x674e4.  Definition tfib_E_SharedPrintfCode : Z := 0x67540.
Definition tfib_A_Report : Z := 0x67540.  Definition tfib_E_Report : Z := 0x6758c.
Definition tfib_A_SuppressionContext_ctor : Z := 0x69084.  Definition tfib_E_SuppressionContext_ctor : Z := 0x690e0.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x690e0.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6931c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6931c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69640.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69be0.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69cb0.




Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a2f0.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a768.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b028.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b34c.

Definition tfib_A_AddDieCallback : Z := 0x6bc08.  Definition tfib_E_AddDieCallback : Z := 0x6bc90.
Definition tfib_A_Die : Z := 0x6bd54.  Definition tfib_E_Die : Z := 0x6be14.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6be14.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6be20.
Definition tfib_A_CheckFailed : Z := 0x6be20.  Definition tfib_E_CheckFailed : Z := 0x6bed8.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c530.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c628.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c628.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c754.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c97c.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c9f8.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6ca2c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6cd14.



Definition tfib_A_AndroidLogInit : Z := 0x6d5bc.  Definition tfib_E_AndroidLogInit : Z := 0x6d5c0.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d5f0.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d638.



Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d994.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6da98.


Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6dddc.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6de7c.

Definition tfib_A_SetAlternateSignalStack : Z := 0x6df08.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6dfcc.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6dfcc.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e054.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e054.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e0cc.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e0cc.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e1b0.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e26c.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e3a0.


Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e768.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e834.





Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70664.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70788.
Definition tfib_A_StackStore_Alloc : Z := 0x70788.  Definition tfib_E_StackStore_Alloc : Z := 0x708bc.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x71170.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x71224.

Definition tfib_A_StackDepotPut : Z := 0x72c60.  Definition tfib_E_StackDepotPut : Z := 0x72c80.
Definition tfib_A_StackDepotBase_Put : Z := 0x72c80.  Definition tfib_E_StackDepotBase_Put : Z := 0x72f04.
Definition tfib_A_StackDepotBase_Get : Z := 0x72f04.  Definition tfib_E_StackDepotBase_Get : Z := 0x73014.


Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x735e4.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x735ec.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x735ec.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x7374c.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x7374c.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x737c0.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73c48.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73d60.


Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79fb0.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a06c.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a06c.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a144.

Definition tfib_A_lsan_flags_init_helper : Z := 0x7a6e4.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7a728.

Definition tfib_A_lsan_InitCommonLsan : Z := 0x7adc8.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7ae80.

Definition tfib_A_lsan_register_root_region : Z := 0x7cde4.  Definition tfib_E_lsan_register_root_region : Z := 0x7d114.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d114.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d59c.


Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x804fc.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80578.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80578.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80628.

Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80640.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80788.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80788.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80794.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80794.  Definition tfib_E_asan_default_options_cli_c : Z := 0x807a0.
Definition tfib_A_main : Z := 0x807a0.  Definition tfib_E_main : Z := 0x80a64.
Definition tfib_A_target_alloc_init : Z := 0x80a64.  Definition tfib_E_target_alloc_init : Z := 0x80a68.
Definition tfib_A_target_alloc_count : Z := 0x80a68.  Definition tfib_E_target_alloc_count : Z := 0x80a70.

Definition tfib_A_emit_printf : Z := 0x80bf8.  Definition tfib_E_emit_printf : Z := 0x80c40.


Definition tfib_A_asan_module_ctor : Z := 0x8493c.  Definition tfib_E_asan_module_ctor : Z := 0x84974.








Definition tfib_A_asan_module_dtor : Z := 0x84974.  Definition tfib_E_asan_module_dtor : Z := 0x849a4.






Definition tfib_A_extenddftf2 : Z := 0x85530.  Definition tfib_E_extenddftf2 : Z := 0x856c0.
Definition tfib_A_sysconf : Z := 0x8bda8.  Definition tfib_E_sysconf : Z := 0x8bfd0.
Definition tfib_A_init : Z := 0x8bfd0.  Definition tfib_E_init : Z := 0x8bfd4.
Definition tfib_A_init_libc : Z := 0x8bfd4.  Definition tfib_E_init_libc : Z := 0x8c200.
Definition tfib_A_libc_start_init : Z := 0x8c200.  Definition tfib_E_libc_start_init : Z := 0x8c24c.
Definition tfib_A_libc_start_main : Z := 0x8c24c.  Definition tfib_E_libc_start_main : Z := 0x8c2ac.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8c2ac.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8c2f4.
Definition tfib_A_init_tls : Z := 0x8c3cc.  Definition tfib_E_init_tls : Z := 0x8c67c.
Definition tfib_A_init_ssp : Z := 0x8c67c.  Definition tfib_E_init_ssp : Z := 0x8c6dc.
Definition tfib_A_stack_chk_fail : Z := 0x8c6dc.  Definition tfib_E_stack_chk_fail : Z := 0x8c6e4.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c72c.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8c7c0.
Definition tfib_A_Exit : Z := 0x8c7c0.  Definition tfib_E_Exit : Z := 0x8c7dc.
Definition tfib_A_funcs_on_exit : Z := 0x8c80c.  Definition tfib_E_funcs_on_exit : Z := 0x8c8d4.

Definition tfib_A_cxa_atexit_atexit : Z := 0x8c8d8.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8c99c.

Definition tfib_A_musl_exit_helper_stub : Z := 0x8c9a0.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8c9a4.
Definition tfib_A_libc_exit_fini : Z := 0x8c9a4.  Definition tfib_E_libc_exit_fini : Z := 0x8c9f0.
Definition tfib_A_exit : Z := 0x8c9f0.  Definition tfib_E_exit : Z := 0x8ca64.
Definition tfib_A_open : Z := 0x8cc64.  Definition tfib_E_open : Z := 0x8cd48.
Definition tfib_A_syscall_ret : Z := 0x8cd48.  Definition tfib_E_syscall_ret : Z := 0x8cd80.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8cd80.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8cf28.
Definition tfib_A_calloc : Z := 0x8d4ec.  Definition tfib_E_calloc : Z := 0x8d624.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8d624.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8d628.
Definition tfib_A_libc_free : Z := 0x8d628.  Definition tfib_E_libc_free : Z := 0x8d7f4.
Definition tfib_A_get_meta : Z := 0x8d7f4.  Definition tfib_E_get_meta : Z := 0x8d904.
Definition tfib_A_alloc_meta : Z := 0x8dcdc.  Definition tfib_E_alloc_meta : Z := 0x8dfb4.
Definition tfib_A_libc_malloc_impl : Z := 0x8dfb4.  Definition tfib_E_libc_malloc_impl : Z := 0x8e324.
Definition tfib_A_alloc_slot : Z := 0x8e324.  Definition tfib_E_alloc_slot : Z := 0x8ebc8.
Definition tfib_A_enframe : Z := 0x8ebc8.  Definition tfib_E_enframe : Z := 0x8ed18.
Definition tfib_A_malloc_allzerop : Z := 0x8ed18.  Definition tfib_E_malloc_allzerop : Z := 0x8ee90.
Definition tfib_A_getrlimit : Z := 0x90260.  Definition tfib_E_getrlimit : Z := 0x90358.
Definition tfib_A_getrusage : Z := 0x90358.  Definition tfib_E_getrusage : Z := 0x90380.
Definition tfib_A_setrlimit : Z := 0x90380.  Definition tfib_E_setrlimit : Z := 0x90448.
Definition tfib_A_mmap : Z := 0x90870.  Definition tfib_E_mmap : Z := 0x9095c.
Definition tfib_A_mprotect : Z := 0x9095c.  Definition tfib_E_mprotect : Z := 0x909a4.
Definition tfib_A_munmap : Z := 0x90a78.  Definition tfib_E_munmap : Z := 0x90ac0.
Definition tfib_A_sched_yield : Z := 0x90d84.  Definition tfib_E_sched_yield : Z := 0x90da8.
Definition tfib_A_raise_tkill_path : Z := 0x90e04.  Definition tfib_E_raise_tkill_path : Z := 0x90e7c.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x90e7c.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x91050.
Definition tfib_A_musl_sigaltstack : Z := 0x91148.  Definition tfib_E_musl_sigaltstack : Z := 0x911d4.


Definition tfib_A_lockfile : Z := 0x91814.  Definition tfib_E_lockfile : Z := 0x91910.
Definition tfib_A_unlockfile : Z := 0x91910.  Definition tfib_E_unlockfile : Z := 0x91970.



Definition tfib_A_stdio_read : Z := 0x91500.  Definition tfib_E_stdio_read : Z := 0x91618.
Definition tfib_A_stdio_write : Z := 0x91620.  Definition tfib_E_stdio_write : Z := 0x917b0.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x914d0.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x914d4.
Definition tfib_A_stdio_close : Z := 0x914d4.  Definition tfib_E_stdio_close : Z := 0x91500.
Definition tfib_A_fwritex : Z := 0x91da4.  Definition tfib_E_fwritex : Z := 0x91edc.
Definition tfib_A_musl_fwrite : Z := 0x91edc.  Definition tfib_E_musl_fwrite : Z := 0x91f94.
Definition tfib_A_towrite : Z := 0x91f94.  Definition tfib_E_towrite : Z := 0x91fe8.
Definition tfib_A_stdio_exit : Z := 0x91c00.  Definition tfib_E_stdio_exit : Z := 0x91da4.
Definition tfib_A_ofl_lock : Z := 0x91fe8.  Definition tfib_E_ofl_lock : Z := 0x92018.

Definition tfib_A_musl_vfprintf : Z := 0x92164.  Definition tfib_E_musl_vfprintf : Z := 0x92314.
Definition tfib_A_printf_core : Z := 0x92314.  Definition tfib_E_printf_core : Z := 0x93144.
Definition tfib_A_pop_arg : Z := 0x93144.  Definition tfib_E_pop_arg : Z := 0x93278.
Definition tfib_A_pad : Z := 0x93278.  Definition tfib_E_pad : Z := 0x9334c.
Definition tfib_A_fmt_fp : Z := 0x9334c.  Definition tfib_E_fmt_fp : Z := 0x94a14.

Definition tfib_A_musl_wctomb : Z := 0x90bec.  Definition tfib_E_musl_wctomb : Z := 0x90c10.
Definition tfib_A_musl_wcrtomb : Z := 0x90ac0.  Definition tfib_E_musl_wcrtomb : Z := 0x90bec.
Definition tfib_A_fpclassifyl : Z := 0x8f668.  Definition tfib_E_fpclassifyl : Z := 0x8f6ac.
Definition tfib_A_letf2 : Z := 0x853ac.  Definition tfib_E_letf2 : Z := 0x85474.
Definition tfib_A_multf3 : Z := 0x8ef68.  Definition tfib_E_multf3 : Z := 0x8f668.
Definition tfib_A_floatsitf : Z := 0x8f6ac.  Definition tfib_E_floatsitf : Z := 0x8f7b4.
Definition tfib_A_scalbn : Z := 0x900b8.  Definition tfib_E_scalbn : Z := 0x90150.
Definition tfib_A_subtf3 : Z := 0x85940.  Definition tfib_E_subtf3 : Z := 0x85950.
Definition tfib_A_addtf3 : Z := 0x85950.  Definition tfib_E_addtf3 : Z := 0x8611c.
Definition tfib_A_fe_getround : Z := 0x8611c.  Definition tfib_E_fe_getround : Z := 0x8614c.
Definition tfib_A_fixunstfsi : Z := 0x94a1c.  Definition tfib_E_fixunstfsi : Z := 0x94ab0.
Definition tfib_A_floatunsitf : Z := 0x94ab0.  Definition tfib_E_floatunsitf : Z := 0x94b9c.
Definition tfib_A_fixtfsi : Z := 0x90150.  Definition tfib_E_fixtfsi : Z := 0x901f8.
Definition tfib_A_divtf3 : Z := 0x8f7b4.  Definition tfib_E_divtf3 : Z := 0x900b8.
Definition tfib_A_musl_vprintf : Z := 0x95274.  Definition tfib_E_musl_vprintf : Z := 0x95290.
Definition tfib_A_stdout_write : Z := 0x92024.  Definition tfib_E_stdout_write : Z := 0x920c4.

Definition tfib_A_musl_memcmp : Z := 0x958f4.  Definition tfib_E_musl_memcmp : Z := 0x95924.
Definition tfib_A_musl_memcpy : Z := 0x95924.  Definition tfib_E_musl_memcpy : Z := 0x95d28.
Definition tfib_A_musl_memset : Z := 0x95d28.  Definition tfib_E_musl_memset : Z := 0x95e20.
Definition tfib_A_musl_strchr : Z := 0x95e20.  Definition tfib_E_musl_strchr : Z := 0x95e5c.
Definition tfib_A_strchrnul : Z := 0x95e5c.  Definition tfib_E_strchrnul : Z := 0x95f3c.
Definition tfib_A_musl_strlen : Z := 0x95f74.  Definition tfib_E_musl_strlen : Z := 0x96004.
Definition tfib_A_musl_strnlen : Z := 0x96210.  Definition tfib_E_musl_strnlen : Z := 0x96254.
Definition tfib_A_musl_memchr : Z := 0x95828.  Definition tfib_E_musl_memchr : Z := 0x958f4.
Definition tfib_A_lock : Z := 0x96254.  Definition tfib_E_lock : Z := 0x964dc.
Definition tfib_A_unlock : Z := 0x964dc.  Definition tfib_E_unlock : Z := 0x96550.
Definition tfib_A_syscall_cp_c : Z := 0x96550.  Definition tfib_E_syscall_cp_c : Z := 0x96574.
Definition tfib_A_syscall_cp_sccp : Z := 0x96574.  Definition tfib_E_syscall_cp_sccp : Z := 0x96578.

Definition tfib_A_pthread_atfork : Z := 0x965b4.  Definition tfib_E_pthread_atfork : Z := 0x96658.
Definition tfib_A_mremap : Z := 0x909a4.  Definition tfib_E_mremap : Z := 0x90a78.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9762c.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x97648.
Definition tfib_A_pthread_key_create : Z := 0x979d4.  Definition tfib_E_pthread_key_create : Z := 0x97aa8.



Definition tfib_A_pthread_setspecific : Z := 0x97f70.  Definition tfib_E_pthread_setspecific : Z := 0x97fa4.
Definition tfib_A_set_thread_area : Z := 0x97fac.  Definition tfib_E_set_thread_area : Z := 0x97fb8.

Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x988d8.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x98990.
Definition tfib_A_close : Z := 0x9afa8.  Definition tfib_E_close : Z := 0x9affc.
Definition tfib_A_musl_read : Z := 0x9b088.  Definition tfib_E_musl_read : Z := 0x9b0bc.
Definition tfib_A_vm_wait : Z := 0x985e8.  Definition tfib_E_vm_wait : Z := 0x98638.
Definition tfib_D_str_sealed : Z := 0x11877.
Definition tfib_D_init_array_0_3 : Z := 0x9c0c0.
Definition tfib_D_fini_array_0_1 : Z := 0x9c0e0.
Definition tfib_D_GOT_common_flags : Z := 0x9c7e0.
Definition tfib_D_GOT_flags : Z := 0x9c7e8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c7f0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c7f8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c800.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c808.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9d358.
Definition tfib_D_environ_musl : Z := 0x9d480.
Definition tfib_D_REAL_read : Z := 0x9e528.
Definition tfib_D_REAL_memcpy : Z := 0x9e650.
Definition tfib_D_REAL_memset : Z := 0x9e658.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa1bd8.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa2a38.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa5238.
Definition tfib_D_asan_inited : Z := 0xa5f18.
Definition tfib_D_replace_intrin_cached : Z := 0xa5f19.
Definition tfib_D_kHighMemEnd : Z := 0xa5f20.
Definition tfib_D_kMidMemBeg : Z := 0xa5f28.
Definition tfib_D_kMidMemEnd : Z := 0xa5f30.
Definition tfib_D_malloc_context_size : Z := 0xa5f3c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136d68.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f8460.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30764.
Definition tfib_at_rw_lo : Z := 0x9e000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x64118.
Definition tfib_at_x_imemcpy : Z := 0x6409c.
Definition tfib_at_x_memset : Z := 0x95d28.
Definition tfib_at_x_memcpy : Z := 0x95924.
Definition tfib_at_x_memiszero : Z := 0x64648.
Definition tfib_at_x_istrncpy : Z := 0x64544.
Definition tfib_at_x_sealed : Z := 0x11877.
Definition tfib_at_x_popfree : Z := 0x36b50.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8c00c.
Definition tfib_at_x_envscan_k : Z := 0x8c018.
Definition tfib_at_x_pnscan : Z := 0x8c0d0.
Definition tfib_at_x_pnscan_k : Z := 0x8c0dc.
Definition tfib_at_stops_more : list Z := (0x347c4 :: 0x35de8 :: 0x54424 :: 0x5a7dc :: 0x5a7f0 :: 0x5a804 :: 0x60194 :: 0x60264 :: 0x6d790 :: 0x6e69c :: 0x6e82c :: 0x78584 :: nil)%list.
