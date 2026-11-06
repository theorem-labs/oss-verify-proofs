(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AB1w.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22b4c.
Definition tfib_text_lo : Z := 0x310d0.  Definition tfib_text_hi : Z := 0xa2948.
Definition tfib_init_array_lo : Z := 0xa3948.  Definition tfib_init_array_hi : Z := 0xa3968.
Definition tfib_fini_array_lo : Z := 0xa3968.  Definition tfib_fini_array_hi : Z := 0xa3978.
Definition tfib_preinit_array_lo : Z := 0xa3978.  Definition tfib_preinit_array_hi : Z := 0xa3980.
Definition tfib_data_rel_ro_lo : Z := 0xa3980.  Definition tfib_data_rel_ro_hi : Z := 0xa4030.
Definition tfib_got_lo : Z := 0xa4030.  Definition tfib_got_hi : Z := 0xa4d88.
Definition tfib_data_lo : Z := 0xa5d88.  Definition tfib_data_hi : Z := 0xa8940.
Definition tfib_asan_globals_lo : Z := 0xa8940.  Definition tfib_asan_globals_hi : Z := 0xa9340.
Definition tfib_bss_lo : Z := 0xa9340.  Definition tfib_bss_hi : Z := 0x6153d0.
Definition tfib_tbss_lo : Z := 0xa2948.  Definition tfib_tbss_hi : Z := 0xa295c.
Definition tfib_img_lo : Z := ltac:(let v := eval vm_compute in IMG_LO in exact v).  Definition tfib_img_hi : Z := ltac:(let v := eval vm_compute in IMG_TOP in exact v).
Definition tfib_entry : Z := 0x310d0.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x310d0.  Definition tfib_E_start : Z := 0x31118.
Definition tfib_A_do_init : Z := 0x31118.  Definition tfib_E_do_init : Z := 0x3118c.
Definition tfib_A_do_fini : Z := 0x3118c.  Definition tfib_E_do_fini : Z := 0x3121c.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x3121c.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x31258.
Definition tfib_A_InitializeAllocator : Z := 0x313c8.  Definition tfib_E_InitializeAllocator : Z := 0x313e0.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x313e0.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x3154c.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31aa8.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31c04.
Definition tfib_A_asan_free : Z := 0x31fd8.  Definition tfib_E_asan_free : Z := 0x32000.
Definition tfib_A_Allocator_Deallocate : Z := 0x32000.  Definition tfib_E_Allocator_Deallocate : Z := 0x322b8.
Definition tfib_A_asan_malloc : Z := 0x322b8.  Definition tfib_E_asan_malloc : Z := 0x32314.
Definition tfib_A_Allocator_Allocate : Z := 0x32314.  Definition tfib_E_Allocator_Allocate : Z := 0x32c9c.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x33604.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x33660.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x33660.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x338b0.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x338b0.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x339a4.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x34360.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x345e4.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x345e4.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34764.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34764.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3492c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x3492c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34af8.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34b98.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34c9c.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34fc4.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x3510c.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x358dc.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35bc4.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x3629c.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36414.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36414.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x365c4.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x365c4.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x367a8.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x367a8.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36a80.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36a80.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36ef8.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36ef8.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36ff8.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36ff8.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x37300.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x37300.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x37670.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37b8c.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37c74.
Definition tfib_A_AsanActivate : Z := 0x37c74.  Definition tfib_E_AsanActivate : Z := 0x37d50.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x3822c.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x38314.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3cdcc.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3cea4.
Definition tfib_A_FakeStack_Create : Z := 0x3cea4.  Definition tfib_E_FakeStack_Create : Z := 0x3cf90.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d668.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d698.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d698.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d80c.  Definition tfib_A_asan_stack_malloc_5 : Z := 0x3dd04.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x3df10.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d80c.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d99c.
Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d99c.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3db38.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3db38.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3dd04.
Definition tfib_A_asan_InitializeFlags : Z := 0x3e100.  Definition tfib_E_asan_InitializeFlags : Z := 0x3f12c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f838.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40654.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x40654.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40c20.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x41374.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x415e4.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x415e4.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x418ec.
Definition tfib_A_strlen : Z := 0x42ce4.  Definition tfib_E_strlen : Z := 0x42ce8.
Definition tfib_A_strnlen : Z := 0x42ce8.  Definition tfib_E_strnlen : Z := 0x42cec.
Definition tfib_A_strcmp : Z := 0x42cec.  Definition tfib_E_strcmp : Z := 0x42cf0.
Definition tfib_A_strchr : Z := 0x42cf0.  Definition tfib_E_strchr : Z := 0x42cf4.
Definition tfib_A_memcmp : Z := 0x42cf4.  Definition tfib_E_memcmp : Z := 0x42cf8.
Definition tfib_A_memchr : Z := 0x42cfc.  Definition tfib_E_memchr : Z := 0x42d00.
Definition tfib_A_frexpl : Z := 0x42d00.  Definition tfib_E_frexpl : Z := 0x42d04.
Definition tfib_A_read : Z := 0x42d04.  Definition tfib_E_read : Z := 0x42d08.
Definition tfib_A_fwrite : Z := 0x42d08.  Definition tfib_E_fwrite : Z := 0x42d0c.
Definition tfib_A_time : Z := 0x42d0c.  Definition tfib_E_time : Z := 0x42d10.
Definition tfib_A_gmtime_r : Z := 0x42d10.  Definition tfib_E_gmtime_r : Z := 0x42d14.
Definition tfib_A_vprintf : Z := 0x42d14.  Definition tfib_E_vprintf : Z := 0x42d18.
Definition tfib_A_vfprintf : Z := 0x42d18.  Definition tfib_E_vfprintf : Z := 0x42d1c.
Definition tfib_A_vsnprintf : Z := 0x42d1c.  Definition tfib_E_vsnprintf : Z := 0x42d20.
Definition tfib_A_thunk_417bc : Z := 0x42d24.  Definition tfib_E_thunk_417bc : Z := 0x42d28.
Definition tfib_A_clock_gettime : Z := 0x42d28.  Definition tfib_E_clock_gettime : Z := 0x42d2c.
Definition tfib_A_wcrtomb : Z := 0x42d2c.  Definition tfib_E_wcrtomb : Z := 0x42d30.
Definition tfib_A_wctomb : Z := 0x42d30.  Definition tfib_E_wctomb : Z := 0x42d34.
Definition tfib_A_thunk_417cc : Z := 0x42d34.  Definition tfib_E_thunk_417cc : Z := 0x42d3c.
Definition tfib_A_pthread_attr_getstack : Z := 0x42d3c.  Definition tfib_E_pthread_attr_getstack : Z := 0x42d40.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42d40.  Definition tfib_E_tls_get_addr_thunk : Z := 0x42d44.
Definition tfib_A_thunk_417dc : Z := 0x42d44.  Definition tfib_E_thunk_417dc : Z := 0x42d48.
Definition tfib_A_thunk_417e4 : Z := 0x42d48.  Definition tfib_E_thunk_417e4 : Z := 0x42d4c.
Definition tfib_A_thunk_417e8 : Z := 0x42d4c.  Definition tfib_E_thunk_417e8 : Z := 0x42d50.
Definition tfib_A_thunk_417ec : Z := 0x42d50.  Definition tfib_E_thunk_417ec : Z := 0x42d54.
Definition tfib_A_thunk_417f0 : Z := 0x42d54.  Definition tfib_E_thunk_417f0 : Z := 0x42d58.
Definition tfib_A_sem_timedwait : Z := 0x42d58.  Definition tfib_E_sem_timedwait : Z := 0x42d5c.
Definition tfib_A_thunk_417f8 : Z := 0x42d5c.  Definition tfib_E_thunk_417f8 : Z := 0x42d60.
Definition tfib_A_pthread_setcancelstate : Z := 0x42d60.  Definition tfib_E_pthread_setcancelstate : Z := 0x42d64.
Definition tfib_A_send : Z := 0x42d64.  Definition tfib_E_send : Z := 0x42d68.
Definition tfib_A_sendto : Z := 0x42d68.  Definition tfib_E_sendto : Z := 0x42d6c.
Definition tfib_A_sigaltstack : Z := 0x42d6c.  Definition tfib_E_sigaltstack : Z := 0x42d70.
Definition tfib_A_thunk_4180c : Z := 0x42d70.  Definition tfib_E_thunk_4180c : Z := 0x42d74.
Definition tfib_A_icpt_strlen : Z := 0x42d74.  Definition tfib_E_icpt_strlen : Z := 0x43008.
Definition tfib_A_icpt_strnlen : Z := 0x43008.  Definition tfib_E_icpt_strnlen : Z := 0x4329c.
Definition tfib_A_icpt_strcmp : Z := 0x432a0.  Definition tfib_E_icpt_strcmp : Z := 0x437d0.
Definition tfib_A_icpt_strchr : Z := 0x437d0.  Definition tfib_E_icpt_strchr : Z := 0x43ab0.
Definition tfib_A_icpt_memcmp : Z := 0x44348.  Definition tfib_E_icpt_memcmp : Z := 0x44404.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x44404.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x444c0.
Definition tfib_A_icpt_memchr : Z := 0x444c0.  Definition tfib_E_icpt_memchr : Z := 0x44790.
Definition tfib_A_icpt_frexpl : Z := 0x44790.  Definition tfib_E_icpt_frexpl : Z := 0x44a08.
Definition tfib_A_icpt_read : Z := 0x44a08.  Definition tfib_E_icpt_read : Z := 0x44c78.
Definition tfib_A_icpt_fwrite : Z := 0x44c78.  Definition tfib_E_icpt_fwrite : Z := 0x44eec.
Definition tfib_A_icpt_time : Z := 0x44eec.  Definition tfib_E_icpt_time : Z := 0x45188.
Definition tfib_A_icpt_gmtime_r : Z := 0x45390.  Definition tfib_E_icpt_gmtime_r : Z := 0x455d0.
Definition tfib_A_icpt_vprintf : Z := 0x455d0.  Definition tfib_E_icpt_vprintf : Z := 0x4566c.
Definition tfib_A_printf_common_format_interceptor : Z := 0x4566c.  Definition tfib_E_printf_common_format_interceptor : Z := 0x46134.
Definition tfib_A_icpt_vfprintf : Z := 0x46134.  Definition tfib_E_icpt_vfprintf : Z := 0x461e8.
Definition tfib_A_icpt_vsnprintf : Z := 0x461e8.  Definition tfib_E_icpt_vsnprintf : Z := 0x46500.
Definition tfib_A_icpt_clock_gettime : Z := 0x4667c.  Definition tfib_E_icpt_clock_gettime : Z := 0x468d4.
Definition tfib_A_icpt_wcrtomb : Z := 0x468d4.  Definition tfib_E_icpt_wcrtomb : Z := 0x46e44.
Definition tfib_A_icpt_wctomb : Z := 0x46e44.  Definition tfib_E_icpt_wctomb : Z := 0x471a0.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x4726c.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x47654.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x47660.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x476dc.
Definition tfib_A_icpt_sem_timedwait : Z := 0x478e8.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47b80.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47bb0.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47dd8.
Definition tfib_A_icpt_send : Z := 0x47dd8.  Definition tfib_E_icpt_send : Z := 0x4808c.
Definition tfib_A_icpt_sendto : Z := 0x4808c.  Definition tfib_E_icpt_sendto : Z := 0x48350.
Definition tfib_A_icpt_sigaltstack : Z := 0x48350.  Definition tfib_E_icpt_sigaltstack : Z := 0x485ac.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x48680.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x48830.
Definition tfib_A_icpt_diouxXn : Z := 0x48830.  Definition tfib_E_icpt_diouxXn : Z := 0x489c8.
Definition tfib_A_memset : Z := 0x523a8.  Definition tfib_E_memset : Z := 0x523ac.
Definition tfib_A_memcpy : Z := 0x523ac.  Definition tfib_E_memcpy : Z := 0x523b0.
Definition tfib_A_asan_memcpy : Z := 0x523b0.  Definition tfib_E_asan_memcpy : Z := 0x5284c.
Definition tfib_A_asan_memset : Z := 0x5284c.  Definition tfib_E_asan_memset : Z := 0x52a8c.
Definition tfib_A_icpt_memset : Z := 0x52a8c.  Definition tfib_E_icpt_memset : Z := 0x52d7c.
Definition tfib_A_icpt_memcpy : Z := 0x52d7c.  Definition tfib_E_icpt_memcpy : Z := 0x5336c.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5336c.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x533a4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x533a4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x533a8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x533a8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x533ac.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x533ac.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5340c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53458.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53594.
Definition tfib_A_free : Z := 0x53700.  Definition tfib_E_free : Z := 0x53704.
Definition tfib_A_malloc : Z := 0x53704.  Definition tfib_E_malloc : Z := 0x53708.
Definition tfib_A_icpt_free : Z := 0x53708.  Definition tfib_E_icpt_free : Z := 0x538d8.
Definition tfib_A_icpt_malloc : Z := 0x538d8.  Definition tfib_E_icpt_malloc : Z := 0x53a34.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53b00.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x53b04.
Definition tfib_A_SetCanPoisonMemory : Z := 0x54580.  Definition tfib_E_SetCanPoisonMemory : Z := 0x54590.
Definition tfib_A_CanPoisonMemory : Z := 0x54590.  Definition tfib_E_CanPoisonMemory : Z := 0x545a4.
Definition tfib_A_PoisonShadow : Z := 0x545a4.  Definition tfib_E_PoisonShadow : Z := 0x54aa0.
Definition tfib_A_MemToShadow_checked : Z := 0x54aa0.  Definition tfib_E_MemToShadow_checked : Z := 0x54bdc.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54f2c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x55270.
Definition tfib_A_AsanTSDInit : Z := 0x55690.  Definition tfib_E_AsanTSDInit : Z := 0x5570c.
Definition tfib_A_AsanTSDGet : Z := 0x5570c.  Definition tfib_E_AsanTSDGet : Z := 0x5574c.
Definition tfib_A_AsanTSDSet : Z := 0x5574c.  Definition tfib_E_AsanTSDSet : Z := 0x5578c.
Definition tfib_A_PlatformTSDDtor : Z := 0x5578c.  Definition tfib_E_PlatformTSDDtor : Z := 0x55810.
Definition tfib_A_InstallAtForkHandler : Z := 0x55810.  Definition tfib_E_InstallAtForkHandler : Z := 0x5582c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x5588c.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x558d0.
Definition tfib_A_ReportDoubleFree : Z := 0x568fc.  Definition tfib_E_ReportDoubleFree : Z := 0x56b8c.
Definition tfib_A_ReportGenericError : Z := 0x58468.  Definition tfib_E_ReportGenericError : Z := 0x58d24.
Definition tfib_A_AsanInited : Z := 0x594b0.  Definition tfib_E_AsanInited : Z := 0x594c8.
Definition tfib_A_asan_report_load1 : Z := 0x594c8.  Definition tfib_E_asan_report_load1 : Z := 0x59518.
Definition tfib_A_asan_report_exp_load1 : Z := 0x59518.  Definition tfib_E_asan_report_exp_load1 : Z := 0x59568.
Definition tfib_A_asan_report_load2 : Z := 0x59568.  Definition tfib_E_asan_report_load2 : Z := 0x595b8.
Definition tfib_A_asan_report_exp_load2 : Z := 0x595b8.  Definition tfib_E_asan_report_exp_load2 : Z := 0x59608.
Definition tfib_A_asan_report_load4 : Z := 0x59608.  Definition tfib_E_asan_report_load4 : Z := 0x59658.
Definition tfib_A_asan_report_exp_load4 : Z := 0x59658.  Definition tfib_E_asan_report_exp_load4 : Z := 0x596a8.
Definition tfib_A_asan_report_load8 : Z := 0x596a8.  Definition tfib_E_asan_report_load8 : Z := 0x596f8.
Definition tfib_A_asan_report_exp_load8 : Z := 0x596f8.  Definition tfib_E_asan_report_exp_load8 : Z := 0x59748.
Definition tfib_A_asan_report_load16 : Z := 0x59748.  Definition tfib_E_asan_report_load16 : Z := 0x59798.
Definition tfib_A_asan_report_exp_load16 : Z := 0x59798.  Definition tfib_E_asan_report_exp_load16 : Z := 0x597e8.
Definition tfib_A_asan_report_store1 : Z := 0x597e8.  Definition tfib_E_asan_report_store1 : Z := 0x59838.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59838.  Definition tfib_E_asan_report_exp_store1 : Z := 0x59888.
Definition tfib_A_asan_report_store2 : Z := 0x59888.  Definition tfib_E_asan_report_store2 : Z := 0x598d8.
Definition tfib_A_asan_report_exp_store2 : Z := 0x598d8.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59928.
Definition tfib_A_asan_report_store4 : Z := 0x59928.  Definition tfib_E_asan_report_store4 : Z := 0x59978.
Definition tfib_A_asan_report_exp_store4 : Z := 0x59978.  Definition tfib_E_asan_report_exp_store4 : Z := 0x599c8.
Definition tfib_A_asan_report_store8 : Z := 0x599c8.  Definition tfib_E_asan_report_store8 : Z := 0x59a18.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59a18.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59a68.
Definition tfib_A_asan_report_store16 : Z := 0x59a68.  Definition tfib_E_asan_report_store16 : Z := 0x59ab8.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59ab8.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59b08.
Definition tfib_A_asan_report_load_n : Z := 0x59b08.  Definition tfib_E_asan_report_load_n : Z := 0x59b58.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59b58.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59ba8.
Definition tfib_A_asan_report_store_n : Z := 0x59ba8.  Definition tfib_E_asan_report_store_n : Z := 0x59bf8.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59bf8.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59c48.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59c48.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59cc8.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59cc8.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5a07c.
Definition tfib_A_AsanInitInternal : Z := 0x5a10c.  Definition tfib_E_AsanInitInternal : Z := 0x5a3c0.
Definition tfib_A_thunk_59674 : Z := 0x5a628.  Definition tfib_E_thunk_59674 : Z := 0x5a62c.
Definition tfib_A_asan_init : Z := 0x5a62c.  Definition tfib_E_asan_init : Z := 0x5a6c0.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a6c0.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a6c4.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a928.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5ac50.
Definition tfib_A_InitializeShadowMemory : Z := 0x5ae30.  Definition tfib_E_InitializeShadowMemory : Z := 0x5b138.
Definition tfib_A_SetMallocContextSize : Z := 0x5b138.  Definition tfib_E_SetMallocContextSize : Z := 0x5b148.
Definition tfib_A_GetMallocContextSize : Z := 0x5b148.  Definition tfib_E_GetMallocContextSize : Z := 0x5b158.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b158.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b2a8.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5bd8c.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5bdc4.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5c06c.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5c078.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5c078.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5c104.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5c104.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5c16c.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5c16c.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5c1e4.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5c1e4.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5c24c.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5c624.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5c630.
Definition tfib_A_AsanThread_Create : Z := 0x5c7b0.  Definition tfib_E_AsanThread_Create : Z := 0x5c94c.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c9a8.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5cbc0.
Definition tfib_A_GetCurrentThread : Z := 0x5cbc0.  Definition tfib_E_GetCurrentThread : Z := 0x5cbe0.
Definition tfib_A_AsanThread_stack_top : Z := 0x5cd84.  Definition tfib_E_AsanThread_stack_top : Z := 0x5cddc.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5cddc.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5ce34.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ce34.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5d064.
Definition tfib_A_AsanThread_Init : Z := 0x5d064.  Definition tfib_E_AsanThread_Init : Z := 0x5d458.
Definition tfib_A_CreateMainThread : Z := 0x5d598.  Definition tfib_E_CreateMainThread : Z := 0x5d6a8.
Definition tfib_A_SetCurrentThread : Z := 0x5d6a8.  Definition tfib_E_SetCurrentThread : Z := 0x5d788.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d98c.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5dac8.
Definition tfib_A_weak_default_hook_ret : Z := 0x5e79c.  Definition tfib_E_weak_default_hook_ret : Z := 0x5e7a0.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5f0d8.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5f124.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5f124.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5f130.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5f160.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5f16c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5f16c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5f178.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f194.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f460.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f460.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f820.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x60788.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x60860.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x60860.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x608fc.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60e20.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60e64.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x610dc.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x611f0.
Definition tfib_A_RunMallocHooks : Z := 0x61394.  Definition tfib_E_RunMallocHooks : Z := 0x6144c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x6144c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x61450.
Definition tfib_A_RunFreeHooks : Z := 0x61450.  Definition tfib_E_RunFreeHooks : Z := 0x614fc.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x61530.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x6157c.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61840.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61a80.
Definition tfib_A_sanitizer_set_report_path : Z := 0x6207c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x62094.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63ca4.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63fb4.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63fb4.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x640f8.
Definition tfib_A_FlagParser_ParseString : Z := 0x640f8.  Definition tfib_E_FlagParser_ParseString : Z := 0x641ec.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x64380.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x643e0.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x643e0.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x64420.
Definition tfib_A_internal_atoll : Z := 0x64420.  Definition tfib_E_internal_atoll : Z := 0x6450c.
Definition tfib_A_internal_simple_strtoll : Z := 0x6450c.  Definition tfib_E_internal_simple_strtoll : Z := 0x64668.
Definition tfib_A_internal_memchr : Z := 0x64668.  Definition tfib_E_internal_memchr : Z := 0x64688.
Definition tfib_A_internal_memcmp : Z := 0x64688.  Definition tfib_E_internal_memcmp : Z := 0x646c0.
Definition tfib_A_internal_memcpy : Z := 0x646c0.  Definition tfib_E_internal_memcpy : Z := 0x646e4.
Definition tfib_A_internal_memmove : Z := 0x646e4.  Definition tfib_E_internal_memmove : Z := 0x6473c.
Definition tfib_A_internal_memset : Z := 0x6473c.  Definition tfib_E_internal_memset : Z := 0x6479c.
Definition tfib_A_internal_strcspn : Z := 0x6479c.  Definition tfib_E_internal_strcspn : Z := 0x647f0.
Definition tfib_A_internal_strdup : Z := 0x64824.  Definition tfib_E_internal_strdup : Z := 0x64890.
Definition tfib_A_internal_strlen : Z := 0x64890.  Definition tfib_E_internal_strlen : Z := 0x648ac.
Definition tfib_A_internal_strchrnul : Z := 0x6493c.  Definition tfib_E_internal_strchrnul : Z := 0x64984.
Definition tfib_A_internal_strrchr : Z := 0x64984.  Definition tfib_E_internal_strrchr : Z := 0x649c4.
Definition tfib_A_internal_strnlen : Z := 0x64af4.  Definition tfib_E_internal_strnlen : Z := 0x64b24.
Definition tfib_A_internal_strncpy : Z := 0x64b68.  Definition tfib_E_internal_strncpy : Z := 0x64bd8.
Definition tfib_A_internal_strstr : Z := 0x64bd8.  Definition tfib_E_internal_strstr : Z := 0x64c6c.
Definition tfib_A_mem_is_zero : Z := 0x64c6c.  Definition tfib_E_mem_is_zero : Z := 0x64d20.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64d20.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64d30.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64d30.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64f10.
Definition tfib_A_internal_iserror : Z := 0x64f1c.  Definition tfib_E_internal_iserror : Z := 0x64f3c.
Definition tfib_A_internal_mmap : Z := 0x64f3c.  Definition tfib_E_internal_mmap : Z := 0x64f48.
Definition tfib_A_internal_munmap : Z := 0x64f48.  Definition tfib_E_internal_munmap : Z := 0x64f54.
Definition tfib_A_internal_mprotect : Z := 0x64f54.  Definition tfib_E_internal_mprotect : Z := 0x64f64.
Definition tfib_A_internal_madvise : Z := 0x64f64.  Definition tfib_E_internal_madvise : Z := 0x64f90.
Definition tfib_A_internal_close : Z := 0x64f90.  Definition tfib_E_internal_close : Z := 0x64f9c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64f9c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64fc0.
Definition tfib_A_internal_read : Z := 0x64fc0.  Definition tfib_E_internal_read : Z := 0x64ff8.
Definition tfib_A_internal_write : Z := 0x64ff8.  Definition tfib_E_internal_write : Z := 0x65030.
Definition tfib_A_internal_ftruncate : Z := 0x65030.  Definition tfib_E_internal_ftruncate : Z := 0x65068.
Definition tfib_A_internal_dup : Z := 0x65068.  Definition tfib_E_internal_dup : Z := 0x65074.
Definition tfib_A_internal_dup2_dup3 : Z := 0x65074.  Definition tfib_E_internal_dup2_dup3 : Z := 0x65084.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x65084.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x6509c.
Definition tfib_A_internal_sched_yield : Z := 0x6509c.  Definition tfib_E_internal_sched_yield : Z := 0x650a8.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x650a8.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x650f4.
Definition tfib_A_internal_execve : Z := 0x650f4.  Definition tfib_E_internal_execve : Z := 0x65100.
Definition tfib_A_internal_exit_exit_group : Z := 0x65100.  Definition tfib_E_internal_exit_exit_group : Z := 0x65114.
Definition tfib_A_FileExists_newfstatat : Z := 0x65114.  Definition tfib_E_FileExists_newfstatat : Z := 0x65194.
Definition tfib_A_DirExists_newfstatat : Z := 0x65194.  Definition tfib_E_DirExists_newfstatat : Z := 0x651f8.
Definition tfib_A_GetTid_gettid : Z := 0x651f8.  Definition tfib_E_GetTid_gettid : Z := 0x65204.
Definition tfib_A_GetEnv : Z := 0x65204.  Definition tfib_E_GetEnv : Z := 0x65334.
Definition tfib_A_FutexWait : Z := 0x65438.  Definition tfib_E_FutexWait : Z := 0x6545c.
Definition tfib_A_FutexWake : Z := 0x6545c.  Definition tfib_E_FutexWake : Z := 0x65480.
Definition tfib_A_internal_ptrace : Z := 0x65480.  Definition tfib_E_internal_ptrace : Z := 0x6548c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6548c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6549c.
Definition tfib_A_internal_getpid : Z := 0x6549c.  Definition tfib_E_internal_getpid : Z := 0x654a8.
Definition tfib_A_internal_getppid : Z := 0x654a8.  Definition tfib_E_internal_getppid : Z := 0x654b4.
Definition tfib_A_internal_prctl : Z := 0x654b4.  Definition tfib_E_internal_prctl : Z := 0x654c0.
Definition tfib_A_internal_sigaltstack : Z := 0x654c0.  Definition tfib_E_internal_sigaltstack : Z := 0x654cc.
Definition tfib_A_internal_fork_clone : Z := 0x654cc.  Definition tfib_E_internal_fork_clone : Z := 0x654e4.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x654e4.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x65610.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65d50.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65e68.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65e70.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65f1c.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65f1c.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x6603c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x66104.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x66184.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x661e0.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x662ac.
Definition tfib_A_thunk_653ec : Z := 0x663a8.  Definition tfib_E_thunk_653ec : Z := 0x663ac.
Definition tfib_A_CheckASLR : Z := 0x663ac.  Definition tfib_E_CheckASLR : Z := 0x663b0.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x665fc.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x66600.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x66600.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x6660c.
Definition tfib_A_MmapOrDie : Z := 0x6660c.  Definition tfib_E_MmapOrDie : Z := 0x66718.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x66718.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6678c.
Definition tfib_A_UnmapOrDie : Z := 0x6678c.  Definition tfib_E_UnmapOrDie : Z := 0x66808.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x66808.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66918.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x66b44.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66c48.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66c54.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66dcc.
Definition tfib_A_thunk_66008 : Z := 0x66fc4.  Definition tfib_E_thunk_66008 : Z := 0x66fc8.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x672e8.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x674f4.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67aac.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67ab8.
Definition tfib_A_Printf : Z := 0x67abc.  Definition tfib_E_Printf : Z := 0x67b08.
Definition tfib_A_SharedPrintfCode : Z := 0x67b08.  Definition tfib_E_SharedPrintfCode : Z := 0x67b64.
Definition tfib_A_Report : Z := 0x67b64.  Definition tfib_E_Report : Z := 0x67bb0.
Definition tfib_A_SuppressionContext_ctor : Z := 0x696a8.  Definition tfib_E_SuppressionContext_ctor : Z := 0x69704.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x69704.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x69940.
Definition tfib_A_SuppressionContext_Parse : Z := 0x69940.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69c64.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6a204.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x6a2d4.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a914.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6ad8c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b64c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b970.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b978.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6ba7c.
Definition tfib_A_AddDieCallback : Z := 0x6c22c.  Definition tfib_E_AddDieCallback : Z := 0x6c2b4.
Definition tfib_A_Die : Z := 0x6c378.  Definition tfib_E_Die : Z := 0x6c438.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c438.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c444.
Definition tfib_A_CheckFailed : Z := 0x6c444.  Definition tfib_E_CheckFailed : Z := 0x6c4fc.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6cb54.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6cc4c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6cc4c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6cd78.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6cfa0.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6d01c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6d050.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6d338.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6d338.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6d33c.
Definition tfib_A_AndroidLogInit : Z := 0x6dbe0.  Definition tfib_E_AndroidLogInit : Z := 0x6dbe4.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6dc14.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6dc5c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dc5c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dea8.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6dea8.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6deac.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dfb8.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6e0bc.
Definition tfib_A_thunk_6d37c : Z := 0x6e338.  Definition tfib_E_thunk_6d37c : Z := 0x6e33c.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e3e0.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6e400.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e400.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e4a0.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6e4ec.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6e4f0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e52c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e5f0.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e5f0.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e678.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e678.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e6f0.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e6f0.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e7d4.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e890.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e9c4.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6ebfc.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6ed2c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ed8c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6ee58.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70c88.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70dac.
Definition tfib_A_StackStore_Alloc : Z := 0x70dac.  Definition tfib_E_StackStore_Alloc : Z := 0x70ee0.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x71794.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x71848.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72f9c.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x72ff8.
Definition tfib_A_StackDepotPut : Z := 0x73284.  Definition tfib_E_StackDepotPut : Z := 0x732a4.
Definition tfib_A_StackDepotBase_Put : Z := 0x732a4.  Definition tfib_E_StackDepotBase_Put : Z := 0x73528.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73c08.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73c10.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73c10.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73d70.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73d70.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x73de4.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7426c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x74384.
Definition tfib_A_thunk_762d8 : Z := 0x773d0.  Definition tfib_E_thunk_762d8 : Z := 0x773d4.
Definition tfib_A_thunk_77ab0 : Z := 0x78ba8.  Definition tfib_E_thunk_77ab0 : Z := 0x78bac.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a5d4.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a690.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a690.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a768.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7ad08.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7ad4c.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ad4c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7b11c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b3ec.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b4a4.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c7fc.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c800.
Definition tfib_A_lsan_register_root_region : Z := 0x7d408.  Definition tfib_E_lsan_register_root_region : Z := 0x7d738.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d738.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7dbc0.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7dbc0.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7dbcc.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80b20.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80b9c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80b9c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80c4c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80c64.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80dac.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80dac.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80db8.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80db8.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80dc4.
Definition tfib_A_main : Z := 0x80dc4.  Definition tfib_E_main : Z := 0x81088.
Definition tfib_A_target_alloc_init : Z := 0x81088.  Definition tfib_E_target_alloc_init : Z := 0x8108c.
Definition tfib_A_target_alloc_count : Z := 0x8108c.  Definition tfib_E_target_alloc_count : Z := 0x81094.
Definition tfib_A_target_run : Z := 0x81094.  Definition tfib_E_target_run : Z := 0x8121c.
Definition tfib_A_emit_printf : Z := 0x8121c.  Definition tfib_E_emit_printf : Z := 0x81264.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x81264.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82d60.  Definition tfib_A_io_send : Z := 0x82d60.  Definition tfib_E_io_send : Z := 0x834c4.  Definition tfib_A_io_recv : Z := 0x834c4.  Definition tfib_E_io_recv : Z := 0x8356c.  Definition tfib_A_io_now : Z := 0x8356c.  Definition tfib_E_io_now : Z := 0x83578.  Definition tfib_A_notice : Z := 0x83578.  Definition tfib_E_notice : Z := 0x837d0.  Definition tfib_A_receive : Z := 0x837d0.  Definition tfib_E_receive : Z := 0x83c34.  Definition tfib_A_m_tick : Z := 0x83c34.  Definition tfib_E_m_tick : Z := 0x83cac.  Definition tfib_A_settle : Z := 0x83cac.  Definition tfib_E_settle : Z := 0x83d00.  Definition tfib_A_m_wake : Z := 0x83d00.  Definition tfib_E_m_wake : Z := 0x83e48.  Definition tfib_A_check_state_wake_code : Z := 0x83e48.  Definition tfib_E_check_state_wake_code : Z := 0x83e68.  Definition tfib_A_check_sent_frame : Z := 0x83e68.  Definition tfib_E_check_sent_frame : Z := 0x8415c.  Definition tfib_A_check_ack_frame : Z := 0x8415c.  Definition tfib_E_check_ack_frame : Z := 0x8420c.  Definition tfib_A_check_latest_control : Z := 0x8420c.  Definition tfib_E_check_latest_control : Z := 0x84268.  Definition tfib_A_check_inflight_retry : Z := 0x84268.  Definition tfib_E_check_inflight_retry : Z := 0x84370.  Definition tfib_A_check_state_wake : Z := 0x84370.  Definition tfib_E_check_state_wake : Z := 0x84398.  Definition tfib_A_check_inflight_new : Z := 0x84398.  Definition tfib_E_check_inflight_new : Z := 0x843e0.  Definition tfib_A_check_latest_frame : Z := 0x843e0.  Definition tfib_E_check_latest_frame : Z := 0x844b0.  Definition tfib_A_check_keepalive_due : Z := 0x844b0.  Definition tfib_E_check_keepalive_due : Z := 0x84500.  Definition tfib_A_check_latest_sent : Z := 0x84500.  Definition tfib_E_check_latest_sent : Z := 0x84844.  Definition tfib_A_check_latest_display : Z := 0x84844.  Definition tfib_E_check_latest_display : Z := 0x8488c.  Definition tfib_A_m_rx : Z := 0x8488c.  Definition tfib_E_m_rx : Z := 0x84f40.  Definition tfib_A_desk_named : Z := 0x84f40.  Definition tfib_E_desk_named : Z := 0x85004.  Definition tfib_A_m_lost : Z := 0x85004.  Definition tfib_E_m_lost : Z := 0x850f0.  Definition tfib_A_m_maybe_online : Z := 0x850f0.  Definition tfib_E_m_maybe_online : Z := 0x8520c.  Definition tfib_A_check_state_online : Z := 0x8520c.  Definition tfib_E_check_state_online : Z := 0x85240.  Definition tfib_A_check_inflight_acked : Z := 0x85240.  Definition tfib_E_check_inflight_acked : Z := 0x852e4.  Definition tfib_A_check_inflight_lost : Z := 0x852e4.  Definition tfib_E_check_inflight_lost : Z := 0x8538c.  Definition tfib_A_check_state_desk : Z := 0x8538c.  Definition tfib_E_check_state_desk : Z := 0x85638.  Definition tfib_A_check_state_data : Z := 0x85638.  Definition tfib_E_check_state_data : Z := 0x857e0.  Definition tfib_A_build_and_receive : Z := 0x857e0.  Definition tfib_E_build_and_receive : Z := 0x85b04.  Definition tfib_A_check_ack_settle : Z := 0x85b04.  Definition tfib_E_check_ack_settle : Z := 0x85b34.  Definition tfib_A_check_state_settle : Z := 0x85b34.  Definition tfib_E_check_state_settle : Z := 0x85d50.  Definition tfib_A_check_inflight_settle : Z := 0x85d50.  Definition tfib_E_check_inflight_settle : Z := 0x85e14.  Definition tfib_A_check_keepalive_settle : Z := 0x85e14.  Definition tfib_E_check_keepalive_settle : Z := 0x85e70.  Definition tfib_A_check_latest_queue : Z := 0x85e70.  Definition tfib_E_check_latest_queue : Z := 0x85fdc.  Definition tfib_A_check_latest_drain : Z := 0x85fdc.  Definition tfib_E_check_latest_drain : Z := 0x86110.  Definition tfib_A_check_refusal_submit : Z := 0x86110.  Definition tfib_E_check_refusal_submit : Z := 0x86230.  Definition tfib_A_check_latest_submit : Z := 0x86230.  Definition tfib_E_check_latest_submit : Z := 0x86250.  Definition tfib_A_diginet_session_config_default : Z := 0x862b8.  Definition tfib_E_diginet_session_config_default : Z := 0x864ec.  Definition tfib_A_diginet_session_init : Z := 0x864ec.  Definition tfib_E_diginet_session_init : Z := 0x866fc.  Definition tfib_A_diginet_session_wake : Z := 0x866fc.  Definition tfib_E_diginet_session_wake : Z := 0x86d5c.  Definition tfib_A_send_control : Z := 0x86d5c.  Definition tfib_E_send_control : Z := 0x8713c.  Definition tfib_A_diginet_session_close : Z := 0x8713c.  Definition tfib_E_diginet_session_close : Z := 0x87594.  Definition tfib_A_diginet_session_rx : Z := 0x87594.  Definition tfib_E_diginet_session_rx : Z := 0x87a74.  Definition tfib_A_on_announce : Z := 0x87a74.  Definition tfib_E_on_announce : Z := 0x8842c.  Definition tfib_A_on_ack : Z := 0x8842c.  Definition tfib_E_on_ack : Z := 0x888d0.  Definition tfib_A_on_data : Z := 0x888d0.  Definition tfib_E_on_data : Z := 0x88f08.  Definition tfib_A_session_lost : Z := 0x88f08.  Definition tfib_E_session_lost : Z := 0x892b8.  Definition tfib_A_diginet_session_tick : Z := 0x892b8.  Definition tfib_E_diginet_session_tick : Z := 0x89ef0.  Definition tfib_A_diginet_session_submit : Z := 0x89ef0.  Definition tfib_E_diginet_session_submit : Z := 0x8a12c.  Definition tfib_A_send_data : Z := 0x8a12c.  Definition tfib_E_send_data : Z := 0x8a508.  Definition tfib_A_take : Z := 0x8a508.  Definition tfib_E_take : Z := 0x8a9d4.  Definition tfib_A_diginet_session_deadline : Z := 0x8a9d4.  Definition tfib_E_diginet_session_deadline : Z := 0x8ad88.  Definition tfib_A_diginet_session_poll : Z := 0x8ad88.  Definition tfib_E_diginet_session_poll : Z := 0x8b170.  Definition tfib_A_maybe_online : Z := 0x8b170.  Definition tfib_E_maybe_online : Z := 0x8b590.  Definition tfib_A_diginet_mac_is_digidesign : Z := 0x8b590.  Definition tfib_E_diginet_mac_is_digidesign : Z := 0x8b63c.  Definition tfib_A_diginet_frame_is_keepalive : Z := 0x8b63c.  Definition tfib_E_diginet_frame_is_keepalive : Z := 0x8b6fc.  Definition tfib_A_diginet_frame_parse : Z := 0x8b6fc.  Definition tfib_E_diginet_frame_parse : Z := 0x8bcf8.  Definition tfib_A_diginet_frame_build : Z := 0x8bcf8.  Definition tfib_E_diginet_frame_build : Z := 0x8c238.  Definition tfib_A_diginet_announce_parse : Z := 0x8c238.  Definition tfib_E_diginet_announce_parse : Z := 0x8c484.  Definition tfib_A_diginet_personality_from_name : Z := 0x8c484.  Definition tfib_E_diginet_personality_from_name : Z := 0x8c530.  Definition tfib_A_diginet_body_check : Z := 0x8c530.  Definition tfib_E_diginet_body_check : Z := 0x8c94c.  Definition tfib_A_diginet_cursor_init : Z := 0x8c94c.  Definition tfib_E_diginet_cursor_init : Z := 0x8c9f8.  Definition tfib_A_diginet_msg_next : Z := 0x8c9f8.  Definition tfib_E_diginet_msg_next : Z := 0x8cfc0.

Definition tfib_A_asan_module_ctor : Z := 0x86250.  Definition tfib_E_asan_module_ctor : Z := 0x86288.
Definition tfib_A_asan_module_dtor : Z := 0x86288.  Definition tfib_E_asan_module_dtor : Z := 0x862b8.





















Definition tfib_A_extenddftf2 : Z := 0x8cfd0.  Definition tfib_E_extenddftf2 : Z := 0x8d160.
Definition tfib_A_sysconf : Z := 0x92db0.  Definition tfib_E_sysconf : Z := 0x92fd8.
Definition tfib_A_init : Z := 0x92fd8.  Definition tfib_E_init : Z := 0x92fdc.
Definition tfib_A_init_libc : Z := 0x92fdc.  Definition tfib_E_init_libc : Z := 0x93208.
Definition tfib_A_libc_start_init : Z := 0x93208.  Definition tfib_E_libc_start_init : Z := 0x93254.
Definition tfib_A_libc_start_main : Z := 0x93254.  Definition tfib_E_libc_start_main : Z := 0x932b4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x932b4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x932fc.
Definition tfib_A_init_tls : Z := 0x933d4.  Definition tfib_E_init_tls : Z := 0x93684.
Definition tfib_A_init_ssp : Z := 0x93684.  Definition tfib_E_init_ssp : Z := 0x936e4.
Definition tfib_A_stack_chk_fail : Z := 0x936e4.  Definition tfib_E_stack_chk_fail : Z := 0x936ec.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x93734.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x937c8.
Definition tfib_A_Exit : Z := 0x937c8.  Definition tfib_E_Exit : Z := 0x937e4.
Definition tfib_A_funcs_on_exit : Z := 0x93814.  Definition tfib_E_funcs_on_exit : Z := 0x938dc.
Definition tfib_A_cxa_atexit_atexit : Z := 0x938e0.  Definition tfib_E_cxa_atexit_atexit : Z := 0x939a4.
Definition tfib_A_libc_exit_fini : Z := 0x939ac.  Definition tfib_E_libc_exit_fini : Z := 0x939f8.
Definition tfib_A_exit : Z := 0x939f8.  Definition tfib_E_exit : Z := 0x93a6c.
Definition tfib_A_open : Z := 0x93c6c.  Definition tfib_E_open : Z := 0x93d50.
Definition tfib_A_syscall_ret : Z := 0x93d50.  Definition tfib_E_syscall_ret : Z := 0x93d88.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x93d88.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x93f30.
Definition tfib_A_calloc : Z := 0x944f4.  Definition tfib_E_calloc : Z := 0x9462c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x9462c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x94630.
Definition tfib_A_libc_free : Z := 0x94630.  Definition tfib_E_libc_free : Z := 0x947fc.
Definition tfib_A_get_meta : Z := 0x947fc.  Definition tfib_E_get_meta : Z := 0x9490c.
Definition tfib_A_alloc_meta : Z := 0x94ce4.  Definition tfib_E_alloc_meta : Z := 0x94fbc.
Definition tfib_A_libc_malloc_impl : Z := 0x94fbc.  Definition tfib_E_libc_malloc_impl : Z := 0x9532c.
Definition tfib_A_alloc_slot : Z := 0x9532c.  Definition tfib_E_alloc_slot : Z := 0x95bd0.
Definition tfib_A_enframe : Z := 0x95bd0.  Definition tfib_E_enframe : Z := 0x95d20.
Definition tfib_A_malloc_allzerop : Z := 0x95d20.  Definition tfib_E_malloc_allzerop : Z := 0x95e98.
Definition tfib_A_getrlimit : Z := 0x97b48.  Definition tfib_E_getrlimit : Z := 0x97c40.
Definition tfib_A_getrusage : Z := 0x97c40.  Definition tfib_E_getrusage : Z := 0x97c68.
Definition tfib_A_setrlimit : Z := 0x97c68.  Definition tfib_E_setrlimit : Z := 0x97d30.
Definition tfib_A_mmap : Z := 0x98158.  Definition tfib_E_mmap : Z := 0x98244.
Definition tfib_A_mprotect : Z := 0x98244.  Definition tfib_E_mprotect : Z := 0x9828c.
Definition tfib_A_munmap : Z := 0x98360.  Definition tfib_E_munmap : Z := 0x983a8.
Definition tfib_A_sched_yield : Z := 0x9866c.  Definition tfib_E_sched_yield : Z := 0x98690.
Definition tfib_A_raise_tkill_path : Z := 0x986ec.  Definition tfib_E_raise_tkill_path : Z := 0x98764.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x98764.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x98938.
Definition tfib_A_musl_sigaltstack : Z := 0x98a30.  Definition tfib_E_musl_sigaltstack : Z := 0x98abc.
Definition tfib_A_lockfile : Z := 0x990fc.  Definition tfib_E_lockfile : Z := 0x991f8.
Definition tfib_A_unlockfile : Z := 0x991f8.  Definition tfib_E_unlockfile : Z := 0x99258.
Definition tfib_A_stdio_read : Z := 0x98de8.  Definition tfib_E_stdio_read : Z := 0x98f00.
Definition tfib_A_stdio_write : Z := 0x98f08.  Definition tfib_E_stdio_write : Z := 0x99098.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x98db8.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x98dbc.
Definition tfib_A_stdio_close : Z := 0x98dbc.  Definition tfib_E_stdio_close : Z := 0x98de8.
Definition tfib_A_fwritex : Z := 0x9968c.  Definition tfib_E_fwritex : Z := 0x997c4.
Definition tfib_A_musl_fwrite : Z := 0x997c4.  Definition tfib_E_musl_fwrite : Z := 0x9987c.
Definition tfib_A_towrite : Z := 0x9987c.  Definition tfib_E_towrite : Z := 0x998d0.
Definition tfib_A_stdio_exit : Z := 0x994e8.  Definition tfib_E_stdio_exit : Z := 0x9968c.
Definition tfib_A_ofl_lock : Z := 0x998d0.  Definition tfib_E_ofl_lock : Z := 0x99900.
Definition tfib_A_musl_vfprintf : Z := 0x99a4c.  Definition tfib_E_musl_vfprintf : Z := 0x99bfc.
Definition tfib_A_printf_core : Z := 0x99bfc.  Definition tfib_E_printf_core : Z := 0x9aa2c.
Definition tfib_A_pop_arg : Z := 0x9aa2c.  Definition tfib_E_pop_arg : Z := 0x9ab60.
Definition tfib_A_pad : Z := 0x9ab60.  Definition tfib_E_pad : Z := 0x9ac34.
Definition tfib_A_fmt_fp : Z := 0x9ac34.  Definition tfib_E_fmt_fp : Z := 0x9c2fc.
Definition tfib_A_thunk_931e0 : Z := 0x94148.  Definition tfib_E_thunk_931e0 : Z := 0x9414c.
Definition tfib_A_musl_wctomb : Z := 0x984d4.  Definition tfib_E_musl_wctomb : Z := 0x984f8.
Definition tfib_A_musl_wcrtomb : Z := 0x983a8.  Definition tfib_E_musl_wcrtomb : Z := 0x984d4.
Definition tfib_A_fpclassifyl : Z := 0x96738.  Definition tfib_E_fpclassifyl : Z := 0x9677c.
Definition tfib_A_letf2 : Z := 0x95f70.  Definition tfib_E_letf2 : Z := 0x96038.
Definition tfib_A_multf3 : Z := 0x96038.  Definition tfib_E_multf3 : Z := 0x96738.
Definition tfib_A_floatsitf : Z := 0x96f94.  Definition tfib_E_floatsitf : Z := 0x9709c.
Definition tfib_A_scalbn : Z := 0x979a0.  Definition tfib_E_scalbn : Z := 0x97a38.
Definition tfib_A_subtf3 : Z := 0x96f84.  Definition tfib_E_subtf3 : Z := 0x96f94.
Definition tfib_A_addtf3 : Z := 0x9677c.  Definition tfib_E_addtf3 : Z := 0x96f48.
Definition tfib_A_fe_getround : Z := 0x96f48.  Definition tfib_E_fe_getround : Z := 0x96f78.
Definition tfib_A_fixunstfsi : Z := 0x9c304.  Definition tfib_E_fixunstfsi : Z := 0x9c398.
Definition tfib_A_floatunsitf : Z := 0x9c398.  Definition tfib_E_floatunsitf : Z := 0x9c484.
Definition tfib_A_fixtfsi : Z := 0x97a38.  Definition tfib_E_fixtfsi : Z := 0x97ae0.
Definition tfib_A_divtf3 : Z := 0x9709c.  Definition tfib_E_divtf3 : Z := 0x979a0.
Definition tfib_A_musl_vprintf : Z := 0x9cb5c.  Definition tfib_E_musl_vprintf : Z := 0x9cb78.
Definition tfib_A_stdout_write : Z := 0x9990c.  Definition tfib_E_stdout_write : Z := 0x999ac.
Definition tfib_A_thunk_95368 : Z := 0x9d110.  Definition tfib_E_thunk_95368 : Z := 0x9d114.
Definition tfib_A_musl_memcmp : Z := 0x9d1e0.  Definition tfib_E_musl_memcmp : Z := 0x9d210.
Definition tfib_A_musl_memcpy : Z := 0x9d210.  Definition tfib_E_musl_memcpy : Z := 0x9d614.
Definition tfib_A_musl_memset : Z := 0x9d614.  Definition tfib_E_musl_memset : Z := 0x9d70c.
Definition tfib_A_musl_strchr : Z := 0x9d70c.  Definition tfib_E_musl_strchr : Z := 0x9d748.
Definition tfib_A_strchrnul : Z := 0x9d748.  Definition tfib_E_strchrnul : Z := 0x9d828.
Definition tfib_A_musl_strlen : Z := 0x9d860.  Definition tfib_E_musl_strlen : Z := 0x9d8f0.
Definition tfib_A_musl_strnlen : Z := 0x9da9c.  Definition tfib_E_musl_strnlen : Z := 0x9dae0.
Definition tfib_A_musl_memchr : Z := 0x9d114.  Definition tfib_E_musl_memchr : Z := 0x9d1e0.
Definition tfib_A_lock : Z := 0x9dae0.  Definition tfib_E_lock : Z := 0x9dd68.
Definition tfib_A_unlock : Z := 0x9dd68.  Definition tfib_E_unlock : Z := 0x9dddc.
Definition tfib_A_syscall_cp_c : Z := 0x9dddc.  Definition tfib_E_syscall_cp_c : Z := 0x9de00.
Definition tfib_A_syscall_cp_sccp : Z := 0x9de00.  Definition tfib_E_syscall_cp_sccp : Z := 0x9de04.
Definition tfib_A_pthread_atfork : Z := 0x9de40.  Definition tfib_E_pthread_atfork : Z := 0x9dee4.
Definition tfib_A_mremap : Z := 0x9828c.  Definition tfib_E_mremap : Z := 0x98360.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9eeb8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9eed4.
Definition tfib_A_pthread_key_create : Z := 0x9f260.  Definition tfib_E_pthread_key_create : Z := 0x9f334.
Definition tfib_A_pthread_setspecific : Z := 0x9f7fc.  Definition tfib_E_pthread_setspecific : Z := 0x9f830.
Definition tfib_A_set_thread_area : Z := 0x9f838.  Definition tfib_E_set_thread_area : Z := 0x9f844.
Definition tfib_A_thunk_96f9c : Z := 0x9f830.  Definition tfib_E_thunk_96f9c : Z := 0x9f838.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa0164.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0xa021c.
Definition tfib_A_close : Z := 0xa2834.  Definition tfib_E_close : Z := 0xa2888.
Definition tfib_A_musl_read : Z := 0xa2914.  Definition tfib_E_musl_read : Z := 0xa2948.
Definition tfib_A_vm_wait : Z := 0x9fe74.  Definition tfib_E_vm_wait : Z := 0x9fec4.
Definition tfib_D_str_sealed : Z := 0x1183c.
Definition tfib_D_init_array_0_3 : Z := 0xa3948.
Definition tfib_D_fini_array_0_1 : Z := 0xa3968.
Definition tfib_D_GOT_common_flags : Z := 0xa4080.
Definition tfib_D_GOT_flags : Z := 0xa4088.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa4090.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa4098.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa40a0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa40a8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa4bf8.
Definition tfib_D_environ_musl : Z := 0xa4d20.
Definition tfib_D_REAL_read : Z := 0xa5dc8.
Definition tfib_D_REAL_memcpy : Z := 0xa5ef0.
Definition tfib_D_REAL_memset : Z := 0xa5ef8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa9398.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xaa1f8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xac9f8.
Definition tfib_D_asan_inited : Z := 0xad6d8.
Definition tfib_D_replace_intrin_cached : Z := 0xad6d9.
Definition tfib_D_kHighMemEnd : Z := 0xad6e0.
Definition tfib_D_kMidMemBeg : Z := 0xad6e8.
Definition tfib_D_kMidMemEnd : Z := 0xad6f0.
Definition tfib_D_malloc_context_size : Z := 0xad6fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13e528.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x613d80.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x616000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x310d0.
Definition tfib_at_rw_lo : Z := 0xa5000.
Definition tfib_at_rw_len : Z := 0x571000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x6473c.
Definition tfib_at_x_imemcpy : Z := 0x646c0.
Definition tfib_at_x_memset : Z := 0x9d614.
Definition tfib_at_x_memcpy : Z := 0x9d210.
Definition tfib_at_x_memiszero : Z := 0x64c6c.
Definition tfib_at_x_istrncpy : Z := 0x64b68.
Definition tfib_at_x_sealed : Z := 0x1183c.
Definition tfib_at_x_popfree : Z := 0x374bc.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x93014.
Definition tfib_at_x_envscan_k : Z := 0x93020.
Definition tfib_at_x_pnscan : Z := 0x930d8.
Definition tfib_at_x_pnscan_k : Z := 0x930e4.
Definition tfib_at_stops_more : list Z := (0x35130 :: 0x36754 :: 0x54a48 :: 0x5ae00 :: 0x5ae14 :: 0x5ae28 :: 0x607b8 :: 0x60888 :: 0x6ddb4 :: 0x6ecc0 :: 0x6ee50 :: 0x78ba8 :: nil)%list.
