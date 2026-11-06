(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1w.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x225cc.   (* .rodata of knock's asan pin (sha256 61768cf4739b...), read from the section header: 0x102d0..0x22564; the donor's 0x2278c was cgif's ASAN-UBSAN .rodata end, 0x40 short of cgif's own 0x227cc *)
Definition tfib_text_lo : Z := 0x2f9e4.  Definition tfib_text_hi : Z := 0x94330.
Definition tfib_init_array_lo : Z := 0x95330.  Definition tfib_init_array_hi : Z := 0x95350.
Definition tfib_fini_array_lo : Z := 0x95350.  Definition tfib_fini_array_hi : Z := 0x95360.
Definition tfib_preinit_array_lo : Z := 0x95360.  Definition tfib_preinit_array_hi : Z := 0x95368.
Definition tfib_data_rel_ro_lo : Z := 0x95368.  Definition tfib_data_rel_ro_hi : Z := 0x95868.
Definition tfib_got_lo : Z := 0x95868.  Definition tfib_got_hi : Z := 0x965c0.
Definition tfib_data_lo : Z := 0x975c0.  Definition tfib_data_hi : Z := 0x9a170.
Definition tfib_bss_lo : Z := 0x9a1c0.  Definition tfib_bss_hi : Z := 0x5f20f0.
Definition tfib_tbss_lo : Z := 0x94330.  Definition tfib_tbss_hi : Z := 0x94344.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f3000.
Definition tfib_entry : Z := 0x2f9e4.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2f9e4.  Definition tfib_E_start : Z := 0x2fa00.
Definition tfib_A_start_c : Z := 0x2fa00.  Definition tfib_E_start_c : Z := 0x2fa2c.
Definition tfib_A_do_init : Z := 0x2fa2c.  Definition tfib_E_do_init : Z := 0x2faa0.
Definition tfib_A_do_fini : Z := 0x2faa0.  Definition tfib_E_do_fini : Z := 0x2fb30.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x2fb30.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x2fb6c.
Definition tfib_A_InitializeAllocator : Z := 0x2fcdc.  Definition tfib_E_InitializeAllocator : Z := 0x2fcf4.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x2fcf4.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x2fe60.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x303bc.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x30518.
Definition tfib_A_asan_free : Z := 0x308ec.  Definition tfib_E_asan_free : Z := 0x30914.
Definition tfib_A_Allocator_Deallocate : Z := 0x30914.  Definition tfib_E_Allocator_Deallocate : Z := 0x30bcc.
Definition tfib_A_asan_malloc : Z := 0x30bcc.  Definition tfib_E_asan_malloc : Z := 0x30c28.
Definition tfib_A_Allocator_Allocate : Z := 0x30c28.  Definition tfib_E_Allocator_Allocate : Z := 0x315b0.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x31ce8.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x31e2c.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x31f18.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x31f74.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x31f74.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x321c4.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x321c4.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x322b8.
Definition tfib_A_Allocator_CheckOptions : Z := 0x322b8.  Definition tfib_E_Allocator_CheckOptions : Z := 0x323a0.
Definition tfib_A_Quarantine_Recycle : Z := 0x327d4.  Definition tfib_E_Quarantine_Recycle : Z := 0x329b8.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x329b8.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x32b3c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x32c74.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x32ef8.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x32ef8.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33078.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33078.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33240.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33240.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3340c.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x3340c.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x334ac.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x334ac.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x335b0.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x338d8.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33a20.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x33a20.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x33a58.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x341f0.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x344d8.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x34bb0.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x34d28.
Definition tfib_A_Quarantine_Put : Z := 0x34d28.  Definition tfib_E_Quarantine_Put : Z := 0x34ed8.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x34ed8.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x350bc.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x350bc.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x35394.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x35394.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x3580c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3580c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x3590c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x3590c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x35c14.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x35c14.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x35f84.
Definition tfib_A_RZSize2Log : Z := 0x35f84.  Definition tfib_E_RZSize2Log : Z := 0x3609c.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x363a4.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x364a0.
Definition tfib_A_AsanDeactivate : Z := 0x364a0.  Definition tfib_E_AsanDeactivate : Z := 0x36588.
Definition tfib_A_AsanActivate : Z := 0x36588.  Definition tfib_E_AsanActivate : Z := 0x36664.
Definition tfib_A_FlagHandler_Parse : Z := 0x36b40.  Definition tfib_E_FlagHandler_Parse : Z := 0x36c28.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3b6e0.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3b7b8.
Definition tfib_A_FakeStack_Create : Z := 0x3b7b8.  Definition tfib_E_FakeStack_Create : Z := 0x3b8a4.
Definition tfib_A_check_slots : Z := 0x7e870.  Definition tfib_E_check_slots : Z := 0x7e8e4.  Definition tfib_A_asan_module_dtor : Z := 0x7e91c.  Definition tfib_E_asan_module_dtor : Z := 0x7e94c.  Definition tfib_A_reac_qdisc_etf_catchup_slots : Z := 0x7e94c.  Definition tfib_E_reac_qdisc_etf_catchup_slots : Z := 0x7e9ac.
Definition tfib_A_SetTLSFakeStack : Z := 0x3bc94.  Definition tfib_E_SetTLSFakeStack : Z := 0x3bcc4.


Definition tfib_A_InitializeFlags : Z := 0x3bcc4.  Definition tfib_E_InitializeFlags : Z := 0x3ccf0.
Definition tfib_A_asan_register_globals : Z := 0x3d3fc.  Definition tfib_E_asan_register_globals : Z := 0x3e218.
Definition tfib_A_asan_unregister_globals : Z := 0x3e218.  Definition tfib_E_asan_unregister_globals : Z := 0x3e7e4.
Definition tfib_A_asan_register_elf_globals : Z := 0x3e7e4.  Definition tfib_E_asan_register_elf_globals : Z := 0x3e850.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x3ef38.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x3f1a8.
Definition tfib_A_asan_after_dynamic_init : Z := 0x3f1a8.  Definition tfib_E_asan_after_dynamic_init : Z := 0x3f4b0.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x3fc24.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x3fd74.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x40790.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x408a8.
Definition tfib_A_strlen : Z := 0x408a8.  Definition tfib_E_strlen : Z := 0x408ac.
Definition tfib_A_strnlen : Z := 0x408ac.  Definition tfib_E_strnlen : Z := 0x408b0.
Definition tfib_A_strcmp : Z := 0x408b0.  Definition tfib_E_strcmp : Z := 0x408b4.
Definition tfib_A_strchr : Z := 0x408b4.  Definition tfib_E_strchr : Z := 0x408b8.
Definition tfib_A_memcmp : Z := 0x408b8.  Definition tfib_E_memcmp : Z := 0x408bc.
Definition tfib_A_memchr : Z := 0x408bc.  Definition tfib_E_memchr : Z := 0x408c0.
Definition tfib_A_frexpl : Z := 0x408c0.  Definition tfib_E_frexpl : Z := 0x408c4.
Definition tfib_A_read : Z := 0x408c4.  Definition tfib_E_read : Z := 0x408c8.
Definition tfib_A_fwrite : Z := 0x408c8.  Definition tfib_E_fwrite : Z := 0x408cc.
Definition tfib_A_time : Z := 0x408cc.  Definition tfib_E_time : Z := 0x408d0.
Definition tfib_A_gmtime_r : Z := 0x408d0.  Definition tfib_E_gmtime_r : Z := 0x408d4.
Definition tfib_A_vprintf : Z := 0x408d4.  Definition tfib_E_vprintf : Z := 0x408d8.
Definition tfib_A_vfprintf : Z := 0x408d8.  Definition tfib_E_vfprintf : Z := 0x408dc.
Definition tfib_A_vsnprintf : Z := 0x408dc.  Definition tfib_E_vsnprintf : Z := 0x408e0.
Definition tfib_A_fprintf : Z := 0x408e0.  Definition tfib_E_fprintf : Z := 0x408e4.
Definition tfib_A_snprintf : Z := 0x408e4.  Definition tfib_E_snprintf : Z := 0x408e8.
Definition tfib_A_clock_gettime : Z := 0x408e8.  Definition tfib_E_clock_gettime : Z := 0x408ec.
Definition tfib_A_wcrtomb : Z := 0x408ec.  Definition tfib_E_wcrtomb : Z := 0x408f0.
Definition tfib_A_wctomb : Z := 0x408f0.  Definition tfib_E_wctomb : Z := 0x408f4.
Definition tfib_A_strerror : Z := 0x408f4.  Definition tfib_E_strerror : Z := 0x408f8.
Definition tfib_A__exit : Z := 0x408f8.  Definition tfib_E__exit : Z := 0x408fc.
Definition tfib_A_pthread_attr_getstack : Z := 0x408fc.  Definition tfib_E_pthread_attr_getstack : Z := 0x40900.
Definition tfib_A___tls_get_addr : Z := 0x40900.  Definition tfib_E___tls_get_addr : Z := 0x40904.
Definition tfib_A_fflush : Z := 0x40904.  Definition tfib_E_fflush : Z := 0x40908.
Definition tfib_A_sem_init : Z := 0x40908.  Definition tfib_E_sem_init : Z := 0x4090c.
Definition tfib_A_sem_destroy : Z := 0x4090c.  Definition tfib_E_sem_destroy : Z := 0x40910.
Definition tfib_A_sem_wait : Z := 0x40910.  Definition tfib_E_sem_wait : Z := 0x40914.
Definition tfib_A_sem_trywait : Z := 0x40914.  Definition tfib_E_sem_trywait : Z := 0x40918.
Definition tfib_A_sem_timedwait : Z := 0x40918.  Definition tfib_E_sem_timedwait : Z := 0x4091c.
Definition tfib_A_sem_post : Z := 0x4091c.  Definition tfib_E_sem_post : Z := 0x40920.
Definition tfib_A_pthread_setcancelstate : Z := 0x40920.  Definition tfib_E_pthread_setcancelstate : Z := 0x40924.
Definition tfib_A_send : Z := 0x40924.  Definition tfib_E_send : Z := 0x40928.
Definition tfib_A_sendto : Z := 0x40928.  Definition tfib_E_sendto : Z := 0x4092c.
Definition tfib_A_sigaltstack : Z := 0x4092c.  Definition tfib_E_sigaltstack : Z := 0x40930.
Definition tfib_A_sigaction : Z := 0x40930.  Definition tfib_E_sigaction : Z := 0x40934.
Definition tfib_A_icpt_strlen : Z := 0x40934.  Definition tfib_E_icpt_strlen : Z := 0x40bc8.
Definition tfib_A_icpt_strnlen : Z := 0x40bc8.  Definition tfib_E_icpt_strnlen : Z := 0x40e5c.
Definition tfib_A_icpt_strcmp : Z := 0x40e60.  Definition tfib_E_icpt_strcmp : Z := 0x41390.
Definition tfib_A_icpt_strchr : Z := 0x41390.  Definition tfib_E_icpt_strchr : Z := 0x41670.
Definition tfib_A_icpt_memcmp : Z := 0x41f08.  Definition tfib_E_icpt_memcmp : Z := 0x41fc4.
Definition tfib_A_icpt_memchr : Z := 0x41fc4.  Definition tfib_E_icpt_memchr : Z := 0x42294.
Definition tfib_A_icpt_frexpl : Z := 0x42294.  Definition tfib_E_icpt_frexpl : Z := 0x4250c.
Definition tfib_A_icpt_read : Z := 0x4250c.  Definition tfib_E_icpt_read : Z := 0x4277c.
Definition tfib_A_icpt_fwrite : Z := 0x4277c.  Definition tfib_E_icpt_fwrite : Z := 0x429f0.
Definition tfib_A_icpt_time : Z := 0x429f0.  Definition tfib_E_icpt_time : Z := 0x42c8c.
Definition tfib_A_icpt_gmtime_r : Z := 0x42e94.  Definition tfib_E_icpt_gmtime_r : Z := 0x430d4.
Definition tfib_A_icpt_vprintf : Z := 0x430d4.  Definition tfib_E_icpt_vprintf : Z := 0x43170.
Definition tfib_A_printf_common : Z := 0x43170.  Definition tfib_E_printf_common : Z := 0x43c38.
Definition tfib_A_icpt_vfprintf : Z := 0x43c38.  Definition tfib_E_icpt_vfprintf : Z := 0x43cec.
Definition tfib_A_icpt_vsnprintf : Z := 0x43cec.  Definition tfib_E_icpt_vsnprintf : Z := 0x44004.
Definition tfib_A_icpt_fprintf : Z := 0x44004.  Definition tfib_E_icpt_fprintf : Z := 0x440dc.
Definition tfib_A_icpt_clock_gettime : Z := 0x44180.  Definition tfib_E_icpt_clock_gettime : Z := 0x443d8.
Definition tfib_A_icpt_wcrtomb : Z := 0x443d8.  Definition tfib_E_icpt_wcrtomb : Z := 0x44948.
Definition tfib_A_icpt_wctomb : Z := 0x44948.  Definition tfib_E_icpt_wctomb : Z := 0x44ca4.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x44d70.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45158.
Definition tfib_A_icpt_tls_get_addr : Z := 0x45164.  Definition tfib_E_icpt_tls_get_addr : Z := 0x451e0.
Definition tfib_A_icpt_sem_timedwait : Z := 0x453ec.  Definition tfib_E_icpt_sem_timedwait : Z := 0x45684.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x456b4.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x458dc.
Definition tfib_A_icpt_send : Z := 0x458dc.  Definition tfib_E_icpt_send : Z := 0x45b90.
Definition tfib_A_icpt_sendto : Z := 0x45b90.  Definition tfib_E_icpt_sendto : Z := 0x45e54.
Definition tfib_A_icpt_sigaltstack : Z := 0x45e54.  Definition tfib_E_icpt_sigaltstack : Z := 0x460b0.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46184.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x46334.
Definition tfib_A_format_get_value_size : Z := 0x46334.  Definition tfib_E_format_get_value_size : Z := 0x464cc.
Definition tfib_A_ioctl_table_fill : Z := 0x47078.  Definition tfib_E_ioctl_table_fill : Z := 0x4fd50.
Definition tfib_A_Sort : Z := 0x4fd50.  Definition tfib_E_Sort : Z := 0x4feac.
Definition tfib_A_memset : Z := 0x4feac.  Definition tfib_E_memset : Z := 0x4feb0.
Definition tfib_A_memcpy : Z := 0x4feb0.  Definition tfib_E_memcpy : Z := 0x4feb4.

Definition tfib_A_icpt_memset : Z := 0x4feb4.  Definition tfib_E_icpt_memset : Z := 0x501a4.
Definition tfib_A_icpt_memcpy : Z := 0x501a4.  Definition tfib_E_icpt_memcpy : Z := 0x50794.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x50794.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x507cc.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x507cc.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x507d0.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x507d0.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x507d4.
Definition tfib_A_FindDynamicShadowStart : Z := 0x507d4.  Definition tfib_E_FindDynamicShadowStart : Z := 0x50834.
Definition tfib_A_MemToShadow_510c4 : Z := 0x50880.  Definition tfib_E_MemToShadow_510c4 : Z := 0x509bc.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x509bc.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x509c0.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x509c0.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x50b28.
Definition tfib_A_free : Z := 0x50b28.  Definition tfib_E_free : Z := 0x50b2c.
Definition tfib_A_malloc : Z := 0x50b2c.  Definition tfib_E_malloc : Z := 0x50b30.
Definition tfib_A_icpt_free : Z := 0x50b30.  Definition tfib_E_icpt_free : Z := 0x50d00.
Definition tfib_A_icpt_malloc : Z := 0x50d00.  Definition tfib_E_icpt_malloc : Z := 0x50e5c.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x50e5c.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x50f28.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x50f28.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x50f2c.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x50f2c.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x5102c.
Definition tfib_A_HeapProfile_Print : Z := 0x51354.  Definition tfib_E_HeapProfile_Print : Z := 0x514c0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x519a8.  Definition tfib_E_SetCanPoisonMemory : Z := 0x519b8.
Definition tfib_A_CanPoisonMemory : Z := 0x519b8.  Definition tfib_E_CanPoisonMemory : Z := 0x519cc.
Definition tfib_A_PoisonShadow : Z := 0x519cc.  Definition tfib_E_PoisonShadow : Z := 0x51ec8.
Definition tfib_A_MemToShadow_5270c : Z := 0x51ec8.  Definition tfib_E_MemToShadow_5270c : Z := 0x52004.
Definition tfib_A_asan_poison_memory_region : Z := 0x52004.  Definition tfib_E_asan_poison_memory_region : Z := 0x521a4.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x521a4.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x52324.
Definition tfib_A_asan_region_is_poisoned : Z := 0x52354.  Definition tfib_E_asan_region_is_poisoned : Z := 0x52698.
Definition tfib_A_AsanTSDInit : Z := 0x52ab8.  Definition tfib_E_AsanTSDInit : Z := 0x52b34.
Definition tfib_A_AsanTSDGet : Z := 0x52b34.  Definition tfib_E_AsanTSDGet : Z := 0x52b74.
Definition tfib_A_AsanTSDSet : Z := 0x52b74.  Definition tfib_E_AsanTSDSet : Z := 0x52bb4.
Definition tfib_A_PlatformTSDDtor : Z := 0x52bb4.  Definition tfib_E_PlatformTSDDtor : Z := 0x52c38.
Definition tfib_A_InstallAtForkHandler : Z := 0x52c38.  Definition tfib_E_InstallAtForkHandler : Z := 0x52c54.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x52cb4.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x52cf8.
Definition tfib_A_ReportDeadlySignal : Z := 0x53410.  Definition tfib_E_ReportDeadlySignal : Z := 0x5361c.
Definition tfib_A_ReportDoubleFree : Z := 0x53d24.  Definition tfib_E_ReportDoubleFree : Z := 0x53fb4.
Definition tfib_A_ReportGenericError : Z := 0x55890.  Definition tfib_E_ReportGenericError : Z := 0x5614c.
Definition tfib_A_AsanInited : Z := 0x568d8.  Definition tfib_E_AsanInited : Z := 0x568f0.
Definition tfib_A_asan_report_load1 : Z := 0x568f0.  Definition tfib_E_asan_report_load1 : Z := 0x56940.
Definition tfib_A_asan_report_exp_load1 : Z := 0x56940.  Definition tfib_E_asan_report_exp_load1 : Z := 0x56990.
Definition tfib_A_asan_report_load2 : Z := 0x56990.  Definition tfib_E_asan_report_load2 : Z := 0x569e0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x569e0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x56a30.
Definition tfib_A_asan_report_load4 : Z := 0x56a30.  Definition tfib_E_asan_report_load4 : Z := 0x56a80.
Definition tfib_A_asan_report_exp_load4 : Z := 0x56a80.  Definition tfib_E_asan_report_exp_load4 : Z := 0x56ad0.
Definition tfib_A_asan_report_load8 : Z := 0x56ad0.  Definition tfib_E_asan_report_load8 : Z := 0x56b20.
Definition tfib_A_asan_report_exp_load8 : Z := 0x56b20.  Definition tfib_E_asan_report_exp_load8 : Z := 0x56b70.
Definition tfib_A_asan_report_load16 : Z := 0x56b70.  Definition tfib_E_asan_report_load16 : Z := 0x56bc0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x56bc0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x56c10.
Definition tfib_A_asan_report_store1 : Z := 0x56c10.  Definition tfib_E_asan_report_store1 : Z := 0x56c60.
Definition tfib_A_asan_report_exp_store1 : Z := 0x56c60.  Definition tfib_E_asan_report_exp_store1 : Z := 0x56cb0.
Definition tfib_A_asan_report_store2 : Z := 0x56cb0.  Definition tfib_E_asan_report_store2 : Z := 0x56d00.
Definition tfib_A_asan_report_exp_store2 : Z := 0x56d00.  Definition tfib_E_asan_report_exp_store2 : Z := 0x56d50.
Definition tfib_A_asan_report_store4 : Z := 0x56d50.  Definition tfib_E_asan_report_store4 : Z := 0x56da0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x56da0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x56df0.
Definition tfib_A_asan_report_store8 : Z := 0x56df0.  Definition tfib_E_asan_report_store8 : Z := 0x56e40.
Definition tfib_A_asan_report_exp_store8 : Z := 0x56e40.  Definition tfib_E_asan_report_exp_store8 : Z := 0x56e90.
Definition tfib_A_asan_report_store16 : Z := 0x56e90.  Definition tfib_E_asan_report_store16 : Z := 0x56ee0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x56ee0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x56f30.
Definition tfib_A_asan_report_load_n : Z := 0x56f30.  Definition tfib_E_asan_report_load_n : Z := 0x56f80.
Definition tfib_A_asan_report_exp_load_n : Z := 0x56f80.  Definition tfib_E_asan_report_exp_load_n : Z := 0x56fd0.
Definition tfib_A_asan_report_store_n : Z := 0x56fd0.  Definition tfib_E_asan_report_store_n : Z := 0x57020.
Definition tfib_A_asan_report_exp_store_n : Z := 0x57020.  Definition tfib_E_asan_report_exp_store_n : Z := 0x57070.
Definition tfib_A_InitializeHighMemEnd : Z := 0x57070.  Definition tfib_E_InitializeHighMemEnd : Z := 0x570f0.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x570f0.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x574a4.
Definition tfib_A_AsanInitInternal : Z := 0x57534.  Definition tfib_E_AsanInitInternal : Z := 0x577e8.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x577e8.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x57888.
Definition tfib_A_asan_set_death_callback : Z := 0x57a50.  Definition tfib_E_asan_set_death_callback : Z := 0x57a54.
Definition tfib_A_asan_init : Z := 0x57a54.  Definition tfib_E_asan_init : Z := 0x57ae8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x57ae8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x57aec.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x57aec.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x57b50.
Definition tfib_A_OnLowLevelAllocate : Z := 0x57cc4.  Definition tfib_E_OnLowLevelAllocate : Z := 0x57ccc.
Definition tfib_A_force_interface_symbols : Z := 0x57d50.  Definition tfib_E_force_interface_symbols : Z := 0x58078.
Definition tfib_A_SealedReserveShadow : Z := 0x58078.  Definition tfib_E_SealedReserveShadow : Z := 0x58258.
Definition tfib_A_InitializeShadowMemory : Z := 0x58258.  Definition tfib_E_InitializeShadowMemory : Z := 0x58560.
Definition tfib_A_SetMallocContextSize : Z := 0x58560.  Definition tfib_E_SetMallocContextSize : Z := 0x58570.
Definition tfib_A_GetMallocContextSize : Z := 0x58570.  Definition tfib_E_GetMallocContextSize : Z := 0x58580.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x58580.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x586d0.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x58ab0.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x58d50.
Definition tfib_A_GetCurrentThreadStats : Z := 0x591b4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x591ec.
Definition tfib_A_asan_default_suppressions : Z := 0x59494.  Definition tfib_E_asan_default_suppressions : Z := 0x594a0.
Definition tfib_A_InitializeSuppressions : Z := 0x594a0.  Definition tfib_E_InitializeSuppressions : Z := 0x5952c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5952c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x59594.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x59594.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5960c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5960c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x59674.
Definition tfib_A_IsAddrSuppressed : Z := 0x59674.  Definition tfib_E_IsAddrSuppressed : Z := 0x597c0.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x59a4c.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x59a58.
Definition tfib_A_AsanThread_Create : Z := 0x59bd8.  Definition tfib_E_AsanThread_Create : Z := 0x59d74.
Definition tfib_A_AsanThread_Destroy : Z := 0x59dd0.  Definition tfib_E_AsanThread_Destroy : Z := 0x59fe8.
Definition tfib_A_GetCurrentThread : Z := 0x59fe8.  Definition tfib_E_GetCurrentThread : Z := 0x5a008.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a008.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a1ac.
Definition tfib_A_AsanThread_stack_top : Z := 0x5a1ac.  Definition tfib_E_AsanThread_stack_top : Z := 0x5a204.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5a204.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5a25c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5a25c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5a48c.
Definition tfib_A_AsanThread_Init : Z := 0x5a48c.  Definition tfib_E_AsanThread_Init : Z := 0x5a880.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5a880.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5a98c.
Definition tfib_A_CreateMainThread : Z := 0x5a9c0.  Definition tfib_E_CreateMainThread : Z := 0x5aad0.
Definition tfib_A_SetCurrentThread : Z := 0x5aad0.  Definition tfib_E_SetCurrentThread : Z := 0x5abb0.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5adb4.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5aef0.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5bbc4.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5bbc8.
Definition tfib_A_GetAsanThreadContext : Z := 0x5bbd0.  Definition tfib_E_GetAsanThreadContext : Z := 0x5be10.
Definition tfib_A_internal_allocator : Z := 0x5c064.  Definition tfib_E_internal_allocator : Z := 0x5c1bc.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5c3a8.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5c3b4.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5c3b4.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5c500.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5c500.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5c54c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5c54c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5c558.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5c588.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5c594.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5c594.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5c5a0.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5c5a0.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5c5b0.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5c5bc.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5c888.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5c888.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5cc48.
Definition tfib_A_SealedSetInitFrame : Z := 0x5dba4.  Definition tfib_E_SealedSetInitFrame : Z := 0x5dbb0.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5dbb0.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5dc88.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5dc88.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5dd24.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5e248.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5e28c.
Definition tfib_A_DecreaseTotalMmap : Z := 0x5e28c.  Definition tfib_E_DecreaseTotalMmap : Z := 0x5e2b0.
Definition tfib_A_CacheBinaryName : Z := 0x5e504.  Definition tfib_E_CacheBinaryName : Z := 0x5e618.
Definition tfib_A_RunMallocHooks : Z := 0x5e7bc.  Definition tfib_E_RunMallocHooks : Z := 0x5e874.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x5e874.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x5e878.
Definition tfib_A_RunFreeHooks : Z := 0x5e878.  Definition tfib_E_RunFreeHooks : Z := 0x5e924.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x5e924.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x5e92c.
Definition tfib_A_sanitizer_free_hook : Z := 0x5e92c.  Definition tfib_E_sanitizer_free_hook : Z := 0x5e930.
Definition tfib_A_WaitForDebugger : Z := 0x5e958.  Definition tfib_E_WaitForDebugger : Z := 0x5e9a4.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x5ec68.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x5eea8.
Definition tfib_A_sanitizer_set_report_path : Z := 0x5f4a4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x5f4bc.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x5f4bc.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x5f600.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x5f600.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x5f608.
Definition tfib_A_RegisterCommonFlags : Z := 0x5f950.  Definition tfib_E_RegisterCommonFlags : Z := 0x60bf4.
Definition tfib_A_InitializeCommonFlags : Z := 0x60bf4.  Definition tfib_E_InitializeCommonFlags : Z := 0x60c18.
Definition tfib_A_FlagParser_parse_flag : Z := 0x610cc.  Definition tfib_E_FlagParser_parse_flag : Z := 0x613dc.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x613dc.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x61520.
Definition tfib_A_FlagParser_ParseString : Z := 0x61520.  Definition tfib_E_FlagParser_ParseString : Z := 0x61614.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x617a8.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x61808.
Definition tfib_A_FlagParser_FlagParser : Z := 0x61808.  Definition tfib_E_FlagParser_FlagParser : Z := 0x61848.
Definition tfib_A_internal_atoll : Z := 0x61848.  Definition tfib_E_internal_atoll : Z := 0x61934.
Definition tfib_A_internal_simple_strtoll : Z := 0x61934.  Definition tfib_E_internal_simple_strtoll : Z := 0x61a90.
Definition tfib_A_internal_memchr : Z := 0x61a90.  Definition tfib_E_internal_memchr : Z := 0x61ab0.
Definition tfib_A_internal_memcmp : Z := 0x61ab0.  Definition tfib_E_internal_memcmp : Z := 0x61ae8.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x61ae8.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x61b0c.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x61b0c.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x61b64.
Definition tfib_A_sanitizer_internal_memset : Z := 0x61b64.  Definition tfib_E_sanitizer_internal_memset : Z := 0x61bc4.
Definition tfib_A_internal_strcspn : Z := 0x61bc4.  Definition tfib_E_internal_strcspn : Z := 0x61c18.
Definition tfib_A_internal_strchr : Z := 0x61c18.  Definition tfib_E_internal_strchr : Z := 0x61c4c.
Definition tfib_A_internal_strdup : Z := 0x61c4c.  Definition tfib_E_internal_strdup : Z := 0x61cb8.
Definition tfib_A_internal_strlen : Z := 0x61cb8.  Definition tfib_E_internal_strlen : Z := 0x61cd4.
Definition tfib_A_internal_strcmp : Z := 0x61cd4.  Definition tfib_E_internal_strcmp : Z := 0x61d18.
Definition tfib_A_internal_strncmp : Z := 0x61d18.  Definition tfib_E_internal_strncmp : Z := 0x61d64.
Definition tfib_A_internal_strchrnul : Z := 0x61d64.  Definition tfib_E_internal_strchrnul : Z := 0x61dac.
Definition tfib_A_internal_strrchr : Z := 0x61dac.  Definition tfib_E_internal_strrchr : Z := 0x61dec.
Definition tfib_A_internal_strnlen : Z := 0x61f1c.  Definition tfib_E_internal_strnlen : Z := 0x61f4c.
Definition tfib_A_internal_strncpy : Z := 0x61f90.  Definition tfib_E_internal_strncpy : Z := 0x62000.
Definition tfib_A_internal_strstr : Z := 0x62000.  Definition tfib_E_internal_strstr : Z := 0x62094.
Definition tfib_A_mem_is_zero : Z := 0x62094.  Definition tfib_E_mem_is_zero : Z := 0x62148.
Definition tfib_A_internal_sigprocmask : Z := 0x62148.  Definition tfib_E_internal_sigprocmask : Z := 0x62158.
Definition tfib_A_BlockSignals : Z := 0x62158.  Definition tfib_E_BlockSignals : Z := 0x62338.
Definition tfib_A_internal_iserror : Z := 0x62344.  Definition tfib_E_internal_iserror : Z := 0x62364.
Definition tfib_A_internal_mmap : Z := 0x62364.  Definition tfib_E_internal_mmap : Z := 0x62370.
Definition tfib_A_internal_munmap : Z := 0x62370.  Definition tfib_E_internal_munmap : Z := 0x6237c.
Definition tfib_A_internal_mprotect : Z := 0x6237c.  Definition tfib_E_internal_mprotect : Z := 0x6238c.
Definition tfib_A_internal_madvise : Z := 0x6238c.  Definition tfib_E_internal_madvise : Z := 0x623b8.
Definition tfib_A_internal_close : Z := 0x623b8.  Definition tfib_E_internal_close : Z := 0x623c4.
Definition tfib_A_internal_open : Z := 0x623c4.  Definition tfib_E_internal_open : Z := 0x623e8.
Definition tfib_A_internal_read : Z := 0x623e8.  Definition tfib_E_internal_read : Z := 0x62420.
Definition tfib_A_internal_write : Z := 0x62420.  Definition tfib_E_internal_write : Z := 0x62458.
Definition tfib_A_internal_ftruncate : Z := 0x62458.  Definition tfib_E_internal_ftruncate : Z := 0x62490.
Definition tfib_A_internal_dup : Z := 0x62490.  Definition tfib_E_internal_dup : Z := 0x6249c.
Definition tfib_A_internal_dup2 : Z := 0x6249c.  Definition tfib_E_internal_dup2 : Z := 0x624ac.
Definition tfib_A_internal_unlink : Z := 0x624ac.  Definition tfib_E_internal_unlink : Z := 0x624c4.
Definition tfib_A_internal_sched_yield : Z := 0x624c4.  Definition tfib_E_internal_sched_yield : Z := 0x624d0.
Definition tfib_A_internal_usleep : Z := 0x624d0.  Definition tfib_E_internal_usleep : Z := 0x6251c.
Definition tfib_A_internal_execve : Z := 0x6251c.  Definition tfib_E_internal_execve : Z := 0x62528.
Definition tfib_A_internal_exit : Z := 0x62528.  Definition tfib_E_internal_exit : Z := 0x6253c.
Definition tfib_A_FileExists : Z := 0x6253c.  Definition tfib_E_FileExists : Z := 0x625bc.
Definition tfib_A_DirExists : Z := 0x625bc.  Definition tfib_E_DirExists : Z := 0x62620.
Definition tfib_A_GetTid : Z := 0x62620.  Definition tfib_E_GetTid : Z := 0x6262c.
Definition tfib_A_GetEnv : Z := 0x6262c.  Definition tfib_E_GetEnv : Z := 0x6275c.
Definition tfib_A_FutexWait : Z := 0x62860.  Definition tfib_E_FutexWait : Z := 0x62884.
Definition tfib_A_FutexWake : Z := 0x62884.  Definition tfib_E_FutexWake : Z := 0x628a8.
Definition tfib_A_internal_ptrace : Z := 0x628a8.  Definition tfib_E_internal_ptrace : Z := 0x628b4.
Definition tfib_A_internal_waitpid : Z := 0x628b4.  Definition tfib_E_internal_waitpid : Z := 0x628c4.
Definition tfib_A_internal_getpid : Z := 0x628c4.  Definition tfib_E_internal_getpid : Z := 0x628d0.
Definition tfib_A_internal_getppid : Z := 0x628d0.  Definition tfib_E_internal_getppid : Z := 0x628dc.
Definition tfib_A_internal_prctl : Z := 0x628dc.  Definition tfib_E_internal_prctl : Z := 0x628e8.
Definition tfib_A_internal_sigaltstack : Z := 0x628e8.  Definition tfib_E_internal_sigaltstack : Z := 0x628f4.
Definition tfib_A_internal_fork : Z := 0x628f4.  Definition tfib_E_internal_fork : Z := 0x6290c.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x6290c.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x62a38.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x62c10.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x6300c.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x63178.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x63290.
Definition tfib_A_GetPageSize : Z := 0x63290.  Definition tfib_E_GetPageSize : Z := 0x63298.
Definition tfib_A_ReadBinaryName : Z := 0x63298.  Definition tfib_E_ReadBinaryName : Z := 0x63344.
Definition tfib_A_ReadLongProcessName : Z := 0x63344.  Definition tfib_E_ReadLongProcessName : Z := 0x63464.
Definition tfib_A_internal_clone : Z := 0x6352c.  Definition tfib_E_internal_clone : Z := 0x635ac.
Definition tfib_A_GetHandleSignalMode : Z := 0x635ac.  Definition tfib_E_GetHandleSignalMode : Z := 0x63608.
Definition tfib_A_internal_start_thread : Z := 0x63608.  Definition tfib_E_internal_start_thread : Z := 0x636d4.
Definition tfib_A_InitializePlatformEarly : Z := 0x637d0.  Definition tfib_E_InitializePlatformEarly : Z := 0x637d4.
Definition tfib_A_CheckASLR : Z := 0x637d4.  Definition tfib_E_CheckASLR : Z := 0x637d8.
Definition tfib_A_GetMmapGranularity : Z := 0x63a24.  Definition tfib_E_GetMmapGranularity : Z := 0x63a28.
Definition tfib_A_ErrorIsOOM : Z := 0x63a28.  Definition tfib_E_ErrorIsOOM : Z := 0x63a34.
Definition tfib_A_MmapOrDie : Z := 0x63a34.  Definition tfib_E_MmapOrDie : Z := 0x63b40.
Definition tfib_A_MmapNamed : Z := 0x63b40.  Definition tfib_E_MmapNamed : Z := 0x63bb4.
Definition tfib_A_UnmapOrDie : Z := 0x63bb4.  Definition tfib_E_UnmapOrDie : Z := 0x63c30.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x63c30.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x63d40.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x63f6c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x64070.
Definition tfib_A_MmapFixedOrDie : Z := 0x64070.  Definition tfib_E_MmapFixedOrDie : Z := 0x6407c.
Definition tfib_A_MmapFixedImpl : Z := 0x6407c.  Definition tfib_E_MmapFixedImpl : Z := 0x641f4.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x641f4.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x64200.
Definition tfib_A_CloseFile : Z := 0x643ec.  Definition tfib_E_CloseFile : Z := 0x643f0.
Definition tfib_A_GetNamedMappingFd : Z := 0x64710.  Definition tfib_E_GetNamedMappingFd : Z := 0x6491c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x64ed4.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x64ee0.
Definition tfib_A_Printf : Z := 0x64ee4.  Definition tfib_E_Printf : Z := 0x64f30.
Definition tfib_A_SharedPrintfCode : Z := 0x64f30.  Definition tfib_E_SharedPrintfCode : Z := 0x64f8c.
Definition tfib_A_Report : Z := 0x64f8c.  Definition tfib_E_Report : Z := 0x64fd8.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x66ad0.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x66b2c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x66b2c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x66d68.
Definition tfib_A_SuppressionContext_Parse : Z := 0x66d68.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6708c.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x6762c.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x676fc.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x676fc.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x67a4c.
Definition tfib_A_DTLS_Get : Z := 0x67a4c.  Definition tfib_E_DTLS_Get : Z := 0x67a5c.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x67c98.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x67cdc.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x67cdc.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x67d3c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x67d3c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x681b4.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x68a74.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x68d98.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x68da0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x68ea4.
Definition tfib_A_AddDieCallback : Z := 0x69654.  Definition tfib_E_AddDieCallback : Z := 0x696dc.
Definition tfib_A_Die : Z := 0x697a0.  Definition tfib_E_Die : Z := 0x69860.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x69860.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6986c.
Definition tfib_A_CheckFailed : Z := 0x6986c.  Definition tfib_E_CheckFailed : Z := 0x69924.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x69f7c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6a074.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6a074.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6a1a0.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6a3c8.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6a444.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6a478.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6a760.
Definition tfib_A_InitTlsSize : Z := 0x6a760.  Definition tfib_E_InitTlsSize : Z := 0x6a764.
Definition tfib_A_GetTls : Z := 0x6a764.  Definition tfib_E_GetTls : Z := 0x6ab54.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6ab54.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6ac24.
Definition tfib_A_AndroidLogInit : Z := 0x6b008.  Definition tfib_E_AndroidLogInit : Z := 0x6b00c.
Definition tfib_A_MonotonicNanoTime : Z := 0x6b03c.  Definition tfib_E_MonotonicNanoTime : Z := 0x6b084.
Definition tfib_A_MapDynamicShadow : Z := 0x6b084.  Definition tfib_E_MapDynamicShadow : Z := 0x6b2d0.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6b2d0.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6b2d4.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6b2d4.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6b3e0.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6b3e0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6b4e4.
Definition tfib_A_GetThreadSelf : Z := 0x6b760.  Definition tfib_E_GetThreadSelf : Z := 0x6b764.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6b808.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6b828.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6b828.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6b8c8.
Definition tfib_A_Atexit : Z := 0x6b914.  Definition tfib_E_Atexit : Z := 0x6b918.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6b954.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6ba18.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6ba18.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6baa0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6baa0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6bb18.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6bb18.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6bbfc.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6bcb8.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6bdec.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6c024.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6c154.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6c154.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6c1b4.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6c1b4.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6c280.
Definition tfib_A_MmapNoAccess : Z := 0x6c294.  Definition tfib_E_MmapNoAccess : Z := 0x6c2b4.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6c2b4.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6c328.
Definition tfib_A_SealedRepairReservation : Z := 0x6c328.  Definition tfib_E_SealedRepairReservation : Z := 0x6c400.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6c400.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6c410.
Definition tfib_A_InitializeCoverage : Z := 0x6dc08.  Definition tfib_E_InitializeCoverage : Z := 0x6dc4c.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6dc4c.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6dc7c.
Definition tfib_A_StackStore_Store : Z := 0x6e0b0.  Definition tfib_E_StackStore_Store : Z := 0x6e1d4.
Definition tfib_A_StackStore_Alloc : Z := 0x6e1d4.  Definition tfib_E_StackStore_Alloc : Z := 0x6e308.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x6ebbc.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x6ec70.
Definition tfib_A_StackDepotNode_store : Z := 0x703c4.  Definition tfib_E_StackDepotNode_store : Z := 0x70420.
Definition tfib_A_StackDepotPut : Z := 0x706ac.  Definition tfib_E_StackDepotPut : Z := 0x706cc.
Definition tfib_A_StackDepotBase_Put : Z := 0x706cc.  Definition tfib_E_StackDepotBase_Put : Z := 0x70950.
Definition tfib_A_StackDepotGet : Z := 0x70950.  Definition tfib_E_StackDepotGet : Z := 0x70a60.
Definition tfib_A_StackDepotBase_lock : Z := 0x70e40.  Definition tfib_E_StackDepotBase_lock : Z := 0x70ed0.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x70ed0.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x70fd0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x71030.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x71038.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x71038.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x71198.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x71198.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x7120c.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x71694.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x717ac.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x747f8.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x747fc.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x75fd0.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x75fd4.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x779fc.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x77ab8.
Definition tfib_A_Unwind_Trace : Z := 0x77ab8.  Definition tfib_E_Unwind_Trace : Z := 0x77b90.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x77b90.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x77e04.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x78130.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x78174.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x78174.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x78544.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x78814.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x788cc.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x79c24.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x79c28.
Definition tfib_A_lsan_register_root_region : Z := 0x7a830.  Definition tfib_E_lsan_register_root_region : Z := 0x7ab60.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7ab60.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7afe8.
Definition tfib_A_lsan_default_options : Z := 0x7afe8.  Definition tfib_E_lsan_default_options : Z := 0x7aff4.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7dbac.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7dbc4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7df48.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7dfc4.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7dfc4.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7e074.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x7e074.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x7e08c.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x7e08c.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x7e1d4.
Definition tfib_A_ubsan_default_options : Z := 0x7e1d4.  Definition tfib_E_ubsan_default_options : Z := 0x7e1e0.
Definition tfib_A_asan_default_options : Z := 0x7e1e0.  Definition tfib_E_asan_default_options : Z := 0x7e1ec.
Definition tfib_A_main : Z := 0x7e1ec.  Definition tfib_E_main : Z := 0x7e4b0.
Definition tfib_A_target_alloc_init : Z := 0x7e4b0.  Definition tfib_E_target_alloc_init : Z := 0x7e4b4.
Definition tfib_A_target_alloc_count : Z := 0x7e4b4.  Definition tfib_E_target_alloc_count : Z := 0x7e4bc.
Definition tfib_A_target_run : Z := 0x7e4bc.  Definition tfib_E_target_run : Z := 0x7e614.
Definition tfib_A_oft_exit_guard : Z := 0x7e614.  Definition tfib_E_oft_exit_guard : Z := 0x7e644.
Definition tfib_A_emit_printf : Z := 0x7e644.  Definition tfib_E_emit_printf : Z := 0x7e68c.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7e68c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7e870.
Definition tfib_A_asan_module_ctor : Z := 0x7e8e4.  Definition tfib_E_asan_module_ctor : Z := 0x7e91c.
Definition tfib_A_extenddftf2 : Z := 0x7e9bc.  Definition tfib_E_extenddftf2 : Z := 0x7eb4c.
Definition tfib_A_sysconf : Z := 0x8479c.  Definition tfib_E_sysconf : Z := 0x849c4.
Definition tfib_A_init : Z := 0x849c4.  Definition tfib_E_init : Z := 0x849c8.
Definition tfib_A_init_libc : Z := 0x849c8.  Definition tfib_E_init_libc : Z := 0x84bf4.
Definition tfib_A_libc_start_init : Z := 0x84bf4.  Definition tfib_E_libc_start_init : Z := 0x84c40.
Definition tfib_A_libc_start_main : Z := 0x84c40.  Definition tfib_E_libc_start_main : Z := 0x84ca0.
Definition tfib_A_libc_start_main_stage2 : Z := 0x84ca0.  Definition tfib_E_libc_start_main_stage2 : Z := 0x84ce8.
Definition tfib_A_static_init_tls : Z := 0x84dc0.  Definition tfib_E_static_init_tls : Z := 0x85070.
Definition tfib_A_init_ssp : Z := 0x85070.  Definition tfib_E_init_ssp : Z := 0x850d0.
Definition tfib_A_stack_chk_fail : Z := 0x850d0.  Definition tfib_E_stack_chk_fail : Z := 0x850d8.
Definition tfib_A_abort : Z := 0x85120.  Definition tfib_E_abort : Z := 0x851b4.
Definition tfib_A_Exit : Z := 0x851b4.  Definition tfib_E_Exit : Z := 0x851d0.
Definition tfib_A_funcs_on_exit : Z := 0x85200.  Definition tfib_E_funcs_on_exit : Z := 0x852c8.
Definition tfib_A_cxa_finalize : Z := 0x852c8.  Definition tfib_E_cxa_finalize : Z := 0x852cc.
Definition tfib_A_atexit : Z := 0x852cc.  Definition tfib_E_atexit : Z := 0x85390.
Definition tfib_A_libc_exit_fini_call : Z := 0x85390.  Definition tfib_E_libc_exit_fini_call : Z := 0x85394.
Definition tfib_A_fini : Z := 0x85394.  Definition tfib_E_fini : Z := 0x85398.
Definition tfib_A_libc_exit_fini : Z := 0x85398.  Definition tfib_E_libc_exit_fini : Z := 0x853e4.
Definition tfib_A_exit : Z := 0x853e4.  Definition tfib_E_exit : Z := 0x85458.
Definition tfib_A_open : Z := 0x85658.  Definition tfib_E_open : Z := 0x8573c.
Definition tfib_A_syscall_ret : Z := 0x8573c.  Definition tfib_E_syscall_ret : Z := 0x85774.
Definition tfib_A_dl_iterate_phdr : Z := 0x85774.  Definition tfib_E_dl_iterate_phdr : Z := 0x8591c.
Definition tfib_A_libc_calloc : Z := 0x85ee0.  Definition tfib_E_libc_calloc : Z := 0x86018.
Definition tfib_A_libc_malloc : Z := 0x86018.  Definition tfib_E_libc_malloc : Z := 0x8601c.
Definition tfib_A_libc_free : Z := 0x8601c.  Definition tfib_E_libc_free : Z := 0x861e8.
Definition tfib_A_get_meta : Z := 0x861e8.  Definition tfib_E_get_meta : Z := 0x862f8.
Definition tfib_A_malloc_alloc_meta : Z := 0x866d0.  Definition tfib_E_malloc_alloc_meta : Z := 0x869a8.
Definition tfib_A_libc_malloc_impl : Z := 0x869a8.  Definition tfib_E_libc_malloc_impl : Z := 0x86d18.
Definition tfib_A_alloc_slot : Z := 0x86d18.  Definition tfib_E_alloc_slot : Z := 0x875bc.
Definition tfib_A_enframe : Z := 0x875bc.  Definition tfib_E_enframe : Z := 0x8770c.
Definition tfib_A_malloc_allzerop : Z := 0x8770c.  Definition tfib_E_malloc_allzerop : Z := 0x87884.
Definition tfib_A_getrlimit : Z := 0x89534.  Definition tfib_E_getrlimit : Z := 0x8962c.
Definition tfib_A_getrusage : Z := 0x8962c.  Definition tfib_E_getrusage : Z := 0x89654.
Definition tfib_A_setrlimit : Z := 0x89654.  Definition tfib_E_setrlimit : Z := 0x8971c.
Definition tfib_A_mmap : Z := 0x89b44.  Definition tfib_E_mmap : Z := 0x89c30.
Definition tfib_A_mprotect : Z := 0x89c30.  Definition tfib_E_mprotect : Z := 0x89c78.
Definition tfib_A_munmap : Z := 0x89d4c.  Definition tfib_E_munmap : Z := 0x89d94.
Definition tfib_A_sched_yield : Z := 0x8a058.  Definition tfib_E_sched_yield : Z := 0x8a07c.
Definition tfib_A_raise : Z := 0x8a0d8.  Definition tfib_E_raise : Z := 0x8a150.
Definition tfib_A_libc_sigaction : Z := 0x8a150.  Definition tfib_E_libc_sigaction : Z := 0x8a324.
Definition tfib_A_musl_sigaltstack : Z := 0x8a41c.  Definition tfib_E_musl_sigaltstack : Z := 0x8a4a8.
Definition tfib_A_dprintf : Z := 0x8aa84.  Definition tfib_E_dprintf : Z := 0x8aae8.
Definition tfib_A_lockfile : Z := 0x8aae8.  Definition tfib_E_lockfile : Z := 0x8abe4.
Definition tfib_A_unlockfile : Z := 0x8abe4.  Definition tfib_E_unlockfile : Z := 0x8ac44.
Definition tfib_A_stdio_read : Z := 0x8a7d4.  Definition tfib_E_stdio_read : Z := 0x8a8ec.
Definition tfib_A_stdio_write : Z := 0x8a8f4.  Definition tfib_E_stdio_write : Z := 0x8aa84.
Definition tfib_A_aio_close : Z := 0x8a7a4.  Definition tfib_E_aio_close : Z := 0x8a7a8.
Definition tfib_A_stdio_close : Z := 0x8a7a8.  Definition tfib_E_stdio_close : Z := 0x8a7d4.
Definition tfib_A_fwritex : Z := 0x8b078.  Definition tfib_E_fwritex : Z := 0x8b1b0.
Definition tfib_A_musl_fwrite : Z := 0x8b1b0.  Definition tfib_E_musl_fwrite : Z := 0x8b268.
Definition tfib_A_towrite : Z := 0x8b268.  Definition tfib_E_towrite : Z := 0x8b2bc.
Definition tfib_A_stdio_exit : Z := 0x8aed4.  Definition tfib_E_stdio_exit : Z := 0x8b078.
Definition tfib_A_ofl_lock : Z := 0x8b2bc.  Definition tfib_E_ofl_lock : Z := 0x8b2ec.
Definition tfib_A_musl_vfprintf : Z := 0x8b438.  Definition tfib_E_musl_vfprintf : Z := 0x8b5e8.
Definition tfib_A_printf_core : Z := 0x8b5e8.  Definition tfib_E_printf_core : Z := 0x8c418.
Definition tfib_A_pop_arg : Z := 0x8c418.  Definition tfib_E_pop_arg : Z := 0x8c54c.
Definition tfib_A_pad : Z := 0x8c54c.  Definition tfib_E_pad : Z := 0x8c620.
Definition tfib_A_fmt_fp : Z := 0x8c620.  Definition tfib_E_fmt_fp : Z := 0x8dce8.
Definition tfib_A_lctrans : Z := 0x85b34.  Definition tfib_E_lctrans : Z := 0x85b38.
Definition tfib_A_musl_wctomb : Z := 0x89ec0.  Definition tfib_E_musl_wctomb : Z := 0x89ee4.
Definition tfib_A_musl_wcrtomb : Z := 0x89d94.  Definition tfib_E_musl_wcrtomb : Z := 0x89ec0.
Definition tfib_A_fpclassifyl : Z := 0x88124.  Definition tfib_E_fpclassifyl : Z := 0x88168.
Definition tfib_A_letf2 : Z := 0x8795c.  Definition tfib_E_letf2 : Z := 0x87a24.
Definition tfib_A_multf3 : Z := 0x87a24.  Definition tfib_E_multf3 : Z := 0x88124.
Definition tfib_A_floatsitf : Z := 0x88980.  Definition tfib_E_floatsitf : Z := 0x88a88.
Definition tfib_A_scalbn : Z := 0x8938c.  Definition tfib_E_scalbn : Z := 0x89424.
Definition tfib_A_subtf3 : Z := 0x88970.  Definition tfib_E_subtf3 : Z := 0x88980.
Definition tfib_A_addtf3 : Z := 0x88168.  Definition tfib_E_addtf3 : Z := 0x88934.
Definition tfib_A_fe_getround : Z := 0x88934.  Definition tfib_E_fe_getround : Z := 0x88964.
Definition tfib_A_fixunstfsi : Z := 0x8dcf0.  Definition tfib_E_fixunstfsi : Z := 0x8dd84.
Definition tfib_A_floatunsitf : Z := 0x8dd84.  Definition tfib_E_floatunsitf : Z := 0x8de70.
Definition tfib_A_fixtfsi : Z := 0x89424.  Definition tfib_E_fixtfsi : Z := 0x894cc.
Definition tfib_A_divtf3 : Z := 0x88a88.  Definition tfib_E_divtf3 : Z := 0x8938c.
Definition tfib_A_musl_vprintf : Z := 0x8e548.  Definition tfib_E_musl_vprintf : Z := 0x8e564.
Definition tfib_A_stdout_write : Z := 0x8b2f8.  Definition tfib_E_stdout_write : Z := 0x8b398.
Definition tfib_A_musl_memcmp : Z := 0x8ebc8.  Definition tfib_E_musl_memcmp : Z := 0x8ebf8.
Definition tfib_A_musl_memcpy : Z := 0x8ebf8.  Definition tfib_E_musl_memcpy : Z := 0x8effc.
Definition tfib_A_musl_memset : Z := 0x8effc.  Definition tfib_E_musl_memset : Z := 0x8f0f4.
Definition tfib_A_musl_strchr : Z := 0x8f0f4.  Definition tfib_E_musl_strchr : Z := 0x8f130.
Definition tfib_A_strchrnul : Z := 0x8f130.  Definition tfib_E_strchrnul : Z := 0x8f210.
Definition tfib_A_musl_strlen : Z := 0x8f248.  Definition tfib_E_musl_strlen : Z := 0x8f2d8.
Definition tfib_A_musl_strnlen : Z := 0x8f484.  Definition tfib_E_musl_strnlen : Z := 0x8f4c8.
Definition tfib_A_musl_memchr : Z := 0x8eafc.  Definition tfib_E_musl_memchr : Z := 0x8ebc8.
Definition tfib_A_lock : Z := 0x8f4c8.  Definition tfib_E_lock : Z := 0x8f750.
Definition tfib_A_unlock : Z := 0x8f750.  Definition tfib_E_unlock : Z := 0x8f7c4.
Definition tfib_A_sccp : Z := 0x8f7c4.  Definition tfib_E_sccp : Z := 0x8f7e8.
Definition tfib_A_syscall_cp : Z := 0x8f7e8.  Definition tfib_E_syscall_cp : Z := 0x8f7ec.
Definition tfib_A_tls_get_addr : Z := 0x8f7ec.  Definition tfib_E_tls_get_addr : Z := 0x8f810.
Definition tfib_A_pthread_atfork : Z := 0x8f828.  Definition tfib_E_pthread_atfork : Z := 0x8f8cc.
Definition tfib_A_mremap : Z := 0x89c78.  Definition tfib_E_mremap : Z := 0x89d4c.
Definition tfib_A_pthread_getspecific : Z := 0x908a0.  Definition tfib_E_pthread_getspecific : Z := 0x908bc.
Definition tfib_A_pthread_key_create : Z := 0x90c48.  Definition tfib_E_pthread_key_create : Z := 0x90d1c.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x90fc0.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x91064.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x91064.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x9106c.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x9106c.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x91180.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x91180.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x911ac.
Definition tfib_A_pthread_setspecific : Z := 0x911e4.  Definition tfib_E_pthread_setspecific : Z := 0x91218.
Definition tfib_A_set_thread_area : Z := 0x91220.  Definition tfib_E_set_thread_area : Z := 0x9122c.
Definition tfib_A_pthread_testcancel : Z := 0x91218.  Definition tfib_E_pthread_testcancel : Z := 0x9121c.

Definition tfib_A_musl_clock_gettime : Z := 0x91b4c.  Definition tfib_E_musl_clock_gettime : Z := 0x91c04.
Definition tfib_A_close : Z := 0x9421c.  Definition tfib_E_close : Z := 0x94270.
Definition tfib_A_musl_read : Z := 0x942fc.  Definition tfib_E_musl_read : Z := 0x94330.
Definition tfib_A_vm_wait : Z := 0x9185c.  Definition tfib_E_vm_wait : Z := 0x918ac.
Definition tfib_D_str_sealed : Z := 0x117f6.
Definition tfib_D_init_array_0_3 : Z := 0x95330.
Definition tfib_D_fini_array_0 : Z := 0x95350.
Definition tfib_D_GOT_common_flags : Z := 0x958b8.
Definition tfib_D_GOT_flags : Z := 0x958c0.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x958c8.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x958d0.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x958d8.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x958e0.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x96430.
Definition tfib_D_GOT_environ : Z := 0x96558.
Definition tfib_D_REAL_read : Z := 0x975f8.
Definition tfib_D_REAL_memcpy : Z := 0x97720.
Definition tfib_D_REAL_memset : Z := 0x97728.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9a218.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9b078.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0x9d878.
Definition tfib_D_asan_inited : Z := 0x9e558.
Definition tfib_D_replace_intrin_cached : Z := 0x9e559.
Definition tfib_D_kHighMemEnd : Z := 0x9e560.
Definition tfib_D_kMidMemBeg : Z := 0x9e568.
Definition tfib_D_kMidMemEnd : Z := 0x9e570.
Definition tfib_D_malloc_context_size : Z := 0x9e57c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x12f3a8.
Definition tfib_D_libc : Z := 0x5f0aa0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f3000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2f9e4.
Definition tfib_at_rw_lo : Z := 0x97000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x61b64.
Definition tfib_at_x_imemcpy : Z := 0x61ae8.
Definition tfib_at_x_memset : Z := 0x8effc.
Definition tfib_at_x_memcpy : Z := 0x8ebf8.
Definition tfib_at_x_memiszero : Z := 0x62094.
Definition tfib_at_x_istrncpy : Z := 0x61f90.
Definition tfib_at_x_sealed : Z := 0x117f6.
Definition tfib_at_x_popfree : Z := 0x35dd0.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x84a00.
Definition tfib_at_x_envscan_k : Z := 0x84a0c.
Definition tfib_at_x_pnscan : Z := 0x84ac4.
Definition tfib_at_x_pnscan_k : Z := 0x84ad0.
Definition tfib_at_stops_more : list Z := (0x33a44 :: 0x35068 :: 0x51e70 :: 0x58228 :: 0x5823c :: 0x58250 :: 0x5dbe0 :: 0x5dcb0 :: 0x6b1dc :: 0x6c0e8 :: 0x6c278 :: 0x75fd0 :: nil)%list.
