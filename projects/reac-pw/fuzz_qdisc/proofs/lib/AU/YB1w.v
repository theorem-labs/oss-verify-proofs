(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1w.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1w.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x225cc.   (* .rodata of knock's asan pin (sha256 61768cf4739b...), read from the section header: 0x102d0..0x22564; the donor's 0x2278c was cgif's ASAN-UBSAN .rodata end, 0x40 short of cgif's own 0x227cc *)
Definition tfib_text_lo : Z := 0x2f9ec.  Definition tfib_text_hi : Z := 0x94368.
Definition tfib_init_array_lo : Z := 0x95368.  Definition tfib_init_array_hi : Z := 0x95388.
Definition tfib_fini_array_lo : Z := 0x95388.  Definition tfib_fini_array_hi : Z := 0x95398.
Definition tfib_preinit_array_lo : Z := 0x95398.  Definition tfib_preinit_array_hi : Z := 0x953a0.
Definition tfib_data_rel_ro_lo : Z := 0x953a0.  Definition tfib_data_rel_ro_hi : Z := 0x958a0.
Definition tfib_got_lo : Z := 0x958a0.  Definition tfib_got_hi : Z := 0x965f8.
Definition tfib_data_lo : Z := 0x975f8.  Definition tfib_data_hi : Z := 0x9a1a8.
Definition tfib_bss_lo : Z := 0x9a200.  Definition tfib_bss_hi : Z := 0x5f2130.
Definition tfib_tbss_lo : Z := 0x94368.  Definition tfib_tbss_hi : Z := 0x9437c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f3000.
Definition tfib_entry : Z := 0x2f9ec.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2f9ec.  Definition tfib_E_start : Z := 0x2fa08.
Definition tfib_A_start_c : Z := 0x2fa08.  Definition tfib_E_start_c : Z := 0x2fa34.
Definition tfib_A_do_init : Z := 0x2fa34.  Definition tfib_E_do_init : Z := 0x2faa8.
Definition tfib_A_do_fini : Z := 0x2faa8.  Definition tfib_E_do_fini : Z := 0x2fb38.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x2fb38.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x2fb74.
Definition tfib_A_InitializeAllocator : Z := 0x2fce4.  Definition tfib_E_InitializeAllocator : Z := 0x2fcfc.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x2fcfc.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x2fe68.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x303c4.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x30520.
Definition tfib_A_asan_free : Z := 0x308f4.  Definition tfib_E_asan_free : Z := 0x3091c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3091c.  Definition tfib_E_Allocator_Deallocate : Z := 0x30bd4.
Definition tfib_A_asan_malloc : Z := 0x30bd4.  Definition tfib_E_asan_malloc : Z := 0x30c30.
Definition tfib_A_Allocator_Allocate : Z := 0x30c30.  Definition tfib_E_Allocator_Allocate : Z := 0x315b8.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x31cf0.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x31e34.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x31f20.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x31f7c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x31f7c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x321cc.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x321cc.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x322c0.
Definition tfib_A_Allocator_CheckOptions : Z := 0x322c0.  Definition tfib_E_Allocator_CheckOptions : Z := 0x323a8.
Definition tfib_A_Quarantine_Recycle : Z := 0x327dc.  Definition tfib_E_Quarantine_Recycle : Z := 0x329c0.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x329c0.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x32b44.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x32c7c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x32f00.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x32f00.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33080.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33080.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33248.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33248.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33414.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x33414.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x334b4.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x334b4.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x335b8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x338e0.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33a28.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x33a28.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x33a60.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x341f8.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x344e0.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x34bb8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x34d30.
Definition tfib_A_Quarantine_Put : Z := 0x34d30.  Definition tfib_E_Quarantine_Put : Z := 0x34ee0.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x34ee0.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x350c4.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x350c4.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x3539c.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x3539c.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x35814.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35814.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35914.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35914.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x35c1c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x35c1c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x35f8c.
Definition tfib_A_RZSize2Log : Z := 0x35f8c.  Definition tfib_E_RZSize2Log : Z := 0x360a4.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x363ac.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x364a8.
Definition tfib_A_AsanDeactivate : Z := 0x364a8.  Definition tfib_E_AsanDeactivate : Z := 0x36590.
Definition tfib_A_AsanActivate : Z := 0x36590.  Definition tfib_E_AsanActivate : Z := 0x3666c.
Definition tfib_A_FlagHandler_Parse : Z := 0x36b48.  Definition tfib_E_FlagHandler_Parse : Z := 0x36c30.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3b6e8.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3b7c0.
Definition tfib_A_FakeStack_Create : Z := 0x3b7c0.  Definition tfib_E_FakeStack_Create : Z := 0x3b8ac.
Definition tfib_A_check_slots : Z := 0x7e8a4.  Definition tfib_E_check_slots : Z := 0x7e91c.  Definition tfib_A_asan_module_dtor : Z := 0x7e954.  Definition tfib_E_asan_module_dtor : Z := 0x7e984.  Definition tfib_A_reac_qdisc_etf_catchup_slots : Z := 0x7e984.  Definition tfib_E_reac_qdisc_etf_catchup_slots : Z := 0x7e9e4.
Definition tfib_A_SetTLSFakeStack : Z := 0x3bc9c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3bccc.


Definition tfib_A_InitializeFlags : Z := 0x3bccc.  Definition tfib_E_InitializeFlags : Z := 0x3ccf8.
Definition tfib_A_asan_register_globals : Z := 0x3d404.  Definition tfib_E_asan_register_globals : Z := 0x3e220.
Definition tfib_A_asan_unregister_globals : Z := 0x3e220.  Definition tfib_E_asan_unregister_globals : Z := 0x3e7ec.
Definition tfib_A_asan_register_elf_globals : Z := 0x3e7ec.  Definition tfib_E_asan_register_elf_globals : Z := 0x3e858.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x3ef40.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x3f1b0.
Definition tfib_A_asan_after_dynamic_init : Z := 0x3f1b0.  Definition tfib_E_asan_after_dynamic_init : Z := 0x3f4b8.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x3fc2c.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x3fd7c.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x40798.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x408b0.
Definition tfib_A_strlen : Z := 0x408b0.  Definition tfib_E_strlen : Z := 0x408b4.
Definition tfib_A_strnlen : Z := 0x408b4.  Definition tfib_E_strnlen : Z := 0x408b8.
Definition tfib_A_strcmp : Z := 0x408b8.  Definition tfib_E_strcmp : Z := 0x408bc.
Definition tfib_A_strchr : Z := 0x408bc.  Definition tfib_E_strchr : Z := 0x408c0.
Definition tfib_A_memcmp : Z := 0x408c0.  Definition tfib_E_memcmp : Z := 0x408c4.
Definition tfib_A_memchr : Z := 0x408c4.  Definition tfib_E_memchr : Z := 0x408c8.
Definition tfib_A_frexpl : Z := 0x408c8.  Definition tfib_E_frexpl : Z := 0x408cc.
Definition tfib_A_read : Z := 0x408cc.  Definition tfib_E_read : Z := 0x408d0.
Definition tfib_A_fwrite : Z := 0x408d0.  Definition tfib_E_fwrite : Z := 0x408d4.
Definition tfib_A_time : Z := 0x408d4.  Definition tfib_E_time : Z := 0x408d8.
Definition tfib_A_gmtime_r : Z := 0x408d8.  Definition tfib_E_gmtime_r : Z := 0x408dc.
Definition tfib_A_vprintf : Z := 0x408dc.  Definition tfib_E_vprintf : Z := 0x408e0.
Definition tfib_A_vfprintf : Z := 0x408e0.  Definition tfib_E_vfprintf : Z := 0x408e4.
Definition tfib_A_vsnprintf : Z := 0x408e4.  Definition tfib_E_vsnprintf : Z := 0x408e8.
Definition tfib_A_fprintf : Z := 0x408e8.  Definition tfib_E_fprintf : Z := 0x408ec.
Definition tfib_A_snprintf : Z := 0x408ec.  Definition tfib_E_snprintf : Z := 0x408f0.
Definition tfib_A_clock_gettime : Z := 0x408f0.  Definition tfib_E_clock_gettime : Z := 0x408f4.
Definition tfib_A_wcrtomb : Z := 0x408f4.  Definition tfib_E_wcrtomb : Z := 0x408f8.
Definition tfib_A_wctomb : Z := 0x408f8.  Definition tfib_E_wctomb : Z := 0x408fc.
Definition tfib_A_strerror : Z := 0x408fc.  Definition tfib_E_strerror : Z := 0x40900.
Definition tfib_A__exit : Z := 0x40900.  Definition tfib_E__exit : Z := 0x40904.
Definition tfib_A_pthread_attr_getstack : Z := 0x40904.  Definition tfib_E_pthread_attr_getstack : Z := 0x40908.
Definition tfib_A___tls_get_addr : Z := 0x40908.  Definition tfib_E___tls_get_addr : Z := 0x4090c.
Definition tfib_A_fflush : Z := 0x4090c.  Definition tfib_E_fflush : Z := 0x40910.
Definition tfib_A_sem_init : Z := 0x40910.  Definition tfib_E_sem_init : Z := 0x40914.
Definition tfib_A_sem_destroy : Z := 0x40914.  Definition tfib_E_sem_destroy : Z := 0x40918.
Definition tfib_A_sem_wait : Z := 0x40918.  Definition tfib_E_sem_wait : Z := 0x4091c.
Definition tfib_A_sem_trywait : Z := 0x4091c.  Definition tfib_E_sem_trywait : Z := 0x40920.
Definition tfib_A_sem_timedwait : Z := 0x40920.  Definition tfib_E_sem_timedwait : Z := 0x40924.
Definition tfib_A_sem_post : Z := 0x40924.  Definition tfib_E_sem_post : Z := 0x40928.
Definition tfib_A_pthread_setcancelstate : Z := 0x40928.  Definition tfib_E_pthread_setcancelstate : Z := 0x4092c.
Definition tfib_A_send : Z := 0x4092c.  Definition tfib_E_send : Z := 0x40930.
Definition tfib_A_sendto : Z := 0x40930.  Definition tfib_E_sendto : Z := 0x40934.
Definition tfib_A_sigaltstack : Z := 0x40934.  Definition tfib_E_sigaltstack : Z := 0x40938.
Definition tfib_A_sigaction : Z := 0x40938.  Definition tfib_E_sigaction : Z := 0x4093c.
Definition tfib_A_icpt_strlen : Z := 0x4093c.  Definition tfib_E_icpt_strlen : Z := 0x40bd0.
Definition tfib_A_icpt_strnlen : Z := 0x40bd0.  Definition tfib_E_icpt_strnlen : Z := 0x40e64.
Definition tfib_A_icpt_strcmp : Z := 0x40e68.  Definition tfib_E_icpt_strcmp : Z := 0x41398.
Definition tfib_A_icpt_strchr : Z := 0x41398.  Definition tfib_E_icpt_strchr : Z := 0x41678.
Definition tfib_A_icpt_memcmp : Z := 0x41f10.  Definition tfib_E_icpt_memcmp : Z := 0x41fcc.
Definition tfib_A_icpt_memchr : Z := 0x41fcc.  Definition tfib_E_icpt_memchr : Z := 0x4229c.
Definition tfib_A_icpt_frexpl : Z := 0x4229c.  Definition tfib_E_icpt_frexpl : Z := 0x42514.
Definition tfib_A_icpt_read : Z := 0x42514.  Definition tfib_E_icpt_read : Z := 0x42784.
Definition tfib_A_icpt_fwrite : Z := 0x42784.  Definition tfib_E_icpt_fwrite : Z := 0x429f8.
Definition tfib_A_icpt_time : Z := 0x429f8.  Definition tfib_E_icpt_time : Z := 0x42c94.
Definition tfib_A_icpt_gmtime_r : Z := 0x42e9c.  Definition tfib_E_icpt_gmtime_r : Z := 0x430dc.
Definition tfib_A_icpt_vprintf : Z := 0x430dc.  Definition tfib_E_icpt_vprintf : Z := 0x43178.
Definition tfib_A_printf_common : Z := 0x43178.  Definition tfib_E_printf_common : Z := 0x43c40.
Definition tfib_A_icpt_vfprintf : Z := 0x43c40.  Definition tfib_E_icpt_vfprintf : Z := 0x43cf4.
Definition tfib_A_icpt_vsnprintf : Z := 0x43cf4.  Definition tfib_E_icpt_vsnprintf : Z := 0x4400c.
Definition tfib_A_icpt_fprintf : Z := 0x4400c.  Definition tfib_E_icpt_fprintf : Z := 0x440e4.
Definition tfib_A_icpt_clock_gettime : Z := 0x44188.  Definition tfib_E_icpt_clock_gettime : Z := 0x443e0.
Definition tfib_A_icpt_wcrtomb : Z := 0x443e0.  Definition tfib_E_icpt_wcrtomb : Z := 0x44950.
Definition tfib_A_icpt_wctomb : Z := 0x44950.  Definition tfib_E_icpt_wctomb : Z := 0x44cac.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x44d78.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45160.
Definition tfib_A_icpt_tls_get_addr : Z := 0x4516c.  Definition tfib_E_icpt_tls_get_addr : Z := 0x451e8.
Definition tfib_A_icpt_sem_timedwait : Z := 0x453f4.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4568c.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x456bc.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x458e4.
Definition tfib_A_icpt_send : Z := 0x458e4.  Definition tfib_E_icpt_send : Z := 0x45b98.
Definition tfib_A_icpt_sendto : Z := 0x45b98.  Definition tfib_E_icpt_sendto : Z := 0x45e5c.
Definition tfib_A_icpt_sigaltstack : Z := 0x45e5c.  Definition tfib_E_icpt_sigaltstack : Z := 0x460b8.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4618c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4633c.
Definition tfib_A_format_get_value_size : Z := 0x4633c.  Definition tfib_E_format_get_value_size : Z := 0x464d4.
Definition tfib_A_ioctl_table_fill : Z := 0x47080.  Definition tfib_E_ioctl_table_fill : Z := 0x4fd58.
Definition tfib_A_Sort : Z := 0x4fd58.  Definition tfib_E_Sort : Z := 0x4feb4.
Definition tfib_A_memset : Z := 0x4feb4.  Definition tfib_E_memset : Z := 0x4feb8.
Definition tfib_A_memcpy : Z := 0x4feb8.  Definition tfib_E_memcpy : Z := 0x4febc.

Definition tfib_A_icpt_memset : Z := 0x4febc.  Definition tfib_E_icpt_memset : Z := 0x501ac.
Definition tfib_A_icpt_memcpy : Z := 0x501ac.  Definition tfib_E_icpt_memcpy : Z := 0x5079c.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x5079c.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x507d4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x507d4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x507d8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x507d8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x507dc.
Definition tfib_A_FindDynamicShadowStart : Z := 0x507dc.  Definition tfib_E_FindDynamicShadowStart : Z := 0x5083c.
Definition tfib_A_MemToShadow_510c4 : Z := 0x50888.  Definition tfib_E_MemToShadow_510c4 : Z := 0x509c4.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x509c4.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x509c8.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x509c8.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x50b30.
Definition tfib_A_free : Z := 0x50b30.  Definition tfib_E_free : Z := 0x50b34.
Definition tfib_A_malloc : Z := 0x50b34.  Definition tfib_E_malloc : Z := 0x50b38.
Definition tfib_A_icpt_free : Z := 0x50b38.  Definition tfib_E_icpt_free : Z := 0x50d08.
Definition tfib_A_icpt_malloc : Z := 0x50d08.  Definition tfib_E_icpt_malloc : Z := 0x50e64.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x50e64.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x50f30.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x50f30.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x50f34.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x50f34.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x51034.
Definition tfib_A_HeapProfile_Print : Z := 0x5135c.  Definition tfib_E_HeapProfile_Print : Z := 0x514c8.
Definition tfib_A_SetCanPoisonMemory : Z := 0x519b0.  Definition tfib_E_SetCanPoisonMemory : Z := 0x519c0.
Definition tfib_A_CanPoisonMemory : Z := 0x519c0.  Definition tfib_E_CanPoisonMemory : Z := 0x519d4.
Definition tfib_A_PoisonShadow : Z := 0x519d4.  Definition tfib_E_PoisonShadow : Z := 0x51ed0.
Definition tfib_A_MemToShadow_5270c : Z := 0x51ed0.  Definition tfib_E_MemToShadow_5270c : Z := 0x5200c.
Definition tfib_A_asan_poison_memory_region : Z := 0x5200c.  Definition tfib_E_asan_poison_memory_region : Z := 0x521ac.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x521ac.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x5232c.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5235c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x526a0.
Definition tfib_A_AsanTSDInit : Z := 0x52ac0.  Definition tfib_E_AsanTSDInit : Z := 0x52b3c.
Definition tfib_A_AsanTSDGet : Z := 0x52b3c.  Definition tfib_E_AsanTSDGet : Z := 0x52b7c.
Definition tfib_A_AsanTSDSet : Z := 0x52b7c.  Definition tfib_E_AsanTSDSet : Z := 0x52bbc.
Definition tfib_A_PlatformTSDDtor : Z := 0x52bbc.  Definition tfib_E_PlatformTSDDtor : Z := 0x52c40.
Definition tfib_A_InstallAtForkHandler : Z := 0x52c40.  Definition tfib_E_InstallAtForkHandler : Z := 0x52c5c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x52cbc.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x52d00.
Definition tfib_A_ReportDeadlySignal : Z := 0x53418.  Definition tfib_E_ReportDeadlySignal : Z := 0x53624.
Definition tfib_A_ReportDoubleFree : Z := 0x53d2c.  Definition tfib_E_ReportDoubleFree : Z := 0x53fbc.
Definition tfib_A_ReportGenericError : Z := 0x55898.  Definition tfib_E_ReportGenericError : Z := 0x56154.
Definition tfib_A_AsanInited : Z := 0x568e0.  Definition tfib_E_AsanInited : Z := 0x568f8.
Definition tfib_A_asan_report_load1 : Z := 0x568f8.  Definition tfib_E_asan_report_load1 : Z := 0x56948.
Definition tfib_A_asan_report_exp_load1 : Z := 0x56948.  Definition tfib_E_asan_report_exp_load1 : Z := 0x56998.
Definition tfib_A_asan_report_load2 : Z := 0x56998.  Definition tfib_E_asan_report_load2 : Z := 0x569e8.
Definition tfib_A_asan_report_exp_load2 : Z := 0x569e8.  Definition tfib_E_asan_report_exp_load2 : Z := 0x56a38.
Definition tfib_A_asan_report_load4 : Z := 0x56a38.  Definition tfib_E_asan_report_load4 : Z := 0x56a88.
Definition tfib_A_asan_report_exp_load4 : Z := 0x56a88.  Definition tfib_E_asan_report_exp_load4 : Z := 0x56ad8.
Definition tfib_A_asan_report_load8 : Z := 0x56ad8.  Definition tfib_E_asan_report_load8 : Z := 0x56b28.
Definition tfib_A_asan_report_exp_load8 : Z := 0x56b28.  Definition tfib_E_asan_report_exp_load8 : Z := 0x56b78.
Definition tfib_A_asan_report_load16 : Z := 0x56b78.  Definition tfib_E_asan_report_load16 : Z := 0x56bc8.
Definition tfib_A_asan_report_exp_load16 : Z := 0x56bc8.  Definition tfib_E_asan_report_exp_load16 : Z := 0x56c18.
Definition tfib_A_asan_report_store1 : Z := 0x56c18.  Definition tfib_E_asan_report_store1 : Z := 0x56c68.
Definition tfib_A_asan_report_exp_store1 : Z := 0x56c68.  Definition tfib_E_asan_report_exp_store1 : Z := 0x56cb8.
Definition tfib_A_asan_report_store2 : Z := 0x56cb8.  Definition tfib_E_asan_report_store2 : Z := 0x56d08.
Definition tfib_A_asan_report_exp_store2 : Z := 0x56d08.  Definition tfib_E_asan_report_exp_store2 : Z := 0x56d58.
Definition tfib_A_asan_report_store4 : Z := 0x56d58.  Definition tfib_E_asan_report_store4 : Z := 0x56da8.
Definition tfib_A_asan_report_exp_store4 : Z := 0x56da8.  Definition tfib_E_asan_report_exp_store4 : Z := 0x56df8.
Definition tfib_A_asan_report_store8 : Z := 0x56df8.  Definition tfib_E_asan_report_store8 : Z := 0x56e48.
Definition tfib_A_asan_report_exp_store8 : Z := 0x56e48.  Definition tfib_E_asan_report_exp_store8 : Z := 0x56e98.
Definition tfib_A_asan_report_store16 : Z := 0x56e98.  Definition tfib_E_asan_report_store16 : Z := 0x56ee8.
Definition tfib_A_asan_report_exp_store16 : Z := 0x56ee8.  Definition tfib_E_asan_report_exp_store16 : Z := 0x56f38.
Definition tfib_A_asan_report_load_n : Z := 0x56f38.  Definition tfib_E_asan_report_load_n : Z := 0x56f88.
Definition tfib_A_asan_report_exp_load_n : Z := 0x56f88.  Definition tfib_E_asan_report_exp_load_n : Z := 0x56fd8.
Definition tfib_A_asan_report_store_n : Z := 0x56fd8.  Definition tfib_E_asan_report_store_n : Z := 0x57028.
Definition tfib_A_asan_report_exp_store_n : Z := 0x57028.  Definition tfib_E_asan_report_exp_store_n : Z := 0x57078.
Definition tfib_A_InitializeHighMemEnd : Z := 0x57078.  Definition tfib_E_InitializeHighMemEnd : Z := 0x570f8.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x570f8.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x574ac.
Definition tfib_A_AsanInitInternal : Z := 0x5753c.  Definition tfib_E_AsanInitInternal : Z := 0x577f0.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x577f0.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x57890.
Definition tfib_A_asan_set_death_callback : Z := 0x57a58.  Definition tfib_E_asan_set_death_callback : Z := 0x57a5c.
Definition tfib_A_asan_init : Z := 0x57a5c.  Definition tfib_E_asan_init : Z := 0x57af0.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x57af0.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x57af4.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x57af4.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x57b58.
Definition tfib_A_OnLowLevelAllocate : Z := 0x57ccc.  Definition tfib_E_OnLowLevelAllocate : Z := 0x57cd4.
Definition tfib_A_force_interface_symbols : Z := 0x57d58.  Definition tfib_E_force_interface_symbols : Z := 0x58080.
Definition tfib_A_SealedReserveShadow : Z := 0x58080.  Definition tfib_E_SealedReserveShadow : Z := 0x58260.
Definition tfib_A_InitializeShadowMemory : Z := 0x58260.  Definition tfib_E_InitializeShadowMemory : Z := 0x58568.
Definition tfib_A_SetMallocContextSize : Z := 0x58568.  Definition tfib_E_SetMallocContextSize : Z := 0x58578.
Definition tfib_A_GetMallocContextSize : Z := 0x58578.  Definition tfib_E_GetMallocContextSize : Z := 0x58588.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x58588.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x586d8.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x58ab8.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x58d58.
Definition tfib_A_GetCurrentThreadStats : Z := 0x591bc.  Definition tfib_E_GetCurrentThreadStats : Z := 0x591f4.
Definition tfib_A_asan_default_suppressions : Z := 0x5949c.  Definition tfib_E_asan_default_suppressions : Z := 0x594a8.
Definition tfib_A_InitializeSuppressions : Z := 0x594a8.  Definition tfib_E_InitializeSuppressions : Z := 0x59534.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x59534.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5959c.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5959c.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x59614.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x59614.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5967c.
Definition tfib_A_IsAddrSuppressed : Z := 0x5967c.  Definition tfib_E_IsAddrSuppressed : Z := 0x597c8.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x59a54.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x59a60.
Definition tfib_A_AsanThread_Create : Z := 0x59be0.  Definition tfib_E_AsanThread_Create : Z := 0x59d7c.
Definition tfib_A_AsanThread_Destroy : Z := 0x59dd8.  Definition tfib_E_AsanThread_Destroy : Z := 0x59ff0.
Definition tfib_A_GetCurrentThread : Z := 0x59ff0.  Definition tfib_E_GetCurrentThread : Z := 0x5a010.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a010.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a1b4.
Definition tfib_A_AsanThread_stack_top : Z := 0x5a1b4.  Definition tfib_E_AsanThread_stack_top : Z := 0x5a20c.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5a20c.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5a264.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5a264.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5a494.
Definition tfib_A_AsanThread_Init : Z := 0x5a494.  Definition tfib_E_AsanThread_Init : Z := 0x5a888.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5a888.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5a994.
Definition tfib_A_CreateMainThread : Z := 0x5a9c8.  Definition tfib_E_CreateMainThread : Z := 0x5aad8.
Definition tfib_A_SetCurrentThread : Z := 0x5aad8.  Definition tfib_E_SetCurrentThread : Z := 0x5abb8.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5adbc.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5aef8.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5bbcc.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5bbd0.
Definition tfib_A_GetAsanThreadContext : Z := 0x5bbd8.  Definition tfib_E_GetAsanThreadContext : Z := 0x5be18.
Definition tfib_A_internal_allocator : Z := 0x5c06c.  Definition tfib_E_internal_allocator : Z := 0x5c1c4.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5c3b0.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5c3bc.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5c3bc.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5c508.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5c508.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5c554.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5c554.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5c560.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5c590.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5c59c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5c59c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5c5a8.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5c5a8.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5c5b8.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5c5c4.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5c890.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5c890.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5cc50.
Definition tfib_A_SealedSetInitFrame : Z := 0x5dbac.  Definition tfib_E_SealedSetInitFrame : Z := 0x5dbb8.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5dbb8.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5dc90.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5dc90.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5dd2c.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5e250.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5e294.
Definition tfib_A_DecreaseTotalMmap : Z := 0x5e294.  Definition tfib_E_DecreaseTotalMmap : Z := 0x5e2b8.
Definition tfib_A_CacheBinaryName : Z := 0x5e50c.  Definition tfib_E_CacheBinaryName : Z := 0x5e620.
Definition tfib_A_RunMallocHooks : Z := 0x5e7c4.  Definition tfib_E_RunMallocHooks : Z := 0x5e87c.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x5e87c.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x5e880.
Definition tfib_A_RunFreeHooks : Z := 0x5e880.  Definition tfib_E_RunFreeHooks : Z := 0x5e92c.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x5e92c.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x5e934.
Definition tfib_A_sanitizer_free_hook : Z := 0x5e934.  Definition tfib_E_sanitizer_free_hook : Z := 0x5e938.
Definition tfib_A_WaitForDebugger : Z := 0x5e960.  Definition tfib_E_WaitForDebugger : Z := 0x5e9ac.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x5ec70.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x5eeb0.
Definition tfib_A_sanitizer_set_report_path : Z := 0x5f4ac.  Definition tfib_E_sanitizer_set_report_path : Z := 0x5f4c4.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x5f4c4.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x5f608.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x5f608.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x5f610.
Definition tfib_A_RegisterCommonFlags : Z := 0x5f958.  Definition tfib_E_RegisterCommonFlags : Z := 0x60bfc.
Definition tfib_A_InitializeCommonFlags : Z := 0x60bfc.  Definition tfib_E_InitializeCommonFlags : Z := 0x60c20.
Definition tfib_A_FlagParser_parse_flag : Z := 0x610d4.  Definition tfib_E_FlagParser_parse_flag : Z := 0x613e4.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x613e4.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x61528.
Definition tfib_A_FlagParser_ParseString : Z := 0x61528.  Definition tfib_E_FlagParser_ParseString : Z := 0x6161c.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x617b0.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x61810.
Definition tfib_A_FlagParser_FlagParser : Z := 0x61810.  Definition tfib_E_FlagParser_FlagParser : Z := 0x61850.
Definition tfib_A_internal_atoll : Z := 0x61850.  Definition tfib_E_internal_atoll : Z := 0x6193c.
Definition tfib_A_internal_simple_strtoll : Z := 0x6193c.  Definition tfib_E_internal_simple_strtoll : Z := 0x61a98.
Definition tfib_A_internal_memchr : Z := 0x61a98.  Definition tfib_E_internal_memchr : Z := 0x61ab8.
Definition tfib_A_internal_memcmp : Z := 0x61ab8.  Definition tfib_E_internal_memcmp : Z := 0x61af0.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x61af0.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x61b14.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x61b14.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x61b6c.
Definition tfib_A_sanitizer_internal_memset : Z := 0x61b6c.  Definition tfib_E_sanitizer_internal_memset : Z := 0x61bcc.
Definition tfib_A_internal_strcspn : Z := 0x61bcc.  Definition tfib_E_internal_strcspn : Z := 0x61c20.
Definition tfib_A_internal_strchr : Z := 0x61c20.  Definition tfib_E_internal_strchr : Z := 0x61c54.
Definition tfib_A_internal_strdup : Z := 0x61c54.  Definition tfib_E_internal_strdup : Z := 0x61cc0.
Definition tfib_A_internal_strlen : Z := 0x61cc0.  Definition tfib_E_internal_strlen : Z := 0x61cdc.
Definition tfib_A_internal_strcmp : Z := 0x61cdc.  Definition tfib_E_internal_strcmp : Z := 0x61d20.
Definition tfib_A_internal_strncmp : Z := 0x61d20.  Definition tfib_E_internal_strncmp : Z := 0x61d6c.
Definition tfib_A_internal_strchrnul : Z := 0x61d6c.  Definition tfib_E_internal_strchrnul : Z := 0x61db4.
Definition tfib_A_internal_strrchr : Z := 0x61db4.  Definition tfib_E_internal_strrchr : Z := 0x61df4.
Definition tfib_A_internal_strnlen : Z := 0x61f24.  Definition tfib_E_internal_strnlen : Z := 0x61f54.
Definition tfib_A_internal_strncpy : Z := 0x61f98.  Definition tfib_E_internal_strncpy : Z := 0x62008.
Definition tfib_A_internal_strstr : Z := 0x62008.  Definition tfib_E_internal_strstr : Z := 0x6209c.
Definition tfib_A_mem_is_zero : Z := 0x6209c.  Definition tfib_E_mem_is_zero : Z := 0x62150.
Definition tfib_A_internal_sigprocmask : Z := 0x62150.  Definition tfib_E_internal_sigprocmask : Z := 0x62160.
Definition tfib_A_BlockSignals : Z := 0x62160.  Definition tfib_E_BlockSignals : Z := 0x62340.
Definition tfib_A_internal_iserror : Z := 0x6234c.  Definition tfib_E_internal_iserror : Z := 0x6236c.
Definition tfib_A_internal_mmap : Z := 0x6236c.  Definition tfib_E_internal_mmap : Z := 0x62378.
Definition tfib_A_internal_munmap : Z := 0x62378.  Definition tfib_E_internal_munmap : Z := 0x62384.
Definition tfib_A_internal_mprotect : Z := 0x62384.  Definition tfib_E_internal_mprotect : Z := 0x62394.
Definition tfib_A_internal_madvise : Z := 0x62394.  Definition tfib_E_internal_madvise : Z := 0x623c0.
Definition tfib_A_internal_close : Z := 0x623c0.  Definition tfib_E_internal_close : Z := 0x623cc.
Definition tfib_A_internal_open : Z := 0x623cc.  Definition tfib_E_internal_open : Z := 0x623f0.
Definition tfib_A_internal_read : Z := 0x623f0.  Definition tfib_E_internal_read : Z := 0x62428.
Definition tfib_A_internal_write : Z := 0x62428.  Definition tfib_E_internal_write : Z := 0x62460.
Definition tfib_A_internal_ftruncate : Z := 0x62460.  Definition tfib_E_internal_ftruncate : Z := 0x62498.
Definition tfib_A_internal_dup : Z := 0x62498.  Definition tfib_E_internal_dup : Z := 0x624a4.
Definition tfib_A_internal_dup2 : Z := 0x624a4.  Definition tfib_E_internal_dup2 : Z := 0x624b4.
Definition tfib_A_internal_unlink : Z := 0x624b4.  Definition tfib_E_internal_unlink : Z := 0x624cc.
Definition tfib_A_internal_sched_yield : Z := 0x624cc.  Definition tfib_E_internal_sched_yield : Z := 0x624d8.
Definition tfib_A_internal_usleep : Z := 0x624d8.  Definition tfib_E_internal_usleep : Z := 0x62524.
Definition tfib_A_internal_execve : Z := 0x62524.  Definition tfib_E_internal_execve : Z := 0x62530.
Definition tfib_A_internal_exit : Z := 0x62530.  Definition tfib_E_internal_exit : Z := 0x62544.
Definition tfib_A_FileExists : Z := 0x62544.  Definition tfib_E_FileExists : Z := 0x625c4.
Definition tfib_A_DirExists : Z := 0x625c4.  Definition tfib_E_DirExists : Z := 0x62628.
Definition tfib_A_GetTid : Z := 0x62628.  Definition tfib_E_GetTid : Z := 0x62634.
Definition tfib_A_GetEnv : Z := 0x62634.  Definition tfib_E_GetEnv : Z := 0x62764.
Definition tfib_A_FutexWait : Z := 0x62868.  Definition tfib_E_FutexWait : Z := 0x6288c.
Definition tfib_A_FutexWake : Z := 0x6288c.  Definition tfib_E_FutexWake : Z := 0x628b0.
Definition tfib_A_internal_ptrace : Z := 0x628b0.  Definition tfib_E_internal_ptrace : Z := 0x628bc.
Definition tfib_A_internal_waitpid : Z := 0x628bc.  Definition tfib_E_internal_waitpid : Z := 0x628cc.
Definition tfib_A_internal_getpid : Z := 0x628cc.  Definition tfib_E_internal_getpid : Z := 0x628d8.
Definition tfib_A_internal_getppid : Z := 0x628d8.  Definition tfib_E_internal_getppid : Z := 0x628e4.
Definition tfib_A_internal_prctl : Z := 0x628e4.  Definition tfib_E_internal_prctl : Z := 0x628f0.
Definition tfib_A_internal_sigaltstack : Z := 0x628f0.  Definition tfib_E_internal_sigaltstack : Z := 0x628fc.
Definition tfib_A_internal_fork : Z := 0x628fc.  Definition tfib_E_internal_fork : Z := 0x62914.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x62914.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x62a40.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x62c18.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x63014.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x63180.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x63298.
Definition tfib_A_GetPageSize : Z := 0x63298.  Definition tfib_E_GetPageSize : Z := 0x632a0.
Definition tfib_A_ReadBinaryName : Z := 0x632a0.  Definition tfib_E_ReadBinaryName : Z := 0x6334c.
Definition tfib_A_ReadLongProcessName : Z := 0x6334c.  Definition tfib_E_ReadLongProcessName : Z := 0x6346c.
Definition tfib_A_internal_clone : Z := 0x63534.  Definition tfib_E_internal_clone : Z := 0x635b4.
Definition tfib_A_GetHandleSignalMode : Z := 0x635b4.  Definition tfib_E_GetHandleSignalMode : Z := 0x63610.
Definition tfib_A_internal_start_thread : Z := 0x63610.  Definition tfib_E_internal_start_thread : Z := 0x636dc.
Definition tfib_A_InitializePlatformEarly : Z := 0x637d8.  Definition tfib_E_InitializePlatformEarly : Z := 0x637dc.
Definition tfib_A_CheckASLR : Z := 0x637dc.  Definition tfib_E_CheckASLR : Z := 0x637e0.
Definition tfib_A_GetMmapGranularity : Z := 0x63a2c.  Definition tfib_E_GetMmapGranularity : Z := 0x63a30.
Definition tfib_A_ErrorIsOOM : Z := 0x63a30.  Definition tfib_E_ErrorIsOOM : Z := 0x63a3c.
Definition tfib_A_MmapOrDie : Z := 0x63a3c.  Definition tfib_E_MmapOrDie : Z := 0x63b48.
Definition tfib_A_MmapNamed : Z := 0x63b48.  Definition tfib_E_MmapNamed : Z := 0x63bbc.
Definition tfib_A_UnmapOrDie : Z := 0x63bbc.  Definition tfib_E_UnmapOrDie : Z := 0x63c38.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x63c38.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x63d48.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x63f74.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x64078.
Definition tfib_A_MmapFixedOrDie : Z := 0x64078.  Definition tfib_E_MmapFixedOrDie : Z := 0x64084.
Definition tfib_A_MmapFixedImpl : Z := 0x64084.  Definition tfib_E_MmapFixedImpl : Z := 0x641fc.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x641fc.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x64208.
Definition tfib_A_CloseFile : Z := 0x643f4.  Definition tfib_E_CloseFile : Z := 0x643f8.
Definition tfib_A_GetNamedMappingFd : Z := 0x64718.  Definition tfib_E_GetNamedMappingFd : Z := 0x64924.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x64edc.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x64ee8.
Definition tfib_A_Printf : Z := 0x64eec.  Definition tfib_E_Printf : Z := 0x64f38.
Definition tfib_A_SharedPrintfCode : Z := 0x64f38.  Definition tfib_E_SharedPrintfCode : Z := 0x64f94.
Definition tfib_A_Report : Z := 0x64f94.  Definition tfib_E_Report : Z := 0x64fe0.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x66ad8.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x66b34.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x66b34.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x66d70.
Definition tfib_A_SuppressionContext_Parse : Z := 0x66d70.  Definition tfib_E_SuppressionContext_Parse : Z := 0x67094.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x67634.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x67704.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x67704.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x67a54.
Definition tfib_A_DTLS_Get : Z := 0x67a54.  Definition tfib_E_DTLS_Get : Z := 0x67a64.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x67ca0.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x67ce4.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x67ce4.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x67d44.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x67d44.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x681bc.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x68a7c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x68da0.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x68da8.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x68eac.
Definition tfib_A_AddDieCallback : Z := 0x6965c.  Definition tfib_E_AddDieCallback : Z := 0x696e4.
Definition tfib_A_Die : Z := 0x697a8.  Definition tfib_E_Die : Z := 0x69868.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x69868.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x69874.
Definition tfib_A_CheckFailed : Z := 0x69874.  Definition tfib_E_CheckFailed : Z := 0x6992c.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x69f84.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6a07c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6a07c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6a1a8.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6a3d0.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6a44c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6a480.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6a768.
Definition tfib_A_InitTlsSize : Z := 0x6a768.  Definition tfib_E_InitTlsSize : Z := 0x6a76c.
Definition tfib_A_GetTls : Z := 0x6a76c.  Definition tfib_E_GetTls : Z := 0x6ab5c.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6ab5c.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6ac2c.
Definition tfib_A_AndroidLogInit : Z := 0x6b010.  Definition tfib_E_AndroidLogInit : Z := 0x6b014.
Definition tfib_A_MonotonicNanoTime : Z := 0x6b044.  Definition tfib_E_MonotonicNanoTime : Z := 0x6b08c.
Definition tfib_A_MapDynamicShadow : Z := 0x6b08c.  Definition tfib_E_MapDynamicShadow : Z := 0x6b2d8.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6b2d8.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6b2dc.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6b2dc.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6b3e8.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6b3e8.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6b4ec.
Definition tfib_A_GetThreadSelf : Z := 0x6b768.  Definition tfib_E_GetThreadSelf : Z := 0x6b76c.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6b810.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6b830.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6b830.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6b8d0.
Definition tfib_A_Atexit : Z := 0x6b91c.  Definition tfib_E_Atexit : Z := 0x6b920.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6b95c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6ba20.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6ba20.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6baa8.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6baa8.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6bb20.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6bb20.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6bc04.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6bcc0.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6bdf4.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6c02c.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6c15c.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6c15c.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6c1bc.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6c1bc.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6c288.
Definition tfib_A_MmapNoAccess : Z := 0x6c29c.  Definition tfib_E_MmapNoAccess : Z := 0x6c2bc.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6c2bc.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6c330.
Definition tfib_A_SealedRepairReservation : Z := 0x6c330.  Definition tfib_E_SealedRepairReservation : Z := 0x6c408.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6c408.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6c418.
Definition tfib_A_InitializeCoverage : Z := 0x6dc10.  Definition tfib_E_InitializeCoverage : Z := 0x6dc54.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6dc54.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6dc84.
Definition tfib_A_StackStore_Store : Z := 0x6e0b8.  Definition tfib_E_StackStore_Store : Z := 0x6e1dc.
Definition tfib_A_StackStore_Alloc : Z := 0x6e1dc.  Definition tfib_E_StackStore_Alloc : Z := 0x6e310.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x6ebc4.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x6ec78.
Definition tfib_A_StackDepotNode_store : Z := 0x703cc.  Definition tfib_E_StackDepotNode_store : Z := 0x70428.
Definition tfib_A_StackDepotPut : Z := 0x706b4.  Definition tfib_E_StackDepotPut : Z := 0x706d4.
Definition tfib_A_StackDepotBase_Put : Z := 0x706d4.  Definition tfib_E_StackDepotBase_Put : Z := 0x70958.
Definition tfib_A_StackDepotGet : Z := 0x70958.  Definition tfib_E_StackDepotGet : Z := 0x70a68.
Definition tfib_A_StackDepotBase_lock : Z := 0x70e48.  Definition tfib_E_StackDepotBase_lock : Z := 0x70ed8.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x70ed8.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x70fd8.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x71038.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x71040.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x71040.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x711a0.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x711a0.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x71214.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x7169c.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x717b4.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x74800.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x74804.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x75fd8.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x75fdc.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x77a04.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x77ac0.
Definition tfib_A_Unwind_Trace : Z := 0x77ac0.  Definition tfib_E_Unwind_Trace : Z := 0x77b98.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x77b98.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x77e0c.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x78138.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x7817c.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x7817c.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x7854c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7881c.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x788d4.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x79c2c.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x79c30.
Definition tfib_A_lsan_register_root_region : Z := 0x7a838.  Definition tfib_E_lsan_register_root_region : Z := 0x7ab68.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7ab68.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7aff0.
Definition tfib_A_lsan_default_options : Z := 0x7aff0.  Definition tfib_E_lsan_default_options : Z := 0x7affc.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7dbb4.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7dbcc.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7df50.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7dfcc.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7dfcc.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7e07c.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x7e07c.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x7e094.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x7e094.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x7e1dc.
Definition tfib_A_ubsan_default_options : Z := 0x7e1dc.  Definition tfib_E_ubsan_default_options : Z := 0x7e1e8.
Definition tfib_A_asan_default_options : Z := 0x7e1e8.  Definition tfib_E_asan_default_options : Z := 0x7e1f4.
Definition tfib_A_main : Z := 0x7e1f4.  Definition tfib_E_main : Z := 0x7e4b8.
Definition tfib_A_target_alloc_init : Z := 0x7e4b8.  Definition tfib_E_target_alloc_init : Z := 0x7e4bc.
Definition tfib_A_target_alloc_count : Z := 0x7e4bc.  Definition tfib_E_target_alloc_count : Z := 0x7e4c4.
Definition tfib_A_target_run : Z := 0x7e4c4.  Definition tfib_E_target_run : Z := 0x7e61c.
Definition tfib_A_oft_exit_guard : Z := 0x7e61c.  Definition tfib_E_oft_exit_guard : Z := 0x7e64c.
Definition tfib_A_emit_printf : Z := 0x7e64c.  Definition tfib_E_emit_printf : Z := 0x7e694.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7e694.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7e8a4.
Definition tfib_A_asan_module_ctor : Z := 0x7e91c.  Definition tfib_E_asan_module_ctor : Z := 0x7e954.
Definition tfib_A_extenddftf2 : Z := 0x7e9f4.  Definition tfib_E_extenddftf2 : Z := 0x7eb84.
Definition tfib_A_sysconf : Z := 0x847d4.  Definition tfib_E_sysconf : Z := 0x849fc.
Definition tfib_A_init : Z := 0x849fc.  Definition tfib_E_init : Z := 0x84a00.
Definition tfib_A_init_libc : Z := 0x84a00.  Definition tfib_E_init_libc : Z := 0x84c2c.
Definition tfib_A_libc_start_init : Z := 0x84c2c.  Definition tfib_E_libc_start_init : Z := 0x84c78.
Definition tfib_A_libc_start_main : Z := 0x84c78.  Definition tfib_E_libc_start_main : Z := 0x84cd8.
Definition tfib_A_libc_start_main_stage2 : Z := 0x84cd8.  Definition tfib_E_libc_start_main_stage2 : Z := 0x84d20.
Definition tfib_A_static_init_tls : Z := 0x84df8.  Definition tfib_E_static_init_tls : Z := 0x850a8.
Definition tfib_A_init_ssp : Z := 0x850a8.  Definition tfib_E_init_ssp : Z := 0x85108.
Definition tfib_A_stack_chk_fail : Z := 0x85108.  Definition tfib_E_stack_chk_fail : Z := 0x85110.
Definition tfib_A_abort : Z := 0x85158.  Definition tfib_E_abort : Z := 0x851ec.
Definition tfib_A_Exit : Z := 0x851ec.  Definition tfib_E_Exit : Z := 0x85208.
Definition tfib_A_funcs_on_exit : Z := 0x85238.  Definition tfib_E_funcs_on_exit : Z := 0x85300.
Definition tfib_A_cxa_finalize : Z := 0x85300.  Definition tfib_E_cxa_finalize : Z := 0x85304.
Definition tfib_A_atexit : Z := 0x85304.  Definition tfib_E_atexit : Z := 0x853c8.
Definition tfib_A_libc_exit_fini_call : Z := 0x853c8.  Definition tfib_E_libc_exit_fini_call : Z := 0x853cc.
Definition tfib_A_fini : Z := 0x853cc.  Definition tfib_E_fini : Z := 0x853d0.
Definition tfib_A_libc_exit_fini : Z := 0x853d0.  Definition tfib_E_libc_exit_fini : Z := 0x8541c.
Definition tfib_A_exit : Z := 0x8541c.  Definition tfib_E_exit : Z := 0x85490.
Definition tfib_A_open : Z := 0x85690.  Definition tfib_E_open : Z := 0x85774.
Definition tfib_A_syscall_ret : Z := 0x85774.  Definition tfib_E_syscall_ret : Z := 0x857ac.
Definition tfib_A_dl_iterate_phdr : Z := 0x857ac.  Definition tfib_E_dl_iterate_phdr : Z := 0x85954.
Definition tfib_A_libc_calloc : Z := 0x85f18.  Definition tfib_E_libc_calloc : Z := 0x86050.
Definition tfib_A_libc_malloc : Z := 0x86050.  Definition tfib_E_libc_malloc : Z := 0x86054.
Definition tfib_A_libc_free : Z := 0x86054.  Definition tfib_E_libc_free : Z := 0x86220.
Definition tfib_A_get_meta : Z := 0x86220.  Definition tfib_E_get_meta : Z := 0x86330.
Definition tfib_A_malloc_alloc_meta : Z := 0x86708.  Definition tfib_E_malloc_alloc_meta : Z := 0x869e0.
Definition tfib_A_libc_malloc_impl : Z := 0x869e0.  Definition tfib_E_libc_malloc_impl : Z := 0x86d50.
Definition tfib_A_alloc_slot : Z := 0x86d50.  Definition tfib_E_alloc_slot : Z := 0x875f4.
Definition tfib_A_enframe : Z := 0x875f4.  Definition tfib_E_enframe : Z := 0x87744.
Definition tfib_A_malloc_allzerop : Z := 0x87744.  Definition tfib_E_malloc_allzerop : Z := 0x878bc.
Definition tfib_A_getrlimit : Z := 0x8956c.  Definition tfib_E_getrlimit : Z := 0x89664.
Definition tfib_A_getrusage : Z := 0x89664.  Definition tfib_E_getrusage : Z := 0x8968c.
Definition tfib_A_setrlimit : Z := 0x8968c.  Definition tfib_E_setrlimit : Z := 0x89754.
Definition tfib_A_mmap : Z := 0x89b7c.  Definition tfib_E_mmap : Z := 0x89c68.
Definition tfib_A_mprotect : Z := 0x89c68.  Definition tfib_E_mprotect : Z := 0x89cb0.
Definition tfib_A_munmap : Z := 0x89d84.  Definition tfib_E_munmap : Z := 0x89dcc.
Definition tfib_A_sched_yield : Z := 0x8a090.  Definition tfib_E_sched_yield : Z := 0x8a0b4.
Definition tfib_A_raise : Z := 0x8a110.  Definition tfib_E_raise : Z := 0x8a188.
Definition tfib_A_libc_sigaction : Z := 0x8a188.  Definition tfib_E_libc_sigaction : Z := 0x8a35c.
Definition tfib_A_musl_sigaltstack : Z := 0x8a454.  Definition tfib_E_musl_sigaltstack : Z := 0x8a4e0.
Definition tfib_A_dprintf : Z := 0x8aabc.  Definition tfib_E_dprintf : Z := 0x8ab20.
Definition tfib_A_lockfile : Z := 0x8ab20.  Definition tfib_E_lockfile : Z := 0x8ac1c.
Definition tfib_A_unlockfile : Z := 0x8ac1c.  Definition tfib_E_unlockfile : Z := 0x8ac7c.
Definition tfib_A_stdio_read : Z := 0x8a80c.  Definition tfib_E_stdio_read : Z := 0x8a924.
Definition tfib_A_stdio_write : Z := 0x8a92c.  Definition tfib_E_stdio_write : Z := 0x8aabc.
Definition tfib_A_aio_close : Z := 0x8a7dc.  Definition tfib_E_aio_close : Z := 0x8a7e0.
Definition tfib_A_stdio_close : Z := 0x8a7e0.  Definition tfib_E_stdio_close : Z := 0x8a80c.
Definition tfib_A_fwritex : Z := 0x8b0b0.  Definition tfib_E_fwritex : Z := 0x8b1e8.
Definition tfib_A_musl_fwrite : Z := 0x8b1e8.  Definition tfib_E_musl_fwrite : Z := 0x8b2a0.
Definition tfib_A_towrite : Z := 0x8b2a0.  Definition tfib_E_towrite : Z := 0x8b2f4.
Definition tfib_A_stdio_exit : Z := 0x8af0c.  Definition tfib_E_stdio_exit : Z := 0x8b0b0.
Definition tfib_A_ofl_lock : Z := 0x8b2f4.  Definition tfib_E_ofl_lock : Z := 0x8b324.
Definition tfib_A_musl_vfprintf : Z := 0x8b470.  Definition tfib_E_musl_vfprintf : Z := 0x8b620.
Definition tfib_A_printf_core : Z := 0x8b620.  Definition tfib_E_printf_core : Z := 0x8c450.
Definition tfib_A_pop_arg : Z := 0x8c450.  Definition tfib_E_pop_arg : Z := 0x8c584.
Definition tfib_A_pad : Z := 0x8c584.  Definition tfib_E_pad : Z := 0x8c658.
Definition tfib_A_fmt_fp : Z := 0x8c658.  Definition tfib_E_fmt_fp : Z := 0x8dd20.
Definition tfib_A_lctrans : Z := 0x85b6c.  Definition tfib_E_lctrans : Z := 0x85b70.
Definition tfib_A_musl_wctomb : Z := 0x89ef8.  Definition tfib_E_musl_wctomb : Z := 0x89f1c.
Definition tfib_A_musl_wcrtomb : Z := 0x89dcc.  Definition tfib_E_musl_wcrtomb : Z := 0x89ef8.
Definition tfib_A_fpclassifyl : Z := 0x8815c.  Definition tfib_E_fpclassifyl : Z := 0x881a0.
Definition tfib_A_letf2 : Z := 0x87994.  Definition tfib_E_letf2 : Z := 0x87a5c.
Definition tfib_A_multf3 : Z := 0x87a5c.  Definition tfib_E_multf3 : Z := 0x8815c.
Definition tfib_A_floatsitf : Z := 0x889b8.  Definition tfib_E_floatsitf : Z := 0x88ac0.
Definition tfib_A_scalbn : Z := 0x893c4.  Definition tfib_E_scalbn : Z := 0x8945c.
Definition tfib_A_subtf3 : Z := 0x889a8.  Definition tfib_E_subtf3 : Z := 0x889b8.
Definition tfib_A_addtf3 : Z := 0x881a0.  Definition tfib_E_addtf3 : Z := 0x8896c.
Definition tfib_A_fe_getround : Z := 0x8896c.  Definition tfib_E_fe_getround : Z := 0x8899c.
Definition tfib_A_fixunstfsi : Z := 0x8dd28.  Definition tfib_E_fixunstfsi : Z := 0x8ddbc.
Definition tfib_A_floatunsitf : Z := 0x8ddbc.  Definition tfib_E_floatunsitf : Z := 0x8dea8.
Definition tfib_A_fixtfsi : Z := 0x8945c.  Definition tfib_E_fixtfsi : Z := 0x89504.
Definition tfib_A_divtf3 : Z := 0x88ac0.  Definition tfib_E_divtf3 : Z := 0x893c4.
Definition tfib_A_musl_vprintf : Z := 0x8e580.  Definition tfib_E_musl_vprintf : Z := 0x8e59c.
Definition tfib_A_stdout_write : Z := 0x8b330.  Definition tfib_E_stdout_write : Z := 0x8b3d0.
Definition tfib_A_musl_memcmp : Z := 0x8ec00.  Definition tfib_E_musl_memcmp : Z := 0x8ec30.
Definition tfib_A_musl_memcpy : Z := 0x8ec30.  Definition tfib_E_musl_memcpy : Z := 0x8f034.
Definition tfib_A_musl_memset : Z := 0x8f034.  Definition tfib_E_musl_memset : Z := 0x8f12c.
Definition tfib_A_musl_strchr : Z := 0x8f12c.  Definition tfib_E_musl_strchr : Z := 0x8f168.
Definition tfib_A_strchrnul : Z := 0x8f168.  Definition tfib_E_strchrnul : Z := 0x8f248.
Definition tfib_A_musl_strlen : Z := 0x8f280.  Definition tfib_E_musl_strlen : Z := 0x8f310.
Definition tfib_A_musl_strnlen : Z := 0x8f4bc.  Definition tfib_E_musl_strnlen : Z := 0x8f500.
Definition tfib_A_musl_memchr : Z := 0x8eb34.  Definition tfib_E_musl_memchr : Z := 0x8ec00.
Definition tfib_A_lock : Z := 0x8f500.  Definition tfib_E_lock : Z := 0x8f788.
Definition tfib_A_unlock : Z := 0x8f788.  Definition tfib_E_unlock : Z := 0x8f7fc.
Definition tfib_A_sccp : Z := 0x8f7fc.  Definition tfib_E_sccp : Z := 0x8f820.
Definition tfib_A_syscall_cp : Z := 0x8f820.  Definition tfib_E_syscall_cp : Z := 0x8f824.
Definition tfib_A_tls_get_addr : Z := 0x8f824.  Definition tfib_E_tls_get_addr : Z := 0x8f848.
Definition tfib_A_pthread_atfork : Z := 0x8f860.  Definition tfib_E_pthread_atfork : Z := 0x8f904.
Definition tfib_A_mremap : Z := 0x89cb0.  Definition tfib_E_mremap : Z := 0x89d84.
Definition tfib_A_pthread_getspecific : Z := 0x908d8.  Definition tfib_E_pthread_getspecific : Z := 0x908f4.
Definition tfib_A_pthread_key_create : Z := 0x90c80.  Definition tfib_E_pthread_key_create : Z := 0x90d54.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x90ff8.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x9109c.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x9109c.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x910a4.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x910a4.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x911b8.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x911b8.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x911e4.
Definition tfib_A_pthread_setspecific : Z := 0x9121c.  Definition tfib_E_pthread_setspecific : Z := 0x91250.
Definition tfib_A_set_thread_area : Z := 0x91258.  Definition tfib_E_set_thread_area : Z := 0x91264.
Definition tfib_A_pthread_testcancel : Z := 0x91250.  Definition tfib_E_pthread_testcancel : Z := 0x91254.

Definition tfib_A_musl_clock_gettime : Z := 0x91b84.  Definition tfib_E_musl_clock_gettime : Z := 0x91c3c.
Definition tfib_A_close : Z := 0x94254.  Definition tfib_E_close : Z := 0x942a8.
Definition tfib_A_musl_read : Z := 0x94334.  Definition tfib_E_musl_read : Z := 0x94368.
Definition tfib_A_vm_wait : Z := 0x91894.  Definition tfib_E_vm_wait : Z := 0x918e4.
Definition tfib_D_str_sealed : Z := 0x117f6.
Definition tfib_D_init_array_0_3 : Z := 0x95368.
Definition tfib_D_fini_array_0 : Z := 0x95388.
Definition tfib_D_GOT_common_flags : Z := 0x958f0.
Definition tfib_D_GOT_flags : Z := 0x958f8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x95900.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x95908.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x95910.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x95918.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x96468.
Definition tfib_D_GOT_environ : Z := 0x96590.
Definition tfib_D_REAL_read : Z := 0x97630.
Definition tfib_D_REAL_memcpy : Z := 0x97758.
Definition tfib_D_REAL_memset : Z := 0x97760.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9a258.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9b0b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0x9d8b8.
Definition tfib_D_asan_inited : Z := 0x9e598.
Definition tfib_D_replace_intrin_cached : Z := 0x9e599.
Definition tfib_D_kHighMemEnd : Z := 0x9e5a0.
Definition tfib_D_kMidMemBeg : Z := 0x9e5a8.
Definition tfib_D_kMidMemEnd : Z := 0x9e5b0.
Definition tfib_D_malloc_context_size : Z := 0x9e5bc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x12f3e8.
Definition tfib_D_libc : Z := 0x5f0ae0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f3000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2f9ec.
Definition tfib_at_rw_lo : Z := 0x97000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x61b6c.
Definition tfib_at_x_imemcpy : Z := 0x61af0.
Definition tfib_at_x_memset : Z := 0x8f034.
Definition tfib_at_x_memcpy : Z := 0x8ec30.
Definition tfib_at_x_memiszero : Z := 0x6209c.
Definition tfib_at_x_istrncpy : Z := 0x61f98.
Definition tfib_at_x_sealed : Z := 0x117f6.
Definition tfib_at_x_popfree : Z := 0x35dd8.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x84a38.
Definition tfib_at_x_envscan_k : Z := 0x84a44.
Definition tfib_at_x_pnscan : Z := 0x84afc.
Definition tfib_at_x_pnscan_k : Z := 0x84b08.
Definition tfib_at_stops_more : list Z := (0x33a4c :: 0x35070 :: 0x51e78 :: 0x58230 :: 0x58244 :: 0x58258 :: 0x5dbe8 :: 0x5dcb8 :: 0x6b1e4 :: 0x6c0f0 :: 0x6c280 :: 0x75fd8 :: nil)%list.
