(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers; two cells that nothing reads are removed: the libc_exit_fini_call entry, whose address holds atexit's static `call` and no code of libc_exit_fini, and the copy of the atable's stops_more list. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1w.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libreac/fuzz_knock's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102d0.  Definition tfib_rodata_hi : Z := 0x22564.
Definition tfib_text_lo : Z := 0x2fa9c.  Definition tfib_text_hi : Z := 0x95084.
Definition tfib_init_array_lo : Z := 0x96088.  Definition tfib_init_array_hi : Z := 0x960a8.
Definition tfib_fini_array_lo : Z := 0x960a8.  Definition tfib_fini_array_hi : Z := 0x960b0.
Definition tfib_preinit_array_lo : Z := 0x960b0.  Definition tfib_preinit_array_hi : Z := 0x960b8.
Definition tfib_data_rel_ro_lo : Z := 0x960b8.  Definition tfib_data_rel_ro_hi : Z := 0x965b8.
Definition tfib_got_lo : Z := 0x965b8.  Definition tfib_got_hi : Z := 0x97310.
Definition tfib_data_lo : Z := 0x98310.  Definition tfib_data_hi : Z := 0x9aec0.
Definition tfib_bss_lo : Z := 0x9aec0.  Definition tfib_bss_hi : Z := 0x5f2df0.
Definition tfib_tbss_lo : Z := 0x95088.  Definition tfib_tbss_hi : Z := 0x9509c.
Definition tfib_img_lo : Z := YImgTop.IMG_LO.  Definition tfib_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_entry : Z := 0x2fa9c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2fa9c.  Definition tfib_E_start : Z := 0x2fab8.
Definition tfib_A_start_c : Z := 0x2fab8.  Definition tfib_E_start_c : Z := 0x2fae4.
Definition tfib_A_do_init : Z := 0x2fae4.  Definition tfib_E_do_init : Z := 0x2fb58.
Definition tfib_A_do_fini : Z := 0x2fb58.  Definition tfib_E_do_fini : Z := 0x2fbe8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x2fbe8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x2fc24.
Definition tfib_A_InitializeAllocator : Z := 0x2fd94.  Definition tfib_E_InitializeAllocator : Z := 0x2fdac.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x2fdac.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x2ff18.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x30474.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x305d0.
Definition tfib_A_asan_free : Z := 0x309a4.  Definition tfib_E_asan_free : Z := 0x309cc.
Definition tfib_A_Allocator_Deallocate : Z := 0x309cc.  Definition tfib_E_Allocator_Deallocate : Z := 0x30c84.
Definition tfib_A_asan_malloc : Z := 0x30c84.  Definition tfib_E_asan_malloc : Z := 0x30ce0.
Definition tfib_A_Allocator_Allocate : Z := 0x30ce0.  Definition tfib_E_Allocator_Allocate : Z := 0x31668.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x31da0.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x31ee4.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x31fd0.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x3202c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x3202c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3227c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3227c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32370.
Definition tfib_A_Allocator_CheckOptions : Z := 0x32370.  Definition tfib_E_Allocator_CheckOptions : Z := 0x32458.
Definition tfib_A_Quarantine_Recycle : Z := 0x3288c.  Definition tfib_E_Quarantine_Recycle : Z := 0x32a70.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x32a70.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x32bf4.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x32d2c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x32fb0.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x32fb0.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33130.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33130.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x332f8.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x332f8.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x334c4.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x334c4.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x33564.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x33564.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x33668.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33990.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33ad8.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x33ad8.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x33b10.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x342a8.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x34590.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x34c68.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x34de0.
Definition tfib_A_Quarantine_Put : Z := 0x34de0.  Definition tfib_E_Quarantine_Put : Z := 0x34f90.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x34f90.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35174.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x35174.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x3544c.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x3544c.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x358c4.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x358c4.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x359c4.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x359c4.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x35ccc.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x35ccc.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x3603c.
Definition tfib_A_RZSize2Log : Z := 0x3603c.  Definition tfib_E_RZSize2Log : Z := 0x36154.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x3645c.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x36558.
Definition tfib_A_AsanDeactivate : Z := 0x36558.  Definition tfib_E_AsanDeactivate : Z := 0x36640.
Definition tfib_A_AsanActivate : Z := 0x36640.  Definition tfib_E_AsanActivate : Z := 0x3671c.
Definition tfib_A_FlagHandler_Parse : Z := 0x36bf8.  Definition tfib_E_FlagHandler_Parse : Z := 0x36ce0.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3b798.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3b870.
Definition tfib_A_FakeStack_Create : Z := 0x3b870.  Definition tfib_E_FakeStack_Create : Z := 0x3b95c.
Definition tfib_A_FakeStack_GC : Z := 0x3bc18.  Definition tfib_E_FakeStack_GC : Z := 0x3bf00.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c034.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c064.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3c064.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3c1f4.
Definition tfib_A_MemToShadow_3c1f4 : Z := 0x3c1f4.  Definition tfib_E_MemToShadow_3c1f4 : Z := 0x3c330.
Definition tfib_A_InitializeFlags : Z := 0x3c330.  Definition tfib_E_InitializeFlags : Z := 0x3d35c.
Definition tfib_A_asan_register_globals : Z := 0x3da68.  Definition tfib_E_asan_register_globals : Z := 0x3e884.
Definition tfib_A_asan_unregister_globals : Z := 0x3e884.  Definition tfib_E_asan_unregister_globals : Z := 0x3ee50.
Definition tfib_A_asan_register_elf_globals : Z := 0x3ee50.  Definition tfib_E_asan_register_elf_globals : Z := 0x3eebc.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x3f53c.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x3f7ac.
Definition tfib_A_asan_after_dynamic_init : Z := 0x3f7ac.  Definition tfib_E_asan_after_dynamic_init : Z := 0x3fab4.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x40228.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x40378.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x40d94.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x40eac.
Definition tfib_A_strlen : Z := 0x40eac.  Definition tfib_E_strlen : Z := 0x40eb0.
Definition tfib_A_strnlen : Z := 0x40eb0.  Definition tfib_E_strnlen : Z := 0x40eb4.
Definition tfib_A_strcmp : Z := 0x40eb4.  Definition tfib_E_strcmp : Z := 0x40eb8.
Definition tfib_A_strchr : Z := 0x40eb8.  Definition tfib_E_strchr : Z := 0x40ebc.
Definition tfib_A_memcmp : Z := 0x40ebc.  Definition tfib_E_memcmp : Z := 0x40ec0.
Definition tfib_A_memchr : Z := 0x40ec0.  Definition tfib_E_memchr : Z := 0x40ec4.
Definition tfib_A_frexpl : Z := 0x40ec4.  Definition tfib_E_frexpl : Z := 0x40ec8.
Definition tfib_A_read : Z := 0x40ec8.  Definition tfib_E_read : Z := 0x40ecc.
Definition tfib_A_fwrite : Z := 0x40ecc.  Definition tfib_E_fwrite : Z := 0x40ed0.
Definition tfib_A_time : Z := 0x40ed0.  Definition tfib_E_time : Z := 0x40ed4.
Definition tfib_A_gmtime_r : Z := 0x40ed4.  Definition tfib_E_gmtime_r : Z := 0x40ed8.
Definition tfib_A_vprintf : Z := 0x40ed8.  Definition tfib_E_vprintf : Z := 0x40edc.
Definition tfib_A_vfprintf : Z := 0x40edc.  Definition tfib_E_vfprintf : Z := 0x40ee0.
Definition tfib_A_vsnprintf : Z := 0x40ee0.  Definition tfib_E_vsnprintf : Z := 0x40ee4.
Definition tfib_A_fprintf : Z := 0x40ee4.  Definition tfib_E_fprintf : Z := 0x40ee8.
Definition tfib_A_snprintf : Z := 0x40ee8.  Definition tfib_E_snprintf : Z := 0x40eec.
Definition tfib_A_clock_gettime : Z := 0x40eec.  Definition tfib_E_clock_gettime : Z := 0x40ef0.
Definition tfib_A_wcrtomb : Z := 0x40ef0.  Definition tfib_E_wcrtomb : Z := 0x40ef4.
Definition tfib_A_wctomb : Z := 0x40ef4.  Definition tfib_E_wctomb : Z := 0x40ef8.
Definition tfib_A_strerror : Z := 0x40ef8.  Definition tfib_E_strerror : Z := 0x40efc.
Definition tfib_A__exit : Z := 0x40efc.  Definition tfib_E__exit : Z := 0x40f00.
Definition tfib_A_pthread_attr_getstack : Z := 0x40f00.  Definition tfib_E_pthread_attr_getstack : Z := 0x40f04.
Definition tfib_A___tls_get_addr : Z := 0x40f04.  Definition tfib_E___tls_get_addr : Z := 0x40f08.
Definition tfib_A_fflush : Z := 0x40f08.  Definition tfib_E_fflush : Z := 0x40f0c.
Definition tfib_A_sem_init : Z := 0x40f0c.  Definition tfib_E_sem_init : Z := 0x40f10.
Definition tfib_A_sem_destroy : Z := 0x40f10.  Definition tfib_E_sem_destroy : Z := 0x40f14.
Definition tfib_A_sem_wait : Z := 0x40f14.  Definition tfib_E_sem_wait : Z := 0x40f18.
Definition tfib_A_sem_trywait : Z := 0x40f18.  Definition tfib_E_sem_trywait : Z := 0x40f1c.
Definition tfib_A_sem_timedwait : Z := 0x40f1c.  Definition tfib_E_sem_timedwait : Z := 0x40f20.
Definition tfib_A_sem_post : Z := 0x40f20.  Definition tfib_E_sem_post : Z := 0x40f24.
Definition tfib_A_pthread_setcancelstate : Z := 0x40f24.  Definition tfib_E_pthread_setcancelstate : Z := 0x40f28.
Definition tfib_A_send : Z := 0x40f28.  Definition tfib_E_send : Z := 0x40f2c.
Definition tfib_A_sendto : Z := 0x40f2c.  Definition tfib_E_sendto : Z := 0x40f30.
Definition tfib_A_sigaltstack : Z := 0x40f30.  Definition tfib_E_sigaltstack : Z := 0x40f34.
Definition tfib_A_sigaction : Z := 0x40f34.  Definition tfib_E_sigaction : Z := 0x40f38.
Definition tfib_A_icpt_strlen : Z := 0x40f38.  Definition tfib_E_icpt_strlen : Z := 0x411cc.
Definition tfib_A_icpt_strnlen : Z := 0x411cc.  Definition tfib_E_icpt_strnlen : Z := 0x41460.
Definition tfib_A_icpt_strcmp : Z := 0x41464.  Definition tfib_E_icpt_strcmp : Z := 0x41994.
Definition tfib_A_icpt_strchr : Z := 0x41994.  Definition tfib_E_icpt_strchr : Z := 0x41c74.
Definition tfib_A_icpt_memcmp : Z := 0x4250c.  Definition tfib_E_icpt_memcmp : Z := 0x425c8.
Definition tfib_A_icpt_memchr : Z := 0x425c8.  Definition tfib_E_icpt_memchr : Z := 0x42898.
Definition tfib_A_icpt_frexpl : Z := 0x42898.  Definition tfib_E_icpt_frexpl : Z := 0x42b10.
Definition tfib_A_icpt_read : Z := 0x42b10.  Definition tfib_E_icpt_read : Z := 0x42d80.
Definition tfib_A_icpt_fwrite : Z := 0x42d80.  Definition tfib_E_icpt_fwrite : Z := 0x42ff4.
Definition tfib_A_icpt_time : Z := 0x42ff4.  Definition tfib_E_icpt_time : Z := 0x43290.
Definition tfib_A_icpt_gmtime_r : Z := 0x43498.  Definition tfib_E_icpt_gmtime_r : Z := 0x436d8.
Definition tfib_A_icpt_vprintf : Z := 0x436d8.  Definition tfib_E_icpt_vprintf : Z := 0x43774.
Definition tfib_A_printf_common : Z := 0x43774.  Definition tfib_E_printf_common : Z := 0x4423c.
Definition tfib_A_icpt_vfprintf : Z := 0x4423c.  Definition tfib_E_icpt_vfprintf : Z := 0x442f0.
Definition tfib_A_icpt_vsnprintf : Z := 0x442f0.  Definition tfib_E_icpt_vsnprintf : Z := 0x44608.
Definition tfib_A_icpt_fprintf : Z := 0x44608.  Definition tfib_E_icpt_fprintf : Z := 0x446e0.
Definition tfib_A_icpt_clock_gettime : Z := 0x44784.  Definition tfib_E_icpt_clock_gettime : Z := 0x449dc.
Definition tfib_A_icpt_wcrtomb : Z := 0x449dc.  Definition tfib_E_icpt_wcrtomb : Z := 0x44f4c.
Definition tfib_A_icpt_wctomb : Z := 0x44f4c.  Definition tfib_E_icpt_wctomb : Z := 0x452a8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45374.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x4575c.
Definition tfib_A_icpt_tls_get_addr : Z := 0x45768.  Definition tfib_E_icpt_tls_get_addr : Z := 0x457e4.
Definition tfib_A_icpt_sem_timedwait : Z := 0x459f0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x45c88.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x45cb8.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x45ee0.
Definition tfib_A_icpt_send : Z := 0x45ee0.  Definition tfib_E_icpt_send : Z := 0x46194.
Definition tfib_A_icpt_sendto : Z := 0x46194.  Definition tfib_E_icpt_sendto : Z := 0x46458.
Definition tfib_A_icpt_sigaltstack : Z := 0x46458.  Definition tfib_E_icpt_sigaltstack : Z := 0x466b4.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46788.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x46938.
Definition tfib_A_format_get_value_size : Z := 0x46938.  Definition tfib_E_format_get_value_size : Z := 0x46ad0.
Definition tfib_A_ioctl_table_fill : Z := 0x4767c.  Definition tfib_E_ioctl_table_fill : Z := 0x50354.
Definition tfib_A_Sort : Z := 0x50354.  Definition tfib_E_Sort : Z := 0x504b0.
Definition tfib_A_memset : Z := 0x504b0.  Definition tfib_E_memset : Z := 0x504b4.
Definition tfib_A_memcpy : Z := 0x504b4.  Definition tfib_E_memcpy : Z := 0x504b8.
Definition tfib_A_asan_memset : Z := 0x504b8.  Definition tfib_E_asan_memset : Z := 0x506f8.
Definition tfib_A_icpt_memset : Z := 0x506f8.  Definition tfib_E_icpt_memset : Z := 0x509e8.
Definition tfib_A_icpt_memcpy : Z := 0x509e8.  Definition tfib_E_icpt_memcpy : Z := 0x50fd8.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x50fd8.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x51010.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51010.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x51014.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x51014.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51018.
Definition tfib_A_FindDynamicShadowStart : Z := 0x51018.  Definition tfib_E_FindDynamicShadowStart : Z := 0x51078.
Definition tfib_A_MemToShadow_510c4 : Z := 0x510c4.  Definition tfib_E_MemToShadow_510c4 : Z := 0x51200.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x51200.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x51204.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x51204.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x5136c.
Definition tfib_A_free : Z := 0x5136c.  Definition tfib_E_free : Z := 0x51370.
Definition tfib_A_malloc : Z := 0x51370.  Definition tfib_E_malloc : Z := 0x51374.
Definition tfib_A_icpt_free : Z := 0x51374.  Definition tfib_E_icpt_free : Z := 0x51544.
Definition tfib_A_icpt_malloc : Z := 0x51544.  Definition tfib_E_icpt_malloc : Z := 0x516a0.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x516a0.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x5176c.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x5176c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x51770.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x51770.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x51870.
Definition tfib_A_HeapProfile_Print : Z := 0x51b98.  Definition tfib_E_HeapProfile_Print : Z := 0x51d04.
Definition tfib_A_SetCanPoisonMemory : Z := 0x521ec.  Definition tfib_E_SetCanPoisonMemory : Z := 0x521fc.
Definition tfib_A_CanPoisonMemory : Z := 0x521fc.  Definition tfib_E_CanPoisonMemory : Z := 0x52210.
Definition tfib_A_PoisonShadow : Z := 0x52210.  Definition tfib_E_PoisonShadow : Z := 0x5270c.
Definition tfib_A_MemToShadow_5270c : Z := 0x5270c.  Definition tfib_E_MemToShadow_5270c : Z := 0x52848.
Definition tfib_A_asan_poison_memory_region : Z := 0x52848.  Definition tfib_E_asan_poison_memory_region : Z := 0x529e8.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x529e8.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x52b68.
Definition tfib_A_asan_region_is_poisoned : Z := 0x52b98.  Definition tfib_E_asan_region_is_poisoned : Z := 0x52edc.
Definition tfib_A_AsanTSDInit : Z := 0x532fc.  Definition tfib_E_AsanTSDInit : Z := 0x53378.
Definition tfib_A_AsanTSDGet : Z := 0x53378.  Definition tfib_E_AsanTSDGet : Z := 0x533b8.
Definition tfib_A_AsanTSDSet : Z := 0x533b8.  Definition tfib_E_AsanTSDSet : Z := 0x533f8.
Definition tfib_A_PlatformTSDDtor : Z := 0x533f8.  Definition tfib_E_PlatformTSDDtor : Z := 0x5347c.
Definition tfib_A_InstallAtForkHandler : Z := 0x5347c.  Definition tfib_E_InstallAtForkHandler : Z := 0x53498.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x534f8.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5353c.
Definition tfib_A_ReportDeadlySignal : Z := 0x53c54.  Definition tfib_E_ReportDeadlySignal : Z := 0x53e60.
Definition tfib_A_ReportDoubleFree : Z := 0x54568.  Definition tfib_E_ReportDoubleFree : Z := 0x547f8.
Definition tfib_A_ReportGenericError : Z := 0x560d4.  Definition tfib_E_ReportGenericError : Z := 0x56990.
Definition tfib_A_AsanInited : Z := 0x5711c.  Definition tfib_E_AsanInited : Z := 0x57134.
Definition tfib_A_asan_report_load1 : Z := 0x57134.  Definition tfib_E_asan_report_load1 : Z := 0x57184.
Definition tfib_A_asan_report_exp_load1 : Z := 0x57184.  Definition tfib_E_asan_report_exp_load1 : Z := 0x571d4.
Definition tfib_A_asan_report_load2 : Z := 0x571d4.  Definition tfib_E_asan_report_load2 : Z := 0x57224.
Definition tfib_A_asan_report_exp_load2 : Z := 0x57224.  Definition tfib_E_asan_report_exp_load2 : Z := 0x57274.
Definition tfib_A_asan_report_load4 : Z := 0x57274.  Definition tfib_E_asan_report_load4 : Z := 0x572c4.
Definition tfib_A_asan_report_exp_load4 : Z := 0x572c4.  Definition tfib_E_asan_report_exp_load4 : Z := 0x57314.
Definition tfib_A_asan_report_load8 : Z := 0x57314.  Definition tfib_E_asan_report_load8 : Z := 0x57364.
Definition tfib_A_asan_report_exp_load8 : Z := 0x57364.  Definition tfib_E_asan_report_exp_load8 : Z := 0x573b4.
Definition tfib_A_asan_report_load16 : Z := 0x573b4.  Definition tfib_E_asan_report_load16 : Z := 0x57404.
Definition tfib_A_asan_report_exp_load16 : Z := 0x57404.  Definition tfib_E_asan_report_exp_load16 : Z := 0x57454.
Definition tfib_A_asan_report_store1 : Z := 0x57454.  Definition tfib_E_asan_report_store1 : Z := 0x574a4.
Definition tfib_A_asan_report_exp_store1 : Z := 0x574a4.  Definition tfib_E_asan_report_exp_store1 : Z := 0x574f4.
Definition tfib_A_asan_report_store2 : Z := 0x574f4.  Definition tfib_E_asan_report_store2 : Z := 0x57544.
Definition tfib_A_asan_report_exp_store2 : Z := 0x57544.  Definition tfib_E_asan_report_exp_store2 : Z := 0x57594.
Definition tfib_A_asan_report_store4 : Z := 0x57594.  Definition tfib_E_asan_report_store4 : Z := 0x575e4.
Definition tfib_A_asan_report_exp_store4 : Z := 0x575e4.  Definition tfib_E_asan_report_exp_store4 : Z := 0x57634.
Definition tfib_A_asan_report_store8 : Z := 0x57634.  Definition tfib_E_asan_report_store8 : Z := 0x57684.
Definition tfib_A_asan_report_exp_store8 : Z := 0x57684.  Definition tfib_E_asan_report_exp_store8 : Z := 0x576d4.
Definition tfib_A_asan_report_store16 : Z := 0x576d4.  Definition tfib_E_asan_report_store16 : Z := 0x57724.
Definition tfib_A_asan_report_exp_store16 : Z := 0x57724.  Definition tfib_E_asan_report_exp_store16 : Z := 0x57774.
Definition tfib_A_asan_report_load_n : Z := 0x57774.  Definition tfib_E_asan_report_load_n : Z := 0x577c4.
Definition tfib_A_asan_report_exp_load_n : Z := 0x577c4.  Definition tfib_E_asan_report_exp_load_n : Z := 0x57814.
Definition tfib_A_asan_report_store_n : Z := 0x57814.  Definition tfib_E_asan_report_store_n : Z := 0x57864.
Definition tfib_A_asan_report_exp_store_n : Z := 0x57864.  Definition tfib_E_asan_report_exp_store_n : Z := 0x578b4.
Definition tfib_A_InitializeHighMemEnd : Z := 0x578b4.  Definition tfib_E_InitializeHighMemEnd : Z := 0x57934.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x57934.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x57ce8.
Definition tfib_A_AsanInitInternal : Z := 0x57d78.  Definition tfib_E_AsanInitInternal : Z := 0x5802c.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x5802c.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x580cc.
Definition tfib_A_asan_set_death_callback : Z := 0x58294.  Definition tfib_E_asan_set_death_callback : Z := 0x58298.
Definition tfib_A_asan_init : Z := 0x58298.  Definition tfib_E_asan_init : Z := 0x5832c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5832c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x58330.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x58330.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x58394.
Definition tfib_A_OnLowLevelAllocate : Z := 0x58508.  Definition tfib_E_OnLowLevelAllocate : Z := 0x58510.
Definition tfib_A_force_interface_symbols : Z := 0x58594.  Definition tfib_E_force_interface_symbols : Z := 0x588bc.
Definition tfib_A_SealedReserveShadow : Z := 0x588bc.  Definition tfib_E_SealedReserveShadow : Z := 0x58a9c.
Definition tfib_A_InitializeShadowMemory : Z := 0x58a9c.  Definition tfib_E_InitializeShadowMemory : Z := 0x58da4.
Definition tfib_A_SetMallocContextSize : Z := 0x58da4.  Definition tfib_E_SetMallocContextSize : Z := 0x58db4.
Definition tfib_A_GetMallocContextSize : Z := 0x58db4.  Definition tfib_E_GetMallocContextSize : Z := 0x58dc4.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x58dc4.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x58f14.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x592f4.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x59594.
Definition tfib_A_GetCurrentThreadStats : Z := 0x599f8.  Definition tfib_E_GetCurrentThreadStats : Z := 0x59a30.
Definition tfib_A_asan_default_suppressions : Z := 0x59cd8.  Definition tfib_E_asan_default_suppressions : Z := 0x59ce4.
Definition tfib_A_InitializeSuppressions : Z := 0x59ce4.  Definition tfib_E_InitializeSuppressions : Z := 0x59d70.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x59d70.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x59dd8.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x59dd8.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x59e50.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x59e50.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x59eb8.
Definition tfib_A_IsAddrSuppressed : Z := 0x59eb8.  Definition tfib_E_IsAddrSuppressed : Z := 0x5a004.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x5a290.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x5a29c.
Definition tfib_A_AsanThread_Create : Z := 0x5a41c.  Definition tfib_E_AsanThread_Create : Z := 0x5a5b8.
Definition tfib_A_AsanThread_Destroy : Z := 0x5a614.  Definition tfib_E_AsanThread_Destroy : Z := 0x5a82c.
Definition tfib_A_GetCurrentThread : Z := 0x5a82c.  Definition tfib_E_GetCurrentThread : Z := 0x5a84c.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a84c.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5a9f0.
Definition tfib_A_AsanThread_stack_top : Z := 0x5a9f0.  Definition tfib_E_AsanThread_stack_top : Z := 0x5aa48.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5aa48.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5aaa0.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5aaa0.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5acd0.
Definition tfib_A_AsanThread_Init : Z := 0x5acd0.  Definition tfib_E_AsanThread_Init : Z := 0x5b0c4.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5b0c4.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5b1d0.
Definition tfib_A_CreateMainThread : Z := 0x5b204.  Definition tfib_E_CreateMainThread : Z := 0x5b314.
Definition tfib_A_SetCurrentThread : Z := 0x5b314.  Definition tfib_E_SetCurrentThread : Z := 0x5b3f4.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5b5f8.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5b734.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5c408.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5c40c.
Definition tfib_A_GetAsanThreadContext : Z := 0x5c414.  Definition tfib_E_GetAsanThreadContext : Z := 0x5c654.
Definition tfib_A_internal_allocator : Z := 0x5c8a8.  Definition tfib_E_internal_allocator : Z := 0x5ca00.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5cbec.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5cbf8.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5cbf8.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5cd44.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5cd44.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5cd90.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5cd90.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5cd9c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5cdcc.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5cdd8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5cdd8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5cde4.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5cde4.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5cdf4.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5ce00.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5d0cc.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5d0cc.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5d48c.
Definition tfib_A_SealedSetInitFrame : Z := 0x5e3e8.  Definition tfib_E_SealedSetInitFrame : Z := 0x5e3f4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5e3f4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5e4cc.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5e4cc.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5e568.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5ea8c.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5ead0.
Definition tfib_A_DecreaseTotalMmap : Z := 0x5ead0.  Definition tfib_E_DecreaseTotalMmap : Z := 0x5eaf4.
Definition tfib_A_CacheBinaryName : Z := 0x5ed48.  Definition tfib_E_CacheBinaryName : Z := 0x5ee5c.
Definition tfib_A_RunMallocHooks : Z := 0x5f000.  Definition tfib_E_RunMallocHooks : Z := 0x5f0b8.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x5f0b8.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x5f0bc.
Definition tfib_A_RunFreeHooks : Z := 0x5f0bc.  Definition tfib_E_RunFreeHooks : Z := 0x5f168.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x5f168.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x5f170.
Definition tfib_A_sanitizer_free_hook : Z := 0x5f170.  Definition tfib_E_sanitizer_free_hook : Z := 0x5f174.
Definition tfib_A_WaitForDebugger : Z := 0x5f19c.  Definition tfib_E_WaitForDebugger : Z := 0x5f1e8.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x5f4ac.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x5f6ec.
Definition tfib_A_sanitizer_set_report_path : Z := 0x5fce8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x5fd00.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x5fd00.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x5fe44.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x5fe44.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x5fe4c.
Definition tfib_A_RegisterCommonFlags : Z := 0x60194.  Definition tfib_E_RegisterCommonFlags : Z := 0x61438.
Definition tfib_A_InitializeCommonFlags : Z := 0x61438.  Definition tfib_E_InitializeCommonFlags : Z := 0x6145c.
Definition tfib_A_FlagParser_parse_flag : Z := 0x61910.  Definition tfib_E_FlagParser_parse_flag : Z := 0x61c20.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x61c20.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x61d64.
Definition tfib_A_FlagParser_ParseString : Z := 0x61d64.  Definition tfib_E_FlagParser_ParseString : Z := 0x61e58.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x61fec.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x6204c.
Definition tfib_A_FlagParser_FlagParser : Z := 0x6204c.  Definition tfib_E_FlagParser_FlagParser : Z := 0x6208c.
Definition tfib_A_internal_atoll : Z := 0x6208c.  Definition tfib_E_internal_atoll : Z := 0x62178.
Definition tfib_A_internal_simple_strtoll : Z := 0x62178.  Definition tfib_E_internal_simple_strtoll : Z := 0x622d4.
Definition tfib_A_internal_memchr : Z := 0x622d4.  Definition tfib_E_internal_memchr : Z := 0x622f4.
Definition tfib_A_internal_memcmp : Z := 0x622f4.  Definition tfib_E_internal_memcmp : Z := 0x6232c.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x6232c.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x62350.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x62350.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x623a8.
Definition tfib_A_sanitizer_internal_memset : Z := 0x623a8.  Definition tfib_E_sanitizer_internal_memset : Z := 0x62408.
Definition tfib_A_internal_strcspn : Z := 0x62408.  Definition tfib_E_internal_strcspn : Z := 0x6245c.
Definition tfib_A_internal_strchr : Z := 0x6245c.  Definition tfib_E_internal_strchr : Z := 0x62490.
Definition tfib_A_internal_strdup : Z := 0x62490.  Definition tfib_E_internal_strdup : Z := 0x624fc.
Definition tfib_A_internal_strlen : Z := 0x624fc.  Definition tfib_E_internal_strlen : Z := 0x62518.
Definition tfib_A_internal_strcmp : Z := 0x62518.  Definition tfib_E_internal_strcmp : Z := 0x6255c.
Definition tfib_A_internal_strncmp : Z := 0x6255c.  Definition tfib_E_internal_strncmp : Z := 0x625a8.
Definition tfib_A_internal_strchrnul : Z := 0x625a8.  Definition tfib_E_internal_strchrnul : Z := 0x625f0.
Definition tfib_A_internal_strrchr : Z := 0x625f0.  Definition tfib_E_internal_strrchr : Z := 0x62630.
Definition tfib_A_internal_strnlen : Z := 0x62760.  Definition tfib_E_internal_strnlen : Z := 0x62790.
Definition tfib_A_internal_strncpy : Z := 0x627d4.  Definition tfib_E_internal_strncpy : Z := 0x62844.
Definition tfib_A_internal_strstr : Z := 0x62844.  Definition tfib_E_internal_strstr : Z := 0x628d8.
Definition tfib_A_mem_is_zero : Z := 0x628d8.  Definition tfib_E_mem_is_zero : Z := 0x6298c.
Definition tfib_A_internal_sigprocmask : Z := 0x6298c.  Definition tfib_E_internal_sigprocmask : Z := 0x6299c.
Definition tfib_A_BlockSignals : Z := 0x6299c.  Definition tfib_E_BlockSignals : Z := 0x62b7c.
Definition tfib_A_internal_iserror : Z := 0x62b88.  Definition tfib_E_internal_iserror : Z := 0x62ba8.
Definition tfib_A_internal_mmap : Z := 0x62ba8.  Definition tfib_E_internal_mmap : Z := 0x62bb4.
Definition tfib_A_internal_munmap : Z := 0x62bb4.  Definition tfib_E_internal_munmap : Z := 0x62bc0.
Definition tfib_A_internal_mprotect : Z := 0x62bc0.  Definition tfib_E_internal_mprotect : Z := 0x62bd0.
Definition tfib_A_internal_madvise : Z := 0x62bd0.  Definition tfib_E_internal_madvise : Z := 0x62bfc.
Definition tfib_A_internal_close : Z := 0x62bfc.  Definition tfib_E_internal_close : Z := 0x62c08.
Definition tfib_A_internal_open : Z := 0x62c08.  Definition tfib_E_internal_open : Z := 0x62c2c.
Definition tfib_A_internal_read : Z := 0x62c2c.  Definition tfib_E_internal_read : Z := 0x62c64.
Definition tfib_A_internal_write : Z := 0x62c64.  Definition tfib_E_internal_write : Z := 0x62c9c.
Definition tfib_A_internal_ftruncate : Z := 0x62c9c.  Definition tfib_E_internal_ftruncate : Z := 0x62cd4.
Definition tfib_A_internal_dup : Z := 0x62cd4.  Definition tfib_E_internal_dup : Z := 0x62ce0.
Definition tfib_A_internal_dup2 : Z := 0x62ce0.  Definition tfib_E_internal_dup2 : Z := 0x62cf0.
Definition tfib_A_internal_unlink : Z := 0x62cf0.  Definition tfib_E_internal_unlink : Z := 0x62d08.
Definition tfib_A_internal_sched_yield : Z := 0x62d08.  Definition tfib_E_internal_sched_yield : Z := 0x62d14.
Definition tfib_A_internal_usleep : Z := 0x62d14.  Definition tfib_E_internal_usleep : Z := 0x62d60.
Definition tfib_A_internal_execve : Z := 0x62d60.  Definition tfib_E_internal_execve : Z := 0x62d6c.
Definition tfib_A_internal_exit : Z := 0x62d6c.  Definition tfib_E_internal_exit : Z := 0x62d80.
Definition tfib_A_FileExists : Z := 0x62d80.  Definition tfib_E_FileExists : Z := 0x62e00.
Definition tfib_A_DirExists : Z := 0x62e00.  Definition tfib_E_DirExists : Z := 0x62e64.
Definition tfib_A_GetTid : Z := 0x62e64.  Definition tfib_E_GetTid : Z := 0x62e70.
Definition tfib_A_GetEnv : Z := 0x62e70.  Definition tfib_E_GetEnv : Z := 0x62fa0.
Definition tfib_A_FutexWait : Z := 0x630a4.  Definition tfib_E_FutexWait : Z := 0x630c8.
Definition tfib_A_FutexWake : Z := 0x630c8.  Definition tfib_E_FutexWake : Z := 0x630ec.
Definition tfib_A_internal_ptrace : Z := 0x630ec.  Definition tfib_E_internal_ptrace : Z := 0x630f8.
Definition tfib_A_internal_waitpid : Z := 0x630f8.  Definition tfib_E_internal_waitpid : Z := 0x63108.
Definition tfib_A_internal_getpid : Z := 0x63108.  Definition tfib_E_internal_getpid : Z := 0x63114.
Definition tfib_A_internal_getppid : Z := 0x63114.  Definition tfib_E_internal_getppid : Z := 0x63120.
Definition tfib_A_internal_prctl : Z := 0x63120.  Definition tfib_E_internal_prctl : Z := 0x6312c.
Definition tfib_A_internal_sigaltstack : Z := 0x6312c.  Definition tfib_E_internal_sigaltstack : Z := 0x63138.
Definition tfib_A_internal_fork : Z := 0x63138.  Definition tfib_E_internal_fork : Z := 0x63150.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x63150.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x6327c.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x63454.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x63850.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x639bc.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x63ad4.
Definition tfib_A_GetPageSize : Z := 0x63ad4.  Definition tfib_E_GetPageSize : Z := 0x63adc.
Definition tfib_A_ReadBinaryName : Z := 0x63adc.  Definition tfib_E_ReadBinaryName : Z := 0x63b88.
Definition tfib_A_ReadLongProcessName : Z := 0x63b88.  Definition tfib_E_ReadLongProcessName : Z := 0x63ca8.
Definition tfib_A_internal_clone : Z := 0x63d70.  Definition tfib_E_internal_clone : Z := 0x63df0.
Definition tfib_A_GetHandleSignalMode : Z := 0x63df0.  Definition tfib_E_GetHandleSignalMode : Z := 0x63e4c.
Definition tfib_A_internal_start_thread : Z := 0x63e4c.  Definition tfib_E_internal_start_thread : Z := 0x63f18.
Definition tfib_A_InitializePlatformEarly : Z := 0x64014.  Definition tfib_E_InitializePlatformEarly : Z := 0x64018.
Definition tfib_A_CheckASLR : Z := 0x64018.  Definition tfib_E_CheckASLR : Z := 0x6401c.
Definition tfib_A_GetMmapGranularity : Z := 0x64268.  Definition tfib_E_GetMmapGranularity : Z := 0x6426c.
Definition tfib_A_ErrorIsOOM : Z := 0x6426c.  Definition tfib_E_ErrorIsOOM : Z := 0x64278.
Definition tfib_A_MmapOrDie : Z := 0x64278.  Definition tfib_E_MmapOrDie : Z := 0x64384.
Definition tfib_A_MmapNamed : Z := 0x64384.  Definition tfib_E_MmapNamed : Z := 0x643f8.
Definition tfib_A_UnmapOrDie : Z := 0x643f8.  Definition tfib_E_UnmapOrDie : Z := 0x64474.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x64474.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x64584.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x647b0.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x648b4.
Definition tfib_A_MmapFixedOrDie : Z := 0x648b4.  Definition tfib_E_MmapFixedOrDie : Z := 0x648c0.
Definition tfib_A_MmapFixedImpl : Z := 0x648c0.  Definition tfib_E_MmapFixedImpl : Z := 0x64a38.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x64a38.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x64a44.
Definition tfib_A_CloseFile : Z := 0x64c30.  Definition tfib_E_CloseFile : Z := 0x64c34.
Definition tfib_A_GetNamedMappingFd : Z := 0x64f54.  Definition tfib_E_GetNamedMappingFd : Z := 0x65160.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x65718.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x65724.
Definition tfib_A_Printf : Z := 0x65728.  Definition tfib_E_Printf : Z := 0x65774.
Definition tfib_A_SharedPrintfCode : Z := 0x65774.  Definition tfib_E_SharedPrintfCode : Z := 0x657d0.
Definition tfib_A_Report : Z := 0x657d0.  Definition tfib_E_Report : Z := 0x6581c.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x67314.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x67370.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x67370.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x675ac.
Definition tfib_A_SuppressionContext_Parse : Z := 0x675ac.  Definition tfib_E_SuppressionContext_Parse : Z := 0x678d0.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x67e70.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x67f40.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x67f40.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x68290.
Definition tfib_A_DTLS_Get : Z := 0x68290.  Definition tfib_E_DTLS_Get : Z := 0x682a0.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x684dc.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x68520.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x68520.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x68580.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x68580.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x689f8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x692b8.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x695dc.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x695e4.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x696e8.
Definition tfib_A_AddDieCallback : Z := 0x69e98.  Definition tfib_E_AddDieCallback : Z := 0x69f20.
Definition tfib_A_Die : Z := 0x69fe4.  Definition tfib_E_Die : Z := 0x6a0a4.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6a0a4.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6a0b0.
Definition tfib_A_CheckFailed : Z := 0x6a0b0.  Definition tfib_E_CheckFailed : Z := 0x6a168.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6a7c0.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6a8b8.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6a8b8.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6a9e4.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6ac0c.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6ac88.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6acbc.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6afa4.
Definition tfib_A_InitTlsSize : Z := 0x6afa4.  Definition tfib_E_InitTlsSize : Z := 0x6afa8.
Definition tfib_A_GetTls : Z := 0x6afa8.  Definition tfib_E_GetTls : Z := 0x6b398.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6b398.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6b468.
Definition tfib_A_AndroidLogInit : Z := 0x6b84c.  Definition tfib_E_AndroidLogInit : Z := 0x6b850.
Definition tfib_A_MonotonicNanoTime : Z := 0x6b880.  Definition tfib_E_MonotonicNanoTime : Z := 0x6b8c8.
Definition tfib_A_MapDynamicShadow : Z := 0x6b8c8.  Definition tfib_E_MapDynamicShadow : Z := 0x6bb14.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6bb14.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6bb18.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6bb18.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6bc24.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6bc24.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6bd28.
Definition tfib_A_GetThreadSelf : Z := 0x6bfa4.  Definition tfib_E_GetThreadSelf : Z := 0x6bfa8.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6c04c.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6c06c.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6c06c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6c10c.
Definition tfib_A_Atexit : Z := 0x6c158.  Definition tfib_E_Atexit : Z := 0x6c15c.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6c198.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6c25c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6c25c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6c2e4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6c2e4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6c35c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6c35c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6c440.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6c4fc.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6c630.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6c868.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6c998.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6c998.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6c9f8.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6c9f8.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6cac4.
Definition tfib_A_MmapNoAccess : Z := 0x6cad8.  Definition tfib_E_MmapNoAccess : Z := 0x6caf8.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6caf8.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6cb6c.
Definition tfib_A_SealedRepairReservation : Z := 0x6cb6c.  Definition tfib_E_SealedRepairReservation : Z := 0x6cc44.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6cc44.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6cc54.
Definition tfib_A_InitializeCoverage : Z := 0x6e44c.  Definition tfib_E_InitializeCoverage : Z := 0x6e490.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6e490.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6e4c0.
Definition tfib_A_StackStore_Store : Z := 0x6e8f4.  Definition tfib_E_StackStore_Store : Z := 0x6ea18.
Definition tfib_A_StackStore_Alloc : Z := 0x6ea18.  Definition tfib_E_StackStore_Alloc : Z := 0x6eb4c.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x6f400.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x6f4b4.
Definition tfib_A_StackDepotNode_store : Z := 0x70c08.  Definition tfib_E_StackDepotNode_store : Z := 0x70c64.
Definition tfib_A_StackDepotPut : Z := 0x70ef0.  Definition tfib_E_StackDepotPut : Z := 0x70f10.
Definition tfib_A_StackDepotBase_Put : Z := 0x70f10.  Definition tfib_E_StackDepotBase_Put : Z := 0x71194.
Definition tfib_A_StackDepotGet : Z := 0x71194.  Definition tfib_E_StackDepotGet : Z := 0x712a4.
Definition tfib_A_StackDepotBase_lock : Z := 0x71684.  Definition tfib_E_StackDepotBase_lock : Z := 0x71714.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x71714.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x71814.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x71874.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x7187c.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x7187c.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x719dc.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x719dc.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x71a50.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x71ed8.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x71ff0.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x7503c.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x75040.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x76814.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x76818.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x78240.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x782fc.
Definition tfib_A_Unwind_Trace : Z := 0x782fc.  Definition tfib_E_Unwind_Trace : Z := 0x783d4.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x783d4.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x78648.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x78974.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x789b8.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x789b8.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x78d88.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x79058.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x79110.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x7a468.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x7a46c.
Definition tfib_A_lsan_register_root_region : Z := 0x7b074.  Definition tfib_E_lsan_register_root_region : Z := 0x7b3a4.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7b3a4.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7b82c.
Definition tfib_A_lsan_default_options : Z := 0x7b82c.  Definition tfib_E_lsan_default_options : Z := 0x7b838.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7e3f0.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7e408.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7e78c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7e808.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7e808.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7e8b8.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x7e8b8.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x7e8d0.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x7e8d0.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x7ea18.
Definition tfib_A_ubsan_default_options : Z := 0x7ea18.  Definition tfib_E_ubsan_default_options : Z := 0x7ea24.
Definition tfib_A_asan_default_options : Z := 0x7ea24.  Definition tfib_E_asan_default_options : Z := 0x7ea30.
Definition tfib_A_main : Z := 0x7ea30.  Definition tfib_E_main : Z := 0x7ecf4.
Definition tfib_A_target_alloc_init : Z := 0x7ecf4.  Definition tfib_E_target_alloc_init : Z := 0x7ecf8.
Definition tfib_A_target_alloc_count : Z := 0x7ecf8.  Definition tfib_E_target_alloc_count : Z := 0x7ed00.
Definition tfib_A_target_run : Z := 0x7ed00.  Definition tfib_E_target_run : Z := 0x7ee58.
Definition tfib_A_oft_exit_guard : Z := 0x7ee58.  Definition tfib_E_oft_exit_guard : Z := 0x7ee88.
Definition tfib_A_emit_printf : Z := 0x7ee88.  Definition tfib_E_emit_printf : Z := 0x7eed0.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7eed0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7f448.
Definition tfib_A_asan_module_ctor : Z := 0x7f448.  Definition tfib_E_asan_module_ctor : Z := 0x7f480.
Definition tfib_A_extenddftf2 : Z := 0x7f710.  Definition tfib_E_extenddftf2 : Z := 0x7f8a0.
Definition tfib_A_sysconf : Z := 0x854f0.  Definition tfib_E_sysconf : Z := 0x85718.
Definition tfib_A_init : Z := 0x85718.  Definition tfib_E_init : Z := 0x8571c.
Definition tfib_A_init_libc : Z := 0x8571c.  Definition tfib_E_init_libc : Z := 0x85948.
Definition tfib_A_libc_start_init : Z := 0x85948.  Definition tfib_E_libc_start_init : Z := 0x85994.
Definition tfib_A_libc_start_main : Z := 0x85994.  Definition tfib_E_libc_start_main : Z := 0x859f4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x859f4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x85a3c.
Definition tfib_A_static_init_tls : Z := 0x85b14.  Definition tfib_E_static_init_tls : Z := 0x85dc4.
Definition tfib_A_init_ssp : Z := 0x85dc4.  Definition tfib_E_init_ssp : Z := 0x85e24.
Definition tfib_A_stack_chk_fail : Z := 0x85e24.  Definition tfib_E_stack_chk_fail : Z := 0x85e2c.
Definition tfib_A_abort : Z := 0x85e74.  Definition tfib_E_abort : Z := 0x85f08.
Definition tfib_A_Exit : Z := 0x85f08.  Definition tfib_E_Exit : Z := 0x85f24.
Definition tfib_A_funcs_on_exit : Z := 0x85f54.  Definition tfib_E_funcs_on_exit : Z := 0x8601c.
Definition tfib_A_cxa_finalize : Z := 0x8601c.  Definition tfib_E_cxa_finalize : Z := 0x86020.
Definition tfib_A_atexit : Z := 0x86020.  Definition tfib_E_atexit : Z := 0x860e4.
Definition tfib_A_fini : Z := 0x860e8.  Definition tfib_E_fini : Z := 0x860ec.
Definition tfib_A_libc_exit_fini : Z := 0x860ec.  Definition tfib_E_libc_exit_fini : Z := 0x86138.
Definition tfib_A_exit : Z := 0x86138.  Definition tfib_E_exit : Z := 0x861ac.
Definition tfib_A_open : Z := 0x863ac.  Definition tfib_E_open : Z := 0x86490.
Definition tfib_A_syscall_ret : Z := 0x86490.  Definition tfib_E_syscall_ret : Z := 0x864c8.
Definition tfib_A_dl_iterate_phdr : Z := 0x864c8.  Definition tfib_E_dl_iterate_phdr : Z := 0x86670.
Definition tfib_A_libc_calloc : Z := 0x86c34.  Definition tfib_E_libc_calloc : Z := 0x86d6c.
Definition tfib_A_libc_malloc : Z := 0x86d6c.  Definition tfib_E_libc_malloc : Z := 0x86d70.
Definition tfib_A_libc_free : Z := 0x86d70.  Definition tfib_E_libc_free : Z := 0x86f3c.
Definition tfib_A_get_meta : Z := 0x86f3c.  Definition tfib_E_get_meta : Z := 0x8704c.
Definition tfib_A_malloc_alloc_meta : Z := 0x87424.  Definition tfib_E_malloc_alloc_meta : Z := 0x876fc.
Definition tfib_A_libc_malloc_impl : Z := 0x876fc.  Definition tfib_E_libc_malloc_impl : Z := 0x87a6c.
Definition tfib_A_alloc_slot : Z := 0x87a6c.  Definition tfib_E_alloc_slot : Z := 0x88310.
Definition tfib_A_enframe : Z := 0x88310.  Definition tfib_E_enframe : Z := 0x88460.
Definition tfib_A_malloc_allzerop : Z := 0x88460.  Definition tfib_E_malloc_allzerop : Z := 0x885d8.
Definition tfib_A_getrlimit : Z := 0x8a288.  Definition tfib_E_getrlimit : Z := 0x8a380.
Definition tfib_A_getrusage : Z := 0x8a380.  Definition tfib_E_getrusage : Z := 0x8a3a8.
Definition tfib_A_setrlimit : Z := 0x8a3a8.  Definition tfib_E_setrlimit : Z := 0x8a470.
Definition tfib_A_mmap : Z := 0x8a898.  Definition tfib_E_mmap : Z := 0x8a984.
Definition tfib_A_mprotect : Z := 0x8a984.  Definition tfib_E_mprotect : Z := 0x8a9cc.
Definition tfib_A_munmap : Z := 0x8aaa0.  Definition tfib_E_munmap : Z := 0x8aae8.
Definition tfib_A_sched_yield : Z := 0x8adac.  Definition tfib_E_sched_yield : Z := 0x8add0.
Definition tfib_A_raise : Z := 0x8ae2c.  Definition tfib_E_raise : Z := 0x8aea4.
Definition tfib_A_libc_sigaction : Z := 0x8aea4.  Definition tfib_E_libc_sigaction : Z := 0x8b078.
Definition tfib_A_musl_sigaltstack : Z := 0x8b170.  Definition tfib_E_musl_sigaltstack : Z := 0x8b1fc.
Definition tfib_A_dprintf : Z := 0x8b7d8.  Definition tfib_E_dprintf : Z := 0x8b83c.
Definition tfib_A_lockfile : Z := 0x8b83c.  Definition tfib_E_lockfile : Z := 0x8b938.
Definition tfib_A_unlockfile : Z := 0x8b938.  Definition tfib_E_unlockfile : Z := 0x8b998.
Definition tfib_A_stdio_read : Z := 0x8b528.  Definition tfib_E_stdio_read : Z := 0x8b640.
Definition tfib_A_stdio_write : Z := 0x8b648.  Definition tfib_E_stdio_write : Z := 0x8b7d8.
Definition tfib_A_aio_close : Z := 0x8b4f8.  Definition tfib_E_aio_close : Z := 0x8b4fc.
Definition tfib_A_stdio_close : Z := 0x8b4fc.  Definition tfib_E_stdio_close : Z := 0x8b528.
Definition tfib_A_fwritex : Z := 0x8bdcc.  Definition tfib_E_fwritex : Z := 0x8bf04.
Definition tfib_A_musl_fwrite : Z := 0x8bf04.  Definition tfib_E_musl_fwrite : Z := 0x8bfbc.
Definition tfib_A_towrite : Z := 0x8bfbc.  Definition tfib_E_towrite : Z := 0x8c010.
Definition tfib_A_stdio_exit : Z := 0x8bc28.  Definition tfib_E_stdio_exit : Z := 0x8bdcc.
Definition tfib_A_ofl_lock : Z := 0x8c010.  Definition tfib_E_ofl_lock : Z := 0x8c040.
Definition tfib_A_musl_vfprintf : Z := 0x8c18c.  Definition tfib_E_musl_vfprintf : Z := 0x8c33c.
Definition tfib_A_printf_core : Z := 0x8c33c.  Definition tfib_E_printf_core : Z := 0x8d16c.
Definition tfib_A_pop_arg : Z := 0x8d16c.  Definition tfib_E_pop_arg : Z := 0x8d2a0.
Definition tfib_A_pad : Z := 0x8d2a0.  Definition tfib_E_pad : Z := 0x8d374.
Definition tfib_A_fmt_fp : Z := 0x8d374.  Definition tfib_E_fmt_fp : Z := 0x8ea3c.
Definition tfib_A_lctrans : Z := 0x86888.  Definition tfib_E_lctrans : Z := 0x8688c.
Definition tfib_A_musl_wctomb : Z := 0x8ac14.  Definition tfib_E_musl_wctomb : Z := 0x8ac38.
Definition tfib_A_musl_wcrtomb : Z := 0x8aae8.  Definition tfib_E_musl_wcrtomb : Z := 0x8ac14.
Definition tfib_A_fpclassifyl : Z := 0x88e78.  Definition tfib_E_fpclassifyl : Z := 0x88ebc.
Definition tfib_A_letf2 : Z := 0x886b0.  Definition tfib_E_letf2 : Z := 0x88778.
Definition tfib_A_multf3 : Z := 0x88778.  Definition tfib_E_multf3 : Z := 0x88e78.
Definition tfib_A_floatsitf : Z := 0x896d4.  Definition tfib_E_floatsitf : Z := 0x897dc.
Definition tfib_A_scalbn : Z := 0x8a0e0.  Definition tfib_E_scalbn : Z := 0x8a178.
Definition tfib_A_subtf3 : Z := 0x896c4.  Definition tfib_E_subtf3 : Z := 0x896d4.
Definition tfib_A_addtf3 : Z := 0x88ebc.  Definition tfib_E_addtf3 : Z := 0x89688.
Definition tfib_A_fe_getround : Z := 0x89688.  Definition tfib_E_fe_getround : Z := 0x896b8.
Definition tfib_A_fixunstfsi : Z := 0x8ea44.  Definition tfib_E_fixunstfsi : Z := 0x8ead8.
Definition tfib_A_floatunsitf : Z := 0x8ead8.  Definition tfib_E_floatunsitf : Z := 0x8ebc4.
Definition tfib_A_fixtfsi : Z := 0x8a178.  Definition tfib_E_fixtfsi : Z := 0x8a220.
Definition tfib_A_divtf3 : Z := 0x897dc.  Definition tfib_E_divtf3 : Z := 0x8a0e0.
Definition tfib_A_musl_vprintf : Z := 0x8f29c.  Definition tfib_E_musl_vprintf : Z := 0x8f2b8.
Definition tfib_A_stdout_write : Z := 0x8c04c.  Definition tfib_E_stdout_write : Z := 0x8c0ec.
Definition tfib_A_musl_memcmp : Z := 0x8f91c.  Definition tfib_E_musl_memcmp : Z := 0x8f94c.
Definition tfib_A_musl_memcpy : Z := 0x8f94c.  Definition tfib_E_musl_memcpy : Z := 0x8fd50.
Definition tfib_A_musl_memset : Z := 0x8fd50.  Definition tfib_E_musl_memset : Z := 0x8fe48.
Definition tfib_A_musl_strchr : Z := 0x8fe48.  Definition tfib_E_musl_strchr : Z := 0x8fe84.
Definition tfib_A_strchrnul : Z := 0x8fe84.  Definition tfib_E_strchrnul : Z := 0x8ff64.
Definition tfib_A_musl_strlen : Z := 0x8ff9c.  Definition tfib_E_musl_strlen : Z := 0x9002c.
Definition tfib_A_musl_strnlen : Z := 0x901d8.  Definition tfib_E_musl_strnlen : Z := 0x9021c.
Definition tfib_A_musl_memchr : Z := 0x8f850.  Definition tfib_E_musl_memchr : Z := 0x8f91c.
Definition tfib_A_lock : Z := 0x9021c.  Definition tfib_E_lock : Z := 0x904a4.
Definition tfib_A_unlock : Z := 0x904a4.  Definition tfib_E_unlock : Z := 0x90518.
Definition tfib_A_sccp : Z := 0x90518.  Definition tfib_E_sccp : Z := 0x9053c.
Definition tfib_A_syscall_cp : Z := 0x9053c.  Definition tfib_E_syscall_cp : Z := 0x90540.
Definition tfib_A_tls_get_addr : Z := 0x90540.  Definition tfib_E_tls_get_addr : Z := 0x90564.
Definition tfib_A_pthread_atfork : Z := 0x9057c.  Definition tfib_E_pthread_atfork : Z := 0x90620.
Definition tfib_A_mremap : Z := 0x8a9cc.  Definition tfib_E_mremap : Z := 0x8aaa0.
Definition tfib_A_pthread_getspecific : Z := 0x915f4.  Definition tfib_E_pthread_getspecific : Z := 0x91610.
Definition tfib_A_pthread_key_create : Z := 0x9199c.  Definition tfib_E_pthread_key_create : Z := 0x91a70.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x91d14.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x91db8.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x91db8.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x91dc0.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x91dc0.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x91ed4.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x91ed4.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x91f00.
Definition tfib_A_pthread_setspecific : Z := 0x91f38.  Definition tfib_E_pthread_setspecific : Z := 0x91f6c.
Definition tfib_A_set_thread_area : Z := 0x91f74.  Definition tfib_E_set_thread_area : Z := 0x91f80.
Definition tfib_A_pthread_testcancel : Z := 0x91f6c.  Definition tfib_E_pthread_testcancel : Z := 0x91f70.
Definition tfib_A_testcancel : Z := 0x91f70.  Definition tfib_E_testcancel : Z := 0x91f74.
Definition tfib_A_musl_clock_gettime : Z := 0x928a0.  Definition tfib_E_musl_clock_gettime : Z := 0x92958.
Definition tfib_A_close : Z := 0x94f70.  Definition tfib_E_close : Z := 0x94fc4.
Definition tfib_A_musl_read : Z := 0x95050.  Definition tfib_E_musl_read : Z := 0x95084.
Definition tfib_A_vm_wait : Z := 0x925b0.  Definition tfib_E_vm_wait : Z := 0x92600.
Definition tfib_D_str_sealed : Z := 0x117ee.
Definition tfib_D_init_array_0_3 : Z := 0x96088.
Definition tfib_D_fini_array_0 : Z := 0x960a8.
Definition tfib_D_GOT_common_flags : Z := 0x96608.
Definition tfib_D_GOT_flags : Z := 0x96610.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x96618.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x96620.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x96628.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x96630.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x97180.
Definition tfib_D_GOT_environ : Z := 0x972a8.
Definition tfib_D_REAL_read : Z := 0x98348.
Definition tfib_D_REAL_memcpy : Z := 0x98470.
Definition tfib_D_REAL_memset : Z := 0x98478.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9af18.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9bd78.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0x9e578.
Definition tfib_D_asan_inited : Z := 0x9f258.
Definition tfib_D_replace_intrin_cached : Z := 0x9f259.
Definition tfib_D_kHighMemEnd : Z := 0x9f260.
Definition tfib_D_kMidMemBeg : Z := 0x9f268.
Definition tfib_D_kMidMemEnd : Z := 0x9f270.
Definition tfib_D_malloc_context_size : Z := 0x9f27c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1300a8.
Definition tfib_D_libc : Z := 0x5f17a0.
Definition tfib_at_img_lo : Z := YImgTop.IMG_LO.
Definition tfib_at_img_hi : Z := YImgTop.IMG_TOP.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2fa9c.
Definition tfib_at_rw_lo : Z := 0x98000.
Definition tfib_at_rw_len : Z := 0x55b000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x623a8.
Definition tfib_at_x_imemcpy : Z := 0x6232c.
Definition tfib_at_x_memset : Z := 0x8fd50.
Definition tfib_at_x_memcpy : Z := 0x8f94c.
Definition tfib_at_x_memiszero : Z := 0x628d8.
Definition tfib_at_x_istrncpy : Z := 0x627d4.
Definition tfib_at_x_sealed : Z := 0x117ee.
Definition tfib_at_x_popfree : Z := 0x35e88.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x85754.
Definition tfib_at_x_envscan_k : Z := 0x85760.
Definition tfib_at_x_pnscan : Z := 0x85818.
Definition tfib_at_x_pnscan_k : Z := 0x85824.
