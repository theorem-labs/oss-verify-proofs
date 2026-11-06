(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AB1w.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22e6c.   (* .rodata of the pinned fuzz_codec.asan image (sha256 7d470194ffdb), read from the section header: 0x102e0..0x22e6c *)
Definition tfib_text_lo : Z := 0x30b34.  Definition tfib_text_hi : Z := 0x9c230.
Definition tfib_init_array_lo : Z := 0x9d230.  Definition tfib_init_array_hi : Z := 0x9d250.
Definition tfib_fini_array_lo : Z := 0x9d250.  Definition tfib_fini_array_hi : Z := 0x9d260.
Definition tfib_preinit_array_lo : Z := 0x9d260.  Definition tfib_preinit_array_hi : Z := 0x9d268.
Definition tfib_data_rel_ro_lo : Z := 0x9d280.  Definition tfib_data_rel_ro_hi : Z := 0x9dab0.
Definition tfib_got_lo : Z := 0x9dab0.  Definition tfib_got_hi : Z := 0x9e808.
Definition tfib_data_lo : Z := 0x9f808.  Definition tfib_data_hi : Z := 0xa23c0.
Definition tfib_bss_lo : Z := 0xa2dc0.  Definition tfib_bss_hi : Z := 0x5facf0.
Definition tfib_tbss_lo : Z := 0x9c230.  Definition tfib_tbss_hi : Z := 0x9c244.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fb000.
Definition tfib_entry : Z := 0x30b34.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30b34.  Definition tfib_E_start : Z := 0x30b50.
Definition tfib_A_start_c : Z := 0x30b50.  Definition tfib_E_start_c : Z := 0x30b7c.
Definition tfib_A_do_init : Z := 0x30b7c.  Definition tfib_E_do_init : Z := 0x30bf0.
Definition tfib_A_do_fini : Z := 0x30bf0.  Definition tfib_E_do_fini : Z := 0x30c80.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30c80.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30cbc.
Definition tfib_A_InitializeAllocator : Z := 0x30e2c.  Definition tfib_E_InitializeAllocator : Z := 0x30e44.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30e44.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30fb0.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x3150c.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x31668.
Definition tfib_A_asan_free : Z := 0x31a3c.  Definition tfib_E_asan_free : Z := 0x31a64.
Definition tfib_A_Allocator_Deallocate : Z := 0x31a64.  Definition tfib_E_Allocator_Deallocate : Z := 0x31d1c.
Definition tfib_A_asan_malloc : Z := 0x31d1c.  Definition tfib_E_asan_malloc : Z := 0x31d78.
Definition tfib_A_Allocator_Allocate : Z := 0x31d78.  Definition tfib_E_Allocator_Allocate : Z := 0x32700.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x32e38.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x32f7c.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x33068.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x330c4.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x330c4.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33314.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33314.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33408.
Definition tfib_A_Allocator_CheckOptions : Z := 0x33408.  Definition tfib_E_Allocator_CheckOptions : Z := 0x334f0.
Definition tfib_A_Quarantine_Recycle : Z := 0x33924.  Definition tfib_E_Quarantine_Recycle : Z := 0x33b08.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x33b08.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x33c8c.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33dc4.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34048.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34048.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x341c8.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x341c8.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34390.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34390.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x3455c.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x3455c.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x345fc.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x345fc.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x34700.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34a28.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34b70.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x34b70.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x34ba8.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x35340.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x35628.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35d00.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35e78.
Definition tfib_A_Quarantine_Put : Z := 0x35e78.  Definition tfib_E_Quarantine_Put : Z := 0x36028.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36028.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3620c.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x3620c.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x364e4.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x364e4.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x3695c.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x3695c.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36a5c.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36a5c.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36d64.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36d64.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x370d4.
Definition tfib_A_RZSize2Log : Z := 0x370d4.  Definition tfib_E_RZSize2Log : Z := 0x371ec.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x374f4.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x375f0.
Definition tfib_A_AsanDeactivate : Z := 0x375f0.  Definition tfib_E_AsanDeactivate : Z := 0x376d8.
Definition tfib_A_AsanActivate : Z := 0x376d8.  Definition tfib_E_AsanActivate : Z := 0x377b4.
Definition tfib_A_FlagHandler_Parse : Z := 0x37c90.  Definition tfib_E_FlagHandler_Parse : Z := 0x37d78.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c830.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c908.
Definition tfib_A_FakeStack_Create : Z := 0x3c908.  Definition tfib_E_FakeStack_Create : Z := 0x3c9f4.
Definition tfib_A_FakeStack_GC : Z := 0x3ccb0.  Definition tfib_E_FakeStack_GC : Z := 0x3cf98.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d0cc.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d0fc.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d0fc.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d270.  Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d270.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d400.  Definition tfib_A_asan_stack_malloc_3 : Z := 0x3d400.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3d5ac.
Definition tfib_A_MemToShadow_3c1f4 : Z := 0x3d5ac.  Definition tfib_E_MemToShadow_3c1f4 : Z := 0x3d6e8.
Definition tfib_A_InitializeFlags : Z := 0x3d6e8.  Definition tfib_E_InitializeFlags : Z := 0x3e714.
Definition tfib_A_asan_register_globals : Z := 0x3ee20.  Definition tfib_E_asan_register_globals : Z := 0x3fc3c.
Definition tfib_A_asan_unregister_globals : Z := 0x3fc3c.  Definition tfib_E_asan_unregister_globals : Z := 0x40208.
Definition tfib_A_asan_register_elf_globals : Z := 0x40208.  Definition tfib_E_asan_register_elf_globals : Z := 0x40274.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x4095c.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x40bcc.
Definition tfib_A_asan_after_dynamic_init : Z := 0x40bcc.  Definition tfib_E_asan_after_dynamic_init : Z := 0x40ed4.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x41648.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x41798.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x421b4.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x422cc.
Definition tfib_A_strlen : Z := 0x422cc.  Definition tfib_E_strlen : Z := 0x422d0.
Definition tfib_A_strnlen : Z := 0x422d0.  Definition tfib_E_strnlen : Z := 0x422d4.
Definition tfib_A_strcmp : Z := 0x422d4.  Definition tfib_E_strcmp : Z := 0x422d8.
Definition tfib_A_strchr : Z := 0x422d8.  Definition tfib_E_strchr : Z := 0x422dc.
Definition tfib_A_memcmp : Z := 0x422dc.  Definition tfib_E_memcmp : Z := 0x422e0.
Definition tfib_A_memchr : Z := 0x422e4.  Definition tfib_E_memchr : Z := 0x422e8.
Definition tfib_A_frexpl : Z := 0x422e8.  Definition tfib_E_frexpl : Z := 0x422ec.
Definition tfib_A_read : Z := 0x422ec.  Definition tfib_E_read : Z := 0x422f0.
Definition tfib_A_fwrite : Z := 0x422f0.  Definition tfib_E_fwrite : Z := 0x422f4.
Definition tfib_A_time : Z := 0x422f4.  Definition tfib_E_time : Z := 0x422f8.
Definition tfib_A_gmtime_r : Z := 0x422f8.  Definition tfib_E_gmtime_r : Z := 0x422fc.
Definition tfib_A_vprintf : Z := 0x422fc.  Definition tfib_E_vprintf : Z := 0x42300.
Definition tfib_A_vfprintf : Z := 0x42300.  Definition tfib_E_vfprintf : Z := 0x42304.
Definition tfib_A_vsnprintf : Z := 0x42304.  Definition tfib_E_vsnprintf : Z := 0x42308.
Definition tfib_A_fprintf : Z := 0x42308.  Definition tfib_E_fprintf : Z := 0x4230c.
Definition tfib_A_snprintf : Z := 0x4230c.  Definition tfib_E_snprintf : Z := 0x42310.
Definition tfib_A_clock_gettime : Z := 0x42310.  Definition tfib_E_clock_gettime : Z := 0x42314.
Definition tfib_A_wcrtomb : Z := 0x42314.  Definition tfib_E_wcrtomb : Z := 0x42318.
Definition tfib_A_wctomb : Z := 0x42318.  Definition tfib_E_wctomb : Z := 0x4231c.
Definition tfib_A_strerror : Z := 0x4231c.  Definition tfib_E_strerror : Z := 0x42320.
Definition tfib_A__exit : Z := 0x42320.  Definition tfib_E__exit : Z := 0x42324.
Definition tfib_A_pthread_attr_getstack : Z := 0x42324.  Definition tfib_E_pthread_attr_getstack : Z := 0x42328.
Definition tfib_A___tls_get_addr : Z := 0x42328.  Definition tfib_E___tls_get_addr : Z := 0x4232c.
Definition tfib_A_fflush : Z := 0x4232c.  Definition tfib_E_fflush : Z := 0x42330.
Definition tfib_A_sem_init : Z := 0x42330.  Definition tfib_E_sem_init : Z := 0x42334.
Definition tfib_A_sem_destroy : Z := 0x42334.  Definition tfib_E_sem_destroy : Z := 0x42338.
Definition tfib_A_sem_wait : Z := 0x42338.  Definition tfib_E_sem_wait : Z := 0x4233c.
Definition tfib_A_sem_trywait : Z := 0x4233c.  Definition tfib_E_sem_trywait : Z := 0x42340.
Definition tfib_A_sem_timedwait : Z := 0x42340.  Definition tfib_E_sem_timedwait : Z := 0x42344.
Definition tfib_A_sem_post : Z := 0x42344.  Definition tfib_E_sem_post : Z := 0x42348.
Definition tfib_A_pthread_setcancelstate : Z := 0x42348.  Definition tfib_E_pthread_setcancelstate : Z := 0x4234c.
Definition tfib_A_send : Z := 0x4234c.  Definition tfib_E_send : Z := 0x42350.
Definition tfib_A_sendto : Z := 0x42350.  Definition tfib_E_sendto : Z := 0x42354.
Definition tfib_A_sigaltstack : Z := 0x42354.  Definition tfib_E_sigaltstack : Z := 0x42358.
Definition tfib_A_sigaction : Z := 0x42358.  Definition tfib_E_sigaction : Z := 0x4235c.
Definition tfib_A_icpt_strlen : Z := 0x4235c.  Definition tfib_E_icpt_strlen : Z := 0x425f0.
Definition tfib_A_icpt_strnlen : Z := 0x425f0.  Definition tfib_E_icpt_strnlen : Z := 0x42884.
Definition tfib_A_icpt_strcmp : Z := 0x42888.  Definition tfib_E_icpt_strcmp : Z := 0x42db8.
Definition tfib_A_icpt_strchr : Z := 0x42db8.  Definition tfib_E_icpt_strchr : Z := 0x43098.
Definition tfib_A_icpt_memcmp : Z := 0x43930.  Definition tfib_E_icpt_memcmp : Z := 0x439ec.
Definition tfib_A_icpt_memchr : Z := 0x43aa8.  Definition tfib_E_icpt_memchr : Z := 0x43d78.
Definition tfib_A_icpt_frexpl : Z := 0x43d78.  Definition tfib_E_icpt_frexpl : Z := 0x43ff0.
Definition tfib_A_icpt_read : Z := 0x43ff0.  Definition tfib_E_icpt_read : Z := 0x44260.
Definition tfib_A_icpt_fwrite : Z := 0x44260.  Definition tfib_E_icpt_fwrite : Z := 0x444d4.
Definition tfib_A_icpt_time : Z := 0x444d4.  Definition tfib_E_icpt_time : Z := 0x44770.
Definition tfib_A_icpt_gmtime_r : Z := 0x44978.  Definition tfib_E_icpt_gmtime_r : Z := 0x44bb8.
Definition tfib_A_icpt_vprintf : Z := 0x44bb8.  Definition tfib_E_icpt_vprintf : Z := 0x44c54.
Definition tfib_A_printf_common : Z := 0x44c54.  Definition tfib_E_printf_common : Z := 0x4571c.
Definition tfib_A_icpt_vfprintf : Z := 0x4571c.  Definition tfib_E_icpt_vfprintf : Z := 0x457d0.
Definition tfib_A_icpt_vsnprintf : Z := 0x457d0.  Definition tfib_E_icpt_vsnprintf : Z := 0x45ae8.
Definition tfib_A_icpt_fprintf : Z := 0x45ae8.  Definition tfib_E_icpt_fprintf : Z := 0x45bc0.
Definition tfib_A_icpt_clock_gettime : Z := 0x45c64.  Definition tfib_E_icpt_clock_gettime : Z := 0x45ebc.
Definition tfib_A_icpt_wcrtomb : Z := 0x45ebc.  Definition tfib_E_icpt_wcrtomb : Z := 0x4642c.
Definition tfib_A_icpt_wctomb : Z := 0x4642c.  Definition tfib_E_icpt_wctomb : Z := 0x46788.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46854.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46c3c.
Definition tfib_A_icpt_tls_get_addr : Z := 0x46c48.  Definition tfib_E_icpt_tls_get_addr : Z := 0x46cc4.
Definition tfib_A_icpt_sem_timedwait : Z := 0x46ed0.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47168.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47198.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x473c0.
Definition tfib_A_icpt_send : Z := 0x473c0.  Definition tfib_E_icpt_send : Z := 0x47674.
Definition tfib_A_icpt_sendto : Z := 0x47674.  Definition tfib_E_icpt_sendto : Z := 0x47938.
Definition tfib_A_icpt_sigaltstack : Z := 0x47938.  Definition tfib_E_icpt_sigaltstack : Z := 0x47b94.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47c68.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47e18.
Definition tfib_A_format_get_value_size : Z := 0x47e18.  Definition tfib_E_format_get_value_size : Z := 0x47fb0.
Definition tfib_A_ioctl_table_fill : Z := 0x48b5c.  Definition tfib_E_ioctl_table_fill : Z := 0x51834.
Definition tfib_A_Sort : Z := 0x51834.  Definition tfib_E_Sort : Z := 0x51990.
Definition tfib_A_memset : Z := 0x51990.  Definition tfib_E_memset : Z := 0x51994.
Definition tfib_A_memcpy : Z := 0x51994.  Definition tfib_E_memcpy : Z := 0x51998.
Definition tfib_A_asan_memset : Z := 0x51e34.  Definition tfib_E_asan_memset : Z := 0x52074.
Definition tfib_A_icpt_memset : Z := 0x52074.  Definition tfib_E_icpt_memset : Z := 0x52364.
Definition tfib_A_icpt_memcpy : Z := 0x52364.  Definition tfib_E_icpt_memcpy : Z := 0x52954.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x52954.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x5298c.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x5298c.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52990.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52990.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52994.
Definition tfib_A_FindDynamicShadowStart : Z := 0x52994.  Definition tfib_E_FindDynamicShadowStart : Z := 0x529f4.
Definition tfib_A_MemToShadow_510c4 : Z := 0x52a40.  Definition tfib_E_MemToShadow_510c4 : Z := 0x52b7c.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x52b7c.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52b80.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52b80.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52ce8.
Definition tfib_A_free : Z := 0x52ce8.  Definition tfib_E_free : Z := 0x52cec.
Definition tfib_A_malloc : Z := 0x52cec.  Definition tfib_E_malloc : Z := 0x52cf0.
Definition tfib_A_icpt_free : Z := 0x52cf0.  Definition tfib_E_icpt_free : Z := 0x52ec0.
Definition tfib_A_icpt_malloc : Z := 0x52ec0.  Definition tfib_E_icpt_malloc : Z := 0x5301c.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x5301c.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x530e8.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x530e8.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x530ec.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x530ec.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x531ec.
Definition tfib_A_HeapProfile_Print : Z := 0x53514.  Definition tfib_E_HeapProfile_Print : Z := 0x53680.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53b68.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53b78.
Definition tfib_A_CanPoisonMemory : Z := 0x53b78.  Definition tfib_E_CanPoisonMemory : Z := 0x53b8c.
Definition tfib_A_PoisonShadow : Z := 0x53b8c.  Definition tfib_E_PoisonShadow : Z := 0x54088.
Definition tfib_A_MemToShadow_5270c : Z := 0x54088.  Definition tfib_E_MemToShadow_5270c : Z := 0x541c4.
Definition tfib_A_asan_poison_memory_region : Z := 0x541c4.  Definition tfib_E_asan_poison_memory_region : Z := 0x54364.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x54364.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x544e4.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54514.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54858.
Definition tfib_A_AsanTSDInit : Z := 0x54c78.  Definition tfib_E_AsanTSDInit : Z := 0x54cf4.
Definition tfib_A_AsanTSDGet : Z := 0x54cf4.  Definition tfib_E_AsanTSDGet : Z := 0x54d34.
Definition tfib_A_AsanTSDSet : Z := 0x54d34.  Definition tfib_E_AsanTSDSet : Z := 0x54d74.
Definition tfib_A_PlatformTSDDtor : Z := 0x54d74.  Definition tfib_E_PlatformTSDDtor : Z := 0x54df8.
Definition tfib_A_InstallAtForkHandler : Z := 0x54df8.  Definition tfib_E_InstallAtForkHandler : Z := 0x54e14.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54e74.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54eb8.
Definition tfib_A_ReportDeadlySignal : Z := 0x555d0.  Definition tfib_E_ReportDeadlySignal : Z := 0x557dc.
Definition tfib_A_ReportDoubleFree : Z := 0x55ee4.  Definition tfib_E_ReportDoubleFree : Z := 0x56174.
Definition tfib_A_ReportGenericError : Z := 0x57a50.  Definition tfib_E_ReportGenericError : Z := 0x5830c.
Definition tfib_A_AsanInited : Z := 0x58a98.  Definition tfib_E_AsanInited : Z := 0x58ab0.
Definition tfib_A_asan_report_load1 : Z := 0x58ab0.  Definition tfib_E_asan_report_load1 : Z := 0x58b00.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58b00.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58b50.
Definition tfib_A_asan_report_load2 : Z := 0x58b50.  Definition tfib_E_asan_report_load2 : Z := 0x58ba0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58ba0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58bf0.
Definition tfib_A_asan_report_load4 : Z := 0x58bf0.  Definition tfib_E_asan_report_load4 : Z := 0x58c40.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58c40.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58c90.
Definition tfib_A_asan_report_load8 : Z := 0x58c90.  Definition tfib_E_asan_report_load8 : Z := 0x58ce0.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58ce0.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58d30.
Definition tfib_A_asan_report_load16 : Z := 0x58d30.  Definition tfib_E_asan_report_load16 : Z := 0x58d80.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58d80.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58dd0.
Definition tfib_A_asan_report_store1 : Z := 0x58dd0.  Definition tfib_E_asan_report_store1 : Z := 0x58e20.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58e20.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58e70.
Definition tfib_A_asan_report_store2 : Z := 0x58e70.  Definition tfib_E_asan_report_store2 : Z := 0x58ec0.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58ec0.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58f10.
Definition tfib_A_asan_report_store4 : Z := 0x58f10.  Definition tfib_E_asan_report_store4 : Z := 0x58f60.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58f60.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58fb0.
Definition tfib_A_asan_report_store8 : Z := 0x58fb0.  Definition tfib_E_asan_report_store8 : Z := 0x59000.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59000.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59050.
Definition tfib_A_asan_report_store16 : Z := 0x59050.  Definition tfib_E_asan_report_store16 : Z := 0x590a0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x590a0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x590f0.
Definition tfib_A_asan_report_load_n : Z := 0x590f0.  Definition tfib_E_asan_report_load_n : Z := 0x59140.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59140.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59190.
Definition tfib_A_asan_report_store_n : Z := 0x59190.  Definition tfib_E_asan_report_store_n : Z := 0x591e0.
Definition tfib_A_asan_report_exp_store_n : Z := 0x591e0.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59230.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59230.  Definition tfib_E_InitializeHighMemEnd : Z := 0x592b0.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x592b0.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x59664.
Definition tfib_A_AsanInitInternal : Z := 0x596f4.  Definition tfib_E_AsanInitInternal : Z := 0x599a8.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x599a8.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x59a48.
Definition tfib_A_asan_set_death_callback : Z := 0x59c10.  Definition tfib_E_asan_set_death_callback : Z := 0x59c14.
Definition tfib_A_asan_init : Z := 0x59c14.  Definition tfib_E_asan_init : Z := 0x59ca8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59ca8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59cac.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x59cac.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x59d10.
Definition tfib_A_OnLowLevelAllocate : Z := 0x59e84.  Definition tfib_E_OnLowLevelAllocate : Z := 0x59e8c.
Definition tfib_A_force_interface_symbols : Z := 0x59f10.  Definition tfib_E_force_interface_symbols : Z := 0x5a238.
Definition tfib_A_SealedReserveShadow : Z := 0x5a238.  Definition tfib_E_SealedReserveShadow : Z := 0x5a418.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a418.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a720.
Definition tfib_A_SetMallocContextSize : Z := 0x5a720.  Definition tfib_E_SetMallocContextSize : Z := 0x5a730.
Definition tfib_A_GetMallocContextSize : Z := 0x5a730.  Definition tfib_E_GetMallocContextSize : Z := 0x5a740.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x5a740.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x5a890.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x5ac70.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x5af10.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b374.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b3ac.
Definition tfib_A_asan_default_suppressions : Z := 0x5b654.  Definition tfib_E_asan_default_suppressions : Z := 0x5b660.
Definition tfib_A_InitializeSuppressions : Z := 0x5b660.  Definition tfib_E_InitializeSuppressions : Z := 0x5b6ec.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b6ec.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b754.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b754.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b7cc.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b7cc.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b834.
Definition tfib_A_IsAddrSuppressed : Z := 0x5b834.  Definition tfib_E_IsAddrSuppressed : Z := 0x5b980.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x5bc0c.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x5bc18.
Definition tfib_A_AsanThread_Create : Z := 0x5bd98.  Definition tfib_E_AsanThread_Create : Z := 0x5bf34.
Definition tfib_A_AsanThread_Destroy : Z := 0x5bf90.  Definition tfib_E_AsanThread_Destroy : Z := 0x5c1a8.
Definition tfib_A_GetCurrentThread : Z := 0x5c1a8.  Definition tfib_E_GetCurrentThread : Z := 0x5c1c8.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c1c8.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c36c.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c36c.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c3c4.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c3c4.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c41c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c41c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c64c.
Definition tfib_A_AsanThread_Init : Z := 0x5c64c.  Definition tfib_E_AsanThread_Init : Z := 0x5ca40.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5ca40.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5cb4c.
Definition tfib_A_CreateMainThread : Z := 0x5cb80.  Definition tfib_E_CreateMainThread : Z := 0x5cc90.
Definition tfib_A_SetCurrentThread : Z := 0x5cc90.  Definition tfib_E_SetCurrentThread : Z := 0x5cd70.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5cf74.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5d0b0.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5dd84.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5dd88.
Definition tfib_A_GetAsanThreadContext : Z := 0x5dd90.  Definition tfib_E_GetAsanThreadContext : Z := 0x5dfd0.
Definition tfib_A_internal_allocator : Z := 0x5e224.  Definition tfib_E_internal_allocator : Z := 0x5e37c.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5e568.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5e574.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5e574.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5e6c0.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e6c0.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e70c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e70c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e718.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e748.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e754.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e754.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e760.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5e760.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5e770.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5e77c.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5ea48.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5ea48.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5ee08.
Definition tfib_A_SealedSetInitFrame : Z := 0x5fd64.  Definition tfib_E_SealedSetInitFrame : Z := 0x5fd70.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fd70.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fe48.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fe48.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fee4.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60408.  Definition tfib_E_IncreaseTotalMmap : Z := 0x6044c.
Definition tfib_A_DecreaseTotalMmap : Z := 0x6044c.  Definition tfib_E_DecreaseTotalMmap : Z := 0x60470.
Definition tfib_A_CacheBinaryName : Z := 0x606c4.  Definition tfib_E_CacheBinaryName : Z := 0x607d8.
Definition tfib_A_RunMallocHooks : Z := 0x6097c.  Definition tfib_E_RunMallocHooks : Z := 0x60a34.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x60a34.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x60a38.
Definition tfib_A_RunFreeHooks : Z := 0x60a38.  Definition tfib_E_RunFreeHooks : Z := 0x60ae4.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x60ae4.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x60aec.
Definition tfib_A_sanitizer_free_hook : Z := 0x60aec.  Definition tfib_E_sanitizer_free_hook : Z := 0x60af0.
Definition tfib_A_WaitForDebugger : Z := 0x60b18.  Definition tfib_E_WaitForDebugger : Z := 0x60b64.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60e28.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x61068.
Definition tfib_A_sanitizer_set_report_path : Z := 0x61664.  Definition tfib_E_sanitizer_set_report_path : Z := 0x6167c.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x6167c.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x617c0.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x617c0.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x617c8.
Definition tfib_A_RegisterCommonFlags : Z := 0x61b10.  Definition tfib_E_RegisterCommonFlags : Z := 0x62db4.
Definition tfib_A_InitializeCommonFlags : Z := 0x62db4.  Definition tfib_E_InitializeCommonFlags : Z := 0x62dd8.
Definition tfib_A_FlagParser_parse_flag : Z := 0x6328c.  Definition tfib_E_FlagParser_parse_flag : Z := 0x6359c.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x6359c.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x636e0.
Definition tfib_A_FlagParser_ParseString : Z := 0x636e0.  Definition tfib_E_FlagParser_ParseString : Z := 0x637d4.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x63968.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x639c8.
Definition tfib_A_FlagParser_FlagParser : Z := 0x639c8.  Definition tfib_E_FlagParser_FlagParser : Z := 0x63a08.
Definition tfib_A_internal_atoll : Z := 0x63a08.  Definition tfib_E_internal_atoll : Z := 0x63af4.
Definition tfib_A_internal_simple_strtoll : Z := 0x63af4.  Definition tfib_E_internal_simple_strtoll : Z := 0x63c50.
Definition tfib_A_internal_memchr : Z := 0x63c50.  Definition tfib_E_internal_memchr : Z := 0x63c70.
Definition tfib_A_internal_memcmp : Z := 0x63c70.  Definition tfib_E_internal_memcmp : Z := 0x63ca8.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x63ca8.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x63ccc.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x63ccc.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x63d24.
Definition tfib_A_sanitizer_internal_memset : Z := 0x63d24.  Definition tfib_E_sanitizer_internal_memset : Z := 0x63d84.
Definition tfib_A_internal_strcspn : Z := 0x63d84.  Definition tfib_E_internal_strcspn : Z := 0x63dd8.
Definition tfib_A_internal_strchr : Z := 0x63dd8.  Definition tfib_E_internal_strchr : Z := 0x63e0c.
Definition tfib_A_internal_strdup : Z := 0x63e0c.  Definition tfib_E_internal_strdup : Z := 0x63e78.
Definition tfib_A_internal_strlen : Z := 0x63e78.  Definition tfib_E_internal_strlen : Z := 0x63e94.
Definition tfib_A_internal_strcmp : Z := 0x63e94.  Definition tfib_E_internal_strcmp : Z := 0x63ed8.
Definition tfib_A_internal_strncmp : Z := 0x63ed8.  Definition tfib_E_internal_strncmp : Z := 0x63f24.
Definition tfib_A_internal_strchrnul : Z := 0x63f24.  Definition tfib_E_internal_strchrnul : Z := 0x63f6c.
Definition tfib_A_internal_strrchr : Z := 0x63f6c.  Definition tfib_E_internal_strrchr : Z := 0x63fac.
Definition tfib_A_internal_strnlen : Z := 0x640dc.  Definition tfib_E_internal_strnlen : Z := 0x6410c.
Definition tfib_A_internal_strncpy : Z := 0x64150.  Definition tfib_E_internal_strncpy : Z := 0x641c0.
Definition tfib_A_internal_strstr : Z := 0x641c0.  Definition tfib_E_internal_strstr : Z := 0x64254.
Definition tfib_A_mem_is_zero : Z := 0x64254.  Definition tfib_E_mem_is_zero : Z := 0x64308.
Definition tfib_A_internal_sigprocmask : Z := 0x64308.  Definition tfib_E_internal_sigprocmask : Z := 0x64318.
Definition tfib_A_BlockSignals : Z := 0x64318.  Definition tfib_E_BlockSignals : Z := 0x644f8.
Definition tfib_A_internal_iserror : Z := 0x64504.  Definition tfib_E_internal_iserror : Z := 0x64524.
Definition tfib_A_internal_mmap : Z := 0x64524.  Definition tfib_E_internal_mmap : Z := 0x64530.
Definition tfib_A_internal_munmap : Z := 0x64530.  Definition tfib_E_internal_munmap : Z := 0x6453c.
Definition tfib_A_internal_mprotect : Z := 0x6453c.  Definition tfib_E_internal_mprotect : Z := 0x6454c.
Definition tfib_A_internal_madvise : Z := 0x6454c.  Definition tfib_E_internal_madvise : Z := 0x64578.
Definition tfib_A_internal_close : Z := 0x64578.  Definition tfib_E_internal_close : Z := 0x64584.
Definition tfib_A_internal_open : Z := 0x64584.  Definition tfib_E_internal_open : Z := 0x645a8.
Definition tfib_A_internal_read : Z := 0x645a8.  Definition tfib_E_internal_read : Z := 0x645e0.
Definition tfib_A_internal_write : Z := 0x645e0.  Definition tfib_E_internal_write : Z := 0x64618.
Definition tfib_A_internal_ftruncate : Z := 0x64618.  Definition tfib_E_internal_ftruncate : Z := 0x64650.
Definition tfib_A_internal_dup : Z := 0x64650.  Definition tfib_E_internal_dup : Z := 0x6465c.
Definition tfib_A_internal_dup2 : Z := 0x6465c.  Definition tfib_E_internal_dup2 : Z := 0x6466c.
Definition tfib_A_internal_unlink : Z := 0x6466c.  Definition tfib_E_internal_unlink : Z := 0x64684.
Definition tfib_A_internal_sched_yield : Z := 0x64684.  Definition tfib_E_internal_sched_yield : Z := 0x64690.
Definition tfib_A_internal_usleep : Z := 0x64690.  Definition tfib_E_internal_usleep : Z := 0x646dc.
Definition tfib_A_internal_execve : Z := 0x646dc.  Definition tfib_E_internal_execve : Z := 0x646e8.
Definition tfib_A_internal_exit : Z := 0x646e8.  Definition tfib_E_internal_exit : Z := 0x646fc.
Definition tfib_A_FileExists : Z := 0x646fc.  Definition tfib_E_FileExists : Z := 0x6477c.
Definition tfib_A_DirExists : Z := 0x6477c.  Definition tfib_E_DirExists : Z := 0x647e0.
Definition tfib_A_GetTid : Z := 0x647e0.  Definition tfib_E_GetTid : Z := 0x647ec.
Definition tfib_A_GetEnv : Z := 0x647ec.  Definition tfib_E_GetEnv : Z := 0x6491c.
Definition tfib_A_FutexWait : Z := 0x64a20.  Definition tfib_E_FutexWait : Z := 0x64a44.
Definition tfib_A_FutexWake : Z := 0x64a44.  Definition tfib_E_FutexWake : Z := 0x64a68.
Definition tfib_A_internal_ptrace : Z := 0x64a68.  Definition tfib_E_internal_ptrace : Z := 0x64a74.
Definition tfib_A_internal_waitpid : Z := 0x64a74.  Definition tfib_E_internal_waitpid : Z := 0x64a84.
Definition tfib_A_internal_getpid : Z := 0x64a84.  Definition tfib_E_internal_getpid : Z := 0x64a90.
Definition tfib_A_internal_getppid : Z := 0x64a90.  Definition tfib_E_internal_getppid : Z := 0x64a9c.
Definition tfib_A_internal_prctl : Z := 0x64a9c.  Definition tfib_E_internal_prctl : Z := 0x64aa8.
Definition tfib_A_internal_sigaltstack : Z := 0x64aa8.  Definition tfib_E_internal_sigaltstack : Z := 0x64ab4.
Definition tfib_A_internal_fork : Z := 0x64ab4.  Definition tfib_E_internal_fork : Z := 0x64acc.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x64acc.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x64bf8.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x64dd0.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x651cc.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x65338.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x65450.
Definition tfib_A_GetPageSize : Z := 0x65450.  Definition tfib_E_GetPageSize : Z := 0x65458.
Definition tfib_A_ReadBinaryName : Z := 0x65458.  Definition tfib_E_ReadBinaryName : Z := 0x65504.
Definition tfib_A_ReadLongProcessName : Z := 0x65504.  Definition tfib_E_ReadLongProcessName : Z := 0x65624.
Definition tfib_A_internal_clone : Z := 0x656ec.  Definition tfib_E_internal_clone : Z := 0x6576c.
Definition tfib_A_GetHandleSignalMode : Z := 0x6576c.  Definition tfib_E_GetHandleSignalMode : Z := 0x657c8.
Definition tfib_A_internal_start_thread : Z := 0x657c8.  Definition tfib_E_internal_start_thread : Z := 0x65894.
Definition tfib_A_InitializePlatformEarly : Z := 0x65990.  Definition tfib_E_InitializePlatformEarly : Z := 0x65994.
Definition tfib_A_CheckASLR : Z := 0x65994.  Definition tfib_E_CheckASLR : Z := 0x65998.
Definition tfib_A_GetMmapGranularity : Z := 0x65be4.  Definition tfib_E_GetMmapGranularity : Z := 0x65be8.
Definition tfib_A_ErrorIsOOM : Z := 0x65be8.  Definition tfib_E_ErrorIsOOM : Z := 0x65bf4.
Definition tfib_A_MmapOrDie : Z := 0x65bf4.  Definition tfib_E_MmapOrDie : Z := 0x65d00.
Definition tfib_A_MmapNamed : Z := 0x65d00.  Definition tfib_E_MmapNamed : Z := 0x65d74.
Definition tfib_A_UnmapOrDie : Z := 0x65d74.  Definition tfib_E_UnmapOrDie : Z := 0x65df0.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65df0.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65f00.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6612c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66230.
Definition tfib_A_MmapFixedOrDie : Z := 0x66230.  Definition tfib_E_MmapFixedOrDie : Z := 0x6623c.
Definition tfib_A_MmapFixedImpl : Z := 0x6623c.  Definition tfib_E_MmapFixedImpl : Z := 0x663b4.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x663b4.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x663c0.
Definition tfib_A_CloseFile : Z := 0x665ac.  Definition tfib_E_CloseFile : Z := 0x665b0.
Definition tfib_A_GetNamedMappingFd : Z := 0x668d0.  Definition tfib_E_GetNamedMappingFd : Z := 0x66adc.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67094.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x670a0.
Definition tfib_A_Printf : Z := 0x670a4.  Definition tfib_E_Printf : Z := 0x670f0.
Definition tfib_A_SharedPrintfCode : Z := 0x670f0.  Definition tfib_E_SharedPrintfCode : Z := 0x6714c.
Definition tfib_A_Report : Z := 0x6714c.  Definition tfib_E_Report : Z := 0x67198.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x68c90.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x68cec.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68cec.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68f28.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68f28.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6924c.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x697ec.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x698bc.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x698bc.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x69c0c.
Definition tfib_A_DTLS_Get : Z := 0x69c0c.  Definition tfib_E_DTLS_Get : Z := 0x69c1c.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x69e58.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x69e9c.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x69e9c.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x69efc.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69efc.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a374.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6ac34.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6af58.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6af60.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6b064.
Definition tfib_A_AddDieCallback : Z := 0x6b814.  Definition tfib_E_AddDieCallback : Z := 0x6b89c.
Definition tfib_A_Die : Z := 0x6b960.  Definition tfib_E_Die : Z := 0x6ba20.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6ba20.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6ba2c.
Definition tfib_A_CheckFailed : Z := 0x6ba2c.  Definition tfib_E_CheckFailed : Z := 0x6bae4.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c13c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c234.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c234.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c360.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c588.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c604.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c638.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c920.
Definition tfib_A_InitTlsSize : Z := 0x6c920.  Definition tfib_E_InitTlsSize : Z := 0x6c924.
Definition tfib_A_GetTls : Z := 0x6c924.  Definition tfib_E_GetTls : Z := 0x6cd14.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6cd14.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6cde4.
Definition tfib_A_AndroidLogInit : Z := 0x6d1c8.  Definition tfib_E_AndroidLogInit : Z := 0x6d1cc.
Definition tfib_A_MonotonicNanoTime : Z := 0x6d1fc.  Definition tfib_E_MonotonicNanoTime : Z := 0x6d244.
Definition tfib_A_MapDynamicShadow : Z := 0x6d244.  Definition tfib_E_MapDynamicShadow : Z := 0x6d490.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6d490.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6d494.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6d494.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6d5a0.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d5a0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d6a4.
Definition tfib_A_GetThreadSelf : Z := 0x6d920.  Definition tfib_E_GetThreadSelf : Z := 0x6d924.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6d9c8.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6d9e8.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d9e8.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6da88.
Definition tfib_A_Atexit : Z := 0x6dad4.  Definition tfib_E_Atexit : Z := 0x6dad8.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6db14.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6dbd8.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6dbd8.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6dc60.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6dc60.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6dcd8.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6dcd8.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6ddbc.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6de78.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6dfac.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6e1e4.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6e314.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6e314.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6e374.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6e374.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6e440.
Definition tfib_A_MmapNoAccess : Z := 0x6e454.  Definition tfib_E_MmapNoAccess : Z := 0x6e474.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6e474.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6e4e8.
Definition tfib_A_SealedRepairReservation : Z := 0x6e4e8.  Definition tfib_E_SealedRepairReservation : Z := 0x6e5c0.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6e5c0.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6e5d0.
Definition tfib_A_InitializeCoverage : Z := 0x6fdc8.  Definition tfib_E_InitializeCoverage : Z := 0x6fe0c.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6fe0c.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6fe3c.
Definition tfib_A_StackStore_Store : Z := 0x70270.  Definition tfib_E_StackStore_Store : Z := 0x70394.
Definition tfib_A_StackStore_Alloc : Z := 0x70394.  Definition tfib_E_StackStore_Alloc : Z := 0x704c8.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x70d7c.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x70e30.
Definition tfib_A_StackDepotNode_store : Z := 0x72584.  Definition tfib_E_StackDepotNode_store : Z := 0x725e0.
Definition tfib_A_StackDepotPut : Z := 0x7286c.  Definition tfib_E_StackDepotPut : Z := 0x7288c.
Definition tfib_A_StackDepotBase_Put : Z := 0x7288c.  Definition tfib_E_StackDepotBase_Put : Z := 0x72b10.
Definition tfib_A_StackDepotGet : Z := 0x72b10.  Definition tfib_E_StackDepotGet : Z := 0x72c20.
Definition tfib_A_StackDepotBase_lock : Z := 0x73000.  Definition tfib_E_StackDepotBase_lock : Z := 0x73090.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x73090.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x73190.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x731f0.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x731f8.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x731f8.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x73358.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x73358.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x733cc.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x73854.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x7396c.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x769b8.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x769bc.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x78190.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x78194.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79bbc.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79c78.
Definition tfib_A_Unwind_Trace : Z := 0x79c78.  Definition tfib_E_Unwind_Trace : Z := 0x79d50.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x79d50.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x79fc4.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x7a2f0.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x7a334.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x7a334.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x7a704.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a9d4.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7aa8c.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bde4.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bde8.
Definition tfib_A_lsan_register_root_region : Z := 0x7c9f0.  Definition tfib_E_lsan_register_root_region : Z := 0x7cd20.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cd20.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d1a8.
Definition tfib_A_lsan_default_options : Z := 0x7d1a8.  Definition tfib_E_lsan_default_options : Z := 0x7d1b4.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7fd6c.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7fd84.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80108.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80184.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80184.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80234.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x80234.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x8024c.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x8024c.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x80394.
Definition tfib_A_ubsan_default_options : Z := 0x80394.  Definition tfib_E_ubsan_default_options : Z := 0x803a0.
Definition tfib_A_asan_default_options : Z := 0x803a0.  Definition tfib_E_asan_default_options : Z := 0x803ac.
Definition tfib_A_main : Z := 0x803ac.  Definition tfib_E_main : Z := 0x80670.
Definition tfib_A_target_alloc_init : Z := 0x80670.  Definition tfib_E_target_alloc_init : Z := 0x80674.
Definition tfib_A_target_alloc_count : Z := 0x80674.  Definition tfib_E_target_alloc_count : Z := 0x8067c.
Definition tfib_A_target_run : Z := 0x8067c.  Definition tfib_E_target_run : Z := 0x807d4.
Definition tfib_A_oft_exit_guard : Z := 0x807d4.  Definition tfib_E_oft_exit_guard : Z := 0x80804.
Definition tfib_A_emit_printf : Z := 0x80804.  Definition tfib_E_emit_printf : Z := 0x8084c.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x8084c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x83364.  Definition tfib_A_check_personality : Z := 0x83364.  Definition tfib_E_check_personality : Z := 0x835d4.  Definition tfib_A_text_arg : Z := 0x835d4.  Definition tfib_E_text_arg : Z := 0x83798.  Definition tfib_A_check_text_scribble : Z := 0x83798.  Definition tfib_E_check_text_scribble : Z := 0x83ae4.  Definition tfib_A_check_text_seg7 : Z := 0x83ae4.  Definition tfib_E_check_text_seg7 : Z := 0x83b5c.  Definition tfib_A_check_text_counter : Z := 0x83b5c.  Definition tfib_E_check_text_counter : Z := 0x83df8.  Definition tfib_A_owed_counter_text : Z := 0x83df8.  Definition tfib_E_owed_counter_text : Z := 0x842b0.  Definition tfib_A_check_text_masks : Z := 0x842b0.  Definition tfib_E_check_text_masks : Z := 0x8438c.  Definition tfib_A_owed_seg7 : Z := 0x8438c.  Definition tfib_E_owed_seg7 : Z := 0x844dc.  Definition tfib_A_check_refusal : Z := 0x844dc.  Definition tfib_E_check_refusal : Z := 0x84590.  Definition tfib_A_check_range : Z := 0x84590.  Definition tfib_E_check_range : Z := 0x84640.  Definition tfib_A_check_bytes : Z := 0x84640.  Definition tfib_E_check_bytes : Z := 0x84774.  Definition tfib_A_asan_module_dtor : Z := 0x847ac.  Definition tfib_E_asan_module_dtor : Z := 0x847dc.  Definition tfib_A_diginet_personality_from_name : Z := 0x847dc.  Definition tfib_E_diginet_personality_from_name : Z := 0x84888.  Definition tfib_A_diginet_personality_of : Z := 0x84888.  Definition tfib_E_diginet_personality_of : Z := 0x848b4.  Definition tfib_A_diginet_sysex_encode : Z := 0x848b4.  Definition tfib_E_diginet_sysex_encode : Z := 0x84ba8.  Definition tfib_A_diginet_fader_encode : Z := 0x84ba8.  Definition tfib_E_diginet_fader_encode : Z := 0x84d5c.  Definition tfib_A_diginet_button_encode : Z := 0x84d5c.  Definition tfib_E_diginet_button_encode : Z := 0x84eb8.  Definition tfib_A_diginet_touch_encode : Z := 0x84eb8.  Definition tfib_E_diginet_touch_encode : Z := 0x8502c.  Definition tfib_A_diginet_vpot_encode : Z := 0x8502c.  Definition tfib_E_diginet_vpot_encode : Z := 0x85190.  Definition tfib_A_diginet_jog_encode : Z := 0x85190.  Definition tfib_E_diginet_jog_encode : Z := 0x852d0.  Definition tfib_A_diginet_ring_dot : Z := 0x852d0.  Definition tfib_E_diginet_ring_dot : Z := 0x852f0.  Definition tfib_A_diginet_ring_fill : Z := 0x852f0.  Definition tfib_E_diginet_ring_fill : Z := 0x85314.  Definition tfib_A_diginet_ring_encode : Z := 0x85314.  Definition tfib_E_diginet_ring_encode : Z := 0x855ac.  Definition tfib_A_diginet_meter_mask : Z := 0x855ac.  Definition tfib_E_diginet_meter_mask : Z := 0x855c8.  Definition tfib_A_diginet_meter_segments : Z := 0x855c8.  Definition tfib_E_diginet_meter_segments : Z := 0x85600.  Definition tfib_A_diginet_meter_encode : Z := 0x85600.  Definition tfib_E_diginet_meter_encode : Z := 0x85834.  Definition tfib_A_diginet_strip_leds_encode : Z := 0x85834.  Definition tfib_E_diginet_strip_leds_encode : Z := 0x85a7c.  Definition tfib_A_diginet_counter_leds_encode : Z := 0x85a7c.  Definition tfib_E_diginet_counter_leds_encode : Z := 0x85cc4.  Definition tfib_A_diginet_scribble_text : Z := 0x85cc4.  Definition tfib_E_diginet_scribble_text : Z := 0x85e24.  Definition tfib_A_diginet_scribble_encode : Z := 0x85e24.  Definition tfib_E_diginet_scribble_encode : Z := 0x860b4.  Definition tfib_A_diginet_seg7 : Z := 0x860b4.  Definition tfib_E_diginet_seg7 : Z := 0x86120.  Definition tfib_A_diginet_counter_text : Z := 0x86120.  Definition tfib_E_diginet_counter_text : Z := 0x86608.  Definition tfib_A_diginet_counter_encode : Z := 0x86608.  Definition tfib_E_diginet_counter_encode : Z := 0x868a8.
Definition tfib_A_asan_module_ctor : Z := 0x84774.  Definition tfib_E_asan_module_ctor : Z := 0x847ac.
Definition tfib_A_extenddftf2 : Z := 0x868b8.  Definition tfib_E_extenddftf2 : Z := 0x86a48.
Definition tfib_A_sysconf : Z := 0x8c698.  Definition tfib_E_sysconf : Z := 0x8c8c0.
Definition tfib_A_init : Z := 0x8c8c0.  Definition tfib_E_init : Z := 0x8c8c4.
Definition tfib_A_init_libc : Z := 0x8c8c4.  Definition tfib_E_init_libc : Z := 0x8caf0.
Definition tfib_A_libc_start_init : Z := 0x8caf0.  Definition tfib_E_libc_start_init : Z := 0x8cb3c.
Definition tfib_A_libc_start_main : Z := 0x8cb3c.  Definition tfib_E_libc_start_main : Z := 0x8cb9c.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8cb9c.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8cbe4.
Definition tfib_A_static_init_tls : Z := 0x8ccbc.  Definition tfib_E_static_init_tls : Z := 0x8cf6c.
Definition tfib_A_init_ssp : Z := 0x8cf6c.  Definition tfib_E_init_ssp : Z := 0x8cfcc.
Definition tfib_A_stack_chk_fail : Z := 0x8cfcc.  Definition tfib_E_stack_chk_fail : Z := 0x8cfd4.
Definition tfib_A_abort : Z := 0x8d01c.  Definition tfib_E_abort : Z := 0x8d0b0.
Definition tfib_A_Exit : Z := 0x8d0b0.  Definition tfib_E_Exit : Z := 0x8d0cc.
Definition tfib_A_funcs_on_exit : Z := 0x8d0fc.  Definition tfib_E_funcs_on_exit : Z := 0x8d1c4.
Definition tfib_A_cxa_finalize : Z := 0x8d1c4.  Definition tfib_E_cxa_finalize : Z := 0x8d1c8.
Definition tfib_A_atexit : Z := 0x8d1c8.  Definition tfib_E_atexit : Z := 0x8d28c.
Definition tfib_A_fini : Z := 0x8d290.  Definition tfib_E_fini : Z := 0x8d294.
Definition tfib_A_libc_exit_fini : Z := 0x8d294.  Definition tfib_E_libc_exit_fini : Z := 0x8d2e0.
Definition tfib_A_exit : Z := 0x8d2e0.  Definition tfib_E_exit : Z := 0x8d354.
Definition tfib_A_open : Z := 0x8d554.  Definition tfib_E_open : Z := 0x8d638.
Definition tfib_A_syscall_ret : Z := 0x8d638.  Definition tfib_E_syscall_ret : Z := 0x8d670.
Definition tfib_A_dl_iterate_phdr : Z := 0x8d670.  Definition tfib_E_dl_iterate_phdr : Z := 0x8d818.
Definition tfib_A_libc_calloc : Z := 0x8dddc.  Definition tfib_E_libc_calloc : Z := 0x8df14.
Definition tfib_A_libc_malloc : Z := 0x8df14.  Definition tfib_E_libc_malloc : Z := 0x8df18.
Definition tfib_A_libc_free : Z := 0x8df18.  Definition tfib_E_libc_free : Z := 0x8e0e4.
Definition tfib_A_get_meta : Z := 0x8e0e4.  Definition tfib_E_get_meta : Z := 0x8e1f4.
Definition tfib_A_malloc_alloc_meta : Z := 0x8e5cc.  Definition tfib_E_malloc_alloc_meta : Z := 0x8e8a4.
Definition tfib_A_libc_malloc_impl : Z := 0x8e8a4.  Definition tfib_E_libc_malloc_impl : Z := 0x8ec14.
Definition tfib_A_alloc_slot : Z := 0x8ec14.  Definition tfib_E_alloc_slot : Z := 0x8f4b8.
Definition tfib_A_enframe : Z := 0x8f4b8.  Definition tfib_E_enframe : Z := 0x8f608.
Definition tfib_A_malloc_allzerop : Z := 0x8f608.  Definition tfib_E_malloc_allzerop : Z := 0x8f780.
Definition tfib_A_getrlimit : Z := 0x91430.  Definition tfib_E_getrlimit : Z := 0x91528.
Definition tfib_A_getrusage : Z := 0x91528.  Definition tfib_E_getrusage : Z := 0x91550.
Definition tfib_A_setrlimit : Z := 0x91550.  Definition tfib_E_setrlimit : Z := 0x91618.
Definition tfib_A_mmap : Z := 0x91a40.  Definition tfib_E_mmap : Z := 0x91b2c.
Definition tfib_A_mprotect : Z := 0x91b2c.  Definition tfib_E_mprotect : Z := 0x91b74.
Definition tfib_A_munmap : Z := 0x91c48.  Definition tfib_E_munmap : Z := 0x91c90.
Definition tfib_A_sched_yield : Z := 0x91f54.  Definition tfib_E_sched_yield : Z := 0x91f78.
Definition tfib_A_raise : Z := 0x91fd4.  Definition tfib_E_raise : Z := 0x9204c.
Definition tfib_A_libc_sigaction : Z := 0x9204c.  Definition tfib_E_libc_sigaction : Z := 0x92220.
Definition tfib_A_musl_sigaltstack : Z := 0x92318.  Definition tfib_E_musl_sigaltstack : Z := 0x923a4.
Definition tfib_A_dprintf : Z := 0x92980.  Definition tfib_E_dprintf : Z := 0x929e4.
Definition tfib_A_lockfile : Z := 0x929e4.  Definition tfib_E_lockfile : Z := 0x92ae0.
Definition tfib_A_unlockfile : Z := 0x92ae0.  Definition tfib_E_unlockfile : Z := 0x92b40.
Definition tfib_A_stdio_read : Z := 0x926d0.  Definition tfib_E_stdio_read : Z := 0x927e8.
Definition tfib_A_stdio_write : Z := 0x927f0.  Definition tfib_E_stdio_write : Z := 0x92980.
Definition tfib_A_aio_close : Z := 0x926a0.  Definition tfib_E_aio_close : Z := 0x926a4.
Definition tfib_A_stdio_close : Z := 0x926a4.  Definition tfib_E_stdio_close : Z := 0x926d0.
Definition tfib_A_fwritex : Z := 0x92f74.  Definition tfib_E_fwritex : Z := 0x930ac.
Definition tfib_A_musl_fwrite : Z := 0x930ac.  Definition tfib_E_musl_fwrite : Z := 0x93164.
Definition tfib_A_towrite : Z := 0x93164.  Definition tfib_E_towrite : Z := 0x931b8.
Definition tfib_A_stdio_exit : Z := 0x92dd0.  Definition tfib_E_stdio_exit : Z := 0x92f74.
Definition tfib_A_ofl_lock : Z := 0x931b8.  Definition tfib_E_ofl_lock : Z := 0x931e8.
Definition tfib_A_musl_vfprintf : Z := 0x93334.  Definition tfib_E_musl_vfprintf : Z := 0x934e4.
Definition tfib_A_printf_core : Z := 0x934e4.  Definition tfib_E_printf_core : Z := 0x94314.
Definition tfib_A_pop_arg : Z := 0x94314.  Definition tfib_E_pop_arg : Z := 0x94448.
Definition tfib_A_pad : Z := 0x94448.  Definition tfib_E_pad : Z := 0x9451c.
Definition tfib_A_fmt_fp : Z := 0x9451c.  Definition tfib_E_fmt_fp : Z := 0x95be4.
Definition tfib_A_lctrans : Z := 0x8da30.  Definition tfib_E_lctrans : Z := 0x8da34.
Definition tfib_A_musl_wctomb : Z := 0x91dbc.  Definition tfib_E_musl_wctomb : Z := 0x91de0.
Definition tfib_A_musl_wcrtomb : Z := 0x91c90.  Definition tfib_E_musl_wcrtomb : Z := 0x91dbc.
Definition tfib_A_fpclassifyl : Z := 0x90020.  Definition tfib_E_fpclassifyl : Z := 0x90064.
Definition tfib_A_letf2 : Z := 0x8f858.  Definition tfib_E_letf2 : Z := 0x8f920.
Definition tfib_A_multf3 : Z := 0x8f920.  Definition tfib_E_multf3 : Z := 0x90020.
Definition tfib_A_floatsitf : Z := 0x9087c.  Definition tfib_E_floatsitf : Z := 0x90984.
Definition tfib_A_scalbn : Z := 0x91288.  Definition tfib_E_scalbn : Z := 0x91320.
Definition tfib_A_subtf3 : Z := 0x9086c.  Definition tfib_E_subtf3 : Z := 0x9087c.
Definition tfib_A_addtf3 : Z := 0x90064.  Definition tfib_E_addtf3 : Z := 0x90830.
Definition tfib_A_fe_getround : Z := 0x90830.  Definition tfib_E_fe_getround : Z := 0x90860.
Definition tfib_A_fixunstfsi : Z := 0x95bec.  Definition tfib_E_fixunstfsi : Z := 0x95c80.
Definition tfib_A_floatunsitf : Z := 0x95c80.  Definition tfib_E_floatunsitf : Z := 0x95d6c.
Definition tfib_A_fixtfsi : Z := 0x91320.  Definition tfib_E_fixtfsi : Z := 0x913c8.
Definition tfib_A_divtf3 : Z := 0x90984.  Definition tfib_E_divtf3 : Z := 0x91288.
Definition tfib_A_musl_vprintf : Z := 0x96444.  Definition tfib_E_musl_vprintf : Z := 0x96460.
Definition tfib_A_stdout_write : Z := 0x931f4.  Definition tfib_E_stdout_write : Z := 0x93294.
Definition tfib_A_musl_memcmp : Z := 0x96ac8.  Definition tfib_E_musl_memcmp : Z := 0x96af8.
Definition tfib_A_musl_memcpy : Z := 0x96af8.  Definition tfib_E_musl_memcpy : Z := 0x96efc.
Definition tfib_A_musl_memset : Z := 0x96efc.  Definition tfib_E_musl_memset : Z := 0x96ff4.
Definition tfib_A_musl_strchr : Z := 0x96ff4.  Definition tfib_E_musl_strchr : Z := 0x97030.
Definition tfib_A_strchrnul : Z := 0x97030.  Definition tfib_E_strchrnul : Z := 0x97110.
Definition tfib_A_musl_strlen : Z := 0x97148.  Definition tfib_E_musl_strlen : Z := 0x971d8.
Definition tfib_A_musl_strnlen : Z := 0x97384.  Definition tfib_E_musl_strnlen : Z := 0x973c8.
Definition tfib_A_musl_memchr : Z := 0x969fc.  Definition tfib_E_musl_memchr : Z := 0x96ac8.
Definition tfib_A_lock : Z := 0x973c8.  Definition tfib_E_lock : Z := 0x97650.
Definition tfib_A_unlock : Z := 0x97650.  Definition tfib_E_unlock : Z := 0x976c4.
Definition tfib_A_sccp : Z := 0x976c4.  Definition tfib_E_sccp : Z := 0x976e8.
Definition tfib_A_syscall_cp : Z := 0x976e8.  Definition tfib_E_syscall_cp : Z := 0x976ec.
Definition tfib_A_tls_get_addr : Z := 0x976ec.  Definition tfib_E_tls_get_addr : Z := 0x97710.
Definition tfib_A_pthread_atfork : Z := 0x97728.  Definition tfib_E_pthread_atfork : Z := 0x977cc.
Definition tfib_A_mremap : Z := 0x91b74.  Definition tfib_E_mremap : Z := 0x91c48.
Definition tfib_A_pthread_getspecific : Z := 0x987a0.  Definition tfib_E_pthread_getspecific : Z := 0x987bc.
Definition tfib_A_pthread_key_create : Z := 0x98b48.  Definition tfib_E_pthread_key_create : Z := 0x98c1c.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x98ec0.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x98f64.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x98f64.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x98f6c.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x98f6c.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x99080.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x99080.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x990ac.
Definition tfib_A_pthread_setspecific : Z := 0x990e4.  Definition tfib_E_pthread_setspecific : Z := 0x99118.
Definition tfib_A_set_thread_area : Z := 0x99120.  Definition tfib_E_set_thread_area : Z := 0x9912c.
Definition tfib_A_pthread_testcancel : Z := 0x99118.  Definition tfib_E_pthread_testcancel : Z := 0x9911c.
Definition tfib_A_testcancel : Z := 0x9911c.  Definition tfib_E_testcancel : Z := 0x99120.
Definition tfib_A_musl_clock_gettime : Z := 0x99a4c.  Definition tfib_E_musl_clock_gettime : Z := 0x99b04.
Definition tfib_A_close : Z := 0x9c11c.  Definition tfib_E_close : Z := 0x9c170.
Definition tfib_A_musl_read : Z := 0x9c1fc.  Definition tfib_E_musl_read : Z := 0x9c230.
Definition tfib_A_vm_wait : Z := 0x9975c.  Definition tfib_E_vm_wait : Z := 0x997ac.
Definition tfib_D_str_sealed : Z := 0x11825.
Definition tfib_D_init_array_0_3 : Z := 0x9d230.
Definition tfib_D_fini_array_0 : Z := 0x9d250.
Definition tfib_D_GOT_common_flags : Z := 0x9db00.
Definition tfib_D_GOT_flags : Z := 0x9db08.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9db10.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9db18.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9db20.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9db28.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9e678.
Definition tfib_D_GOT_environ : Z := 0x9e7a0.
Definition tfib_D_REAL_read : Z := 0x9f848.
Definition tfib_D_REAL_memcpy : Z := 0x9f970.
Definition tfib_D_REAL_memset : Z := 0x9f978.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa2e18.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa3c78.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa6478.
Definition tfib_D_asan_inited : Z := 0xa7158.
Definition tfib_D_replace_intrin_cached : Z := 0xa7159.
Definition tfib_D_kHighMemEnd : Z := 0xa7160.
Definition tfib_D_kMidMemBeg : Z := 0xa7168.
Definition tfib_D_kMidMemEnd : Z := 0xa7170.
Definition tfib_D_malloc_context_size : Z := 0xa717c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x137fa8.
Definition tfib_D_libc : Z := 0x5f96a0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fb000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30b34.
Definition tfib_at_rw_lo : Z := 0x9f000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63d24.
Definition tfib_at_x_imemcpy : Z := 0x63ca8.
Definition tfib_at_x_memset : Z := 0x96efc.
Definition tfib_at_x_memcpy : Z := 0x96af8.
Definition tfib_at_x_memiszero : Z := 0x64254.
Definition tfib_at_x_istrncpy : Z := 0x64150.
Definition tfib_at_x_sealed : Z := 0x11825.
Definition tfib_at_x_popfree : Z := 0x36f20.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8c8fc.
Definition tfib_at_x_envscan_k : Z := 0x8c908.
Definition tfib_at_x_pnscan : Z := 0x8c9c0.
Definition tfib_at_x_pnscan_k : Z := 0x8c9cc.
Definition tfib_at_stops_more : list Z := (0x34b94 :: 0x361b8 :: 0x54030 :: 0x5a3e8 :: 0x5a3fc :: 0x5a410 :: 0x5fda0 :: 0x5fe70 :: 0x6d39c :: 0x6e2a8 :: 0x6e438 :: 0x78190 :: nil)%list.
