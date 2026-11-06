(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AB1w.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1w.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YImgTopU.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22ecc.   (* .rodata of the pinned fuzz_codec.asan-ubsan image (sha256 73109e32e77b), read from the section header: 0x102e0..0x22ecc *)
Definition tfib_text_lo : Z := 0x30c84.  Definition tfib_text_hi : Z := 0x9cb68.
Definition tfib_init_array_lo : Z := 0x9db68.  Definition tfib_init_array_hi : Z := 0x9db88.
Definition tfib_fini_array_lo : Z := 0x9db88.  Definition tfib_fini_array_hi : Z := 0x9db98.
Definition tfib_preinit_array_lo : Z := 0x9db98.  Definition tfib_preinit_array_hi : Z := 0x9dba0.
Definition tfib_data_rel_ro_lo : Z := 0x9dba0.  Definition tfib_data_rel_ro_hi : Z := 0x9e3d0.
Definition tfib_got_lo : Z := 0x9e3d0.  Definition tfib_got_hi : Z := 0x9f128.
Definition tfib_data_lo : Z := 0xa0128.  Definition tfib_data_hi : Z := 0xa2ce0.
Definition tfib_bss_lo : Z := 0xa3700.  Definition tfib_bss_hi : Z := 0x5fb630.
Definition tfib_tbss_lo : Z := 0x9cb68.  Definition tfib_tbss_hi : Z := 0x9cb7c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fc000.
Definition tfib_entry : Z := 0x30c84.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30c84.  Definition tfib_E_start : Z := 0x30ca0.
Definition tfib_A_start_c : Z := 0x30ca0.  Definition tfib_E_start_c : Z := 0x30ccc.
Definition tfib_A_do_init : Z := 0x30ccc.  Definition tfib_E_do_init : Z := 0x30d40.
Definition tfib_A_do_fini : Z := 0x30d40.  Definition tfib_E_do_fini : Z := 0x30dd0.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30dd0.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30e0c.
Definition tfib_A_InitializeAllocator : Z := 0x30f7c.  Definition tfib_E_InitializeAllocator : Z := 0x30f94.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30f94.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x31100.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x3165c.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x317b8.
Definition tfib_A_asan_free : Z := 0x31b8c.  Definition tfib_E_asan_free : Z := 0x31bb4.
Definition tfib_A_Allocator_Deallocate : Z := 0x31bb4.  Definition tfib_E_Allocator_Deallocate : Z := 0x31e6c.
Definition tfib_A_asan_malloc : Z := 0x31e6c.  Definition tfib_E_asan_malloc : Z := 0x31ec8.
Definition tfib_A_Allocator_Allocate : Z := 0x31ec8.  Definition tfib_E_Allocator_Allocate : Z := 0x32850.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x32f88.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x330cc.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x331b8.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x33214.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x33214.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33464.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33464.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33558.
Definition tfib_A_Allocator_CheckOptions : Z := 0x33558.  Definition tfib_E_Allocator_CheckOptions : Z := 0x33640.
Definition tfib_A_Quarantine_Recycle : Z := 0x33a74.  Definition tfib_E_Quarantine_Recycle : Z := 0x33c58.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x33c58.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x33ddc.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33f14.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34198.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34198.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x34318.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34318.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x344e0.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x344e0.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x346ac.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x346ac.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x3474c.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x3474c.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x34850.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34b78.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34cc0.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x34cc0.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x34cf8.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x35490.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x35778.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35e50.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35fc8.
Definition tfib_A_Quarantine_Put : Z := 0x35fc8.  Definition tfib_E_Quarantine_Put : Z := 0x36178.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36178.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x3635c.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x3635c.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x36634.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x36634.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x36aac.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36aac.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36bac.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36bac.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36eb4.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36eb4.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x37224.
Definition tfib_A_RZSize2Log : Z := 0x37224.  Definition tfib_E_RZSize2Log : Z := 0x3733c.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x37644.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x37740.
Definition tfib_A_AsanDeactivate : Z := 0x37740.  Definition tfib_E_AsanDeactivate : Z := 0x37828.
Definition tfib_A_AsanActivate : Z := 0x37828.  Definition tfib_E_AsanActivate : Z := 0x37904.
Definition tfib_A_FlagHandler_Parse : Z := 0x37de0.  Definition tfib_E_FlagHandler_Parse : Z := 0x37ec8.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c980.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3ca58.
Definition tfib_A_FakeStack_Create : Z := 0x3ca58.  Definition tfib_E_FakeStack_Create : Z := 0x3cb44.
Definition tfib_A_FakeStack_GC : Z := 0x3ce00.  Definition tfib_E_FakeStack_GC : Z := 0x3d0e8.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d21c.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d24c.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d24c.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d3c0.  Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d3c0.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d550.  Definition tfib_A_asan_stack_malloc_3 : Z := 0x3d550.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3d6fc.
Definition tfib_A_MemToShadow_3c1f4 : Z := 0x3d6fc.  Definition tfib_E_MemToShadow_3c1f4 : Z := 0x3d838.
Definition tfib_A_InitializeFlags : Z := 0x3d838.  Definition tfib_E_InitializeFlags : Z := 0x3e864.
Definition tfib_A_asan_register_globals : Z := 0x3ef70.  Definition tfib_E_asan_register_globals : Z := 0x3fd8c.
Definition tfib_A_asan_unregister_globals : Z := 0x3fd8c.  Definition tfib_E_asan_unregister_globals : Z := 0x40358.
Definition tfib_A_asan_register_elf_globals : Z := 0x40358.  Definition tfib_E_asan_register_elf_globals : Z := 0x403c4.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x40aac.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x40d1c.
Definition tfib_A_asan_after_dynamic_init : Z := 0x40d1c.  Definition tfib_E_asan_after_dynamic_init : Z := 0x41024.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x41798.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x418e8.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x42304.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x4241c.
Definition tfib_A_strlen : Z := 0x4241c.  Definition tfib_E_strlen : Z := 0x42420.
Definition tfib_A_strnlen : Z := 0x42420.  Definition tfib_E_strnlen : Z := 0x42424.
Definition tfib_A_strcmp : Z := 0x42424.  Definition tfib_E_strcmp : Z := 0x42428.
Definition tfib_A_strchr : Z := 0x42428.  Definition tfib_E_strchr : Z := 0x4242c.
Definition tfib_A_memcmp : Z := 0x4242c.  Definition tfib_E_memcmp : Z := 0x42430.
Definition tfib_A_memchr : Z := 0x42434.  Definition tfib_E_memchr : Z := 0x42438.
Definition tfib_A_frexpl : Z := 0x42438.  Definition tfib_E_frexpl : Z := 0x4243c.
Definition tfib_A_read : Z := 0x4243c.  Definition tfib_E_read : Z := 0x42440.
Definition tfib_A_fwrite : Z := 0x42440.  Definition tfib_E_fwrite : Z := 0x42444.
Definition tfib_A_time : Z := 0x42444.  Definition tfib_E_time : Z := 0x42448.
Definition tfib_A_gmtime_r : Z := 0x42448.  Definition tfib_E_gmtime_r : Z := 0x4244c.
Definition tfib_A_vprintf : Z := 0x4244c.  Definition tfib_E_vprintf : Z := 0x42450.
Definition tfib_A_vfprintf : Z := 0x42450.  Definition tfib_E_vfprintf : Z := 0x42454.
Definition tfib_A_vsnprintf : Z := 0x42454.  Definition tfib_E_vsnprintf : Z := 0x42458.
Definition tfib_A_fprintf : Z := 0x42458.  Definition tfib_E_fprintf : Z := 0x4245c.
Definition tfib_A_snprintf : Z := 0x4245c.  Definition tfib_E_snprintf : Z := 0x42460.
Definition tfib_A_clock_gettime : Z := 0x42460.  Definition tfib_E_clock_gettime : Z := 0x42464.
Definition tfib_A_wcrtomb : Z := 0x42464.  Definition tfib_E_wcrtomb : Z := 0x42468.
Definition tfib_A_wctomb : Z := 0x42468.  Definition tfib_E_wctomb : Z := 0x4246c.
Definition tfib_A_strerror : Z := 0x4246c.  Definition tfib_E_strerror : Z := 0x42470.
Definition tfib_A__exit : Z := 0x42470.  Definition tfib_E__exit : Z := 0x42474.
Definition tfib_A_pthread_attr_getstack : Z := 0x42474.  Definition tfib_E_pthread_attr_getstack : Z := 0x42478.
Definition tfib_A___tls_get_addr : Z := 0x42478.  Definition tfib_E___tls_get_addr : Z := 0x4247c.
Definition tfib_A_fflush : Z := 0x4247c.  Definition tfib_E_fflush : Z := 0x42480.
Definition tfib_A_sem_init : Z := 0x42480.  Definition tfib_E_sem_init : Z := 0x42484.
Definition tfib_A_sem_destroy : Z := 0x42484.  Definition tfib_E_sem_destroy : Z := 0x42488.
Definition tfib_A_sem_wait : Z := 0x42488.  Definition tfib_E_sem_wait : Z := 0x4248c.
Definition tfib_A_sem_trywait : Z := 0x4248c.  Definition tfib_E_sem_trywait : Z := 0x42490.
Definition tfib_A_sem_timedwait : Z := 0x42490.  Definition tfib_E_sem_timedwait : Z := 0x42494.
Definition tfib_A_sem_post : Z := 0x42494.  Definition tfib_E_sem_post : Z := 0x42498.
Definition tfib_A_pthread_setcancelstate : Z := 0x42498.  Definition tfib_E_pthread_setcancelstate : Z := 0x4249c.
Definition tfib_A_send : Z := 0x4249c.  Definition tfib_E_send : Z := 0x424a0.
Definition tfib_A_sendto : Z := 0x424a0.  Definition tfib_E_sendto : Z := 0x424a4.
Definition tfib_A_sigaltstack : Z := 0x424a4.  Definition tfib_E_sigaltstack : Z := 0x424a8.
Definition tfib_A_sigaction : Z := 0x424a8.  Definition tfib_E_sigaction : Z := 0x424ac.
Definition tfib_A_icpt_strlen : Z := 0x424ac.  Definition tfib_E_icpt_strlen : Z := 0x42740.
Definition tfib_A_icpt_strnlen : Z := 0x42740.  Definition tfib_E_icpt_strnlen : Z := 0x429d4.
Definition tfib_A_icpt_strcmp : Z := 0x429d8.  Definition tfib_E_icpt_strcmp : Z := 0x42f08.
Definition tfib_A_icpt_strchr : Z := 0x42f08.  Definition tfib_E_icpt_strchr : Z := 0x431e8.
Definition tfib_A_icpt_memcmp : Z := 0x43a80.  Definition tfib_E_icpt_memcmp : Z := 0x43b3c.
Definition tfib_A_icpt_memchr : Z := 0x43bf8.  Definition tfib_E_icpt_memchr : Z := 0x43ec8.
Definition tfib_A_icpt_frexpl : Z := 0x43ec8.  Definition tfib_E_icpt_frexpl : Z := 0x44140.
Definition tfib_A_icpt_read : Z := 0x44140.  Definition tfib_E_icpt_read : Z := 0x443b0.
Definition tfib_A_icpt_fwrite : Z := 0x443b0.  Definition tfib_E_icpt_fwrite : Z := 0x44624.
Definition tfib_A_icpt_time : Z := 0x44624.  Definition tfib_E_icpt_time : Z := 0x448c0.
Definition tfib_A_icpt_gmtime_r : Z := 0x44ac8.  Definition tfib_E_icpt_gmtime_r : Z := 0x44d08.
Definition tfib_A_icpt_vprintf : Z := 0x44d08.  Definition tfib_E_icpt_vprintf : Z := 0x44da4.
Definition tfib_A_printf_common : Z := 0x44da4.  Definition tfib_E_printf_common : Z := 0x4586c.
Definition tfib_A_icpt_vfprintf : Z := 0x4586c.  Definition tfib_E_icpt_vfprintf : Z := 0x45920.
Definition tfib_A_icpt_vsnprintf : Z := 0x45920.  Definition tfib_E_icpt_vsnprintf : Z := 0x45c38.
Definition tfib_A_icpt_fprintf : Z := 0x45c38.  Definition tfib_E_icpt_fprintf : Z := 0x45d10.
Definition tfib_A_icpt_clock_gettime : Z := 0x45db4.  Definition tfib_E_icpt_clock_gettime : Z := 0x4600c.
Definition tfib_A_icpt_wcrtomb : Z := 0x4600c.  Definition tfib_E_icpt_wcrtomb : Z := 0x4657c.
Definition tfib_A_icpt_wctomb : Z := 0x4657c.  Definition tfib_E_icpt_wctomb : Z := 0x468d8.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x469a4.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46d8c.
Definition tfib_A_icpt_tls_get_addr : Z := 0x46d98.  Definition tfib_E_icpt_tls_get_addr : Z := 0x46e14.
Definition tfib_A_icpt_sem_timedwait : Z := 0x47020.  Definition tfib_E_icpt_sem_timedwait : Z := 0x472b8.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x472e8.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47510.
Definition tfib_A_icpt_send : Z := 0x47510.  Definition tfib_E_icpt_send : Z := 0x477c4.
Definition tfib_A_icpt_sendto : Z := 0x477c4.  Definition tfib_E_icpt_sendto : Z := 0x47a88.
Definition tfib_A_icpt_sigaltstack : Z := 0x47a88.  Definition tfib_E_icpt_sigaltstack : Z := 0x47ce4.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47db8.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47f68.
Definition tfib_A_format_get_value_size : Z := 0x47f68.  Definition tfib_E_format_get_value_size : Z := 0x48100.
Definition tfib_A_ioctl_table_fill : Z := 0x48cac.  Definition tfib_E_ioctl_table_fill : Z := 0x51984.
Definition tfib_A_Sort : Z := 0x51984.  Definition tfib_E_Sort : Z := 0x51ae0.
Definition tfib_A_memset : Z := 0x51ae0.  Definition tfib_E_memset : Z := 0x51ae4.
Definition tfib_A_memcpy : Z := 0x51ae4.  Definition tfib_E_memcpy : Z := 0x51ae8.
Definition tfib_A_asan_memset : Z := 0x51f84.  Definition tfib_E_asan_memset : Z := 0x521c4.
Definition tfib_A_icpt_memset : Z := 0x521c4.  Definition tfib_E_icpt_memset : Z := 0x524b4.
Definition tfib_A_icpt_memcpy : Z := 0x524b4.  Definition tfib_E_icpt_memcpy : Z := 0x52aa4.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x52aa4.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x52adc.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52adc.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52ae0.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52ae0.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52ae4.
Definition tfib_A_FindDynamicShadowStart : Z := 0x52ae4.  Definition tfib_E_FindDynamicShadowStart : Z := 0x52b44.
Definition tfib_A_MemToShadow_510c4 : Z := 0x52b90.  Definition tfib_E_MemToShadow_510c4 : Z := 0x52ccc.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x52ccc.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x52cd0.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52cd0.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52e38.
Definition tfib_A_free : Z := 0x52e38.  Definition tfib_E_free : Z := 0x52e3c.
Definition tfib_A_malloc : Z := 0x52e3c.  Definition tfib_E_malloc : Z := 0x52e40.
Definition tfib_A_icpt_free : Z := 0x52e40.  Definition tfib_E_icpt_free : Z := 0x53010.
Definition tfib_A_icpt_malloc : Z := 0x53010.  Definition tfib_E_icpt_malloc : Z := 0x5316c.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x5316c.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x53238.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53238.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x5323c.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x5323c.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x5333c.
Definition tfib_A_HeapProfile_Print : Z := 0x53664.  Definition tfib_E_HeapProfile_Print : Z := 0x537d0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53cb8.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53cc8.
Definition tfib_A_CanPoisonMemory : Z := 0x53cc8.  Definition tfib_E_CanPoisonMemory : Z := 0x53cdc.
Definition tfib_A_PoisonShadow : Z := 0x53cdc.  Definition tfib_E_PoisonShadow : Z := 0x541d8.
Definition tfib_A_MemToShadow_5270c : Z := 0x541d8.  Definition tfib_E_MemToShadow_5270c : Z := 0x54314.
Definition tfib_A_asan_poison_memory_region : Z := 0x54314.  Definition tfib_E_asan_poison_memory_region : Z := 0x544b4.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x544b4.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x54634.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54664.  Definition tfib_E_asan_region_is_poisoned : Z := 0x549a8.
Definition tfib_A_AsanTSDInit : Z := 0x54dc8.  Definition tfib_E_AsanTSDInit : Z := 0x54e44.
Definition tfib_A_AsanTSDGet : Z := 0x54e44.  Definition tfib_E_AsanTSDGet : Z := 0x54e84.
Definition tfib_A_AsanTSDSet : Z := 0x54e84.  Definition tfib_E_AsanTSDSet : Z := 0x54ec4.
Definition tfib_A_PlatformTSDDtor : Z := 0x54ec4.  Definition tfib_E_PlatformTSDDtor : Z := 0x54f48.
Definition tfib_A_InstallAtForkHandler : Z := 0x54f48.  Definition tfib_E_InstallAtForkHandler : Z := 0x54f64.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54fc4.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x55008.
Definition tfib_A_ReportDeadlySignal : Z := 0x55720.  Definition tfib_E_ReportDeadlySignal : Z := 0x5592c.
Definition tfib_A_ReportDoubleFree : Z := 0x56034.  Definition tfib_E_ReportDoubleFree : Z := 0x562c4.
Definition tfib_A_ReportGenericError : Z := 0x57ba0.  Definition tfib_E_ReportGenericError : Z := 0x5845c.
Definition tfib_A_AsanInited : Z := 0x58be8.  Definition tfib_E_AsanInited : Z := 0x58c00.
Definition tfib_A_asan_report_load1 : Z := 0x58c00.  Definition tfib_E_asan_report_load1 : Z := 0x58c50.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58c50.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58ca0.
Definition tfib_A_asan_report_load2 : Z := 0x58ca0.  Definition tfib_E_asan_report_load2 : Z := 0x58cf0.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58cf0.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58d40.
Definition tfib_A_asan_report_load4 : Z := 0x58d40.  Definition tfib_E_asan_report_load4 : Z := 0x58d90.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58d90.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58de0.
Definition tfib_A_asan_report_load8 : Z := 0x58de0.  Definition tfib_E_asan_report_load8 : Z := 0x58e30.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58e30.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58e80.
Definition tfib_A_asan_report_load16 : Z := 0x58e80.  Definition tfib_E_asan_report_load16 : Z := 0x58ed0.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58ed0.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58f20.
Definition tfib_A_asan_report_store1 : Z := 0x58f20.  Definition tfib_E_asan_report_store1 : Z := 0x58f70.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58f70.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58fc0.
Definition tfib_A_asan_report_store2 : Z := 0x58fc0.  Definition tfib_E_asan_report_store2 : Z := 0x59010.
Definition tfib_A_asan_report_exp_store2 : Z := 0x59010.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59060.
Definition tfib_A_asan_report_store4 : Z := 0x59060.  Definition tfib_E_asan_report_store4 : Z := 0x590b0.
Definition tfib_A_asan_report_exp_store4 : Z := 0x590b0.  Definition tfib_E_asan_report_exp_store4 : Z := 0x59100.
Definition tfib_A_asan_report_store8 : Z := 0x59100.  Definition tfib_E_asan_report_store8 : Z := 0x59150.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59150.  Definition tfib_E_asan_report_exp_store8 : Z := 0x591a0.
Definition tfib_A_asan_report_store16 : Z := 0x591a0.  Definition tfib_E_asan_report_store16 : Z := 0x591f0.
Definition tfib_A_asan_report_exp_store16 : Z := 0x591f0.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59240.
Definition tfib_A_asan_report_load_n : Z := 0x59240.  Definition tfib_E_asan_report_load_n : Z := 0x59290.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59290.  Definition tfib_E_asan_report_exp_load_n : Z := 0x592e0.
Definition tfib_A_asan_report_store_n : Z := 0x592e0.  Definition tfib_E_asan_report_store_n : Z := 0x59330.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59330.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59380.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59380.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59400.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59400.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x597b4.
Definition tfib_A_AsanInitInternal : Z := 0x59844.  Definition tfib_E_AsanInitInternal : Z := 0x59af8.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x59af8.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x59b98.
Definition tfib_A_asan_set_death_callback : Z := 0x59d60.  Definition tfib_E_asan_set_death_callback : Z := 0x59d64.
Definition tfib_A_asan_init : Z := 0x59d64.  Definition tfib_E_asan_init : Z := 0x59df8.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59df8.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59dfc.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x59dfc.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x59e60.
Definition tfib_A_OnLowLevelAllocate : Z := 0x59fd4.  Definition tfib_E_OnLowLevelAllocate : Z := 0x59fdc.
Definition tfib_A_force_interface_symbols : Z := 0x5a060.  Definition tfib_E_force_interface_symbols : Z := 0x5a388.
Definition tfib_A_SealedReserveShadow : Z := 0x5a388.  Definition tfib_E_SealedReserveShadow : Z := 0x5a568.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a568.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a870.
Definition tfib_A_SetMallocContextSize : Z := 0x5a870.  Definition tfib_E_SetMallocContextSize : Z := 0x5a880.
Definition tfib_A_GetMallocContextSize : Z := 0x5a880.  Definition tfib_E_GetMallocContextSize : Z := 0x5a890.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x5a890.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x5a9e0.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x5adc0.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x5b060.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b4c4.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b4fc.
Definition tfib_A_asan_default_suppressions : Z := 0x5b7a4.  Definition tfib_E_asan_default_suppressions : Z := 0x5b7b0.
Definition tfib_A_InitializeSuppressions : Z := 0x5b7b0.  Definition tfib_E_InitializeSuppressions : Z := 0x5b83c.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b83c.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b8a4.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b8a4.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b91c.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b91c.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b984.
Definition tfib_A_IsAddrSuppressed : Z := 0x5b984.  Definition tfib_E_IsAddrSuppressed : Z := 0x5bad0.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x5bd5c.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x5bd68.
Definition tfib_A_AsanThread_Create : Z := 0x5bee8.  Definition tfib_E_AsanThread_Create : Z := 0x5c084.
Definition tfib_A_AsanThread_Destroy : Z := 0x5c0e0.  Definition tfib_E_AsanThread_Destroy : Z := 0x5c2f8.
Definition tfib_A_GetCurrentThread : Z := 0x5c2f8.  Definition tfib_E_GetCurrentThread : Z := 0x5c318.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c318.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c4bc.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c4bc.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c514.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c514.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c56c.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c56c.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c79c.
Definition tfib_A_AsanThread_Init : Z := 0x5c79c.  Definition tfib_E_AsanThread_Init : Z := 0x5cb90.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5cb90.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5cc9c.
Definition tfib_A_CreateMainThread : Z := 0x5ccd0.  Definition tfib_E_CreateMainThread : Z := 0x5cde0.
Definition tfib_A_SetCurrentThread : Z := 0x5cde0.  Definition tfib_E_SetCurrentThread : Z := 0x5cec0.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5d0c4.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5d200.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5ded4.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5ded8.
Definition tfib_A_GetAsanThreadContext : Z := 0x5dee0.  Definition tfib_E_GetAsanThreadContext : Z := 0x5e120.
Definition tfib_A_internal_allocator : Z := 0x5e374.  Definition tfib_E_internal_allocator : Z := 0x5e4cc.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5e6b8.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5e6c4.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5e6c4.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5e810.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e810.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e85c.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e85c.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e868.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e898.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e8a4.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e8a4.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e8b0.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5e8b0.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5e8c0.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5e8cc.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5eb98.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5eb98.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5ef58.
Definition tfib_A_SealedSetInitFrame : Z := 0x5feb4.  Definition tfib_E_SealedSetInitFrame : Z := 0x5fec0.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fec0.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5ff98.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5ff98.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x60034.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60558.  Definition tfib_E_IncreaseTotalMmap : Z := 0x6059c.
Definition tfib_A_DecreaseTotalMmap : Z := 0x6059c.  Definition tfib_E_DecreaseTotalMmap : Z := 0x605c0.
Definition tfib_A_CacheBinaryName : Z := 0x60814.  Definition tfib_E_CacheBinaryName : Z := 0x60928.
Definition tfib_A_RunMallocHooks : Z := 0x60acc.  Definition tfib_E_RunMallocHooks : Z := 0x60b84.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x60b84.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x60b88.
Definition tfib_A_RunFreeHooks : Z := 0x60b88.  Definition tfib_E_RunFreeHooks : Z := 0x60c34.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x60c34.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x60c3c.
Definition tfib_A_sanitizer_free_hook : Z := 0x60c3c.  Definition tfib_E_sanitizer_free_hook : Z := 0x60c40.
Definition tfib_A_WaitForDebugger : Z := 0x60c68.  Definition tfib_E_WaitForDebugger : Z := 0x60cb4.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60f78.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x611b8.
Definition tfib_A_sanitizer_set_report_path : Z := 0x617b4.  Definition tfib_E_sanitizer_set_report_path : Z := 0x617cc.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x617cc.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x61910.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x61910.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x61918.
Definition tfib_A_RegisterCommonFlags : Z := 0x61c60.  Definition tfib_E_RegisterCommonFlags : Z := 0x62f04.
Definition tfib_A_InitializeCommonFlags : Z := 0x62f04.  Definition tfib_E_InitializeCommonFlags : Z := 0x62f28.
Definition tfib_A_FlagParser_parse_flag : Z := 0x633dc.  Definition tfib_E_FlagParser_parse_flag : Z := 0x636ec.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x636ec.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63830.
Definition tfib_A_FlagParser_ParseString : Z := 0x63830.  Definition tfib_E_FlagParser_ParseString : Z := 0x63924.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x63ab8.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x63b18.
Definition tfib_A_FlagParser_FlagParser : Z := 0x63b18.  Definition tfib_E_FlagParser_FlagParser : Z := 0x63b58.
Definition tfib_A_internal_atoll : Z := 0x63b58.  Definition tfib_E_internal_atoll : Z := 0x63c44.
Definition tfib_A_internal_simple_strtoll : Z := 0x63c44.  Definition tfib_E_internal_simple_strtoll : Z := 0x63da0.
Definition tfib_A_internal_memchr : Z := 0x63da0.  Definition tfib_E_internal_memchr : Z := 0x63dc0.
Definition tfib_A_internal_memcmp : Z := 0x63dc0.  Definition tfib_E_internal_memcmp : Z := 0x63df8.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x63df8.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x63e1c.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x63e1c.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x63e74.
Definition tfib_A_sanitizer_internal_memset : Z := 0x63e74.  Definition tfib_E_sanitizer_internal_memset : Z := 0x63ed4.
Definition tfib_A_internal_strcspn : Z := 0x63ed4.  Definition tfib_E_internal_strcspn : Z := 0x63f28.
Definition tfib_A_internal_strchr : Z := 0x63f28.  Definition tfib_E_internal_strchr : Z := 0x63f5c.
Definition tfib_A_internal_strdup : Z := 0x63f5c.  Definition tfib_E_internal_strdup : Z := 0x63fc8.
Definition tfib_A_internal_strlen : Z := 0x63fc8.  Definition tfib_E_internal_strlen : Z := 0x63fe4.
Definition tfib_A_internal_strcmp : Z := 0x63fe4.  Definition tfib_E_internal_strcmp : Z := 0x64028.
Definition tfib_A_internal_strncmp : Z := 0x64028.  Definition tfib_E_internal_strncmp : Z := 0x64074.
Definition tfib_A_internal_strchrnul : Z := 0x64074.  Definition tfib_E_internal_strchrnul : Z := 0x640bc.
Definition tfib_A_internal_strrchr : Z := 0x640bc.  Definition tfib_E_internal_strrchr : Z := 0x640fc.
Definition tfib_A_internal_strnlen : Z := 0x6422c.  Definition tfib_E_internal_strnlen : Z := 0x6425c.
Definition tfib_A_internal_strncpy : Z := 0x642a0.  Definition tfib_E_internal_strncpy : Z := 0x64310.
Definition tfib_A_internal_strstr : Z := 0x64310.  Definition tfib_E_internal_strstr : Z := 0x643a4.
Definition tfib_A_mem_is_zero : Z := 0x643a4.  Definition tfib_E_mem_is_zero : Z := 0x64458.
Definition tfib_A_internal_sigprocmask : Z := 0x64458.  Definition tfib_E_internal_sigprocmask : Z := 0x64468.
Definition tfib_A_BlockSignals : Z := 0x64468.  Definition tfib_E_BlockSignals : Z := 0x64648.
Definition tfib_A_internal_iserror : Z := 0x64654.  Definition tfib_E_internal_iserror : Z := 0x64674.
Definition tfib_A_internal_mmap : Z := 0x64674.  Definition tfib_E_internal_mmap : Z := 0x64680.
Definition tfib_A_internal_munmap : Z := 0x64680.  Definition tfib_E_internal_munmap : Z := 0x6468c.
Definition tfib_A_internal_mprotect : Z := 0x6468c.  Definition tfib_E_internal_mprotect : Z := 0x6469c.
Definition tfib_A_internal_madvise : Z := 0x6469c.  Definition tfib_E_internal_madvise : Z := 0x646c8.
Definition tfib_A_internal_close : Z := 0x646c8.  Definition tfib_E_internal_close : Z := 0x646d4.
Definition tfib_A_internal_open : Z := 0x646d4.  Definition tfib_E_internal_open : Z := 0x646f8.
Definition tfib_A_internal_read : Z := 0x646f8.  Definition tfib_E_internal_read : Z := 0x64730.
Definition tfib_A_internal_write : Z := 0x64730.  Definition tfib_E_internal_write : Z := 0x64768.
Definition tfib_A_internal_ftruncate : Z := 0x64768.  Definition tfib_E_internal_ftruncate : Z := 0x647a0.
Definition tfib_A_internal_dup : Z := 0x647a0.  Definition tfib_E_internal_dup : Z := 0x647ac.
Definition tfib_A_internal_dup2 : Z := 0x647ac.  Definition tfib_E_internal_dup2 : Z := 0x647bc.
Definition tfib_A_internal_unlink : Z := 0x647bc.  Definition tfib_E_internal_unlink : Z := 0x647d4.
Definition tfib_A_internal_sched_yield : Z := 0x647d4.  Definition tfib_E_internal_sched_yield : Z := 0x647e0.
Definition tfib_A_internal_usleep : Z := 0x647e0.  Definition tfib_E_internal_usleep : Z := 0x6482c.
Definition tfib_A_internal_execve : Z := 0x6482c.  Definition tfib_E_internal_execve : Z := 0x64838.
Definition tfib_A_internal_exit : Z := 0x64838.  Definition tfib_E_internal_exit : Z := 0x6484c.
Definition tfib_A_FileExists : Z := 0x6484c.  Definition tfib_E_FileExists : Z := 0x648cc.
Definition tfib_A_DirExists : Z := 0x648cc.  Definition tfib_E_DirExists : Z := 0x64930.
Definition tfib_A_GetTid : Z := 0x64930.  Definition tfib_E_GetTid : Z := 0x6493c.
Definition tfib_A_GetEnv : Z := 0x6493c.  Definition tfib_E_GetEnv : Z := 0x64a6c.
Definition tfib_A_FutexWait : Z := 0x64b70.  Definition tfib_E_FutexWait : Z := 0x64b94.
Definition tfib_A_FutexWake : Z := 0x64b94.  Definition tfib_E_FutexWake : Z := 0x64bb8.
Definition tfib_A_internal_ptrace : Z := 0x64bb8.  Definition tfib_E_internal_ptrace : Z := 0x64bc4.
Definition tfib_A_internal_waitpid : Z := 0x64bc4.  Definition tfib_E_internal_waitpid : Z := 0x64bd4.
Definition tfib_A_internal_getpid : Z := 0x64bd4.  Definition tfib_E_internal_getpid : Z := 0x64be0.
Definition tfib_A_internal_getppid : Z := 0x64be0.  Definition tfib_E_internal_getppid : Z := 0x64bec.
Definition tfib_A_internal_prctl : Z := 0x64bec.  Definition tfib_E_internal_prctl : Z := 0x64bf8.
Definition tfib_A_internal_sigaltstack : Z := 0x64bf8.  Definition tfib_E_internal_sigaltstack : Z := 0x64c04.
Definition tfib_A_internal_fork : Z := 0x64c04.  Definition tfib_E_internal_fork : Z := 0x64c1c.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x64c1c.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x64d48.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x64f20.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x6531c.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x65488.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x655a0.
Definition tfib_A_GetPageSize : Z := 0x655a0.  Definition tfib_E_GetPageSize : Z := 0x655a8.
Definition tfib_A_ReadBinaryName : Z := 0x655a8.  Definition tfib_E_ReadBinaryName : Z := 0x65654.
Definition tfib_A_ReadLongProcessName : Z := 0x65654.  Definition tfib_E_ReadLongProcessName : Z := 0x65774.
Definition tfib_A_internal_clone : Z := 0x6583c.  Definition tfib_E_internal_clone : Z := 0x658bc.
Definition tfib_A_GetHandleSignalMode : Z := 0x658bc.  Definition tfib_E_GetHandleSignalMode : Z := 0x65918.
Definition tfib_A_internal_start_thread : Z := 0x65918.  Definition tfib_E_internal_start_thread : Z := 0x659e4.
Definition tfib_A_InitializePlatformEarly : Z := 0x65ae0.  Definition tfib_E_InitializePlatformEarly : Z := 0x65ae4.
Definition tfib_A_CheckASLR : Z := 0x65ae4.  Definition tfib_E_CheckASLR : Z := 0x65ae8.
Definition tfib_A_GetMmapGranularity : Z := 0x65d34.  Definition tfib_E_GetMmapGranularity : Z := 0x65d38.
Definition tfib_A_ErrorIsOOM : Z := 0x65d38.  Definition tfib_E_ErrorIsOOM : Z := 0x65d44.
Definition tfib_A_MmapOrDie : Z := 0x65d44.  Definition tfib_E_MmapOrDie : Z := 0x65e50.
Definition tfib_A_MmapNamed : Z := 0x65e50.  Definition tfib_E_MmapNamed : Z := 0x65ec4.
Definition tfib_A_UnmapOrDie : Z := 0x65ec4.  Definition tfib_E_UnmapOrDie : Z := 0x65f40.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65f40.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66050.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x6627c.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66380.
Definition tfib_A_MmapFixedOrDie : Z := 0x66380.  Definition tfib_E_MmapFixedOrDie : Z := 0x6638c.
Definition tfib_A_MmapFixedImpl : Z := 0x6638c.  Definition tfib_E_MmapFixedImpl : Z := 0x66504.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x66504.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x66510.
Definition tfib_A_CloseFile : Z := 0x666fc.  Definition tfib_E_CloseFile : Z := 0x66700.
Definition tfib_A_GetNamedMappingFd : Z := 0x66a20.  Definition tfib_E_GetNamedMappingFd : Z := 0x66c2c.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x671e4.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x671f0.
Definition tfib_A_Printf : Z := 0x671f4.  Definition tfib_E_Printf : Z := 0x67240.
Definition tfib_A_SharedPrintfCode : Z := 0x67240.  Definition tfib_E_SharedPrintfCode : Z := 0x6729c.
Definition tfib_A_Report : Z := 0x6729c.  Definition tfib_E_Report : Z := 0x672e8.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x68de0.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x68e3c.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68e3c.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x69078.
Definition tfib_A_SuppressionContext_Parse : Z := 0x69078.  Definition tfib_E_SuppressionContext_Parse : Z := 0x6939c.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x6993c.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x69a0c.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x69a0c.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x69d5c.
Definition tfib_A_DTLS_Get : Z := 0x69d5c.  Definition tfib_E_DTLS_Get : Z := 0x69d6c.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x69fa8.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x69fec.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x69fec.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x6a04c.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a04c.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a4c4.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6ad84.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b0a8.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6b0b0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6b1b4.
Definition tfib_A_AddDieCallback : Z := 0x6b964.  Definition tfib_E_AddDieCallback : Z := 0x6b9ec.
Definition tfib_A_Die : Z := 0x6bab0.  Definition tfib_E_Die : Z := 0x6bb70.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6bb70.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6bb7c.
Definition tfib_A_CheckFailed : Z := 0x6bb7c.  Definition tfib_E_CheckFailed : Z := 0x6bc34.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c28c.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c384.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c384.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c4b0.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c6d8.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c754.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c788.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6ca70.
Definition tfib_A_InitTlsSize : Z := 0x6ca70.  Definition tfib_E_InitTlsSize : Z := 0x6ca74.
Definition tfib_A_GetTls : Z := 0x6ca74.  Definition tfib_E_GetTls : Z := 0x6ce64.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6ce64.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6cf34.
Definition tfib_A_AndroidLogInit : Z := 0x6d318.  Definition tfib_E_AndroidLogInit : Z := 0x6d31c.
Definition tfib_A_MonotonicNanoTime : Z := 0x6d34c.  Definition tfib_E_MonotonicNanoTime : Z := 0x6d394.
Definition tfib_A_MapDynamicShadow : Z := 0x6d394.  Definition tfib_E_MapDynamicShadow : Z := 0x6d5e0.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6d5e0.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6d5e4.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6d5e4.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6d6f0.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d6f0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d7f4.
Definition tfib_A_GetThreadSelf : Z := 0x6da70.  Definition tfib_E_GetThreadSelf : Z := 0x6da74.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6db18.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6db38.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6db38.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6dbd8.
Definition tfib_A_Atexit : Z := 0x6dc24.  Definition tfib_E_Atexit : Z := 0x6dc28.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6dc64.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6dd28.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6dd28.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6ddb0.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6ddb0.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6de28.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6de28.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6df0c.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dfc8.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6e0fc.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6e334.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6e464.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6e464.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6e4c4.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6e4c4.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6e590.
Definition tfib_A_MmapNoAccess : Z := 0x6e5a4.  Definition tfib_E_MmapNoAccess : Z := 0x6e5c4.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6e5c4.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6e638.
Definition tfib_A_SealedRepairReservation : Z := 0x6e638.  Definition tfib_E_SealedRepairReservation : Z := 0x6e710.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6e710.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6e720.
Definition tfib_A_InitializeCoverage : Z := 0x6ff18.  Definition tfib_E_InitializeCoverage : Z := 0x6ff5c.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6ff5c.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6ff8c.
Definition tfib_A_StackStore_Store : Z := 0x703c0.  Definition tfib_E_StackStore_Store : Z := 0x704e4.
Definition tfib_A_StackStore_Alloc : Z := 0x704e4.  Definition tfib_E_StackStore_Alloc : Z := 0x70618.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x70ecc.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x70f80.
Definition tfib_A_StackDepotNode_store : Z := 0x726d4.  Definition tfib_E_StackDepotNode_store : Z := 0x72730.
Definition tfib_A_StackDepotPut : Z := 0x729bc.  Definition tfib_E_StackDepotPut : Z := 0x729dc.
Definition tfib_A_StackDepotBase_Put : Z := 0x729dc.  Definition tfib_E_StackDepotBase_Put : Z := 0x72c60.
Definition tfib_A_StackDepotGet : Z := 0x72c60.  Definition tfib_E_StackDepotGet : Z := 0x72d70.
Definition tfib_A_StackDepotBase_lock : Z := 0x73150.  Definition tfib_E_StackDepotBase_lock : Z := 0x731e0.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x731e0.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x732e0.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73340.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73348.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x73348.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x734a8.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x734a8.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x7351c.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x739a4.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x73abc.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x76b08.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x76b0c.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x782e0.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x782e4.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79d0c.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79dc8.
Definition tfib_A_Unwind_Trace : Z := 0x79dc8.  Definition tfib_E_Unwind_Trace : Z := 0x79ea0.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x79ea0.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x7a114.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x7a440.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x7a484.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x7a484.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x7a854.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7ab24.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7abdc.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bf34.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bf38.
Definition tfib_A_lsan_register_root_region : Z := 0x7cb40.  Definition tfib_E_lsan_register_root_region : Z := 0x7ce70.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7ce70.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d2f8.
Definition tfib_A_lsan_default_options : Z := 0x7d2f8.  Definition tfib_E_lsan_default_options : Z := 0x7d304.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7febc.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7fed4.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80258.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x802d4.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x802d4.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80384.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x80384.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x8039c.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x8039c.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x804e4.
Definition tfib_A_ubsan_default_options : Z := 0x804e4.  Definition tfib_E_ubsan_default_options : Z := 0x804f0.
Definition tfib_A_asan_default_options : Z := 0x804f0.  Definition tfib_E_asan_default_options : Z := 0x804fc.
Definition tfib_A_main : Z := 0x804fc.  Definition tfib_E_main : Z := 0x807c0.
Definition tfib_A_target_alloc_init : Z := 0x807c0.  Definition tfib_E_target_alloc_init : Z := 0x807c4.
Definition tfib_A_target_alloc_count : Z := 0x807c4.  Definition tfib_E_target_alloc_count : Z := 0x807cc.
Definition tfib_A_target_run : Z := 0x807cc.  Definition tfib_E_target_run : Z := 0x80924.
Definition tfib_A_oft_exit_guard : Z := 0x80924.  Definition tfib_E_oft_exit_guard : Z := 0x80954.
Definition tfib_A_emit_printf : Z := 0x80954.  Definition tfib_E_emit_printf : Z := 0x8099c.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x8099c.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x8391c.  Definition tfib_A_check_personality : Z := 0x8391c.  Definition tfib_E_check_personality : Z := 0x83ba0.  Definition tfib_A_text_arg : Z := 0x83ba0.  Definition tfib_E_text_arg : Z := 0x83dbc.  Definition tfib_A_check_text_scribble : Z := 0x83dbc.  Definition tfib_E_check_text_scribble : Z := 0x84148.  Definition tfib_A_check_text_seg7 : Z := 0x84148.  Definition tfib_E_check_text_seg7 : Z := 0x841c4.  Definition tfib_A_check_text_counter : Z := 0x841c4.  Definition tfib_E_check_text_counter : Z := 0x84474.  Definition tfib_A_owed_counter_text : Z := 0x84474.  Definition tfib_E_owed_counter_text : Z := 0x84974.  Definition tfib_A_check_text_masks : Z := 0x84974.  Definition tfib_E_check_text_masks : Z := 0x84a54.  Definition tfib_A_owed_seg7 : Z := 0x84a54.  Definition tfib_E_owed_seg7 : Z := 0x84bc4.  Definition tfib_A_check_refusal : Z := 0x84bc4.  Definition tfib_E_check_refusal : Z := 0x84c84.  Definition tfib_A_check_range : Z := 0x84c84.  Definition tfib_E_check_range : Z := 0x84d40.  Definition tfib_A_check_bytes : Z := 0x84d40.  Definition tfib_E_check_bytes : Z := 0x84e8c.  Definition tfib_A_asan_module_dtor : Z := 0x85060.  Definition tfib_E_asan_module_dtor : Z := 0x85090.  Definition tfib_A_diginet_personality_from_name : Z := 0x85090.  Definition tfib_E_diginet_personality_from_name : Z := 0x8513c.  Definition tfib_A_diginet_personality_of : Z := 0x8513c.  Definition tfib_E_diginet_personality_of : Z := 0x85174.  Definition tfib_A_diginet_sysex_encode : Z := 0x85174.  Definition tfib_E_diginet_sysex_encode : Z := 0x8540c.  Definition tfib_A_diginet_fader_encode : Z := 0x8540c.  Definition tfib_E_diginet_fader_encode : Z := 0x855dc.  Definition tfib_A_diginet_button_encode : Z := 0x855dc.  Definition tfib_E_diginet_button_encode : Z := 0x85744.  Definition tfib_A_diginet_touch_encode : Z := 0x85744.  Definition tfib_E_diginet_touch_encode : Z := 0x85914.  Definition tfib_A_diginet_vpot_encode : Z := 0x85914.  Definition tfib_E_diginet_vpot_encode : Z := 0x85a8c.  Definition tfib_A_diginet_jog_encode : Z := 0x85a8c.  Definition tfib_E_diginet_jog_encode : Z := 0x85bd8.  Definition tfib_A_diginet_ring_dot : Z := 0x85bd8.  Definition tfib_E_diginet_ring_dot : Z := 0x85bf8.  Definition tfib_A_diginet_ring_fill : Z := 0x85bf8.  Definition tfib_E_diginet_ring_fill : Z := 0x85c1c.  Definition tfib_A_diginet_ring_encode : Z := 0x85c1c.  Definition tfib_E_diginet_ring_encode : Z := 0x85ef8.  Definition tfib_A_diginet_meter_mask : Z := 0x85ef8.  Definition tfib_E_diginet_meter_mask : Z := 0x85f14.  Definition tfib_A_diginet_meter_segments : Z := 0x85f14.  Definition tfib_E_diginet_meter_segments : Z := 0x85f4c.  Definition tfib_A_diginet_meter_encode : Z := 0x85f4c.  Definition tfib_E_diginet_meter_encode : Z := 0x861d0.  Definition tfib_A_diginet_strip_leds_encode : Z := 0x861d0.  Definition tfib_E_diginet_strip_leds_encode : Z := 0x86248.  Definition tfib_A_diginet_counter_leds_encode : Z := 0x8648c.  Definition tfib_E_diginet_counter_leds_encode : Z := 0x86500.  Definition tfib_A_diginet_scribble_text : Z := 0x86500.  Definition tfib_E_diginet_scribble_text : Z := 0x866c4.  Definition tfib_A_diginet_scribble_encode : Z := 0x866c4.  Definition tfib_E_diginet_scribble_encode : Z := 0x86978.  Definition tfib_A_diginet_seg7 : Z := 0x86978.  Definition tfib_E_diginet_seg7 : Z := 0x869e4.  Definition tfib_A_diginet_counter_text : Z := 0x869e4.  Definition tfib_E_diginet_counter_text : Z := 0x86ee4.  Definition tfib_A_diginet_counter_encode : Z := 0x86ee4.  Definition tfib_E_diginet_counter_encode : Z := 0x871e0.
Definition tfib_A_asan_module_ctor : Z := 0x85028.  Definition tfib_E_asan_module_ctor : Z := 0x85060.
Definition tfib_A_extenddftf2 : Z := 0x871f0.  Definition tfib_E_extenddftf2 : Z := 0x87380.
Definition tfib_A_sysconf : Z := 0x8cfd0.  Definition tfib_E_sysconf : Z := 0x8d1f8.
Definition tfib_A_init : Z := 0x8d1f8.  Definition tfib_E_init : Z := 0x8d1fc.
Definition tfib_A_init_libc : Z := 0x8d1fc.  Definition tfib_E_init_libc : Z := 0x8d428.
Definition tfib_A_libc_start_init : Z := 0x8d428.  Definition tfib_E_libc_start_init : Z := 0x8d474.
Definition tfib_A_libc_start_main : Z := 0x8d474.  Definition tfib_E_libc_start_main : Z := 0x8d4d4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8d4d4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8d51c.
Definition tfib_A_static_init_tls : Z := 0x8d5f4.  Definition tfib_E_static_init_tls : Z := 0x8d8a4.
Definition tfib_A_init_ssp : Z := 0x8d8a4.  Definition tfib_E_init_ssp : Z := 0x8d904.
Definition tfib_A_stack_chk_fail : Z := 0x8d904.  Definition tfib_E_stack_chk_fail : Z := 0x8d90c.
Definition tfib_A_abort : Z := 0x8d954.  Definition tfib_E_abort : Z := 0x8d9e8.
Definition tfib_A_Exit : Z := 0x8d9e8.  Definition tfib_E_Exit : Z := 0x8da04.
Definition tfib_A_funcs_on_exit : Z := 0x8da34.  Definition tfib_E_funcs_on_exit : Z := 0x8dafc.
Definition tfib_A_cxa_finalize : Z := 0x8dafc.  Definition tfib_E_cxa_finalize : Z := 0x8db00.
Definition tfib_A_atexit : Z := 0x8db00.  Definition tfib_E_atexit : Z := 0x8dbc4.
Definition tfib_A_fini : Z := 0x8dbc8.  Definition tfib_E_fini : Z := 0x8dbcc.
Definition tfib_A_libc_exit_fini : Z := 0x8dbcc.  Definition tfib_E_libc_exit_fini : Z := 0x8dc18.
Definition tfib_A_exit : Z := 0x8dc18.  Definition tfib_E_exit : Z := 0x8dc8c.
Definition tfib_A_open : Z := 0x8de8c.  Definition tfib_E_open : Z := 0x8df70.
Definition tfib_A_syscall_ret : Z := 0x8df70.  Definition tfib_E_syscall_ret : Z := 0x8dfa8.
Definition tfib_A_dl_iterate_phdr : Z := 0x8dfa8.  Definition tfib_E_dl_iterate_phdr : Z := 0x8e150.
Definition tfib_A_libc_calloc : Z := 0x8e714.  Definition tfib_E_libc_calloc : Z := 0x8e84c.
Definition tfib_A_libc_malloc : Z := 0x8e84c.  Definition tfib_E_libc_malloc : Z := 0x8e850.
Definition tfib_A_libc_free : Z := 0x8e850.  Definition tfib_E_libc_free : Z := 0x8ea1c.
Definition tfib_A_get_meta : Z := 0x8ea1c.  Definition tfib_E_get_meta : Z := 0x8eb2c.
Definition tfib_A_malloc_alloc_meta : Z := 0x8ef04.  Definition tfib_E_malloc_alloc_meta : Z := 0x8f1dc.
Definition tfib_A_libc_malloc_impl : Z := 0x8f1dc.  Definition tfib_E_libc_malloc_impl : Z := 0x8f54c.
Definition tfib_A_alloc_slot : Z := 0x8f54c.  Definition tfib_E_alloc_slot : Z := 0x8fdf0.
Definition tfib_A_enframe : Z := 0x8fdf0.  Definition tfib_E_enframe : Z := 0x8ff40.
Definition tfib_A_malloc_allzerop : Z := 0x8ff40.  Definition tfib_E_malloc_allzerop : Z := 0x900b8.
Definition tfib_A_getrlimit : Z := 0x91d68.  Definition tfib_E_getrlimit : Z := 0x91e60.
Definition tfib_A_getrusage : Z := 0x91e60.  Definition tfib_E_getrusage : Z := 0x91e88.
Definition tfib_A_setrlimit : Z := 0x91e88.  Definition tfib_E_setrlimit : Z := 0x91f50.
Definition tfib_A_mmap : Z := 0x92378.  Definition tfib_E_mmap : Z := 0x92464.
Definition tfib_A_mprotect : Z := 0x92464.  Definition tfib_E_mprotect : Z := 0x924ac.
Definition tfib_A_munmap : Z := 0x92580.  Definition tfib_E_munmap : Z := 0x925c8.
Definition tfib_A_sched_yield : Z := 0x9288c.  Definition tfib_E_sched_yield : Z := 0x928b0.
Definition tfib_A_raise : Z := 0x9290c.  Definition tfib_E_raise : Z := 0x92984.
Definition tfib_A_libc_sigaction : Z := 0x92984.  Definition tfib_E_libc_sigaction : Z := 0x92b58.
Definition tfib_A_musl_sigaltstack : Z := 0x92c50.  Definition tfib_E_musl_sigaltstack : Z := 0x92cdc.
Definition tfib_A_dprintf : Z := 0x932b8.  Definition tfib_E_dprintf : Z := 0x9331c.
Definition tfib_A_lockfile : Z := 0x9331c.  Definition tfib_E_lockfile : Z := 0x93418.
Definition tfib_A_unlockfile : Z := 0x93418.  Definition tfib_E_unlockfile : Z := 0x93478.
Definition tfib_A_stdio_read : Z := 0x93008.  Definition tfib_E_stdio_read : Z := 0x93120.
Definition tfib_A_stdio_write : Z := 0x93128.  Definition tfib_E_stdio_write : Z := 0x932b8.
Definition tfib_A_aio_close : Z := 0x92fd8.  Definition tfib_E_aio_close : Z := 0x92fdc.
Definition tfib_A_stdio_close : Z := 0x92fdc.  Definition tfib_E_stdio_close : Z := 0x93008.
Definition tfib_A_fwritex : Z := 0x938ac.  Definition tfib_E_fwritex : Z := 0x939e4.
Definition tfib_A_musl_fwrite : Z := 0x939e4.  Definition tfib_E_musl_fwrite : Z := 0x93a9c.
Definition tfib_A_towrite : Z := 0x93a9c.  Definition tfib_E_towrite : Z := 0x93af0.
Definition tfib_A_stdio_exit : Z := 0x93708.  Definition tfib_E_stdio_exit : Z := 0x938ac.
Definition tfib_A_ofl_lock : Z := 0x93af0.  Definition tfib_E_ofl_lock : Z := 0x93b20.
Definition tfib_A_musl_vfprintf : Z := 0x93c6c.  Definition tfib_E_musl_vfprintf : Z := 0x93e1c.
Definition tfib_A_printf_core : Z := 0x93e1c.  Definition tfib_E_printf_core : Z := 0x94c4c.
Definition tfib_A_pop_arg : Z := 0x94c4c.  Definition tfib_E_pop_arg : Z := 0x94d80.
Definition tfib_A_pad : Z := 0x94d80.  Definition tfib_E_pad : Z := 0x94e54.
Definition tfib_A_fmt_fp : Z := 0x94e54.  Definition tfib_E_fmt_fp : Z := 0x9651c.
Definition tfib_A_lctrans : Z := 0x8e368.  Definition tfib_E_lctrans : Z := 0x8e36c.
Definition tfib_A_musl_wctomb : Z := 0x926f4.  Definition tfib_E_musl_wctomb : Z := 0x92718.
Definition tfib_A_musl_wcrtomb : Z := 0x925c8.  Definition tfib_E_musl_wcrtomb : Z := 0x926f4.
Definition tfib_A_fpclassifyl : Z := 0x90958.  Definition tfib_E_fpclassifyl : Z := 0x9099c.
Definition tfib_A_letf2 : Z := 0x90190.  Definition tfib_E_letf2 : Z := 0x90258.
Definition tfib_A_multf3 : Z := 0x90258.  Definition tfib_E_multf3 : Z := 0x90958.
Definition tfib_A_floatsitf : Z := 0x911b4.  Definition tfib_E_floatsitf : Z := 0x912bc.
Definition tfib_A_scalbn : Z := 0x91bc0.  Definition tfib_E_scalbn : Z := 0x91c58.
Definition tfib_A_subtf3 : Z := 0x911a4.  Definition tfib_E_subtf3 : Z := 0x911b4.
Definition tfib_A_addtf3 : Z := 0x9099c.  Definition tfib_E_addtf3 : Z := 0x91168.
Definition tfib_A_fe_getround : Z := 0x91168.  Definition tfib_E_fe_getround : Z := 0x91198.
Definition tfib_A_fixunstfsi : Z := 0x96524.  Definition tfib_E_fixunstfsi : Z := 0x965b8.
Definition tfib_A_floatunsitf : Z := 0x965b8.  Definition tfib_E_floatunsitf : Z := 0x966a4.
Definition tfib_A_fixtfsi : Z := 0x91c58.  Definition tfib_E_fixtfsi : Z := 0x91d00.
Definition tfib_A_divtf3 : Z := 0x912bc.  Definition tfib_E_divtf3 : Z := 0x91bc0.
Definition tfib_A_musl_vprintf : Z := 0x96d7c.  Definition tfib_E_musl_vprintf : Z := 0x96d98.
Definition tfib_A_stdout_write : Z := 0x93b2c.  Definition tfib_E_stdout_write : Z := 0x93bcc.
Definition tfib_A_musl_memcmp : Z := 0x97400.  Definition tfib_E_musl_memcmp : Z := 0x97430.
Definition tfib_A_musl_memcpy : Z := 0x97430.  Definition tfib_E_musl_memcpy : Z := 0x97834.
Definition tfib_A_musl_memset : Z := 0x97834.  Definition tfib_E_musl_memset : Z := 0x9792c.
Definition tfib_A_musl_strchr : Z := 0x9792c.  Definition tfib_E_musl_strchr : Z := 0x97968.
Definition tfib_A_strchrnul : Z := 0x97968.  Definition tfib_E_strchrnul : Z := 0x97a48.
Definition tfib_A_musl_strlen : Z := 0x97a80.  Definition tfib_E_musl_strlen : Z := 0x97b10.
Definition tfib_A_musl_strnlen : Z := 0x97cbc.  Definition tfib_E_musl_strnlen : Z := 0x97d00.
Definition tfib_A_musl_memchr : Z := 0x97334.  Definition tfib_E_musl_memchr : Z := 0x97400.
Definition tfib_A_lock : Z := 0x97d00.  Definition tfib_E_lock : Z := 0x97f88.
Definition tfib_A_unlock : Z := 0x97f88.  Definition tfib_E_unlock : Z := 0x97ffc.
Definition tfib_A_sccp : Z := 0x97ffc.  Definition tfib_E_sccp : Z := 0x98020.
Definition tfib_A_syscall_cp : Z := 0x98020.  Definition tfib_E_syscall_cp : Z := 0x98024.
Definition tfib_A_tls_get_addr : Z := 0x98024.  Definition tfib_E_tls_get_addr : Z := 0x98048.
Definition tfib_A_pthread_atfork : Z := 0x98060.  Definition tfib_E_pthread_atfork : Z := 0x98104.
Definition tfib_A_mremap : Z := 0x924ac.  Definition tfib_E_mremap : Z := 0x92580.
Definition tfib_A_pthread_getspecific : Z := 0x990d8.  Definition tfib_E_pthread_getspecific : Z := 0x990f4.
Definition tfib_A_pthread_key_create : Z := 0x99480.  Definition tfib_E_pthread_key_create : Z := 0x99554.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x997f8.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x9989c.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x9989c.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x998a4.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x998a4.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x999b8.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x999b8.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x999e4.
Definition tfib_A_pthread_setspecific : Z := 0x99a1c.  Definition tfib_E_pthread_setspecific : Z := 0x99a50.
Definition tfib_A_set_thread_area : Z := 0x99a58.  Definition tfib_E_set_thread_area : Z := 0x99a64.
Definition tfib_A_pthread_testcancel : Z := 0x99a50.  Definition tfib_E_pthread_testcancel : Z := 0x99a54.
Definition tfib_A_testcancel : Z := 0x99a54.  Definition tfib_E_testcancel : Z := 0x99a58.
Definition tfib_A_musl_clock_gettime : Z := 0x9a384.  Definition tfib_E_musl_clock_gettime : Z := 0x9a43c.
Definition tfib_A_close : Z := 0x9ca54.  Definition tfib_E_close : Z := 0x9caa8.
Definition tfib_A_musl_read : Z := 0x9cb34.  Definition tfib_E_musl_read : Z := 0x9cb68.
Definition tfib_A_vm_wait : Z := 0x9a094.  Definition tfib_E_vm_wait : Z := 0x9a0e4.
Definition tfib_D_str_sealed : Z := 0x11825.
Definition tfib_D_init_array_0_3 : Z := 0x9db68.
Definition tfib_D_fini_array_0 : Z := 0x9db88.
Definition tfib_D_GOT_common_flags : Z := 0x9e420.
Definition tfib_D_GOT_flags : Z := 0x9e428.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9e430.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9e438.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9e440.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9e448.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9ef98.
Definition tfib_D_GOT_environ : Z := 0x9f0c0.
Definition tfib_D_REAL_read : Z := 0xa0168.
Definition tfib_D_REAL_memcpy : Z := 0xa0290.
Definition tfib_D_REAL_memset : Z := 0xa0298.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa3758.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa45b8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa6db8.
Definition tfib_D_asan_inited : Z := 0xa7a98.
Definition tfib_D_replace_intrin_cached : Z := 0xa7a99.
Definition tfib_D_kHighMemEnd : Z := 0xa7aa0.
Definition tfib_D_kMidMemBeg : Z := 0xa7aa8.
Definition tfib_D_kMidMemEnd : Z := 0xa7ab0.
Definition tfib_D_malloc_context_size : Z := 0xa7abc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1388e8.
Definition tfib_D_libc : Z := 0x5f9fe0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fc000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30c84.
Definition tfib_at_rw_lo : Z := 0xa0000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63e74.
Definition tfib_at_x_imemcpy : Z := 0x63df8.
Definition tfib_at_x_memset : Z := 0x97834.
Definition tfib_at_x_memcpy : Z := 0x97430.
Definition tfib_at_x_memiszero : Z := 0x643a4.
Definition tfib_at_x_istrncpy : Z := 0x642a0.
Definition tfib_at_x_sealed : Z := 0x11825.
Definition tfib_at_x_popfree : Z := 0x37070.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8d234.
Definition tfib_at_x_envscan_k : Z := 0x8d240.
Definition tfib_at_x_pnscan : Z := 0x8d2f8.
Definition tfib_at_x_pnscan_k : Z := 0x8d304.
Definition tfib_at_stops_more : list Z := (0x34ce4 :: 0x36308 :: 0x54180 :: 0x5a538 :: 0x5a54c :: 0x5a560 :: 0x5fef0 :: 0x5ffc0 :: 0x6d4ec :: 0x6e3f8 :: 0x6e588 :: 0x782e0 :: nil)%list.
