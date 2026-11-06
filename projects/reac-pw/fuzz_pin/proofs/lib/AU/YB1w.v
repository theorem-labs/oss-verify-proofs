(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, regenerated from libreac/fuzz_knock's asan image and its unstripped symbol table: section bounds, function entries (matched to cgif's by code identity, named by knock's symbols), data cells and image parameters; entries for code knock does not link and the asan_globals bounds are dropped; the image low and top bounds now cite YImgTop.IMG_LO and YImgTop.IMG_TOP instead of repeating their numbers. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1w.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1w.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22aec.   (* .rodata of knock's asan pin (sha256 61768cf4739b...), read from the section header: 0x102d0..0x22564; the donor's 0x2278c was cgif's ASAN-UBSAN .rodata end, 0x40 short of cgif's own 0x227cc *)
Definition tfib_text_lo : Z := 0x3031c.  Definition tfib_text_hi : Z := 0x96bd0.
Definition tfib_init_array_lo : Z := 0x97bd0.  Definition tfib_init_array_hi : Z := 0x97bf0.
Definition tfib_fini_array_lo : Z := 0x97bf0.  Definition tfib_fini_array_hi : Z := 0x97c00.
Definition tfib_preinit_array_lo : Z := 0x97c00.  Definition tfib_preinit_array_hi : Z := 0x97c08.
Definition tfib_data_rel_ro_lo : Z := 0x97c20.  Definition tfib_data_rel_ro_hi : Z := 0x99110.
Definition tfib_got_lo : Z := 0x99110.  Definition tfib_got_hi : Z := 0x99e68.
Definition tfib_data_lo : Z := 0x9ae68.  Definition tfib_data_hi : Z := 0x9da30.
Definition tfib_bss_lo : Z := 0x9e040.  Definition tfib_bss_hi : Z := 0x5f5f78.
Definition tfib_tbss_lo : Z := 0x96bd0.  Definition tfib_tbss_hi : Z := 0x96be4.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f6000.
Definition tfib_entry : Z := 0x3031c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x3031c.  Definition tfib_E_start : Z := 0x30338.
Definition tfib_A_start_c : Z := 0x30338.  Definition tfib_E_start_c : Z := 0x30364.
Definition tfib_A_do_init : Z := 0x30364.  Definition tfib_E_do_init : Z := 0x303d8.
Definition tfib_A_do_fini : Z := 0x303d8.  Definition tfib_E_do_fini : Z := 0x30468.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30468.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x304a4.
Definition tfib_A_InitializeAllocator : Z := 0x30614.  Definition tfib_E_InitializeAllocator : Z := 0x3062c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3062c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30798.
Definition tfib_A_Allocator_FindHeapChunkByAddress : Z := 0x30cf4.  Definition tfib_E_Allocator_FindHeapChunkByAddress : Z := 0x30e50.
Definition tfib_A_asan_free : Z := 0x31224.  Definition tfib_E_asan_free : Z := 0x3124c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3124c.  Definition tfib_E_Allocator_Deallocate : Z := 0x31504.
Definition tfib_A_asan_malloc : Z := 0x31504.  Definition tfib_E_asan_malloc : Z := 0x31560.
Definition tfib_A_Allocator_Allocate : Z := 0x31560.  Definition tfib_E_Allocator_Allocate : Z := 0x31ee8.
Definition tfib_A_Allocator_GetAsanChunkByAddr : Z := 0x32620.  Definition tfib_E_Allocator_GetAsanChunkByAddr : Z := 0x32764.
Definition tfib_A_sanitizer_get_allocated_begin : Z := 0x32850.  Definition tfib_E_sanitizer_get_allocated_begin : Z := 0x328ac.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x328ac.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32afc.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32afc.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32bf0.
Definition tfib_A_Allocator_CheckOptions : Z := 0x32bf0.  Definition tfib_E_Allocator_CheckOptions : Z := 0x32cd8.
Definition tfib_A_Quarantine_Recycle : Z := 0x3310c.  Definition tfib_E_Quarantine_Recycle : Z := 0x332f0.
Definition tfib_A_QuarantineCache_MergeBatches : Z := 0x332f0.  Definition tfib_E_QuarantineCache_MergeBatches : Z := 0x33474.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x335ac.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33830.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33830.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x339b0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x339b0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33b78.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33b78.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33d44.
Definition tfib_A_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x33d44.  Definition tfib_E_SizeClassAllocator64LocalCache_DrainHalfMax : Z := 0x33de4.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x33de4.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_33564 : Z := 0x33ee8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34210.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34358.
Definition tfib_A_SealedHangOnAllocationFailure : Z := 0x34358.  Definition tfib_E_SealedHangOnAllocationFailure : Z := 0x34390.
Definition tfib_A_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x34b28.  Definition tfib_E_SizeClassAllocator64_PackedCounterArray_PackedCounterArray : Z := 0x34e10.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x354e8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35660.
Definition tfib_A_Quarantine_Put : Z := 0x35660.  Definition tfib_E_Quarantine_Put : Z := 0x35810.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35810.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x359f4.
Definition tfib_A_CombinedAllocator_Allocate_35174 : Z := 0x359f4.  Definition tfib_E_CombinedAllocator_Allocate_35174 : Z := 0x35ccc.
Definition tfib_A_LargeMmapAllocator_Allocate_3544c : Z := 0x35ccc.  Definition tfib_E_LargeMmapAllocator_Allocate_3544c : Z := 0x36144.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36144.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36244.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36244.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x3654c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x3654c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x368bc.
Definition tfib_A_RZSize2Log : Z := 0x368bc.  Definition tfib_E_RZSize2Log : Z := 0x369d4.
Definition tfib_A_LargeMmapAllocator_ForEachChunk : Z := 0x36cdc.  Definition tfib_E_LargeMmapAllocator_ForEachChunk : Z := 0x36dd8.
Definition tfib_A_AsanDeactivate : Z := 0x36dd8.  Definition tfib_E_AsanDeactivate : Z := 0x36ec0.
Definition tfib_A_AsanActivate : Z := 0x36ec0.  Definition tfib_E_AsanActivate : Z := 0x36f9c.
Definition tfib_A_FlagHandler_Parse : Z := 0x37478.  Definition tfib_E_FlagHandler_Parse : Z := 0x37560.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c018.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c0f0.
Definition tfib_A_FakeStack_Create : Z := 0x3c0f0.  Definition tfib_E_FakeStack_Create : Z := 0x3c1dc.
Definition tfib_A_FakeStack_GC : Z := 0x3c498.  Definition tfib_E_FakeStack_GC : Z := 0x3c780.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c8b4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c8e4.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3c8e4.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3ca58.  Definition tfib_A_asan_stack_malloc_1 : Z := 0x3ca58.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3cbe8.
Definition tfib_A_MemToShadow_3c1f4 : Z := 0x3cbe8.  Definition tfib_E_MemToShadow_3c1f4 : Z := 0x3cd24.
Definition tfib_A_InitializeFlags : Z := 0x3cd24.  Definition tfib_E_InitializeFlags : Z := 0x3dd50.
Definition tfib_A_asan_register_globals : Z := 0x3e45c.  Definition tfib_E_asan_register_globals : Z := 0x3f278.
Definition tfib_A_asan_unregister_globals : Z := 0x3f278.  Definition tfib_E_asan_unregister_globals : Z := 0x3f844.
Definition tfib_A_asan_register_elf_globals : Z := 0x3f844.  Definition tfib_E_asan_register_elf_globals : Z := 0x3f8b0.
Definition tfib_A_UnpoisonBeforeMain : Z := 0x3ff98.  Definition tfib_E_UnpoisonBeforeMain : Z := 0x40208.
Definition tfib_A_asan_after_dynamic_init : Z := 0x40208.  Definition tfib_E_asan_after_dynamic_init : Z := 0x40510.
Definition tfib_A_RoundUpToPowerOfTwo : Z := 0x40c84.  Definition tfib_E_RoundUpToPowerOfTwo : Z := 0x40dd4.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x417f0.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_40d94 : Z := 0x41908.
Definition tfib_A_strlen : Z := 0x41908.  Definition tfib_E_strlen : Z := 0x4190c.
Definition tfib_A_strnlen : Z := 0x4190c.  Definition tfib_E_strnlen : Z := 0x41910.
Definition tfib_A_strcmp : Z := 0x41910.  Definition tfib_E_strcmp : Z := 0x41914.
Definition tfib_A_strchr : Z := 0x41918.  Definition tfib_E_strchr : Z := 0x4191c.
Definition tfib_A_memcmp : Z := 0x41920.  Definition tfib_E_memcmp : Z := 0x41924.
Definition tfib_A_memchr : Z := 0x41928.  Definition tfib_E_memchr : Z := 0x4192c.
Definition tfib_A_frexpl : Z := 0x4192c.  Definition tfib_E_frexpl : Z := 0x41930.
Definition tfib_A_read : Z := 0x41930.  Definition tfib_E_read : Z := 0x41934.
Definition tfib_A_fwrite : Z := 0x41934.  Definition tfib_E_fwrite : Z := 0x41938.
Definition tfib_A_time : Z := 0x41938.  Definition tfib_E_time : Z := 0x4193c.
Definition tfib_A_gmtime_r : Z := 0x4193c.  Definition tfib_E_gmtime_r : Z := 0x41940.
Definition tfib_A_vprintf : Z := 0x41940.  Definition tfib_E_vprintf : Z := 0x41944.
Definition tfib_A_vfprintf : Z := 0x41944.  Definition tfib_E_vfprintf : Z := 0x41948.
Definition tfib_A_vsnprintf : Z := 0x41948.  Definition tfib_E_vsnprintf : Z := 0x4194c.
Definition tfib_A_fprintf : Z := 0x4194c.  Definition tfib_E_fprintf : Z := 0x41950.
Definition tfib_A_snprintf : Z := 0x41950.  Definition tfib_E_snprintf : Z := 0x41954.
Definition tfib_A_clock_gettime : Z := 0x41954.  Definition tfib_E_clock_gettime : Z := 0x41958.
Definition tfib_A_wcrtomb : Z := 0x41958.  Definition tfib_E_wcrtomb : Z := 0x4195c.
Definition tfib_A_wctomb : Z := 0x4195c.  Definition tfib_E_wctomb : Z := 0x41960.
Definition tfib_A_strerror : Z := 0x41960.  Definition tfib_E_strerror : Z := 0x41964.
Definition tfib_A__exit : Z := 0x41964.  Definition tfib_E__exit : Z := 0x41968.
Definition tfib_A_pthread_attr_getstack : Z := 0x41968.  Definition tfib_E_pthread_attr_getstack : Z := 0x4196c.
Definition tfib_A___tls_get_addr : Z := 0x4196c.  Definition tfib_E___tls_get_addr : Z := 0x41970.
Definition tfib_A_fflush : Z := 0x41970.  Definition tfib_E_fflush : Z := 0x41974.
Definition tfib_A_sem_init : Z := 0x41974.  Definition tfib_E_sem_init : Z := 0x41978.
Definition tfib_A_sem_destroy : Z := 0x41978.  Definition tfib_E_sem_destroy : Z := 0x4197c.
Definition tfib_A_sem_wait : Z := 0x4197c.  Definition tfib_E_sem_wait : Z := 0x41980.
Definition tfib_A_sem_trywait : Z := 0x41980.  Definition tfib_E_sem_trywait : Z := 0x41984.
Definition tfib_A_sem_timedwait : Z := 0x41984.  Definition tfib_E_sem_timedwait : Z := 0x41988.
Definition tfib_A_sem_post : Z := 0x41988.  Definition tfib_E_sem_post : Z := 0x4198c.
Definition tfib_A_pthread_setcancelstate : Z := 0x4198c.  Definition tfib_E_pthread_setcancelstate : Z := 0x41990.
Definition tfib_A_send : Z := 0x41990.  Definition tfib_E_send : Z := 0x41994.
Definition tfib_A_sendto : Z := 0x41994.  Definition tfib_E_sendto : Z := 0x41998.
Definition tfib_A_sigaltstack : Z := 0x41998.  Definition tfib_E_sigaltstack : Z := 0x4199c.
Definition tfib_A_sigaction : Z := 0x4199c.  Definition tfib_E_sigaction : Z := 0x419a0.
Definition tfib_A_icpt_strlen : Z := 0x419a0.  Definition tfib_E_icpt_strlen : Z := 0x41c34.
Definition tfib_A_icpt_strnlen : Z := 0x41c34.  Definition tfib_E_icpt_strnlen : Z := 0x41ec8.
Definition tfib_A_icpt_strcmp : Z := 0x41ecc.  Definition tfib_E_icpt_strcmp : Z := 0x423fc.
Definition tfib_A_icpt_strchr : Z := 0x429d8.  Definition tfib_E_icpt_strchr : Z := 0x42cb8.
Definition tfib_A_icpt_memcmp : Z := 0x439d8.  Definition tfib_E_icpt_memcmp : Z := 0x43a94.
Definition tfib_A_icpt_memchr : Z := 0x43b50.  Definition tfib_E_icpt_memchr : Z := 0x43e20.
Definition tfib_A_icpt_frexpl : Z := 0x43e20.  Definition tfib_E_icpt_frexpl : Z := 0x44098.
Definition tfib_A_icpt_read : Z := 0x44098.  Definition tfib_E_icpt_read : Z := 0x44308.
Definition tfib_A_icpt_fwrite : Z := 0x44308.  Definition tfib_E_icpt_fwrite : Z := 0x4457c.
Definition tfib_A_icpt_time : Z := 0x4457c.  Definition tfib_E_icpt_time : Z := 0x44818.
Definition tfib_A_icpt_gmtime_r : Z := 0x44a20.  Definition tfib_E_icpt_gmtime_r : Z := 0x44c60.
Definition tfib_A_icpt_vprintf : Z := 0x44c60.  Definition tfib_E_icpt_vprintf : Z := 0x44cfc.
Definition tfib_A_printf_common : Z := 0x44cfc.  Definition tfib_E_printf_common : Z := 0x457c4.
Definition tfib_A_icpt_vfprintf : Z := 0x457c4.  Definition tfib_E_icpt_vfprintf : Z := 0x45878.
Definition tfib_A_icpt_vsnprintf : Z := 0x45878.  Definition tfib_E_icpt_vsnprintf : Z := 0x45b90.
Definition tfib_A_icpt_fprintf : Z := 0x45b90.  Definition tfib_E_icpt_fprintf : Z := 0x45c68.
Definition tfib_A_icpt_clock_gettime : Z := 0x45d0c.  Definition tfib_E_icpt_clock_gettime : Z := 0x45f64.
Definition tfib_A_icpt_wcrtomb : Z := 0x45f64.  Definition tfib_E_icpt_wcrtomb : Z := 0x464d4.
Definition tfib_A_icpt_wctomb : Z := 0x464d4.  Definition tfib_E_icpt_wctomb : Z := 0x46830.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x468fc.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46ce4.
Definition tfib_A_icpt_tls_get_addr : Z := 0x46cf0.  Definition tfib_E_icpt_tls_get_addr : Z := 0x46d6c.
Definition tfib_A_icpt_sem_timedwait : Z := 0x46f78.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47210.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47240.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47468.
Definition tfib_A_icpt_send : Z := 0x47468.  Definition tfib_E_icpt_send : Z := 0x4771c.
Definition tfib_A_icpt_sendto : Z := 0x4771c.  Definition tfib_E_icpt_sendto : Z := 0x479e0.
Definition tfib_A_icpt_sigaltstack : Z := 0x479e0.  Definition tfib_E_icpt_sigaltstack : Z := 0x47c3c.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47d10.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47ec0.
Definition tfib_A_format_get_value_size : Z := 0x47ec0.  Definition tfib_E_format_get_value_size : Z := 0x48058.
Definition tfib_A_ioctl_table_fill : Z := 0x48c04.  Definition tfib_E_ioctl_table_fill : Z := 0x518dc.
Definition tfib_A_Sort : Z := 0x518dc.  Definition tfib_E_Sort : Z := 0x51a38.
Definition tfib_A_memset : Z := 0x51a38.  Definition tfib_E_memset : Z := 0x51a3c.
Definition tfib_A_memcpy : Z := 0x51a3c.  Definition tfib_E_memcpy : Z := 0x51a40.
Definition tfib_A_check_known : Z := 0x80af8.  Definition tfib_E_check_known : Z := 0x80b24.  Definition tfib_A_check_row : Z := 0x80b24.  Definition tfib_E_check_row : Z := 0x80b48.  Definition tfib_A_check_label : Z := 0x80b48.  Definition tfib_E_check_label : Z := 0x80b6c.  Definition tfib_A_reac_box_pin_parse : Z := 0x80ba4.  Definition tfib_E_reac_box_pin_parse : Z := 0x80f84.  Definition tfib_A_asan_module_dtor : Z := 0x80f84.  Definition tfib_E_asan_module_dtor : Z := 0x80fb4.  Definition tfib_A_fuzz_catalogue_row : Z := 0x80fb4.  Definition tfib_E_fuzz_catalogue_row : Z := 0x8107c.  Definition tfib_A_reac_box_catalogue : Z := 0x8107c.  Definition tfib_E_reac_box_catalogue : Z := 0x810d0.
Definition tfib_A_icpt_memset : Z := 0x51edc.  Definition tfib_E_icpt_memset : Z := 0x521cc.
Definition tfib_A_icpt_memcpy : Z := 0x521cc.  Definition tfib_E_icpt_memcpy : Z := 0x527bc.
Definition tfib_A_InitializeMemintrinsicInterceptors : Z := 0x527bc.  Definition tfib_E_InitializeMemintrinsicInterceptors : Z := 0x527f4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x527f4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x527f8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x527f8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x527fc.
Definition tfib_A_FindDynamicShadowStart : Z := 0x527fc.  Definition tfib_E_FindDynamicShadowStart : Z := 0x5285c.
Definition tfib_A_MemToShadow_510c4 : Z := 0x528a8.  Definition tfib_E_MemToShadow_510c4 : Z := 0x529e4.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x529e4.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x529e8.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x529e8.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52b50.
Definition tfib_A_free : Z := 0x52b50.  Definition tfib_E_free : Z := 0x52b54.
Definition tfib_A_malloc : Z := 0x52b54.  Definition tfib_E_malloc : Z := 0x52b58.
Definition tfib_A_icpt_free : Z := 0x52b58.  Definition tfib_E_icpt_free : Z := 0x52d28.
Definition tfib_A_icpt_malloc : Z := 0x52d28.  Definition tfib_E_icpt_malloc : Z := 0x52e84.
Definition tfib_A_DlSymAllocator_Allocate : Z := 0x52e84.  Definition tfib_E_DlSymAllocator_Allocate : Z := 0x52f50.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52f50.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52f54.
Definition tfib_A_TwoLevelMap_Create_51770 : Z := 0x52f54.  Definition tfib_E_TwoLevelMap_Create_51770 : Z := 0x53054.
Definition tfib_A_HeapProfile_Print : Z := 0x5337c.  Definition tfib_E_HeapProfile_Print : Z := 0x534e8.
Definition tfib_A_SetCanPoisonMemory : Z := 0x539d0.  Definition tfib_E_SetCanPoisonMemory : Z := 0x539e0.
Definition tfib_A_CanPoisonMemory : Z := 0x539e0.  Definition tfib_E_CanPoisonMemory : Z := 0x539f4.
Definition tfib_A_PoisonShadow : Z := 0x539f4.  Definition tfib_E_PoisonShadow : Z := 0x53ef0.
Definition tfib_A_MemToShadow_5270c : Z := 0x53ef0.  Definition tfib_E_MemToShadow_5270c : Z := 0x5402c.
Definition tfib_A_asan_poison_memory_region : Z := 0x5402c.  Definition tfib_E_asan_poison_memory_region : Z := 0x541cc.
Definition tfib_A_asan_unpoison_memory_region : Z := 0x541cc.  Definition tfib_E_asan_unpoison_memory_region : Z := 0x5434c.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5437c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x546c0.
Definition tfib_A_AsanTSDInit : Z := 0x54ae0.  Definition tfib_E_AsanTSDInit : Z := 0x54b5c.
Definition tfib_A_AsanTSDGet : Z := 0x54b5c.  Definition tfib_E_AsanTSDGet : Z := 0x54b9c.
Definition tfib_A_AsanTSDSet : Z := 0x54b9c.  Definition tfib_E_AsanTSDSet : Z := 0x54bdc.
Definition tfib_A_PlatformTSDDtor : Z := 0x54bdc.  Definition tfib_E_PlatformTSDDtor : Z := 0x54c60.
Definition tfib_A_InstallAtForkHandler : Z := 0x54c60.  Definition tfib_E_InstallAtForkHandler : Z := 0x54c7c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54cdc.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54d20.
Definition tfib_A_ReportDeadlySignal : Z := 0x55438.  Definition tfib_E_ReportDeadlySignal : Z := 0x55644.
Definition tfib_A_ReportDoubleFree : Z := 0x55d4c.  Definition tfib_E_ReportDoubleFree : Z := 0x55fdc.
Definition tfib_A_ReportGenericError : Z := 0x578b8.  Definition tfib_E_ReportGenericError : Z := 0x58174.
Definition tfib_A_AsanInited : Z := 0x58900.  Definition tfib_E_AsanInited : Z := 0x58918.
Definition tfib_A_asan_report_load1 : Z := 0x58918.  Definition tfib_E_asan_report_load1 : Z := 0x58968.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58968.  Definition tfib_E_asan_report_exp_load1 : Z := 0x589b8.
Definition tfib_A_asan_report_load2 : Z := 0x589b8.  Definition tfib_E_asan_report_load2 : Z := 0x58a08.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58a08.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58a58.
Definition tfib_A_asan_report_load4 : Z := 0x58a58.  Definition tfib_E_asan_report_load4 : Z := 0x58aa8.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58aa8.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58af8.
Definition tfib_A_asan_report_load8 : Z := 0x58af8.  Definition tfib_E_asan_report_load8 : Z := 0x58b48.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58b48.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58b98.
Definition tfib_A_asan_report_load16 : Z := 0x58b98.  Definition tfib_E_asan_report_load16 : Z := 0x58be8.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58be8.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58c38.
Definition tfib_A_asan_report_store1 : Z := 0x58c38.  Definition tfib_E_asan_report_store1 : Z := 0x58c88.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58c88.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58cd8.
Definition tfib_A_asan_report_store2 : Z := 0x58cd8.  Definition tfib_E_asan_report_store2 : Z := 0x58d28.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58d28.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58d78.
Definition tfib_A_asan_report_store4 : Z := 0x58d78.  Definition tfib_E_asan_report_store4 : Z := 0x58dc8.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58dc8.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58e18.
Definition tfib_A_asan_report_store8 : Z := 0x58e18.  Definition tfib_E_asan_report_store8 : Z := 0x58e68.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58e68.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58eb8.
Definition tfib_A_asan_report_store16 : Z := 0x58eb8.  Definition tfib_E_asan_report_store16 : Z := 0x58f08.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58f08.  Definition tfib_E_asan_report_exp_store16 : Z := 0x58f58.
Definition tfib_A_asan_report_load_n : Z := 0x58f58.  Definition tfib_E_asan_report_load_n : Z := 0x58fa8.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58fa8.  Definition tfib_E_asan_report_exp_load_n : Z := 0x58ff8.
Definition tfib_A_asan_report_store_n : Z := 0x58ff8.  Definition tfib_E_asan_report_store_n : Z := 0x59048.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59048.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59098.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59098.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59118.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59118.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x594cc.
Definition tfib_A_AsanInitInternal : Z := 0x5955c.  Definition tfib_E_AsanInitInternal : Z := 0x59810.
Definition tfib_A_TryAsanInitFromRtl : Z := 0x59810.  Definition tfib_E_TryAsanInitFromRtl : Z := 0x598b0.
Definition tfib_A_asan_set_death_callback : Z := 0x59a78.  Definition tfib_E_asan_set_death_callback : Z := 0x59a7c.
Definition tfib_A_asan_init : Z := 0x59a7c.  Definition tfib_E_asan_init : Z := 0x59b10.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59b10.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59b14.
Definition tfib_A_CheckSealedAddressSpace : Z := 0x59b14.  Definition tfib_E_CheckSealedAddressSpace : Z := 0x59b78.
Definition tfib_A_OnLowLevelAllocate : Z := 0x59cec.  Definition tfib_E_OnLowLevelAllocate : Z := 0x59cf4.
Definition tfib_A_force_interface_symbols : Z := 0x59d78.  Definition tfib_E_force_interface_symbols : Z := 0x5a0a0.
Definition tfib_A_SealedReserveShadow : Z := 0x5a0a0.  Definition tfib_E_SealedReserveShadow : Z := 0x5a280.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a280.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a588.
Definition tfib_A_SetMallocContextSize : Z := 0x5a588.  Definition tfib_E_SetMallocContextSize : Z := 0x5a598.
Definition tfib_A_GetMallocContextSize : Z := 0x5a598.  Definition tfib_E_GetMallocContextSize : Z := 0x5a5a8.
Definition tfib_A_BufferedStackTrace_UnwindImpl : Z := 0x5a5a8.  Definition tfib_E_BufferedStackTrace_UnwindImpl : Z := 0x5a6f8.
Definition tfib_A_FlushToDeadThreadStats : Z := 0x5aad8.  Definition tfib_E_FlushToDeadThreadStats : Z := 0x5ad78.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b1dc.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b214.
Definition tfib_A_asan_default_suppressions : Z := 0x5b4bc.  Definition tfib_E_asan_default_suppressions : Z := 0x5b4c8.
Definition tfib_A_InitializeSuppressions : Z := 0x5b4c8.  Definition tfib_E_InitializeSuppressions : Z := 0x5b554.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b554.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b5bc.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b5bc.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b634.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b634.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b69c.
Definition tfib_A_IsAddrSuppressed : Z := 0x5b69c.  Definition tfib_E_IsAddrSuppressed : Z := 0x5b7e8.
Definition tfib_A_AsanThreadContext_OnCreated : Z := 0x5ba74.  Definition tfib_E_AsanThreadContext_OnCreated : Z := 0x5ba80.
Definition tfib_A_AsanThread_Create : Z := 0x5bc00.  Definition tfib_E_AsanThread_Create : Z := 0x5bd9c.
Definition tfib_A_AsanThread_Destroy : Z := 0x5bdf8.  Definition tfib_E_AsanThread_Destroy : Z := 0x5c010.
Definition tfib_A_GetCurrentThread : Z := 0x5c010.  Definition tfib_E_GetCurrentThread : Z := 0x5c030.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c030.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c1d4.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c1d4.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c22c.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c22c.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c284.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c284.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c4b4.
Definition tfib_A_AsanThread_Init : Z := 0x5c4b4.  Definition tfib_E_AsanThread_Init : Z := 0x5c8a8.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5c8a8.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5c9b4.
Definition tfib_A_CreateMainThread : Z := 0x5c9e8.  Definition tfib_E_CreateMainThread : Z := 0x5caf8.
Definition tfib_A_SetCurrentThread : Z := 0x5caf8.  Definition tfib_E_SetCurrentThread : Z := 0x5cbd8.
Definition tfib_A_MemToShadow_5b5f8 : Z := 0x5cddc.  Definition tfib_E_MemToShadow_5b5f8 : Z := 0x5cf18.
Definition tfib_A_ThreadContextBase_OnStarted : Z := 0x5dbec.  Definition tfib_E_ThreadContextBase_OnStarted : Z := 0x5dbf0.
Definition tfib_A_GetAsanThreadContext : Z := 0x5dbf8.  Definition tfib_E_GetAsanThreadContext : Z := 0x5de38.
Definition tfib_A_internal_allocator : Z := 0x5e08c.  Definition tfib_E_internal_allocator : Z := 0x5e1e4.
Definition tfib_A_GetGlobalLowLevelAllocator : Z := 0x5e3d0.  Definition tfib_E_GetGlobalLowLevelAllocator : Z := 0x5e3dc.
Definition tfib_A_LowLevelAllocator_Allocate : Z := 0x5e3dc.  Definition tfib_E_LowLevelAllocator_Allocate : Z := 0x5e528.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e528.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e574.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e574.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e580.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e5b0.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e5bc.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e5bc.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e5c8.
Definition tfib_A_IsRssLimitExceeded : Z := 0x5e5c8.  Definition tfib_E_IsRssLimitExceeded : Z := 0x5e5d8.
Definition tfib_A_CombinedAllocator_Allocate_5ce00 : Z := 0x5e5e4.  Definition tfib_E_CombinedAllocator_Allocate_5ce00 : Z := 0x5e8b0.
Definition tfib_A_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5e8b0.  Definition tfib_E_LargeMmapAllocator_Allocate_5d0cc : Z := 0x5ec70.
Definition tfib_A_SealedSetInitFrame : Z := 0x5fbcc.  Definition tfib_E_SealedSetInitFrame : Z := 0x5fbd8.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fbd8.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fcb0.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fcb0.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fd4c.
Definition tfib_A_IncreaseTotalMmap : Z := 0x60270.  Definition tfib_E_IncreaseTotalMmap : Z := 0x602b4.
Definition tfib_A_DecreaseTotalMmap : Z := 0x602b4.  Definition tfib_E_DecreaseTotalMmap : Z := 0x602d8.
Definition tfib_A_CacheBinaryName : Z := 0x6052c.  Definition tfib_E_CacheBinaryName : Z := 0x60640.
Definition tfib_A_RunMallocHooks : Z := 0x607e4.  Definition tfib_E_RunMallocHooks : Z := 0x6089c.
Definition tfib_A_sanitizer_malloc_hook : Z := 0x6089c.  Definition tfib_E_sanitizer_malloc_hook : Z := 0x608a0.
Definition tfib_A_RunFreeHooks : Z := 0x608a0.  Definition tfib_E_RunFreeHooks : Z := 0x6094c.
Definition tfib_A_sanitizer_ignore_free_hook : Z := 0x6094c.  Definition tfib_E_sanitizer_ignore_free_hook : Z := 0x60954.
Definition tfib_A_sanitizer_free_hook : Z := 0x60954.  Definition tfib_E_sanitizer_free_hook : Z := 0x60958.
Definition tfib_A_WaitForDebugger : Z := 0x60980.  Definition tfib_E_WaitForDebugger : Z := 0x609cc.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60c90.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x60ed0.
Definition tfib_A_sanitizer_set_report_path : Z := 0x614cc.  Definition tfib_E_sanitizer_set_report_path : Z := 0x614e4.
Definition tfib_A_CommonFlags_SetDefaults : Z := 0x614e4.  Definition tfib_E_CommonFlags_SetDefaults : Z := 0x61628.
Definition tfib_A_CommonFlags_CopyFrom : Z := 0x61628.  Definition tfib_E_CommonFlags_CopyFrom : Z := 0x61630.
Definition tfib_A_RegisterCommonFlags : Z := 0x61978.  Definition tfib_E_RegisterCommonFlags : Z := 0x62c1c.
Definition tfib_A_InitializeCommonFlags : Z := 0x62c1c.  Definition tfib_E_InitializeCommonFlags : Z := 0x62c40.
Definition tfib_A_FlagParser_parse_flag : Z := 0x630f4.  Definition tfib_E_FlagParser_parse_flag : Z := 0x63404.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63404.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63548.
Definition tfib_A_FlagParser_ParseString : Z := 0x63548.  Definition tfib_E_FlagParser_ParseString : Z := 0x6363c.
Definition tfib_A_FlagParser_RegisterHandler : Z := 0x637d0.  Definition tfib_E_FlagParser_RegisterHandler : Z := 0x63830.
Definition tfib_A_FlagParser_FlagParser : Z := 0x63830.  Definition tfib_E_FlagParser_FlagParser : Z := 0x63870.
Definition tfib_A_internal_atoll : Z := 0x63870.  Definition tfib_E_internal_atoll : Z := 0x6395c.
Definition tfib_A_internal_simple_strtoll : Z := 0x6395c.  Definition tfib_E_internal_simple_strtoll : Z := 0x63ab8.
Definition tfib_A_internal_memchr : Z := 0x63ab8.  Definition tfib_E_internal_memchr : Z := 0x63ad8.
Definition tfib_A_internal_memcmp : Z := 0x63ad8.  Definition tfib_E_internal_memcmp : Z := 0x63b10.
Definition tfib_A_sanitizer_internal_memcpy : Z := 0x63b10.  Definition tfib_E_sanitizer_internal_memcpy : Z := 0x63b34.
Definition tfib_A_sanitizer_internal_memmove : Z := 0x63b34.  Definition tfib_E_sanitizer_internal_memmove : Z := 0x63b8c.
Definition tfib_A_sanitizer_internal_memset : Z := 0x63b8c.  Definition tfib_E_sanitizer_internal_memset : Z := 0x63bec.
Definition tfib_A_internal_strcspn : Z := 0x63bec.  Definition tfib_E_internal_strcspn : Z := 0x63c40.
Definition tfib_A_internal_strchr : Z := 0x63c40.  Definition tfib_E_internal_strchr : Z := 0x63c74.
Definition tfib_A_internal_strdup : Z := 0x63c74.  Definition tfib_E_internal_strdup : Z := 0x63ce0.
Definition tfib_A_internal_strlen : Z := 0x63ce0.  Definition tfib_E_internal_strlen : Z := 0x63cfc.
Definition tfib_A_internal_strcmp : Z := 0x63cfc.  Definition tfib_E_internal_strcmp : Z := 0x63d40.
Definition tfib_A_internal_strncmp : Z := 0x63d40.  Definition tfib_E_internal_strncmp : Z := 0x63d8c.
Definition tfib_A_internal_strchrnul : Z := 0x63d8c.  Definition tfib_E_internal_strchrnul : Z := 0x63dd4.
Definition tfib_A_internal_strrchr : Z := 0x63dd4.  Definition tfib_E_internal_strrchr : Z := 0x63e14.
Definition tfib_A_internal_strnlen : Z := 0x63f44.  Definition tfib_E_internal_strnlen : Z := 0x63f74.
Definition tfib_A_internal_strncpy : Z := 0x63fb8.  Definition tfib_E_internal_strncpy : Z := 0x64028.
Definition tfib_A_internal_strstr : Z := 0x64028.  Definition tfib_E_internal_strstr : Z := 0x640bc.
Definition tfib_A_mem_is_zero : Z := 0x640bc.  Definition tfib_E_mem_is_zero : Z := 0x64170.
Definition tfib_A_internal_sigprocmask : Z := 0x64170.  Definition tfib_E_internal_sigprocmask : Z := 0x64180.
Definition tfib_A_BlockSignals : Z := 0x64180.  Definition tfib_E_BlockSignals : Z := 0x64360.
Definition tfib_A_internal_iserror : Z := 0x6436c.  Definition tfib_E_internal_iserror : Z := 0x6438c.
Definition tfib_A_internal_mmap : Z := 0x6438c.  Definition tfib_E_internal_mmap : Z := 0x64398.
Definition tfib_A_internal_munmap : Z := 0x64398.  Definition tfib_E_internal_munmap : Z := 0x643a4.
Definition tfib_A_internal_mprotect : Z := 0x643a4.  Definition tfib_E_internal_mprotect : Z := 0x643b4.
Definition tfib_A_internal_madvise : Z := 0x643b4.  Definition tfib_E_internal_madvise : Z := 0x643e0.
Definition tfib_A_internal_close : Z := 0x643e0.  Definition tfib_E_internal_close : Z := 0x643ec.
Definition tfib_A_internal_open : Z := 0x643ec.  Definition tfib_E_internal_open : Z := 0x64410.
Definition tfib_A_internal_read : Z := 0x64410.  Definition tfib_E_internal_read : Z := 0x64448.
Definition tfib_A_internal_write : Z := 0x64448.  Definition tfib_E_internal_write : Z := 0x64480.
Definition tfib_A_internal_ftruncate : Z := 0x64480.  Definition tfib_E_internal_ftruncate : Z := 0x644b8.
Definition tfib_A_internal_dup : Z := 0x644b8.  Definition tfib_E_internal_dup : Z := 0x644c4.
Definition tfib_A_internal_dup2 : Z := 0x644c4.  Definition tfib_E_internal_dup2 : Z := 0x644d4.
Definition tfib_A_internal_unlink : Z := 0x644d4.  Definition tfib_E_internal_unlink : Z := 0x644ec.
Definition tfib_A_internal_sched_yield : Z := 0x644ec.  Definition tfib_E_internal_sched_yield : Z := 0x644f8.
Definition tfib_A_internal_usleep : Z := 0x644f8.  Definition tfib_E_internal_usleep : Z := 0x64544.
Definition tfib_A_internal_execve : Z := 0x64544.  Definition tfib_E_internal_execve : Z := 0x64550.
Definition tfib_A_internal_exit : Z := 0x64550.  Definition tfib_E_internal_exit : Z := 0x64564.
Definition tfib_A_FileExists : Z := 0x64564.  Definition tfib_E_FileExists : Z := 0x645e4.
Definition tfib_A_DirExists : Z := 0x645e4.  Definition tfib_E_DirExists : Z := 0x64648.
Definition tfib_A_GetTid : Z := 0x64648.  Definition tfib_E_GetTid : Z := 0x64654.
Definition tfib_A_GetEnv : Z := 0x64654.  Definition tfib_E_GetEnv : Z := 0x64784.
Definition tfib_A_FutexWait : Z := 0x64888.  Definition tfib_E_FutexWait : Z := 0x648ac.
Definition tfib_A_FutexWake : Z := 0x648ac.  Definition tfib_E_FutexWake : Z := 0x648d0.
Definition tfib_A_internal_ptrace : Z := 0x648d0.  Definition tfib_E_internal_ptrace : Z := 0x648dc.
Definition tfib_A_internal_waitpid : Z := 0x648dc.  Definition tfib_E_internal_waitpid : Z := 0x648ec.
Definition tfib_A_internal_getpid : Z := 0x648ec.  Definition tfib_E_internal_getpid : Z := 0x648f8.
Definition tfib_A_internal_getppid : Z := 0x648f8.  Definition tfib_E_internal_getppid : Z := 0x64904.
Definition tfib_A_internal_prctl : Z := 0x64904.  Definition tfib_E_internal_prctl : Z := 0x64910.
Definition tfib_A_internal_sigaltstack : Z := 0x64910.  Definition tfib_E_internal_sigaltstack : Z := 0x6491c.
Definition tfib_A_internal_fork : Z := 0x6491c.  Definition tfib_E_internal_fork : Z := 0x64934.
Definition tfib_A_internal_sigaction_norestorer : Z := 0x64934.  Definition tfib_E_internal_sigaction_norestorer : Z := 0x64a60.
Definition tfib_A_ThreadLister_ListThreads : Z := 0x64c38.  Definition tfib_E_ThreadLister_ListThreads : Z := 0x65034.
Definition tfib_A_GetMaxUserVirtualAddress : Z := 0x651a0.  Definition tfib_E_GetMaxUserVirtualAddress : Z := 0x652b8.
Definition tfib_A_GetPageSize : Z := 0x652b8.  Definition tfib_E_GetPageSize : Z := 0x652c0.
Definition tfib_A_ReadBinaryName : Z := 0x652c0.  Definition tfib_E_ReadBinaryName : Z := 0x6536c.
Definition tfib_A_ReadLongProcessName : Z := 0x6536c.  Definition tfib_E_ReadLongProcessName : Z := 0x6548c.
Definition tfib_A_internal_clone : Z := 0x65554.  Definition tfib_E_internal_clone : Z := 0x655d4.
Definition tfib_A_GetHandleSignalMode : Z := 0x655d4.  Definition tfib_E_GetHandleSignalMode : Z := 0x65630.
Definition tfib_A_internal_start_thread : Z := 0x65630.  Definition tfib_E_internal_start_thread : Z := 0x656fc.
Definition tfib_A_InitializePlatformEarly : Z := 0x657f8.  Definition tfib_E_InitializePlatformEarly : Z := 0x657fc.
Definition tfib_A_CheckASLR : Z := 0x657fc.  Definition tfib_E_CheckASLR : Z := 0x65800.
Definition tfib_A_GetMmapGranularity : Z := 0x65a4c.  Definition tfib_E_GetMmapGranularity : Z := 0x65a50.
Definition tfib_A_ErrorIsOOM : Z := 0x65a50.  Definition tfib_E_ErrorIsOOM : Z := 0x65a5c.
Definition tfib_A_MmapOrDie : Z := 0x65a5c.  Definition tfib_E_MmapOrDie : Z := 0x65b68.
Definition tfib_A_MmapNamed : Z := 0x65b68.  Definition tfib_E_MmapNamed : Z := 0x65bdc.
Definition tfib_A_UnmapOrDie : Z := 0x65bdc.  Definition tfib_E_UnmapOrDie : Z := 0x65c58.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65c58.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65d68.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65f94.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66098.
Definition tfib_A_MmapFixedOrDie : Z := 0x66098.  Definition tfib_E_MmapFixedOrDie : Z := 0x660a4.
Definition tfib_A_MmapFixedImpl : Z := 0x660a4.  Definition tfib_E_MmapFixedImpl : Z := 0x6621c.
Definition tfib_A_MmapFixedOrDieOnFatalError : Z := 0x6621c.  Definition tfib_E_MmapFixedOrDieOnFatalError : Z := 0x66228.
Definition tfib_A_CloseFile : Z := 0x66414.  Definition tfib_E_CloseFile : Z := 0x66418.
Definition tfib_A_GetNamedMappingFd : Z := 0x66738.  Definition tfib_E_GetNamedMappingFd : Z := 0x66944.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66efc.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66f08.
Definition tfib_A_Printf : Z := 0x66f0c.  Definition tfib_E_Printf : Z := 0x66f58.
Definition tfib_A_SharedPrintfCode : Z := 0x66f58.  Definition tfib_E_SharedPrintfCode : Z := 0x66fb4.
Definition tfib_A_Report : Z := 0x66fb4.  Definition tfib_E_Report : Z := 0x67000.
Definition tfib_A_SuppressionContext_SuppressionContext : Z := 0x68af8.  Definition tfib_E_SuppressionContext_SuppressionContext : Z := 0x68b54.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68b54.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68d90.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68d90.  Definition tfib_E_SuppressionContext_Parse : Z := 0x690b4.
Definition tfib_A_sanitizer_get_dtls_size : Z := 0x69654.  Definition tfib_E_sanitizer_get_dtls_size : Z := 0x69724.
Definition tfib_A_DTLS_on_tls_get_addr : Z := 0x69724.  Definition tfib_E_DTLS_on_tls_get_addr : Z := 0x69a74.
Definition tfib_A_DTLS_Get : Z := 0x69a74.  Definition tfib_E_DTLS_Get : Z := 0x69a84.
Definition tfib_A_ThreadContextBase_ThreadContextBase : Z := 0x69cc0.  Definition tfib_E_ThreadContextBase_ThreadContextBase : Z := 0x69d04.
Definition tfib_A_ThreadRegistry_ThreadRegistry : Z := 0x69d04.  Definition tfib_E_ThreadRegistry_ThreadRegistry : Z := 0x69d64.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69d64.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a1dc.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6aa9c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6adc0.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6adc8.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_695e4 : Z := 0x6aecc.
Definition tfib_A_AddDieCallback : Z := 0x6b67c.  Definition tfib_E_AddDieCallback : Z := 0x6b704.
Definition tfib_A_Die : Z := 0x6b7c8.  Definition tfib_E_Die : Z := 0x6b888.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b888.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b894.
Definition tfib_A_CheckFailed : Z := 0x6b894.  Definition tfib_E_CheckFailed : Z := 0x6b94c.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6bfa4.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c09c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c09c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c1c8.
Definition tfib_A_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c3f0.  Definition tfib_E_GLOBAL_sub_I_sanitizer_common_libcdep_cpp : Z := 0x6c46c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c4a0.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c788.
Definition tfib_A_InitTlsSize : Z := 0x6c788.  Definition tfib_E_InitTlsSize : Z := 0x6c78c.
Definition tfib_A_GetTls : Z := 0x6c78c.  Definition tfib_E_GetTls : Z := 0x6cb7c.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6cb7c.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6cc4c.
Definition tfib_A_AndroidLogInit : Z := 0x6d030.  Definition tfib_E_AndroidLogInit : Z := 0x6d034.
Definition tfib_A_MonotonicNanoTime : Z := 0x6d064.  Definition tfib_E_MonotonicNanoTime : Z := 0x6d0ac.
Definition tfib_A_MapDynamicShadow : Z := 0x6d0ac.  Definition tfib_E_MapDynamicShadow : Z := 0x6d2f8.
Definition tfib_A_InitializePlatformCommonFlags : Z := 0x6d2f8.  Definition tfib_E_InitializePlatformCommonFlags : Z := 0x6d2fc.
Definition tfib_A_CollectStaticTlsBlocks : Z := 0x6d2fc.  Definition tfib_E_CollectStaticTlsBlocks : Z := 0x6d408.
Definition tfib_A_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d408.  Definition tfib_E_InternalMmapVectorNoCtor_Realloc_6bc24 : Z := 0x6d50c.
Definition tfib_A_GetThreadSelf : Z := 0x6d788.  Definition tfib_E_GetThreadSelf : Z := 0x6d78c.
Definition tfib_A_DontDumpShadowMemory : Z := 0x6d830.  Definition tfib_E_DontDumpShadowMemory : Z := 0x6d850.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d850.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d8f0.
Definition tfib_A_Atexit : Z := 0x6d93c.  Definition tfib_E_Atexit : Z := 0x6d940.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d97c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6da40.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6da40.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6dac8.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6dac8.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6db40.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6db40.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dc24.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dce0.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6de14.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6e04c.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6e17c.
Definition tfib_A_MmapFixedSuperNoReserve : Z := 0x6e17c.  Definition tfib_E_MmapFixedSuperNoReserve : Z := 0x6e1dc.
Definition tfib_A_ReservedAddressRange_Init : Z := 0x6e1dc.  Definition tfib_E_ReservedAddressRange_Init : Z := 0x6e2a8.
Definition tfib_A_MmapNoAccess : Z := 0x6e2bc.  Definition tfib_E_MmapNoAccess : Z := 0x6e2dc.
Definition tfib_A_ReservedAddressRange_Map : Z := 0x6e2dc.  Definition tfib_E_ReservedAddressRange_Map : Z := 0x6e350.
Definition tfib_A_SealedRepairReservation : Z := 0x6e350.  Definition tfib_E_SealedRepairReservation : Z := 0x6e428.
Definition tfib_A_ReservedAddressRange_MapOrDie : Z := 0x6e428.  Definition tfib_E_ReservedAddressRange_MapOrDie : Z := 0x6e438.
Definition tfib_A_InitializeCoverage : Z := 0x6fc30.  Definition tfib_E_InitializeCoverage : Z := 0x6fc74.
Definition tfib_A_sanitizer_cov_dump : Z := 0x6fc74.  Definition tfib_E_sanitizer_cov_dump : Z := 0x6fca4.
Definition tfib_A_StackStore_Store : Z := 0x700d8.  Definition tfib_E_StackStore_Store : Z := 0x701fc.
Definition tfib_A_StackStore_Alloc : Z := 0x701fc.  Definition tfib_E_StackStore_Alloc : Z := 0x70330.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x70be4.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x70c98.
Definition tfib_A_StackDepotNode_store : Z := 0x723ec.  Definition tfib_E_StackDepotNode_store : Z := 0x72448.
Definition tfib_A_StackDepotPut : Z := 0x726d4.  Definition tfib_E_StackDepotPut : Z := 0x726f4.
Definition tfib_A_StackDepotBase_Put : Z := 0x726f4.  Definition tfib_E_StackDepotBase_Put : Z := 0x72978.
Definition tfib_A_StackDepotGet : Z := 0x72978.  Definition tfib_E_StackDepotGet : Z := 0x72a88.
Definition tfib_A_StackDepotBase_lock : Z := 0x72e68.  Definition tfib_E_StackDepotBase_lock : Z := 0x72ef8.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x72ef8.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x72ff8.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73058.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73060.
Definition tfib_A_BufferedStackTrace_UnwindFast : Z := 0x73060.  Definition tfib_E_BufferedStackTrace_UnwindFast : Z := 0x731c0.
Definition tfib_A_BufferedStackTrace_PopStackFrames : Z := 0x731c0.  Definition tfib_E_BufferedStackTrace_PopStackFrames : Z := 0x73234.
Definition tfib_A_BufferedStackTrace_Unwind : Z := 0x736bc.  Definition tfib_E_BufferedStackTrace_Unwind : Z := 0x737d4.
Definition tfib_A_SymbolizerProcess_GetEnvP : Z := 0x76820.  Definition tfib_E_SymbolizerProcess_GetEnvP : Z := 0x76824.
Definition tfib_A_InternalSymbolizer_Flush : Z := 0x77ff8.  Definition tfib_E_InternalSymbolizer_Flush : Z := 0x77ffc.
Definition tfib_A_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79a24.  Definition tfib_E_BufferedStackTrace_UnwindSlow_78240 : Z := 0x79ae0.
Definition tfib_A_Unwind_Trace : Z := 0x79ae0.  Definition tfib_E_Unwind_Trace : Z := 0x79bb8.
Definition tfib_A_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x79bb8.  Definition tfib_E_BufferedStackTrace_UnwindSlow_783d4 : Z := 0x79e2c.
Definition tfib_A_lsan_Flags_SetDefaults : Z := 0x7a158.  Definition tfib_E_lsan_Flags_SetDefaults : Z := 0x7a19c.
Definition tfib_A_lsan_RegisterLsanFlags : Z := 0x7a19c.  Definition tfib_E_lsan_RegisterLsanFlags : Z := 0x7a56c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a83c.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a8f4.
Definition tfib_A_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bc4c.  Definition tfib_E_lsan_DoRecoverableLeakCheckVoid : Z := 0x7bc50.
Definition tfib_A_lsan_register_root_region : Z := 0x7c858.  Definition tfib_E_lsan_register_root_region : Z := 0x7cb88.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cb88.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d010.
Definition tfib_A_lsan_default_options : Z := 0x7d010.  Definition tfib_E_lsan_default_options : Z := 0x7d01c.
Definition tfib_A_lsan_DisabledInThisThread : Z := 0x7fbd4.  Definition tfib_E_lsan_DisabledInThisThread : Z := 0x7fbec.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7ff70.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7ffec.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7ffec.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x8009c.
Definition tfib_A_ubsan_Flags_SetDefaults : Z := 0x8009c.  Definition tfib_E_ubsan_Flags_SetDefaults : Z := 0x800b4.
Definition tfib_A_ubsan_RegisterUbsanFlags : Z := 0x800b4.  Definition tfib_E_ubsan_RegisterUbsanFlags : Z := 0x801fc.
Definition tfib_A_ubsan_default_options : Z := 0x801fc.  Definition tfib_E_ubsan_default_options : Z := 0x80208.
Definition tfib_A_asan_default_options : Z := 0x80208.  Definition tfib_E_asan_default_options : Z := 0x80214.
Definition tfib_A_main : Z := 0x80214.  Definition tfib_E_main : Z := 0x804d8.
Definition tfib_A_target_alloc_init : Z := 0x804d8.  Definition tfib_E_target_alloc_init : Z := 0x804dc.
Definition tfib_A_target_alloc_count : Z := 0x804dc.  Definition tfib_E_target_alloc_count : Z := 0x804e4.
Definition tfib_A_target_run : Z := 0x804e4.  Definition tfib_E_target_run : Z := 0x8063c.
Definition tfib_A_oft_exit_guard : Z := 0x8063c.  Definition tfib_E_oft_exit_guard : Z := 0x8066c.
Definition tfib_A_emit_printf : Z := 0x8066c.  Definition tfib_E_emit_printf : Z := 0x806b4.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x806b4.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x80af8.
Definition tfib_A_asan_module_ctor : Z := 0x80b6c.  Definition tfib_E_asan_module_ctor : Z := 0x80ba4.
Definition tfib_A_extenddftf2 : Z := 0x810e0.  Definition tfib_E_extenddftf2 : Z := 0x81270.
Definition tfib_A_sysconf : Z := 0x86ec0.  Definition tfib_E_sysconf : Z := 0x870e8.
Definition tfib_A_init : Z := 0x870e8.  Definition tfib_E_init : Z := 0x870ec.
Definition tfib_A_init_libc : Z := 0x870ec.  Definition tfib_E_init_libc : Z := 0x87318.
Definition tfib_A_libc_start_init : Z := 0x87318.  Definition tfib_E_libc_start_init : Z := 0x87364.
Definition tfib_A_libc_start_main : Z := 0x87364.  Definition tfib_E_libc_start_main : Z := 0x873c4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x873c4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8740c.
Definition tfib_A_static_init_tls : Z := 0x874e4.  Definition tfib_E_static_init_tls : Z := 0x87794.
Definition tfib_A_init_ssp : Z := 0x87794.  Definition tfib_E_init_ssp : Z := 0x877f4.
Definition tfib_A_stack_chk_fail : Z := 0x877f4.  Definition tfib_E_stack_chk_fail : Z := 0x877fc.
Definition tfib_A_abort : Z := 0x87844.  Definition tfib_E_abort : Z := 0x878d8.
Definition tfib_A_Exit : Z := 0x878d8.  Definition tfib_E_Exit : Z := 0x878f4.
Definition tfib_A_funcs_on_exit : Z := 0x87924.  Definition tfib_E_funcs_on_exit : Z := 0x879ec.
Definition tfib_A_cxa_finalize : Z := 0x879ec.  Definition tfib_E_cxa_finalize : Z := 0x879f0.
Definition tfib_A_atexit : Z := 0x879f0.  Definition tfib_E_atexit : Z := 0x87ab4.
Definition tfib_A_libc_exit_fini_call : Z := 0x87ab4.  Definition tfib_E_libc_exit_fini_call : Z := 0x87ab8.
Definition tfib_A_fini : Z := 0x87ab8.  Definition tfib_E_fini : Z := 0x87abc.
Definition tfib_A_libc_exit_fini : Z := 0x87abc.  Definition tfib_E_libc_exit_fini : Z := 0x87b08.
Definition tfib_A_exit : Z := 0x87b08.  Definition tfib_E_exit : Z := 0x87b7c.
Definition tfib_A_open : Z := 0x87d7c.  Definition tfib_E_open : Z := 0x87e60.
Definition tfib_A_syscall_ret : Z := 0x87e60.  Definition tfib_E_syscall_ret : Z := 0x87e98.
Definition tfib_A_dl_iterate_phdr : Z := 0x87e98.  Definition tfib_E_dl_iterate_phdr : Z := 0x88040.
Definition tfib_A_libc_calloc : Z := 0x88604.  Definition tfib_E_libc_calloc : Z := 0x8873c.
Definition tfib_A_libc_malloc : Z := 0x8873c.  Definition tfib_E_libc_malloc : Z := 0x88740.
Definition tfib_A_libc_free : Z := 0x88740.  Definition tfib_E_libc_free : Z := 0x8890c.
Definition tfib_A_get_meta : Z := 0x8890c.  Definition tfib_E_get_meta : Z := 0x88a1c.
Definition tfib_A_malloc_alloc_meta : Z := 0x88df4.  Definition tfib_E_malloc_alloc_meta : Z := 0x890cc.
Definition tfib_A_libc_malloc_impl : Z := 0x890cc.  Definition tfib_E_libc_malloc_impl : Z := 0x8943c.
Definition tfib_A_alloc_slot : Z := 0x8943c.  Definition tfib_E_alloc_slot : Z := 0x89ce0.
Definition tfib_A_enframe : Z := 0x89ce0.  Definition tfib_E_enframe : Z := 0x89e30.
Definition tfib_A_malloc_allzerop : Z := 0x89e30.  Definition tfib_E_malloc_allzerop : Z := 0x89fa8.
Definition tfib_A_getrlimit : Z := 0x8bc58.  Definition tfib_E_getrlimit : Z := 0x8bd50.
Definition tfib_A_getrusage : Z := 0x8bd50.  Definition tfib_E_getrusage : Z := 0x8bd78.
Definition tfib_A_setrlimit : Z := 0x8bd78.  Definition tfib_E_setrlimit : Z := 0x8be40.
Definition tfib_A_mmap : Z := 0x8c268.  Definition tfib_E_mmap : Z := 0x8c354.
Definition tfib_A_mprotect : Z := 0x8c354.  Definition tfib_E_mprotect : Z := 0x8c39c.
Definition tfib_A_munmap : Z := 0x8c470.  Definition tfib_E_munmap : Z := 0x8c4b8.
Definition tfib_A_sched_yield : Z := 0x8c77c.  Definition tfib_E_sched_yield : Z := 0x8c7a0.
Definition tfib_A_raise : Z := 0x8c7fc.  Definition tfib_E_raise : Z := 0x8c874.
Definition tfib_A_libc_sigaction : Z := 0x8c874.  Definition tfib_E_libc_sigaction : Z := 0x8ca48.
Definition tfib_A_musl_sigaltstack : Z := 0x8cb40.  Definition tfib_E_musl_sigaltstack : Z := 0x8cbcc.
Definition tfib_A_dprintf : Z := 0x8d1a8.  Definition tfib_E_dprintf : Z := 0x8d20c.
Definition tfib_A_lockfile : Z := 0x8d20c.  Definition tfib_E_lockfile : Z := 0x8d308.
Definition tfib_A_unlockfile : Z := 0x8d308.  Definition tfib_E_unlockfile : Z := 0x8d368.
Definition tfib_A_stdio_read : Z := 0x8cef8.  Definition tfib_E_stdio_read : Z := 0x8d010.
Definition tfib_A_stdio_write : Z := 0x8d018.  Definition tfib_E_stdio_write : Z := 0x8d1a8.
Definition tfib_A_aio_close : Z := 0x8cec8.  Definition tfib_E_aio_close : Z := 0x8cecc.
Definition tfib_A_stdio_close : Z := 0x8cecc.  Definition tfib_E_stdio_close : Z := 0x8cef8.
Definition tfib_A_fwritex : Z := 0x8d79c.  Definition tfib_E_fwritex : Z := 0x8d8d4.
Definition tfib_A_musl_fwrite : Z := 0x8d8d4.  Definition tfib_E_musl_fwrite : Z := 0x8d98c.
Definition tfib_A_towrite : Z := 0x8d98c.  Definition tfib_E_towrite : Z := 0x8d9e0.
Definition tfib_A_stdio_exit : Z := 0x8d5f8.  Definition tfib_E_stdio_exit : Z := 0x8d79c.
Definition tfib_A_ofl_lock : Z := 0x8d9e0.  Definition tfib_E_ofl_lock : Z := 0x8da10.
Definition tfib_A_musl_vfprintf : Z := 0x8db5c.  Definition tfib_E_musl_vfprintf : Z := 0x8dd0c.
Definition tfib_A_printf_core : Z := 0x8dd0c.  Definition tfib_E_printf_core : Z := 0x8eb3c.
Definition tfib_A_pop_arg : Z := 0x8eb3c.  Definition tfib_E_pop_arg : Z := 0x8ec70.
Definition tfib_A_pad : Z := 0x8ec70.  Definition tfib_E_pad : Z := 0x8ed44.
Definition tfib_A_fmt_fp : Z := 0x8ed44.  Definition tfib_E_fmt_fp : Z := 0x9040c.
Definition tfib_A_lctrans : Z := 0x88258.  Definition tfib_E_lctrans : Z := 0x8825c.
Definition tfib_A_musl_wctomb : Z := 0x8c5e4.  Definition tfib_E_musl_wctomb : Z := 0x8c608.
Definition tfib_A_musl_wcrtomb : Z := 0x8c4b8.  Definition tfib_E_musl_wcrtomb : Z := 0x8c5e4.
Definition tfib_A_fpclassifyl : Z := 0x8a848.  Definition tfib_E_fpclassifyl : Z := 0x8a88c.
Definition tfib_A_letf2 : Z := 0x8a080.  Definition tfib_E_letf2 : Z := 0x8a148.
Definition tfib_A_multf3 : Z := 0x8a148.  Definition tfib_E_multf3 : Z := 0x8a848.
Definition tfib_A_floatsitf : Z := 0x8b0a4.  Definition tfib_E_floatsitf : Z := 0x8b1ac.
Definition tfib_A_scalbn : Z := 0x8bab0.  Definition tfib_E_scalbn : Z := 0x8bb48.
Definition tfib_A_subtf3 : Z := 0x8b094.  Definition tfib_E_subtf3 : Z := 0x8b0a4.
Definition tfib_A_addtf3 : Z := 0x8a88c.  Definition tfib_E_addtf3 : Z := 0x8b058.
Definition tfib_A_fe_getround : Z := 0x8b058.  Definition tfib_E_fe_getround : Z := 0x8b088.
Definition tfib_A_fixunstfsi : Z := 0x90414.  Definition tfib_E_fixunstfsi : Z := 0x904a8.
Definition tfib_A_floatunsitf : Z := 0x904a8.  Definition tfib_E_floatunsitf : Z := 0x90594.
Definition tfib_A_fixtfsi : Z := 0x8bb48.  Definition tfib_E_fixtfsi : Z := 0x8bbf0.
Definition tfib_A_divtf3 : Z := 0x8b1ac.  Definition tfib_E_divtf3 : Z := 0x8bab0.
Definition tfib_A_musl_vprintf : Z := 0x90c6c.  Definition tfib_E_musl_vprintf : Z := 0x90c88.
Definition tfib_A_stdout_write : Z := 0x8da1c.  Definition tfib_E_stdout_write : Z := 0x8dabc.
Definition tfib_A_musl_memcmp : Z := 0x912f0.  Definition tfib_E_musl_memcmp : Z := 0x91320.
Definition tfib_A_musl_memcpy : Z := 0x91320.  Definition tfib_E_musl_memcpy : Z := 0x91724.
Definition tfib_A_musl_memset : Z := 0x91724.  Definition tfib_E_musl_memset : Z := 0x9181c.
Definition tfib_A_musl_strchr : Z := 0x9181c.  Definition tfib_E_musl_strchr : Z := 0x91858.
Definition tfib_A_strchrnul : Z := 0x91858.  Definition tfib_E_strchrnul : Z := 0x91938.
Definition tfib_A_musl_strlen : Z := 0x91a88.  Definition tfib_E_musl_strlen : Z := 0x91b18.
Definition tfib_A_musl_strnlen : Z := 0x91d24.  Definition tfib_E_musl_strnlen : Z := 0x91d68.
Definition tfib_A_musl_memchr : Z := 0x91224.  Definition tfib_E_musl_memchr : Z := 0x912f0.
Definition tfib_A_lock : Z := 0x91d68.  Definition tfib_E_lock : Z := 0x91ff0.
Definition tfib_A_unlock : Z := 0x91ff0.  Definition tfib_E_unlock : Z := 0x92064.
Definition tfib_A_sccp : Z := 0x92064.  Definition tfib_E_sccp : Z := 0x92088.
Definition tfib_A_syscall_cp : Z := 0x92088.  Definition tfib_E_syscall_cp : Z := 0x9208c.
Definition tfib_A_tls_get_addr : Z := 0x9208c.  Definition tfib_E_tls_get_addr : Z := 0x920b0.
Definition tfib_A_pthread_atfork : Z := 0x920c8.  Definition tfib_E_pthread_atfork : Z := 0x9216c.
Definition tfib_A_mremap : Z := 0x8c39c.  Definition tfib_E_mremap : Z := 0x8c470.
Definition tfib_A_pthread_getspecific : Z := 0x93140.  Definition tfib_E_pthread_getspecific : Z := 0x9315c.
Definition tfib_A_pthread_key_create : Z := 0x934e8.  Definition tfib_E_pthread_key_create : Z := 0x935bc.
Definition tfib_A_pthread_rwlock_unlock : Z := 0x93860.  Definition tfib_E_pthread_rwlock_unlock : Z := 0x93904.
Definition tfib_A_pthread_rwlock_wrlock : Z := 0x93904.  Definition tfib_E_pthread_rwlock_wrlock : Z := 0x9390c.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x9390c.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x93a20.
Definition tfib_A_pthread_rwlock_trywrlock : Z := 0x93a20.  Definition tfib_E_pthread_rwlock_trywrlock : Z := 0x93a4c.
Definition tfib_A_pthread_setspecific : Z := 0x93a84.  Definition tfib_E_pthread_setspecific : Z := 0x93ab8.
Definition tfib_A_set_thread_area : Z := 0x93ac0.  Definition tfib_E_set_thread_area : Z := 0x93acc.
Definition tfib_A_pthread_testcancel : Z := 0x93ab8.  Definition tfib_E_pthread_testcancel : Z := 0x93abc.

Definition tfib_A_musl_clock_gettime : Z := 0x943ec.  Definition tfib_E_musl_clock_gettime : Z := 0x944a4.
Definition tfib_A_close : Z := 0x96abc.  Definition tfib_E_close : Z := 0x96b10.

Definition tfib_A_vm_wait : Z := 0x940fc.  Definition tfib_E_vm_wait : Z := 0x9414c.
Definition tfib_D_str_sealed : Z := 0x1181b.
Definition tfib_D_init_array_0_3 : Z := 0x97bd0.
Definition tfib_D_fini_array_0 : Z := 0x97bf0.
Definition tfib_D_GOT_common_flags : Z := 0x99160.
Definition tfib_D_GOT_flags : Z := 0x99168.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x99170.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x99178.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x99180.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x99188.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x99cd8.
Definition tfib_D_GOT_environ : Z := 0x99e00.
Definition tfib_D_REAL_read : Z := 0x9aeb8.
Definition tfib_D_REAL_memcpy : Z := 0x9afe0.
Definition tfib_D_REAL_memset : Z := 0x9afe8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0x9e098.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0x9eef8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa16f8.
Definition tfib_D_asan_inited : Z := 0xa23d8.
Definition tfib_D_replace_intrin_cached : Z := 0xa23d9.
Definition tfib_D_kHighMemEnd : Z := 0xa23e0.
Definition tfib_D_kMidMemBeg : Z := 0xa23e8.
Definition tfib_D_kMidMemEnd : Z := 0xa23f0.
Definition tfib_D_malloc_context_size : Z := 0xa23fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x133228.
Definition tfib_D_libc : Z := 0x5f4928.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f6000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x3031c.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63b8c.
Definition tfib_at_x_imemcpy : Z := 0x63b10.
Definition tfib_at_x_memset : Z := 0x91724.
Definition tfib_at_x_memcpy : Z := 0x91320.
Definition tfib_at_x_memiszero : Z := 0x640bc.
Definition tfib_at_x_istrncpy : Z := 0x63fb8.
Definition tfib_at_x_sealed : Z := 0x1181b.
Definition tfib_at_x_popfree : Z := 0x36708.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x87124.
Definition tfib_at_x_envscan_k : Z := 0x87130.
Definition tfib_at_x_pnscan : Z := 0x871e8.
Definition tfib_at_x_pnscan_k : Z := 0x871f4.
Definition tfib_at_stops_more : list Z := (0x3437c :: 0x359a0 :: 0x53e98 :: 0x5a250 :: 0x5a264 :: 0x5a278 :: 0x5fc08 :: 0x5fcd8 :: 0x6d204 :: 0x6e110 :: 0x6e2a0 :: 0x77ff8 :: nil)%list.
