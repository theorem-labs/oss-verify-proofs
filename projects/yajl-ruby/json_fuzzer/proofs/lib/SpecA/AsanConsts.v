(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record aimg_consts := mkAIC {
  aic_wrap_free : Z;   (* [comment removed for export] *)
  aic_wrap_malloc : Z;   (* [comment removed for export] *)
  aic_wrap_realloc : Z;   (* [comment removed for export] *)
  aic_malloc_interceptor : Z;   (* [comment removed for export] *)
  aic_free_interceptor : Z;   (* [comment removed for export] *)
  aic_realloc_interceptor : Z;   (* [comment removed for export] *)
  aic_malloc_pc : Z;   (* [comment removed for export] *)
  aic_free_pc : Z;   (* [comment removed for export] *)
  aic_realloc_pc : Z;   (* [comment removed for export] *)
  aic_TryAsanInitFromRtl : Z;   (* [comment removed for export] *)
  aic_AsanInited : Z;   (* [comment removed for export] *)
  aic_GetMallocContextSize : Z;   (* [comment removed for export] *)
  aic_GetCurrentPc : Z;   (* [comment removed for export] *)
  aic_UnwindImpl : Z;   (* [comment removed for export] *)
  aic_Unwind : Z;   (* [comment removed for export] *)
  aic_UnwindFast : Z;   (* [comment removed for export] *)
  aic_GetCurrentThread : Z;   (* [comment removed for export] *)
  aic_AsanTSDGet : Z;   (* [comment removed for export] *)
  aic_musl_tss_get : Z;   (* [comment removed for export] *)
  aic_stack_top : Z;   (* [comment removed for export] *)
  aic_stack_bottom : Z;   (* [comment removed for export] *)
  aic_GetThreadStackTopAndBottom : Z;   (* [comment removed for export] *)
  aic_GetCurrentThreadStats : Z;   (* [comment removed for export] *)
  aic_asan_malloc : Z;   (* [comment removed for export] *)
  aic_Allocate : Z;   (* [comment removed for export] *)
  aic_RZSize2Log : Z;   (* [comment removed for export] *)
  aic_CombinedAllocate : Z;   (* [comment removed for export] *)
  aic_Refill : Z;   (* [comment removed for export] *)
  aic_GetFromAllocator : Z;   (* [comment removed for export] *)
  aic_PopulateFreeArray : Z;   (* [comment removed for export] *)
  aic_EnsureFreeArraySpace : Z;   (* [comment removed for export] *)
  aic_RAR_Map : Z;   (* [comment removed for export] *)
  aic_RAR_MapOrDie : Z;   (* [comment removed for export] *)
  aic_MmapFixedOrDieOnFatalError : Z;   (* [comment removed for export] *)
  aic_MmapFixedOrDie : Z;   (* [comment removed for export] *)
  aic_MmapFixedImpl : Z;   (* [comment removed for export] *)
  aic_GetNamedMappingFd : Z;   (* [comment removed for export] *)
  aic_LargeMmapAllocate : Z;   (* [comment removed for export] *)
  aic_MmapOrDieOnFatalError : Z;   (* [comment removed for export] *)
  aic_MmapOrDie : Z;   (* [comment removed for export] *)
  aic_MmapNoReserveOrDie : Z;   (* [comment removed for export] *)
  aic_MmapNamed : Z;   (* [comment removed for export] *)
  aic_internal_mmap : Z;   (* [comment removed for export] *)
  aic_internal_munmap : Z;   (* [comment removed for export] *)
  aic_internal_mprotect : Z;   (* [comment removed for export] *)
  aic_internal_madvise : Z;   (* [comment removed for export] *)
  aic_internal_sched_yield : Z;   (* [comment removed for export] *)
  aic_internal_iserror : Z;   (* [comment removed for export] *)
  aic_internal_gettid : Z;   (* [comment removed for export] *)
  aic_internal__exit : Z;   (* [comment removed for export] *)
  aic_IncreaseTotalMmap : Z;   (* [comment removed for export] *)
  aic_DecreaseTotalMmap : Z;   (* [comment removed for export] *)
  aic_PoisonShadow : Z;   (* [comment removed for export] *)
  aic_CanPoisonMemory : Z;   (* [comment removed for export] *)
  aic_ReserveShadowMemoryRange : Z;   (* [comment removed for export] *)
  aic_MmapFixedSuperNoReserve : Z;   (* [comment removed for export] *)
  aic_MmapFixedNoReserve : Z;   (* [comment removed for export] *)
  aic_DontDumpShadowMemory : Z;   (* [comment removed for export] *)
  aic_GetPageSize : Z;   (* [comment removed for export] *)
  aic_GetMmapGranularity : Z;   (* [comment removed for export] *)
  aic_musl_sysconf : Z;   (* [comment removed for export] *)
  aic_StackDepotPut : Z;   (* [comment removed for export] *)
  aic_StackDepotBase_Put : Z;   (* [comment removed for export] *)
  aic_depot_lock : Z;   (* [comment removed for export] *)
  aic_depot_find : Z;   (* [comment removed for export] *)
  aic_StackDepotNode_store : Z;   (* [comment removed for export] *)
  aic_StackStore_Store : Z;   (* [comment removed for export] *)
  aic_StackStore_Alloc : Z;   (* [comment removed for export] *)
  aic_TwoLevelMap_Create : Z;   (* [comment removed for export] *)
  aic_BlockInfo_Create : Z;   (* [comment removed for export] *)
  aic_CompressThread_NewWorkNotify : Z;   (* [comment removed for export] *)
  aic_RunMallocHooks : Z;   (* [comment removed for export] *)
  aic_RunFreeHooks : Z;   (* [comment removed for export] *)
  aic_lsan_DisabledInThisThread : Z;   (* [comment removed for export] *)
  aic_internal_allocator : Z;   (* [comment removed for export] *)
  aic_InternalAlloc : Z;   (* [comment removed for export] *)
  aic_asan_free : Z;   (* [comment removed for export] *)
  aic_Deallocate : Z;   (* [comment removed for export] *)
  aic_QuarantineChunk : Z;   (* [comment removed for export] *)
  aic_QuarantinePut : Z;   (* [comment removed for export] *)
  aic_Enqueue : Z;   (* [comment removed for export] *)
  aic_QuarantineDrain : Z;   (* [comment removed for export] *)
  aic_QuarantineRecycle : Z;   (* [comment removed for export] *)
  aic_MergeBatches : Z;   (* [comment removed for export] *)
  aic_DoRecycle : Z;   (* [comment removed for export] *)
  aic_QCB_Recycle : Z;   (* [comment removed for export] *)
  aic_GetBlockBegin : Z;   (* [comment removed for export] *)
  aic_LocalCache_Deallocate : Z;   (* [comment removed for export] *)
  aic_LocalCache_Drain : Z;   (* [comment removed for export] *)
  aic_ReturnToAllocator : Z;   (* [comment removed for export] *)
  aic_FreeArrayDieHelper : Z;   (* [comment removed for export] *)
  aic_MaybeReleaseToOS : Z;   (* [comment removed for export] *)
  aic_LargeMmapDeallocate : Z;   (* [comment removed for export] *)
  aic_OnUnmap : Z;   (* [comment removed for export] *)
  aic_FlushUnneededASanShadowMemory : Z;   (* [comment removed for export] *)
  aic_ReleaseMemoryPagesToOS : Z;   (* [comment removed for export] *)
  aic_UnmapOrDie : Z;   (* [comment removed for export] *)
  aic_asan_realloc : Z;   (* [comment removed for export] *)
  aic_Reallocate : Z;   (* [comment removed for export] *)
  aic_internal_memcpy : Z;   (* [comment removed for export] *)
  aic_internal_memset : Z;   (* [comment removed for export] *)
  aic_musl_memcpy : Z;   (* [comment removed for export] *)
  aic_musl_memset : Z;   (* [comment removed for export] *)
  aic_errno_location : Z;   (* [comment removed for export] *)
  aic_AllocatorMayReturnNull : Z;   (* [comment removed for export] *)
  aic_RssLimitExceeded : Z;   (* [comment removed for export] *)
  aic_SetAllocatorOutOfMemory : Z;   (* [comment removed for export] *)
  aic_SetErrnoOnNull : Z;   (* [comment removed for export] *)
  aic_Report : Z;   (* [comment removed for export] *)
  aic_CheckFailed : Z;   (* [comment removed for export] *)
  aic_Die : Z;   (* [comment removed for export] *)
  aic_Abort : Z;   (* [comment removed for export] *)
  aic_ReportDoubleFree : Z;   (* [comment removed for export] *)
  aic_ReportFreeNotMalloced : Z;   (* [comment removed for export] *)
  aic_ReportNewDeleteTypeMismatch : Z;   (* [comment removed for export] *)
  aic_ReportAllocTypeMismatch : Z;   (* [comment removed for export] *)
  aic_ReportAllocationSizeTooBig : Z;   (* [comment removed for export] *)
  aic_ReportOutOfMemory : Z;   (* [comment removed for export] *)
  aic_ReportMmapFailureAndDie : Z;   (* [comment removed for export] *)
  aic_ReportMunmapFailureAndDie : Z;   (* [comment removed for export] *)
  aic_LockSlow : Z;   (* [comment removed for export] *)
  aic_SemaphoreWait : Z;   (* [comment removed for export] *)
  aic_SemaphorePost : Z;   (* [comment removed for export] *)
  aic_MonotonicNanoTime : Z;   (* [comment removed for export] *)
  aic_spin_freearray : Z;   (* [comment removed for export] *)
  aic_spin_batch : Z;   (* [comment removed for export] *)
  aic_spin_poisonshadow : Z;   (* [comment removed for export] *)
  aic_spin_mmapdie : Z;   (* [comment removed for export] *)
  aic_spin_munmapdie : Z;   (* [comment removed for export] *)
  aic_spin_fixednoreserve : Z;   (* [comment removed for export] *)
  aic_spin_rar_init : Z;   (* [comment removed for export] *)
  aic_spin_fa514 : Z;   (* [comment removed for export] *)
  aic_main : Z;   (* [comment removed for export] *)
  aic_target_run : Z;   (* [comment removed for export] *)
  aic_LLVMFuzzerTestOneInput : Z;   (* [comment removed for export] *)
  aic_instance : Z;   (* [comment removed for export] *)
  aic_asan_flags : Z;   (* [comment removed for export] *)
  aic_common_flags : Z;   (* [comment removed for export] *)
  aic_shadow_dyn_addr : Z;   (* [comment removed for export] *)
  aic_kHighMemEnd : Z;   (* [comment removed for export] *)
  aic_kMidMemBeg : Z;   (* [comment removed for export] *)
  aic_kMidMemEnd : Z;   (* [comment removed for export] *)
  aic_can_poison_memory : Z;   (* [comment removed for export] *)
  aic_asan_inited : Z;   (* [comment removed for export] *)
  aic_malloc_context_size : Z;   (* [comment removed for export] *)
  aic_unknown_thread_stats : Z;   (* [comment removed for export] *)
  aic_internal_alloc_initialized : Z;   (* [comment removed for export] *)
  aic_internal_alloc_init_mu : Z;   (* [comment removed for export] *)
  aic_internal_allocator_instance : Z;   (* [comment removed for export] *)
  aic_stack_anchor : Z;   (* [comment removed for export] *)
  aic_page_size_cached : Z;   (* [comment removed for export] *)
  aic_dying_flag : Z;   (* [comment removed for export] *)
  aic_malloc_hook_table : Z;   (* [comment removed for export] *)
  aic_theDepot : Z;   (* [comment removed for export] *)
  aic_n_uniq_ids : Z;   (* [comment removed for export] *)
  aic_stackStore : Z;   (* [comment removed for export] *)
  aic_total_mmaped : Z;   (* [comment removed for export] *)
  aic_REAL_memcpy_var : Z;   (* [comment removed for export] *)
  aic_REAL_memset_var : Z;   (* [comment removed for export] *)
  aic_GOT_pagesize : Z;   (* [comment removed for export] *)
  aic_GOT_common_flags : Z;   (* [comment removed for export] *)
  aic_GOT_asan_flags : Z;   (* [comment removed for export] *)
  aic_GOT_shadow : Z;   (* [comment removed for export] *)
  aic_GOT_kMidBeg : Z;   (* [comment removed for export] *)
  aic_GOT_kMidEnd : Z;   (* [comment removed for export] *)
  aic_GOT_kHighMemEnd : Z;   (* [comment removed for export] *)
  aic_GOT_REAL_memset : Z;   (* [comment removed for export] *)
  aic_GOT_REAL_memcpy : Z;   (* [comment removed for export] *)
  aic_GOT_report_file : Z;   (* [comment removed for export] *)
  aic_GOT_sealed : Z;   (* [comment removed for export] *)
  aic_GOT_dying : Z;   (* [comment removed for export] *)
  aic_GOT_stack_anchor : Z;   (* [comment removed for export] *)
  aic_kAllocBegMagic : Z;   (* [comment removed for export] *)
  aic_debruijn64 : Z;   (* [comment removed for export] *)
  aic_log2tab_a : Z;   (* [comment removed for export] *)
  aic_log2tab_b : Z;   (* [comment removed for export] *)
  aic_murmur_m : Z;   (* [comment removed for export] *)
  aic_murmur_seed1 : Z;   (* [comment removed for export] *)
  aic_murmur_seed2 : Z;   (* [comment removed for export] *)
  aic_sysconf_values : Z;   (* [comment removed for export] *)
  aic_read_stage : Z;   (* [comment removed for export] *)
  aic_GetMaxUserVirtualAddress : Z;   (* [comment removed for export] *)
  aic_InitializeShadowMemory : Z;   (* [comment removed for export] *)
  aic_AsanInitInternal : Z;   (* [comment removed for export] *)
  aic_sysconf : Z    (* [comment removed for export] *)
}.

Definition asan_ic : aimg_consts := {|
  aic_wrap_free := 0x54098;
  aic_wrap_malloc := 0x5409c;
  aic_wrap_realloc := 0x540a0;
  aic_malloc_interceptor := 0x54274;
  aic_free_interceptor := 0x540a4;
  aic_realloc_interceptor := 0x5449c;
  aic_malloc_pc := 0x5433c;
  aic_free_pc := 0x541dc;
  aic_realloc_pc := 0x545d8;
  aic_TryAsanInitFromRtl := 0x5b0a0;
  aic_AsanInited := 0x5a190;
  aic_GetMallocContextSize := 0x5be28;
  aic_GetCurrentPc := 0x748e8;
  aic_UnwindImpl := 0x5be38;
  aic_Unwind := 0x74f4c;
  aic_UnwindFast := 0x748f0;
  aic_GetCurrentThread := 0x5d8a0;
  aic_AsanTSDGet := 0x563ec;
  aic_musl_tss_get := 0x9f984;
  aic_stack_top := 0x5da64;
  aic_stack_bottom := 0x5dabc;
  aic_GetThreadStackTopAndBottom := 0x6dd30;
  aic_GetCurrentThreadStats := 0x5ca6c;
  aic_asan_malloc := 0x32ba4;
  aic_Allocate := 0x32c00;
  aic_RZSize2Log := 0x38168;
  aic_CombinedAllocate := 0x372a0;
  aic_Refill := 0x379f0;
  aic_GetFromAllocator := 0x37af0;
  aic_PopulateFreeArray := 0x37df8;
  aic_EnsureFreeArraySpace := 0x35abc;
  aic_RAR_Map := 0x6fb6c;
  aic_RAR_MapOrDie := 0x6fcb8;
  aic_MmapFixedOrDieOnFatalError := 0x67aac;
  aic_MmapFixedOrDie := 0x67928;
  aic_MmapFixedImpl := 0x67934;
  aic_GetNamedMappingFd := 0x67fc8;
  aic_LargeMmapAllocate := 0x37578;
  aic_MmapOrDieOnFatalError := 0x674e8;
  aic_MmapOrDie := 0x672ec;
  aic_MmapNoReserveOrDie := 0x67824;
  aic_MmapNamed := 0x673f8;
  aic_internal_mmap := 0x65c1c;
  aic_internal_munmap := 0x65c28;
  aic_internal_mprotect := 0x65c34;
  aic_internal_madvise := 0x65c44;
  aic_internal_sched_yield := 0x65d7c;
  aic_internal_iserror := 0x65bfc;
  aic_internal_gettid := 0x65ed8;
  aic_internal__exit := 0x65de0;
  aic_IncreaseTotalMmap := 0x61b00;
  aic_DecreaseTotalMmap := 0x61b44;
  aic_PoisonShadow := 0x55284;
  aic_CanPoisonMemory := 0x55270;
  aic_ReserveShadowMemoryRange := 0x6d92c;
  aic_MmapFixedSuperNoReserve := 0x6fa0c;
  aic_MmapFixedNoReserve := 0x6f8dc;
  aic_DontDumpShadowMemory := 0x6f0c0;
  aic_GetPageSize := 0x66b48;
  aic_GetMmapGranularity := 0x672dc;
  aic_musl_sysconf := 0x910c8;
  aic_StackDepotPut := 0x73f64;
  aic_StackDepotBase_Put := 0x73f84;
  aic_depot_lock := 0x746f8;
  aic_depot_find := 0x74644;
  aic_StackDepotNode_store := 0x73c7c;
  aic_StackStore_Store := 0x71968;
  aic_StackStore_Alloc := 0x71a8c;
  aic_TwoLevelMap_Create := 0x74788;
  aic_BlockInfo_Create := 0x72474;
  aic_CompressThread_NewWorkNotify := 0x73cd8;
  aic_RunMallocHooks := 0x62074;
  aic_RunFreeHooks := 0x62130;
  aic_lsan_DisabledInThisThread := 0x81464;
  aic_internal_allocator := 0x5f91c;
  aic_InternalAlloc := 0x5fa74;
  aic_asan_free := 0x328c4;
  aic_Deallocate := 0x328ec;
  aic_QuarantineChunk := 0x36d94;
  aic_QuarantinePut := 0x36f0c;
  aic_Enqueue := 0x370bc;
  aic_QuarantineDrain := 0x34814;
  aic_QuarantineRecycle := 0x349b8;
  aic_MergeBatches := 0x34b9c;
  aic_DoRecycle := 0x34d20;
  aic_QCB_Recycle := 0x34e58;
  aic_GetBlockBegin := 0x350dc;
  aic_LocalCache_Deallocate := 0x3525c;
  aic_LocalCache_Drain := 0x355f0;
  aic_ReturnToAllocator := 0x35794;
  aic_FreeArrayDieHelper := 0x35c04;
  aic_MaybeReleaseToOS := 0x35c3c;
  aic_LargeMmapDeallocate := 0x35424;
  aic_OnUnmap := 0x53da4;
  aic_FlushUnneededASanShadowMemory := 0x53df0;
  aic_ReleaseMemoryPagesToOS := 0x6f01c;
  aic_UnmapOrDie := 0x6746c;
  aic_asan_realloc := 0x33588;
  aic_Reallocate := 0x33634;
  aic_internal_memcpy := 0x653a0;
  aic_internal_memset := 0x6541c;
  aic_musl_memcpy := 0x9dcdc;
  aic_musl_memset := 0x9e0e0;
  aic_errno_location := 0x91a04;
  aic_AllocatorMayReturnNull := 0x5fe30;
  aic_RssLimitExceeded := 0x5fe58;
  aic_SetAllocatorOutOfMemory := 0x5fe20;
  aic_SetErrnoOnNull := 0x6dcfc;
  aic_Report := 0x68844;
  aic_CheckFailed := 0x6d124;
  aic_Die := 0x6d058;
  aic_Abort := 0x6f180;
  aic_ReportDoubleFree := 0x575dc;
  aic_ReportFreeNotMalloced := 0x57ae8;
  aic_ReportNewDeleteTypeMismatch := 0x5786c;
  aic_ReportAllocTypeMismatch := 0x57d54;
  aic_ReportAllocationSizeTooBig := 0x58240;
  aic_ReportOutOfMemory := 0x586d4;
  aic_ReportMmapFailureAndDie := 0x61468;
  aic_ReportMunmapFailureAndDie := 0x61540;
  aic_LockSlow := 0x67198;
  aic_SemaphoreWait := 0x67258;
  aic_SemaphorePost := 0x672a8;
  aic_MonotonicNanoTime := 0x6e8f4;
  aic_spin_freearray := 0x35c28;
  aic_spin_batch := 0x3724c;
  aic_spin_poisonshadow := 0x55728;
  aic_spin_mmapdie := 0x61498;
  aic_spin_munmapdie := 0x61568;
  aic_spin_fixednoreserve := 0x6f9a0;
  aic_spin_rar_init := 0x6fb30;
  aic_spin_fa514 := 0x79888;
  aic_main := 0x81aa4;
  aic_target_run := 0x81d74;
  aic_LLVMFuzzerTestOneInput := 0x81f44;
  aic_instance := 0xaa518;
  aic_asan_flags := 0xab378;
  aic_common_flags := 0x13f6a8;
  aic_shadow_dyn_addr := 0xadb78;
  aic_kHighMemEnd := 0xae860;
  aic_kMidMemBeg := 0xae868;
  aic_kMidMemEnd := 0xae870;
  aic_can_poison_memory := 0xad3dc;
  aic_asan_inited := 0xae858;
  aic_malloc_context_size := 0xae87c;
  aic_unknown_thread_stats := 0xae8a8;
  aic_internal_alloc_initialized := 0x13d608;
  aic_internal_alloc_init_mu := 0x13d609;
  aic_internal_allocator_instance := 0xaed80;
  aic_stack_anchor := 0x13d610;
  aic_page_size_cached := 0x13d620;
  aic_dying_flag := 0x13f69c;
  aic_malloc_hook_table := 0x13f640;
  aic_theDepot := 0x18fa58;
  aic_n_uniq_ids := 0x58fa58;
  aic_stackStore := 0x17fa48;
  aic_total_mmaped := 0x13d638;
  aic_REAL_memcpy_var := 0xa6820;
  aic_REAL_memset_var := 0xa6828;
  aic_GOT_pagesize := 0xa4990;
  aic_GOT_common_flags := 0xa49a0;
  aic_GOT_asan_flags := 0xa49a8;
  aic_GOT_shadow := 0xa49b0;
  aic_GOT_kMidBeg := 0xa49b8;
  aic_GOT_kMidEnd := 0xa49c0;
  aic_GOT_kHighMemEnd := 0xa49c8;
  aic_GOT_REAL_memset := 0xa49d0;
  aic_GOT_REAL_memcpy := 0xa49d8;
  aic_GOT_report_file := 0xa49e8;
  aic_GOT_sealed := 0xa49f0;
  aic_GOT_dying := 0xa49f8;
  aic_GOT_stack_anchor := 0xa5560;
  aic_kAllocBegMagic := 0x10328;
  aic_debruijn64 := 0x103c8;
  aic_log2tab_a := 0x10438;
  aic_log2tab_b := 0x103f8;
  aic_murmur_m := 0x102e8;
  aic_murmur_seed1 := 0x10308;
  aic_murmur_seed2 := 0x103b0;
  aic_sysconf_values := 0x22830;
  aic_read_stage := 0x5d01d0;
  aic_GetMaxUserVirtualAddress := 0x66a30;
  aic_InitializeShadowMemory := 0x5bb10;
  aic_AsanInitInternal := 0x5adec;
  aic_sysconf := 0x910c8
|}.

Definition both_ic : aimg_consts := {|
  aic_wrap_free := 0x53ea4;
  aic_wrap_malloc := 0x53ea8;
  aic_wrap_realloc := 0x53eac;
  aic_malloc_interceptor := 0x54080;
  aic_free_interceptor := 0x53eb0;
  aic_realloc_interceptor := 0x542a8;
  aic_malloc_pc := 0x54148;
  aic_free_pc := 0x53fe8;
  aic_realloc_pc := 0x543e4;
  aic_TryAsanInitFromRtl := 0x5aeac;
  aic_AsanInited := 0x59f9c;
  aic_GetMallocContextSize := 0x5bc34;
  aic_GetCurrentPc := 0x746f4;
  aic_UnwindImpl := 0x5bc44;
  aic_Unwind := 0x74d58;
  aic_UnwindFast := 0x746fc;
  aic_GetCurrentThread := 0x5d6ac;
  aic_AsanTSDGet := 0x561f8;
  aic_musl_tss_get := 0xa0574;
  aic_stack_top := 0x5d870;
  aic_stack_bottom := 0x5d8c8;
  aic_GetThreadStackTopAndBottom := 0x6db3c;
  aic_GetCurrentThreadStats := 0x5c878;
  aic_asan_malloc := 0x329b0;
  aic_Allocate := 0x32a0c;
  aic_RZSize2Log := 0x37f74;
  aic_CombinedAllocate := 0x370ac;
  aic_Refill := 0x377fc;
  aic_GetFromAllocator := 0x378fc;
  aic_PopulateFreeArray := 0x37c04;
  aic_EnsureFreeArraySpace := 0x358c8;
  aic_RAR_Map := 0x6f978;
  aic_RAR_MapOrDie := 0x6fac4;
  aic_MmapFixedOrDieOnFatalError := 0x678b8;
  aic_MmapFixedOrDie := 0x67734;
  aic_MmapFixedImpl := 0x67740;
  aic_GetNamedMappingFd := 0x67dd4;
  aic_LargeMmapAllocate := 0x37384;
  aic_MmapOrDieOnFatalError := 0x672f4;
  aic_MmapOrDie := 0x670f8;
  aic_MmapNoReserveOrDie := 0x67630;
  aic_MmapNamed := 0x67204;
  aic_internal_mmap := 0x65a28;
  aic_internal_munmap := 0x65a34;
  aic_internal_mprotect := 0x65a40;
  aic_internal_madvise := 0x65a50;
  aic_internal_sched_yield := 0x65b88;
  aic_internal_iserror := 0x65a08;
  aic_internal_gettid := 0x65ce4;
  aic_internal__exit := 0x65bec;
  aic_IncreaseTotalMmap := 0x6190c;
  aic_DecreaseTotalMmap := 0x61950;
  aic_PoisonShadow := 0x55090;
  aic_CanPoisonMemory := 0x5507c;
  aic_ReserveShadowMemoryRange := 0x6d738;
  aic_MmapFixedSuperNoReserve := 0x6f818;
  aic_MmapFixedNoReserve := 0x6f6e8;
  aic_DontDumpShadowMemory := 0x6eecc;
  aic_GetPageSize := 0x66954;
  aic_GetMmapGranularity := 0x670e8;
  aic_musl_sysconf := 0x91cb8;
  aic_StackDepotPut := 0x73d70;
  aic_StackDepotBase_Put := 0x73d90;
  aic_depot_lock := 0x74504;
  aic_depot_find := 0x74450;
  aic_StackDepotNode_store := 0x73a88;
  aic_StackStore_Store := 0x71774;
  aic_StackStore_Alloc := 0x71898;
  aic_TwoLevelMap_Create := 0x74594;
  aic_BlockInfo_Create := 0x72280;
  aic_CompressThread_NewWorkNotify := 0x73ae4;
  aic_RunMallocHooks := 0x61e80;
  aic_RunFreeHooks := 0x61f3c;
  aic_lsan_DisabledInThisThread := 0x81270;
  aic_internal_allocator := 0x5f728;
  aic_InternalAlloc := 0x5f880;
  aic_asan_free := 0x326d0;
  aic_Deallocate := 0x326f8;
  aic_QuarantineChunk := 0x36ba0;
  aic_QuarantinePut := 0x36d18;
  aic_Enqueue := 0x36ec8;
  aic_QuarantineDrain := 0x34620;
  aic_QuarantineRecycle := 0x347c4;
  aic_MergeBatches := 0x349a8;
  aic_DoRecycle := 0x34b2c;
  aic_QCB_Recycle := 0x34c64;
  aic_GetBlockBegin := 0x34ee8;
  aic_LocalCache_Deallocate := 0x35068;
  aic_LocalCache_Drain := 0x353fc;
  aic_ReturnToAllocator := 0x355a0;
  aic_FreeArrayDieHelper := 0x35a10;
  aic_MaybeReleaseToOS := 0x35a48;
  aic_LargeMmapDeallocate := 0x35230;
  aic_OnUnmap := 0x53bb0;
  aic_FlushUnneededASanShadowMemory := 0x53bfc;
  aic_ReleaseMemoryPagesToOS := 0x6ee28;
  aic_UnmapOrDie := 0x67278;
  aic_asan_realloc := 0x33394;
  aic_Reallocate := 0x33440;
  aic_internal_memcpy := 0x651ac;
  aic_internal_memset := 0x65228;
  aic_musl_memcpy := 0x9e8cc;
  aic_musl_memset := 0x9ecd0;
  aic_errno_location := 0x925f4;
  aic_AllocatorMayReturnNull := 0x5fc3c;
  aic_RssLimitExceeded := 0x5fc64;
  aic_SetAllocatorOutOfMemory := 0x5fc2c;
  aic_SetErrnoOnNull := 0x6db08;
  aic_Report := 0x68650;
  aic_CheckFailed := 0x6cf30;
  aic_Die := 0x6ce64;
  aic_Abort := 0x6ef8c;
  aic_ReportDoubleFree := 0x573e8;
  aic_ReportFreeNotMalloced := 0x578f4;
  aic_ReportNewDeleteTypeMismatch := 0x57678;
  aic_ReportAllocTypeMismatch := 0x57b60;
  aic_ReportAllocationSizeTooBig := 0x5804c;
  aic_ReportOutOfMemory := 0x584e0;
  aic_ReportMmapFailureAndDie := 0x61274;
  aic_ReportMunmapFailureAndDie := 0x6134c;
  aic_LockSlow := 0x66fa4;
  aic_SemaphoreWait := 0x67064;
  aic_SemaphorePost := 0x670b4;
  aic_MonotonicNanoTime := 0x6e700;
  aic_spin_freearray := 0x35a34;
  aic_spin_batch := 0x37058;
  aic_spin_poisonshadow := 0x55534;
  aic_spin_mmapdie := 0x612a4;
  aic_spin_munmapdie := 0x61374;
  aic_spin_fixednoreserve := 0x6f7ac;
  aic_spin_rar_init := 0x6f93c;
  aic_spin_fa514 := 0x79694;
  aic_main := 0x818b0;
  aic_target_run := 0x81b80;
  aic_LLVMFuzzerTestOneInput := 0x81d50;
  aic_instance := 0xaaf58;
  aic_asan_flags := 0xabdb8;
  aic_common_flags := 0x1400e8;
  aic_shadow_dyn_addr := 0xae5b8;
  aic_kHighMemEnd := 0xaf2a0;
  aic_kMidMemBeg := 0xaf2a8;
  aic_kMidMemEnd := 0xaf2b0;
  aic_can_poison_memory := 0xade1c;
  aic_asan_inited := 0xaf298;
  aic_malloc_context_size := 0xaf2bc;
  aic_unknown_thread_stats := 0xaf2e8;
  aic_internal_alloc_initialized := 0x13e048;
  aic_internal_alloc_init_mu := 0x13e049;
  aic_internal_allocator_instance := 0xaf7c0;
  aic_stack_anchor := 0x13e050;
  aic_page_size_cached := 0x13e060;
  aic_dying_flag := 0x1400dc;
  aic_malloc_hook_table := 0x140080;
  aic_theDepot := 0x190498;
  aic_n_uniq_ids := 0x590498;
  aic_stackStore := 0x180488;
  aic_total_mmaped := 0x13e078;
  aic_REAL_memcpy_var := 0xa7400;
  aic_REAL_memset_var := 0xa7408;
  aic_GOT_pagesize := 0xa5580;
  aic_GOT_common_flags := 0xa5590;
  aic_GOT_asan_flags := 0xa5598;
  aic_GOT_shadow := 0xa55a0;
  aic_GOT_kMidBeg := 0xa55a8;
  aic_GOT_kMidEnd := 0xa55b0;
  aic_GOT_kHighMemEnd := 0xa55b8;
  aic_GOT_REAL_memset := 0xa55c0;
  aic_GOT_REAL_memcpy := 0xa55c8;
  aic_GOT_report_file := 0xa55d8;
  aic_GOT_sealed := 0xa55e0;
  aic_GOT_dying := 0xa55e8;
  aic_GOT_stack_anchor := 0xa6150;
  aic_kAllocBegMagic := 0x10328;
  aic_debruijn64 := 0x103c8;
  aic_log2tab_a := 0x10438;
  aic_log2tab_b := 0x103f8;
  aic_murmur_m := 0x102e8;
  aic_murmur_seed1 := 0x10308;
  aic_murmur_seed2 := 0x103b0;
  aic_sysconf_values := 0x225d8;
  aic_read_stage := 0x5d0c10;
  aic_GetMaxUserVirtualAddress := 0x6683c;
  aic_InitializeShadowMemory := 0x5b91c;
  aic_AsanInitInternal := 0x5abf8;
  aic_sysconf := 0x91cb8
|}.

(* [comment removed for export] *)
Definition kFlagsNoReplaceNoReserve : Z := 0x104022.   (* [comment removed for export] *)
Definition kMapFixedNoreplace : Z := 0x100000.
Definition kLowShadowMap  : Z * Z * Z * Z := (0x7fff7000, 2^28, 3, 0x104022).            (* [comment removed for export] *)
Definition kShadowGapMap  : Z * Z * Z * Z := (0x8fff7000, 2^41, 0, 0x104022).            (* [comment removed for export] *)
Definition kHighShadowMap : Z * Z * Z * Z := (0x2008fff7000, 0xdfff0001000, 3, 0x104022).  (* [comment removed for export] *)
Definition kHighMemEnd47 : Z := 2^47 - 1.

(* [comment removed for export] *)
Definition kMallocContextSize : Z := 30.
Definition kAllocBegMagicVal : Z := 0xCC6E96B9CC6E96B9.
Definition kInvalidTidShifted : Z := 0xFFFFFFFF00000000.   (* [comment removed for export] *)
Definition kChunkAllocated : Z := 2.
Definition kChunkQuarantine : Z := 3.
Definition kChunkInvalid : Z := 0.
Definition kHeaderByte1 : Z := 0x11.       (* [comment removed for export] *)
Definition kAsanHeapLeftRedzoneMagic : Z := 0xfa.
Definition kAsanHeapFreeMagic : Z := 0xfd.
Definition kStackSizeForThread : Z := 2^23.   (* [comment removed for export] *)
Definition kStackAnchorDelta : Z := 0xa0.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kFlagsAnonRw : Z := 0x22.          (* [comment removed for export] *)
Definition kFlagsFixedRw : Z := 0x32.         (* [comment removed for export] *)
Definition kFlagsFixedNoReserve : Z := 0x4032. (* [comment removed for export] *)
Definition kFlagsNoReserveRw : Z := 0x4022.    (* [comment removed for export] *)
Definition kDepotNodeBlockBytes : Z := 2^20.  (* [comment removed for export] *)
Definition kDepotNodesPerBlock : Z := 65536.
Definition kStoreBlockBytes : Z := 2^23.      (* [comment removed for export] *)
Definition kStoreBlockFrames : Z := 2^20.
Definition kProtRw : Z := 3.
Definition ENOMEM : Z := 12.

(* [comment removed for export] *)
Definition kThrStackTop : Z := 8.
Definition kThrStackBottom : Z := 16.
Definition kThrQCache : Z := 80.             (* [comment removed for export] *)
Definition kThrCache : Z := 208.             (* [comment removed for export] *)
Definition kPerClassSize : Z := 80.
Definition kThrCacheStats : Z := 208 + 2560. (* [comment removed for export] *)
Definition kThrStats : Z := 2800.            (* [comment removed for export] *)
Definition kThrUnwinding : Z := 3168.
(* [comment removed for export] *)
Definition kInsSpaceBeg : Z := 32.
Definition kInsReleaseInterval : Z := 40.
Definition kInsRegionInfo : Z := 48.
Definition kInsSecondary : Z := 64.          (* [comment removed for export] *)
Definition kInsNReserved : Z := 112.
Definition kInsNChunks : Z := 120.
Definition kInsChunksSorted : Z := 128.
Definition kInsSecStats : Z := 136.
Definition kInsSecMutex : Z := 680.
Definition kInsGlobalStats : Z := 688.        (* [comment removed for export] *)
Definition kInsQuarantine : Z := 728.         (* [comment removed for export] *)
Definition kInsQMutex : Z := 880.
Definition kInsQRecycleMutex : Z := 881.
Definition kInsQGlobal : Z := 888.
Definition kInsFallbackMutex : Z := 984.
Definition kInsMaxUserDefined : Z := 3616.
Definition kInsMinRedzone : Z := 3624.
Definition kInsMaxRedzone : Z := 3626.
Definition kInsAllocDeallocMismatch : Z := 3628.
(* [comment removed for export] *)
Definition kRegSize : Z := 128.
Definition kRegMutex : Z := 0.
Definition kRegNumFreed : Z := 16.
Definition kRegMappedFreeArray : Z := 24.
Definition kRegAllocatedUser : Z := 32.
Definition kRegAllocatedMeta : Z := 40.
Definition kRegMappedUser : Z := 48.
Definition kRegMappedMeta : Z := 56.
Definition kRegExhausted : Z := 68.
Definition kRegNAllocated : Z := 72.
Definition kRegNFreed : Z := 80.
(* [comment removed for export] *)
Definition kIaMemsets : list (Z * Z) := [(0x81008, 40); (8, 0x40000); (0x40040, 0xd80); (0x40dc0, 0x40248)].
Definition kIaPageSizeOff : Z := 0x40dc0.
Definition kIaChunksPtrOff : Z := 0x40dc8.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kDepotTabOff : Z := 0.             (* [comment removed for export] *)
Definition kDepotNUniq : Z := 0x400000.
Definition kDepotNodesMap1 : Z := 0x400010.
